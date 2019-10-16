module Core.Ltt

open FStar.OrdSet
open FStar.String
module T = FStar.Tactics

open Core.Weaken
open Core.Fc
open Core.Name

(** A predicate that guarentees that a natural number is
    within bounds for a list. *)
val valid_index_in : nat -> list 'a -> Tot Type0
let valid_index_in idx l = idx < List.length l

(** Verified way to to get the element at an index that's guarenteed to
    be within bounds. *)
private val element_at : l:list 'a -> idx:nat{idx `valid_index_in` l} -> Tot 'a
let rec element_at l idx =
  match l, idx with
  | x :: xs, 0 -> x
  | x :: xs, _ -> element_at xs (idx-1)

private val name_of : l:list local_name -> idx:nat{idx `valid_index_in` l} -> Tot local_name
let rec name_of l idx = element_at l idx

val is_bound_var : local_name -> nat -> list local_name -> Tot Type0
let is_bound_var n idx ns = idx `valid_index_in` ns /\ n = name_of ns idx

type var_index (n:local_name) (vars:list local_name) =
  idx:nat{is_bound_var n idx vars}

type bound_var (vars:list local_name) =
  | BoundVar : #bound_name:local_name
             -> index:var_index bound_name vars
             -> bound_var vars

(** Binders are parameterized by the term representation to
    make them easier to re-use for other representations. *)
type binder (exp:Type) =
  | Lam : ty:exp -> binder exp
  | Let : value:exp -> ty:exp -> binder exp
  | Pi : ty:exp -> binder exp

(** Get the type that a binder binds a variable to be. *)
val binder_ty : binder 'a -> Tot 'a
let binder_ty = function
  | Lam ty -> ty
  | Let _ ty -> ty
  | Pi ty -> ty

(** Map over the expressions in a binder. *)
val map_binder : ('a -> Tot 'b) -> binder 'a -> Tot (binder 'b)
let map_binder f = function
  | Lam ty -> Lam (f ty)
  | Let v ty -> Let (f v) (f ty)
  | Pi ty -> Pi (f ty)

(** Implementation of `weaken_ns` for `binder`. *)
private let binder_weaken_ns'
  (tm:list local_name -> Type)
  [|weaken tm|]
  (vars:list local_name)
  (ns:list local_name)
  (t:binder (tm vars))
  : binder (tm (ns @ vars))
  = map_binder (weaken_ns tm ns) t

unfold type binder_tm (tm:list local_name -> Type) =
  fun vars -> binder (tm vars)

(** Implementation of `weaken` for `binder`. *)
instance weaken_binder (_:weaken 'tm): weaken (binder_tm 'tm) = {
  weaken_ns' = (binder_weaken_ns' 'tm)
}

(** The core representation that is used for type checking. *)
type term (vars:list local_name) =
  | Local : fc -> bound_var vars -> term vars
  | Ref : fc -> global_name -> term vars
  | Universe : fc -> term vars
  | Abs : fc -> var:local_name
             -> bnd:binder (term vars)
             -> body:term (var :: vars)
             -> term vars
  | App : fc -> l:term vars
             -> r:term vars
             -> term vars

type closed_term = term []

(** Size metric for `ltt` terms. *)
val term_size : #vars:list local_name -> t:term vars -> Tot nat (decreases t)

(** Size metric for `binder`s. *)
val binder_size : #vars:list local_name
                -> b:binder (term vars)
                -> Tot nat (decreases b)

let rec term_size #vars = function
  | Local _ _ | Ref _ _ | Universe _ -> 1
  | Abs _ _ bnd body ->
    let bnd_size = binder_size bnd in
    bnd_size + term_size body + 1
  | App _ l r -> term_size l + term_size r + 1
and binder_size #vars = function
  | Pi ty -> 1 + term_size ty
  | Lam ty -> 1 + term_size ty
  | Let value ty -> 1 + term_size value + term_size ty

(** Alpha equality implementation for terms. *)
val alpha_eq : #vs1:list local_name -> #vs2:list local_name
             -> t1:term vs1 -> t2:term vs2
             -> Tot bool (decreases (term_size t1 + term_size t2))
let rec alpha_eq #vs1 #vs2 t t' =
  match t, t' with
  | Local _ bv1, Local _ bv2 -> bv1.index = bv2.index
  | Ref _ tln1, Ref _ tln2 -> tln1 = tln2
  | Abs _ _ bnd1 body1, Abs _ _ bnd2 body2 ->
    alpha_eq body1 body2 &&
    (match bnd1, bnd2 with
    | Lam t1, Lam t2 -> alpha_eq t1 t2
    | Let v1 t1, Let v2 t2 -> alpha_eq v1 v2 && alpha_eq t1 t2
    | Pi t1, Pi t2 -> alpha_eq t1 t2
    | _ -> false)
  | App _ l1 r1, App _ l2 r2 ->
    alpha_eq l1 l2 && alpha_eq r1 r2
  | _ -> false

(** Insert a variable into the local context and adjust
    the bound variable `var` to still be accurate in the
    new environment. *)
val insert_var : #outer:list local_name
               -> #inner:list local_name
               -> #existing_name:local_name
               -> new_name:local_name
               -> idx:var_index existing_name (outer @ inner)
               -> Tot (var_index existing_name (outer @ new_name :: inner))
let rec insert_var #outer #inner #existing_name new_name idx =
  match outer, idx with
  // If `outer` is empty, that means that we simply need to bump
  // `idx` by one to account for the new name that has been added
  // to the scope.
  | [], i -> i+1
  // If `existing_name` (the one we're adjusting the index of) is
  // at the top of the `outer` scope, then we just leave it's index
  // as-is.
  | x :: xs, 0 -> assert (x = existing_name); 0
  // If the variable is further down the scope stack, we remove the
  // head of `outer` and decrement the index by one, then recurse.
  // Once we have the result from that, we add one to it.
  | x :: xs, i ->
    let i' = insert_var #xs #inner #existing_name new_name (i-1) in
    i'+1

(** A lemma used in the `weaken_var` function that basically says
    that all it takes to adjust an index to having added names to
    the outer scope is to increment the index by the length of
    the outer scope. *)
private val weaken_var_lemma : ns:list local_name
                             -> Lemma
  (ensures forall inner existing (idx:var_index existing inner).
    let bump = List.length ns in
    is_bound_var existing (idx+bump) (ns@inner))
let rec weaken_var_lemma ns =
  // We prove the lemma by performing induction over the structure
  // of `ns`.
  match ns with
  // If we're not adding anything to the scope, the index
  // stays the same--a trivial case.
  | [] -> ()
  // For each element we need to add one to the index, which is
  // trivial for the SMT solver to infer once we tell it to perform
  // induction.
  | x :: xs -> weaken_var_lemma xs; ()

(** Add additional names to the outer scope of a variable. *)
val weaken_var : #inner:list local_name
               -> #existing_name:local_name
               -> ns:list local_name
               -> idx:var_index existing_name inner
               -> Tot (var_index existing_name (ns @ inner))
let weaken_var #inner #existing_name ns idx =
  weaken_var_lemma ns;
  idx + List.length ns

(** Insert a series of variable names inside of an existing scope.

    Adjusts the passed variable index to still point to the correct
    point in the scope for the corresponding name. *)
val insert_var_names : #outer:list local_name
                     -> #inner:list local_name
                     -> #existing_name:local_name
                     -> ns:list local_name
                     -> idx:var_index existing_name (outer @ inner)
                     -> Tot (var_index existing_name (outer @ ns @ inner))
let rec insert_var_names #outer #inner #existing_name ns idx =
  match outer, idx with
  | [], _ -> weaken_var ns idx
  | x :: xs, 0 -> 0
  | y :: ys, _ ->
    let idx' = insert_var_names #ys #inner #existing_name ns (idx-1) in
    idx' + 1

(** Insert multiple names into a term's scope. *)
private val thin : #outer:list local_name
                 -> #inner:list local_name
                 -> ns:list local_name
                 -> t:term (outer @ inner)
                 -> Tot (term (outer @ ns @ inner)) (decreases %[term_size t])
let rec thin #outer #inner ns t =
  match t with
  | Local fc bv -> let idx' = insert_var_names ns bv.index in
                  Local fc (BoundVar idx')
  | Ref fc gn -> Ref fc gn
  | Universe fc -> Universe fc
  | Abs fc var bnd body ->
    let outer' = var :: outer in
    let bnd' = match bnd with
      | Pi ty -> Pi (thin ns ty)
      | Let v ty -> Let (thin ns v) (thin ns ty)
      | Lam ty -> Lam (thin ns ty) in
    let body' = thin #outer' #inner ns body in
    Abs fc var bnd' body'
  | App fc l r -> App fc (thin ns l) (thin ns r)


(** Implementation of `weaken_ns'` for `term`. *)
private val weaken_term_ns' : vars:list local_name
                            -> ns:list local_name
                            -> term vars
                            -> Tot (term (ns @ vars))
let weaken_term_ns' vars = thin #[] #vars

(** Implementation of `weaken` for `term`. *)
instance weaken_term : weaken term =
  Mkweaken weaken_term_ns'

(** Lemma for renaming variable indices. *)
private val rename_var_index_lemma : #xs:list local_name
                                   -> #ys:list local_name
                                   -> #cur_name:local_name
                                   -> idx:nat{is_bound_var cur_name idx xs}
                                   -> Lemma
  (requires idx `valid_index_in` ys)
  (ensures is_bound_var (name_of ys idx) idx ys) (decreases %[xs; ys])
let rec rename_var_index_lemma #xs #ys #cur_name idx =
  match xs, ys, idx with
  | x :: xs', _, 0 -> assert (x = cur_name)
  | x :: xs', y :: ys', _ ->
    rename_var_index_lemma #xs' #ys' #cur_name (idx - 1)

private type subst_env (vars:list local_name) (drops:list local_name) =
  terms:list (term vars){List.length terms = List.length drops}

private val sub_index_lemma : #outer:list local_name
                            -> #inner:list local_name
                            -> #name:local_name
                            -> idx:nat
                            -> Lemma
  (requires (is_bound_var name idx (outer @ inner))
            /\ (idx `valid_index_in` outer))
  (ensures (is_bound_var name idx outer))
  (decreases %[outer])
let rec sub_index_lemma #outer #inner #name idx =
  if idx = 0 then () else
    let idx':nat = idx - 1 in
    let outer' = List.Tot.tail outer in
    sub_index_lemma #outer' #inner #name idx'

private val super_index_lemma : #outer:list local_name
                              -> #inner:list local_name
                              -> #name:local_name
                              -> idx:nat
                              -> Lemma
  (requires (is_bound_var name idx outer))
  (ensures (is_bound_var name idx (outer @ inner)))
  (decreases outer)
let rec super_index_lemma #outer #inner #name idx =
  if idx = 0 then () else
    let idx':nat = idx - 1 in
    let outer' = List.Tot.tail outer in
    super_index_lemma #outer' #inner #name idx'

private val strip_index_lemma : outer:list local_name
                              -> inner:list local_name
                              -> name:local_name
                              -> idx:var_index name (outer @ inner)
                              -> Lemma
  (requires idx >= List.length outer)
  (ensures is_bound_var name (idx - List.length outer) inner)
  (decreases outer)
let rec strip_index_lemma outer inner name idx =
  match outer with
  | [] -> ()
  | x :: xs ->
    let idx' = idx-1 in
    strip_index_lemma xs inner name idx'

private val try_to_drop : #outer:list local_name
                        -> #vars:list local_name
                        -> #drop:list local_name
                        -> #name:local_name
                        -> fc -> idx:var_index name (outer @ drop @ vars)
                        -> subst_env vars drop
                        -> Tot (term (outer @ vars))
let try_to_drop #outer #vars #drop #name fc idx env =
  let start = List.length outer in
  let stop = List.length outer + List.length drop in

  let all_vars = outer @ drop @ vars in
  let new_vars = outer @ vars in

  // If `idx` is in `outer`
  if idx < start then (
    assert (idx `valid_index_in` outer);
    sub_index_lemma #outer #(drop @ vars) #name idx;
    let outer_idx: var_index name outer = idx in
    super_index_lemma #outer #vars #name outer_idx;
    let new_idx: var_index name new_vars = outer_idx in
    (Local fc (BoundVar new_idx)) <: term new_vars

  // If `idx` is in `drop`
  ) else if idx < stop then (
    let tm_index = idx - start in
    let tm = element_at env tm_index in
    (weaken_ns term outer tm) <: term new_vars

  // If `idx` is in `vars`
  ) else (
    List.Tot.append_assoc outer drop vars;
    strip_index_lemma (outer @ drop) vars name idx;
    let vars_index: var_index name vars = idx - stop in
    weaken_var_lemma outer;
    let new_idx: var_index name new_vars = vars_index + start in
    (Local fc (BoundVar new_idx)) <: term new_vars
  )

private val subst : #outer:list local_name
                  -> #vars:list local_name
                  -> #drop:list local_name
                  -> subst_env vars drop
                  -> t:term (outer @ drop @ vars)
                  -> Tot (term (outer @ vars)) (decreases t)
let rec subst #outer #vars #drop env = function
  | Local fc (BoundVar idx) -> try_to_drop fc idx env
  | Ref fc gn -> Ref fc gn
  | Universe fc -> Universe fc
  | Abs fc var bnd body ->
    let outer' = var :: outer in
    let bnd' = match bnd with
      | Pi ty -> Pi (subst env ty)
      | Let v ty -> Let (subst env v) (subst env ty)
      | Lam ty -> Lam (subst env ty) in
    let body' = subst #outer' env body in
    Abs fc var bnd' body'
  | App fc l r -> App fc (subst env l) (subst env r)
