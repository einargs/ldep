module Core.Ltt

open FStar.OrdSet
open FStar.String
open FStar.Tactics

type name = {
  index : nat;
  str : string;
}

val intro : string -> Tot name
let intro s = {index=0;str=s}

val inc_name : name -> Tot name
let inc_name n = { index = n.index+1; str = n.str }

type ltt =
  | Var : var:name -> ltt
  | Universe : level:nat -> ltt
  | Abs : bnd:binder -> var:name -> body:ltt -> ltt
  | App : l:ltt -> r:ltt -> ltt
and binder = 
  | Pi : ltt -> binder
  | Lam : binder

val name_order : name -> name -> Tot bool
let name_order n1 n2 =
  if n1.index = n1.index
    then 0 <= compare n1.str n2.str
    else n1.index > n2.index

// I can't figure out how to prove this :(
assume NameOrderIsTotal: total_order name name_order

type name_set = ordset name name_order

val free_variables : ltt -> Tot name_set
val binder_free_variables : binder -> Tot name_set
let rec free_variables t =
  match t with
  | Var var -> singleton var
  | Universe _ -> empty
  | Abs bnd var body ->
    let binder_fv = binder_free_variables bnd in
    union binder_fv (remove var (free_variables body))
  | App l r -> union (free_variables l) (free_variables r)
and binder_free_variables b =
  match b with
  | Pi ty -> free_variables ty
  | Lam -> empty

val free_in : name -> ltt -> Tot bool
let free_in v e = mem v (free_variables e)

val is_closed : ltt -> Tot bool
let is_closed t = free_variables t = empty

val find_non_capturing_name : n:name -> s:name_set -> Tot name (decreases (size s))
let rec find_non_capturing_name n s =
  if mem n s
    then let s': name_set = remove n s in
         find_non_capturing_name (inc_name n) s'
    else n

val ltt_size : ltt -> Tot nat
val binder_size : binder -> Tot nat
let rec ltt_size = function
  | Var _ | Universe _ -> 1
  | Abs bnd _ body ->
    let bnd_size = binder_size bnd in
    bnd_size + ltt_size body + 1
  | App l r -> ltt_size l + ltt_size r + 1
and binder_size = function
  | Pi ty -> 1 + ltt_size ty
  | Lam -> 1

(** Replaces all occurances of `n2` with `n1` *)
private val replace_var : n1:name -> n2:name -> t:ltt -> Tot (ret:ltt{ltt_size ret = ltt_size t})
let rec replace_var n1 target t =
  match t with
  | Var v -> if v = target then Var n1 else t
  | _ -> t

val subst : arg:ltt -> name -> bod:ltt -> Tot ltt (decreases %[ltt_size arg; ltt_size bod])
val binder_subst : arg:ltt -> name -> bnd:binder -> Tot binder (decreases %[ltt_size arg; binder_size bnd])
let rec subst arg v t =
  match t with
  | Var v' -> if v' = v then arg else t
  | Universe l -> Universe l
  | App l r -> App (subst arg v l) (subst arg v r)
  | Abs bnd bv body ->
    if bv = v
      then t
      else
        let bnd' = binder_subst arg v bnd in
        let fvs = union (free_variables arg) (free_variables body) in
        let bv' = find_non_capturing_name bv fvs in
        let body' = replace_var bv' bv body in
        assert (ltt_size body << ltt_size t);
        assert (ltt_size body = ltt_size body');
        assert (ltt_size body' << ltt_size t);
        Abs bnd' bv' (subst arg v body')
and binder_subst arg v b =
  match b with
  | Pi ty -> Pi (subst arg v ty)
  | Lam -> Lam

val alpha_eq : ltt -> ltt -> Tot bool
val binder_alpha_eq : binder -> binder -> Tot bool
let rec alpha_eq t1 t2 =
  match t1, t2 with
  | Abs b1 v1 e1, Abs b2 v2 e2 ->
    binder_alpha_eq b1 b2
    && alpha_eq e1 (subst (Var v1) v2 e2)
  | App l1 r1, App l2 r2 -> alpha_eq l1 l2 && alpha_eq r1 r2
  | _ -> t1 = t2
and binder_alpha_eq b1 b2 =
  match b1, b2 with
  | Pi ty1, Pi ty2 -> alpha_eq ty1 ty2
  | Lam, Lam -> true
  | _ -> false

let _ =
  let x = intro "x" in
  let y = intro "y" in
  let id = Abs Lam x (Var x) in
  let xy = Abs Lam x (Var y) in
  assert (subst (Universe 0) y xy = Abs Lam x (Universe 0));
  assert (subst (Universe 0) x id = id)
  
