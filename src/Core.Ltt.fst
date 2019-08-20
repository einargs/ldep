module Core.Ltt

open FStar.OrdSet
open FStar.String
open FStar.Tactics

(**
Represents an identifier.

If there's a conflict during the capture-avoiding
substitution process, the `index` value is
incremented.
*)
type name = {
  index : nat;
  str : string;
}

(**
Introduce a new name.

Initializes the name with `index` at `0`.
*)
val intro : string -> Tot name
let intro s = {index=0;str=s}

(**
Increment the index of a name.
*)
val inc_name : name -> Tot name
let inc_name n = { index = n.index+1; str = n.str }

(**
`type` is the core logic that type-checking occurs within.

`binder` is a binder in the core logic.

NOTE: the docs for both of these types are together like
this because putting the binder docs where
[this wiki page](https://github.com/FStarLang/FStar/wiki/Generating-documentation-with-fsdoc-comments)
says to results in the F* subprocess for interactive
typechecking exiting.

TODO: ask about how to fix that.
*)
type ltt =
  | Var : var:name -> ltt
  | Universe : ltt
  | Abs : bnd:binder -> var:name -> body:ltt -> ltt
  | App : l:ltt -> r:ltt -> ltt
and binder =
  | Pi : ltt -> binder
  | Lam : binder

(**
A total ordering on names.
*)
val name_order : name -> name -> Tot bool
let name_order n1 n2 =
  if n1.index = n1.index
    then 0 <= compare n1.str n2.str
    else n1.index > n2.index

(*
I can't figure out how to prove that string
comparison is total, so I'm just making this
an axiom.

NOTE: if this is an `fsdoc` comment, it again
seems to crash the F* subprocess for interactive
typechecking.

TODO: figure out how to fix that.
*)
assume NameOrderIsTotal: total_order name name_order

(**
A type alias for a set of names.

Generally used when calculating free variables.
*)
type name_set = ordset name name_order

(** Calculate the free variables in an `ltt` term. *)
val free_variables : t:ltt -> Tot name_set
(** Calculate the free variables in a `ltt` binder. *)
val binder_free_variables : binder -> Tot name_set
let rec free_variables t =
  match t with
  | Var var -> singleton var
  | Universe -> empty
  | Abs bnd var body ->
    let binder_fv = binder_free_variables bnd in
    union binder_fv (remove var (free_variables body))
  | App l r -> union (free_variables l) (free_variables r)
and binder_free_variables b =
  match b with
  | Pi ty -> free_variables ty
  | Lam -> empty

(**
Predicate for checking if a name is free in a `ltt` term.
*)
val free_in : name -> ltt -> Tot bool
let free_in v e = mem v (free_variables e)

(**
Predicate for checking if a `ltt` term is closed--i.e.
the set of free variables is empty.
*)
val is_closed : ltt -> Tot bool
let is_closed t = free_variables t = empty

(**
Calculate a name that does not occur within the set of
names `s` by incrementing the `index` of `n` until it
is not within `s`.

This is probably more inefficient than it needs to be,
because if `n` is in `s`, `find_non_capturing_name`
removes `n` from `s` before recursing. This is done
to show termination, but it's a quick hack that I
should go back and fix if this project ever gets anywhere.
*)
val find_non_capturing_name : n:name -> s:name_set -> Tot name (decreases (size s))
let rec find_non_capturing_name n s =
  if mem n s
    then let s': name_set = remove n s in
         find_non_capturing_name (inc_name n) s'
    else n

(** Size metric for `ltt` terms. *)
val ltt_size : ltt -> Tot nat

(** Size metric for `binder`s. *)
val binder_size : binder -> Tot nat

let rec ltt_size = function
  | Var _ | Universe -> 1
  | Abs bnd _ body ->
    let bnd_size = binder_size bnd in
    bnd_size + ltt_size body + 1
  | App l r -> ltt_size l + ltt_size r + 1
and binder_size = function
  | Pi ty -> 1 + ltt_size ty
  | Lam -> 1

(**
Replaces all occurances of `replacee` with `substitute`.

This is essentially a specialized version of `subst`;
I created it bec
*)
private val replace_var : name -> name -> t:ltt -> Tot (ret:ltt{ltt_size ret = ltt_size t})
let rec replace_var substitute replacee t =
  let rep = replace_var substitute replacee in
  match t with
  | Var v -> if v = replacee then Var substitute else t
  | Universe -> t
  | Abs bnd v body ->
    let bnd' = match bnd with
      | Pi ty -> Pi (rep ty)
      | Lam -> Lam in
    Abs bnd' v (rep body)
  | App l r -> App (rep l) (rep r)

// This seems to be necessary for the `smt` solver to
// have enough fuel to verify `subst`.
#reset-options

(**
Perform capture-avoiding substitution of `arg` for `v` in  `bod`.
*)
val subst : arg:ltt -> v:name -> bod:ltt
  -> Tot ltt (decreases %[ltt_size arg; ltt_size bod])

(**
Perform capture-avoiding substitution of `arg` for `v` in  `bnd`.
*)
val binder_subst : arg:ltt -> v:name -> bnd:binder
  -> Tot binder (decreases %[ltt_size arg; binder_size bnd])

let rec subst arg v t =
  match t with
  | Var v' -> if v' = v then arg else t
  | Universe -> Universe
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

(** Check if two `ltt` terms are alpha equivalent. *)
val alpha_eq : ltt -> ltt -> Tot bool

(** Check if two `binder`s are alpha equivalent. *)
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

(** Assorted assertions. *)
let _ =
  let x = intro "x" in
  let y = intro "y" in
  let id = Abs Lam x (Var x) in
  let xy = Abs Lam x (Var y) in
  assert (subst (Universe) y xy = Abs Lam x (Universe));
  assert (subst (Universe) x id = id)
  
