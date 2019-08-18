module Core.Ltt

open FStar.OrdSet
open FStar.String

type name = {
  index : nat;
  str : string;
}

val inc_name : name -> Tot name
let inc_name n = { index = n.index+1; str = n.str; }

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

val is_closed : ltt -> Tot bool
let is_closed t = free_variables t = empty

val find_non_capturing_name : n:name -> s:name_set -> Tot name (decreases (size s))
let rec find_non_capturing_name n s =
  if mem n s
    then let s': name_set = remove n s in
         find_non_capturing_name (inc_name n) s'
    else n

val alpha_eq : ltt -> ltt -> Tot bool
val binder_alpha_eq : binder -> binder -> Tot bool
let rec alpha_eq t1 t2 =
  match t1, t2 with
  | Var v1, Var v2 -> v1  
and binder_alpha_eq b1 b2 =
  match b1, b2 with
  | Pi ty1, Pi ty2 -> alpha_eq ty1 ty2
  | Lam, Lam -> true
  | _ -> false
