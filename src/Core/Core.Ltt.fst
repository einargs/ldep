module Core.Ltt

type bound_name = nat

type unsafe_ltt =
  | Var : var:name -> unsafe_ltt
  | Universe : level:nat -> unsafe_ltt
  | Abs : bnd:binder -> var:bound_name -> expr:unsafe_ltt -> unsafe_ltt
  | App : l:unsafe_ltt -> r:unsafe_ltt -> unsafe_ltt
and binder = 
  | Pi : unsafe_ltt -> binder
  | Lam : binder
and name =
  | Free : unsafe_ltt -> name
  | Bound : bound_name -> name

val top_bound_name : unsafe_ltt -> Tot (option bound_name)
let rec top_bound_name t =
  match t with
  | App l r ->
    let ltop = (top_bound_name l) in
    let rtop = (top_bound_name r) in
    (match ltop, rtop with
     | (Some lval), (Some rval) ->
       Some (if lval > rval then lval else rval)
     | Some lval, None -> lval
     | None, Some rval -> rval
     | None, None -> None)
  | Abs bnd v t' -> Some v
  | _ -> None

val enclosing_name_of : unsafe_ltt -> Tot bound_name
let enclosing_name_of t =
  match top_bound_name t with
  | Some v' -> v'+1
  | None -> 0

val bound_names_increase : unsafe_ltt -> Tot bool
let rec bound_names_increase t =
  match t with
  | App l r -> bound_names_increase l && bound_names_increase r
  | Abs bnd v t' -> 
     (enclosing_name_of t' = v) && bound_names_increase t'
  | _ -> true
and inc_in_binder (b:binder) : bool =
  match b with
  | Pi t1 -> bound_names_increase t1
  | Lam -> true

(* Replace this with a way of asserting that `bound_names_increase` is
   is true for all of type `ltt` so that I don't have to define
   `unsafe_ltt` *)
type ltt = t:unsafe_ltt{bound_names_increase t}
