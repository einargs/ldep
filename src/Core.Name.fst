module Core.Name

open FStar.OrdSet

module M = FStar.OrdMap
module O = FStar.Order

(** Represents an identifier.

    If there's a conflict during the capture-avoiding
    substitution process, the `index` value is
    incremented. *)
type base_name = {
  index : nat;
  str : string;
}

(** Useful information about a name, such as
    its origin. *)
type name_sort =
  | UserGen
  | MachineGen

(** A name used to identify something. *)
type name = {
  base : base_name;
  sort : name_sort
}

(** Apply a modification to the base name. *)
val mod_base_name : (base_name -> Tot base_name) -> name -> Tot name
let mod_base_name f n = { sort = n.sort; base = f n.base }

(** Introduce a new user-generated name.

    Initializes the name with `index` at `0`. *)
val intro : string -> Tot name
let intro s = {
  sort = UserGen;
  base = {
    str = s;
    index = 0
  }
}

(** Introduce a new machine-generated name. *)
val mintro : string -> Tot name
let mintro s = {
  sort = MachineGen;
  base = {
    str = s;
    index = 0
  }
}

(** Increment the index of a name. *)
val inc_name : name -> Tot name
let inc_name = mod_base_name
  (fun n -> { index = n.index+1; str = n.str })

(** A total ordering on names. *)
abstract val name_order : name -> name -> Tot bool
let name_order n1 n2 =
  let compare_sort s1 s2 =
    let rank (s:name_sort): nat =
      match s with
      | UserGen -> 1
      | MachineGen -> 0 in

    O.compare_int (rank s1) (rank s2) in

  let compare_string s1 s2 =
    Order.order_from_int (String.compare s1 s2) in

  let compare_name n1 n2 =
    O.lex (compare_sort n1.sort n2.sort)
      (fun () -> O.lex (O.compare_int n1.base.index n2.base.index)
        (fun () -> compare_string n1.base.str n2.base.str)) in

  O.gt (compare_name n1 n2)

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

let name_order_cmp: cmp name = name_order

(** A type alias for a set of names.

    Generally used when calculating free variables. *)
let name_set: Type0 = ordset name name_order

(** A type alias for a map from names to `a`. *)
type name_map (a:Type) = M.ordmap name a name_order
