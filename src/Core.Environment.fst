module Core.Environment

open Core.Name
open Core.Ltt

module M = FStar.OrdMap

(**
Represents a declaration.
*)
type decl =
  | Function : term : ltt -> ty : ltt -> decl

(**
The environment that typechecking occurs within.

`ordmap` doesn't work with the `READER` effect,
so I have to use something else. As such, I'm
just falling back on a list.

NOTE: look at the [FStar.DM4F.StMap](https://github.com/FStarLang/FStar/blob/master/examples/dm4free/FStar.DM4F.StMap.fst)
example--it uses `FStar.Map` in a STATE monad.
*)
abstract type env = name_map decl

(** Look up a declaration within the typechecking
    environment. *)
val env_lookup : env -> name -> Tot (option decl)
let rec env_lookup e n = M.select n e

(**
`env_add` adds a declaration to an environment.
*)
val env_add : env -> name -> decl -> Tot env
let env_add e n d = M.update n d e

(**
`env_init` initializes an environment using a
list of tuples pairing a name and a declaration.
*)
val env_init : list (name * decl) -> Tot env
let env_init = List.Tot.fold_left
  (fun envr (n,d) -> env_add envr n d) M.empty

(**
Predicate for checking if a name is in the environment.
*)
val env_has : env -> name -> Tot bool
let rec env_has e n = M.contains n e

val env_has_in : env -> name -> decl -> Type0
let env_has_in e n d =
  match env_lookup e n with
  | Some v -> v = d
  | None -> false
