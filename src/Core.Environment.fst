module Core.Environment

open Util.Reader

open Core.Ltt

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
type env = list (name * decl)

(** Look up a declaration within the typechecking
    environment. *)
abstract val env_lookup : env -> name -> Tot (option decl)
let rec env_lookup e n =
  match e with
  | [] -> None
  | (sn,sd) :: xs -> if sn = n
      then Some sd
      else env_lookup xs n

(**
`env_add` adds a declaration to an environment.
*)
abstract val env_add : env -> name -> decl -> Tot env
let env_add e n d = (n,d) :: e

(**
`env_init` initializes an environment using a
list of tuples pairing a name and a declaration.
*)
abstract val env_init : list (name * decl) -> Tot env
let env_init = id

(**
Predicate for checking if a name is in the environment.
*)
val env_has : env -> name -> Tot bool
let rec env_has e n =
  Option.isSome (env_lookup e n)
