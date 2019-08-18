module Core.Environment

open Util.Reader

open Core.Ltt

type decl =
  | Function : term : ltt -> ty : ltt -> decl

(**
The environment that typechecking occurs within.

`ordmap` doesn't work with the `READER` effect,
so I have to use something else. As such, I'm
just falling back on a list.
*)
type env = list (name * decl)

(** Look up a declaration within the typechecking
    environment. *)
val env_lookup : env -> name -> option decl
let rec env_lookup e n =
  match e with
  | [] -> None
  | (sn,sd) :: xs -> if sn = n
      then Some sd
      else env_lookup xs n

(** The base effect that typechecking occurs within. *)
total reifiable reflectable new_effect TC = READER env

(** Pre- and post-condition form for the `TC` effect. *)
effect Tc (a:Type) (pre:TC?.pre) (post:env -> a -> GTot Type0) =
  TC a (fun l0 p -> pre l0 /\ (forall x. pre l0 /\ post l0 x ==> p x))

effect TcNull (a:Type) =
  TC a (fun (e0:env) (p:(a -> Type0)) -> forall (x:a). p x)

val read : unit -> TcNull env
let read = TC?.get

val lookup : name -> TcNull (option decl)
let lookup n =
  let e = read () in
  env_lookup e n

val lookup_term : name -> TcNull (option ltt)
let lookup_term n =
  match lookup n with
  | Some (Function t _) -> Some t
  | _ -> None
