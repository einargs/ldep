module Core.TypeCheck

open Core.Fc
open Core.Name
open Core.Raw
open Core.Ltt
open Core.Tc
open Core.Environment

(** A mapping of the in-scope names to the type that they
    are bound to. *)
private type local_ctxt vars = local_env raw_term vars

//private val expand_binder : #vars:list local_name -> #

private val lookup_ty : #vars:list local_name
                      -> fc
                      -> any_name
                      -> local_ctxt vars
                      -> TcNull (raw_term vars)
let lookup_ty #vars fc n ctx =
  let res = match n with
  | LocalName ln ->
    (match env_lookup ln ctx with
    Some v -> v
    None -> None)
  | _ -> None in
  match res with
  | Some v -> v
  | None -> lookup' fc n

val infer_type : body:raw_term -> env:local_scope -> TcNull (ty:raw_term)
