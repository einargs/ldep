module Core.Tc

open Core.Fc
open Core.Name
open Core.Ltt
open Core.Raw
open Core.Context

open Util.Result

(** Representation of a type checking error. *)
type tc_err =
  | TcMissingDefFor : fc -> global_name -> tc_err
  | TcCannotEquate : fc -> #vars:list local_name -> term vars -> term vars -> tc_err
  | TcTermIsNotAType : fc -> #vars:list local_name -> term vars -> tc_err
  | TcExpectedTermToHaveType : fc -> #vars:list local_name -> term vars -> tc_err
  | TcErrMsg : fc -> string -> tc_err

(** The result of a type checking operation: either a
    success (`Ok`) or a failure (`Err`). *)
private type tc_result (a:Type) = result tc_err a

(** The context used for type checking.

    This is a local type alias used for convenience if it
    needs to change. *)
private type tc_env = context

(** Internal representation of the tc monad. *)
private let tc (a:Type) = tc_env -> M (tc_result a)

(** Lift a value `x` into the tc monad. *)
private val return_tc : a:Type0 -> a -> Tot (tc a)
let return_tc _ x = fun _ -> Ok x

(** Bind a function in the tc monad. *)
private val bind_tc : a:Type -> b:Type
                    -> x:tc a -> f:(a -> tc b) -> Tot (tc b)
let bind_tc _ _ x f =
  fun env ->
    let res = x env in
    match res with
    | Ok v -> f v env
    | Err err -> Err err

(** Implementation of the `raise` action in the tc monad. *)
private val tc_raise : a:Type -> tc_err -> Tot (tc a)
let tc_raise a err: tc a = fun _ -> Err err

(** Implementation of the `get` action in the tc monad. *)
private val tc_get : unit -> Tot (tc tc_env)
let tc_get (): tc tc_env = fun envr -> Ok envr

(** Definition of the `TC` effect. *)
reifiable reflectable new_effect {
  TC : a:Type -> Effect
  with repr   = tc
     ; bind   = bind_tc
     ; return = return_tc
     ; get    = tc_get
     ; raise  = tc_raise
}

(** The post-condition for the tc monad. *)
private type tc_post (a:Type) = tc_env -> tc_result a -> GTot Type0

(** Pre- and post-condition form for the `TC` effect. *)
effect Tc (a:Type) (pre:TC?.pre) (post:tc_post a) =
  TC a
    (fun (envr:tc_env) (p:TC?.post a) ->
      pre envr /\
        (forall (r:tc_result a). pre envr /\ post envr r ==> p r))

(** Utility effect for trivial conditions for the `TC` effect. *)
effect TcNull (a:Type) =
  TC a (fun (e0:tc_env) (p:(tc_result a -> Type0)) -> forall (x:tc_result a). p x)

(** Get the typechecking environment. *)
val get : unit -> TcNull tc_env
let get = TC?.get

(** Raise a typechecking error. *)
val raise : (#a:Type) -> err:tc_err -> Tc a
  (requires fun _ -> True)
  (ensures fun _ r -> r == Err err)
let raise #a err = TC?.raise a err

(** Specification of the behavior of `unwrap_opt`. *)
private val unwrap_opt_spec : #a:Type -> tc_err -> option a -> tc_result a -> Type0
let unwrap_opt_spec #a err o r =
  match r with
  | Ok v -> o == Some v
  | Err err' -> o == None /\ err' == err

(** Unwrap an `option`, and if it's `None` raise the passed error. *)
val unwrap_opt : #a:Type -> err:tc_err -> o:option a -> Tc a
  (requires fun _ -> True)
  (ensures fun _ r -> unwrap_opt_spec err o r)
let unwrap_opt #a err o =
  match o with
  | Some v -> v
  | None -> raise err

(** A form of runtime assert that raises `err` if `b = false`. *)
val require : err:tc_err -> b:bool -> Tc unit
  (ensures fun _ -> True)
  (requires fun _ r -> if b
    then r = Ok ()
    else r = Err err)
let require err b =
  if b then () else raise err

(** Lookup a declaration in the typechecking environment. *)
val lookup : global_name -> TcNull (option global_def)
let lookup n =
  let e = get () in
  lookup_gdef n e

(** Lookup the value associated with a name in the typechecking
    environment. *)
val lookup_value : global_name -> TcNull (option closed_term)
let lookup_value n =
  Option.mapTot (body_of_gdef) (lookup n)

(* made invalid by removing `total`

val lookup_lemma : envr:tc_env -> n:any_name -> Lemma
  (ensures (let lookup_res = reify (lookup n) envr in
           lookup_res = Ok (lookup_gdef n envr)
           ))
let lookup_lemma _ _ = () *)


(* made invalid by removing `total`
(** Specification of the behavior of `lookup'`. *)
private val lookup'_spec : tc_env -> any_name -> tc_result global_def -> Type0
let lookup'_spec envr n r =
  let o = Ok?.value (reify (lookup n) envr) in
  match r with
  | Ok v -> o = Some v
  | Err _ -> o = None*)

(** Unwrapped version of `lookup` that raises an error
    if `n` is not in the typechecking environment.

    Takes a file location to include in the error. *)
val lookup' : fc -> n:global_name -> Tc global_def
  (requires fun envr -> True)
  (ensures fun e r -> True)
let lookup' fc n =
  let o: option global_def = lookup n in
  unwrap_opt (TcMissingDefFor fc n) o

(** Execute a `Tc` effect starting with the provided
    environment. *)
val run_tc :
  #a:Type -> #pre:TC?.pre -> #post:tc_post a
  -> envr:context -> f:(unit -> Tc a pre post)
  -> Div (result tc_err a)
    (requires pre envr)
    (ensures fun r -> post envr r)
let run_tc #a #pre #post envr eff =
  let res = reify (eff ()) envr in
  res

(** Execute a `TcNull` effect starting with the provided
    environment. *)
val run_tc_null : #a:Type -> envr:context
                -> f:(unit -> TcNull a)
                -> Dv (result tc_err a)
let run_tc_null #a envr eff =
  let res = reify (eff ()) envr in
  res
