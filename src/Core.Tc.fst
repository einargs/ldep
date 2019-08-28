module Core.Tc

open Core.Name
open Core.Ltt
open Core.Environment

open Util.Result

(** Representation of a type checking error. *)
type tc_err =
  | MissingDeclFor : name -> tc_err
  | CannotEquate : ltt -> ltt -> tc_err
  | ExpectedFunctionType : ltt -> tc_err
  | Msg : string -> tc_err

(** The result of a type checking operation: either a
    success (`Ok`) or a failure (`Err`). *)
type tc_result (a:Type) = result tc_err a

(** Internal representation of the tc monad. *)
private let tc (a:Type) = env -> M (tc_result a)

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
private val tc_get : unit -> Tot (tc env)
let tc_get (): tc env = fun envr -> Ok envr

(** Definition of the `TC` effect. *)
total reifiable reflectable new_effect {
  TC : a:Type -> Effect
  with repr   = tc
     ; bind   = bind_tc
     ; return = return_tc
     ; get    = tc_get
     ; raise  = tc_raise
}

private type tc_post (a:Type) = env -> tc_result a -> GTot Type0

(** Pre- and post-condition form for the `TC` effect. *)
effect Tc (a:Type) (pre:TC?.pre) (post:tc_post a) =
  TC a
    (fun (envr:env) (p:TC?.post a) ->
      pre envr /\
        (forall (r:tc_result a). pre envr /\ post envr r ==> p r))

(** Utility effect for trivial conditions for the `TC` effect. *)
effect TcNull (a:Type) =
  TC a (fun (e0:env) (p:(tc_result a -> Type0)) -> forall (x:tc_result a). p x)

(** Get the typechecking environment. *)
val get : unit -> TcNull env
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
val lookup : name -> TcNull (option decl)
let lookup n =
  let e = get () in
  env_lookup e n

(** Lookup the value associated with a name in the typechecking
    environment. *)
val lookup_def : name -> TcNull (option ltt)
let lookup_def n =
  match lookup n with
  | Some (Function t _) -> Some t
  | _ -> None

val lookup_lemma : envr:env -> n:name -> Lemma
  (ensures
    (let lookup_res = reify (lookup n) envr in
    lookup_res = Ok (env_lookup envr n)
    ))
let lookup_lemma _ _ = ()

(** Specification of the behavior of `lookup'`. *)
val lookup'_spec : env -> name -> tc_result decl -> Type0
let lookup'_spec envr n r =
  let o = Ok?.value (reify (lookup n) envr) in
  match r with
  | Ok v -> o = Some v
  | Err _ -> o = None

(** Unwrapped version of `lookup` that raises an error
    if `n` is not in the typechecking environment. *)
val lookup' : n:name -> Tc decl
  (requires fun envr -> True)
  (ensures fun e r -> True)
let lookup' n =
  let o: option decl = lookup n in
  unwrap_opt (MissingDeclFor n) o

(** Execute a `Tc` effect starting with the provided
    environment. *)
val run_tc :
  #a:Type -> #pre:TC?.pre -> #post:tc_post a
  -> envr:env -> f:(unit -> Tc a pre post)
  -> Pure (tc_result a)
    (requires pre envr)
    (ensures fun r -> post envr r)
let run_tc #a #pre #post envr eff =
  let res = reify (eff ()) envr in
  res

(** Execute a `TcNull` effect starting with the provided
    environment. *)
val run_tc_null : #a:Type -> envr:env -> f:(unit -> TcNull a) -> Tot (tc_result a)
let run_tc_null #a envr eff =
  let res = reify (eff ()) envr in
  res

(** Some tests. *)
[@ "opaque_to_smt"]
let _ =
  let x = intro "x" in
  let x_def = Function Universe Universe in
  let envr = env_init [(x,x_def)] in

  // This stops working if you remove the type annotation
  // for `tcr` for some reason.
  let _ =
    let tcr: env -> Tot (tc_result (option decl)) = reify (lookup x) in
    let target = Ok (Some x_def) in
    assert_norm (tcr envr == target) in

  let _ =
    let r = run_tc_null envr (fun () -> (lookup x)) in
    let target = Ok (Some x_def) in
    assert_norm (r = target) in

  let _ =
    let r = reify (lookup' x) envr in
    assert_norm (r = Ok x_def) in
  ()
