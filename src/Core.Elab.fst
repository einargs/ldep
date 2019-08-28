module Core.Elab

open Core.Name
open Core.Ltt
open Core.Environment
module Tc = Core.Tc

module UList = Util.UList
open Util.Result

open FStar.OrdMap

(** The development calculus used during the elaboration process.

    Adds `Guess` and `Hole` binders to the LTT calculus. *)
type dev_ltt =
  | DVar : var:name -> dev_ltt
  | DUniverse : dev_ltt
  | DAbs : bnd:dev_binder -> var:name -> body:dev_ltt -> dev_ltt
  | DApp : l:dev_ltt -> r:dev_ltt -> dev_ltt
and dev_binder =
  | DPi : ty:dev_ltt -> dev_binder
  | DLam : dev_binder
  | Guess : dev_ltt -> dev_binder
  | Hole : dev_binder

(** Does the dev_ltt term contain anything that explicitly makes
    it dev, and therefore not convertible to ltt. *)
val is_ltt_dev : dev_ltt -> Tot bool

(** Does the dev_binder term contain anything that explicitly makes
    it dev, and therefore not convertible to binder. *)
val is_binder_dev : dev_binder -> Tot bool

let rec is_ltt_dev = function
  | DVar _ -> false
  | DUniverse -> false
  | DAbs bnd var body -> is_binder_dev bnd || is_ltt_dev body
  | DApp l r -> is_ltt_dev l || is_ltt_dev r
and is_binder_dev = function
  | DPi t -> is_ltt_dev t
  | DLam -> false
  | Guess _ -> true
  | Hole -> true

(** Convert a dev_ltt term that has no dev_ltt only members to ltt. *)
val to_std_ltt : t:dev_ltt{not (is_ltt_dev t)} -> ltt
(** Convert a dev_binder term that has no dev_binder only
    members to binder. *)
val to_std_binder : bnd:dev_binder{not (is_binder_dev bnd)} -> binder

let rec to_std_ltt = function
  | DVar v -> Var v
  | DUniverse -> Universe
  | DAbs bnd var body ->
    Abs (to_std_binder bnd) var (to_std_ltt body)
  | DApp l r ->
    App (to_std_ltt l) (to_std_ltt r)
and to_std_binder = function
  | DPi t -> Pi (to_std_ltt t)
  | DLam -> Lam

(** An error that can occur during elaboration. *)
type elab_err =
  | TcErr of Tc.tc_err

(** A mapping of names to `dev_ltt` terms. *)
abstract type dev_ltt_context = name_map dev_ltt

(** A unification problem. *)
unopteq type unification_problem = {
  context : dev_ltt_context;
  e1 : ltt;
  e2 : ltt
}

abstract type global_context = name_map decl

type pattern_binding = unit

(** The state of the elaboration monad. *)
unopteq type elab_state = {
  global_context : global_context;
  local_context : list pattern_binding;
  proof_term : dev_ltt;
  unification_problems : list unification_problem;
  hole_queue : UList.t name
}

(** A result from the elaboration monad. *)
type elab_result a = Util.Result.result elab_err (elab_state * a)

(** The representation of the elaboration monad. *)
private let elab (a:Type) = elab_state -> M (elab_result a)

(** Return implementation for ELAB. *)
private val return_elab : a:Type -> a -> Tot (elab a)
let return_elab a x = fun s -> Ok (s, x)

(** Bind implementation for ELAB. *)
private val bind_elab : a:Type -> b:Type
                      -> x:elab a -> f:(a -> elab b) -> Tot (elab b)
let bind_elab a b x f =
  fun state ->
    let res = x state in
    bind_result res (fun (state', v) -> f v state')

(** Retrieve the state of the ELAB monad. *)
private val elab_get : unit -> Tot (elab elab_state)
let elab_get (): Tot (elab elab_state) = fun state -> Ok (state, state)

(** Put a new state into the ELAB monad. *)
private val elab_put : elab_state -> Tot (elab unit)
let elab_put s: elab unit = fun _ -> Ok (s, ())

(** Raise an error in the ELAB monad. *)
private val elab_raise : a:Type -> elab_err -> Tot (elab a)
let elab_raise a err: elab a = fun _ -> Err err

total reifiable reflectable new_effect {
  ELAB : a:Type -> Effect
  with repr = elab
     ; bind = bind_elab
     ; return = return_elab
     ; get = elab_get
     ; put = elab_put
     ; raise = elab_raise
}

private type elab_post (a:Type) = elab_state -> elab_result a -> GTot Type0

effect Elab (a:Type) (pre:ELAB?.pre) (post:elab_post a) =
  ELAB a
    (fun (state:elab_state) (p:ELAB?.post a) ->
      pre state /\
        (forall (r:elab_result a). pre state /\ post state r ==> p r))

effect TrivElab (a:Type) =
  Elab a (requires fun _ -> True) (ensures fun _ _ -> True)

let get () = ELAB?.get ()
let put (s:elab_state) = ELAB?.put s
let raise (#a:Type) (err:elab_err) = ELAB?.raise a err

reifiable reflectable new_effect {
  DIV_ELAB : a:Type -> Effect
  with repr = elab
     ; bind = bind_elab
     ; return = return_elab
     ; get = elab_get
     ; put = elab_put
     ; raise = elab_raise
}

effect DivElab (a:Type) (pre:ELAB?.pre) (post:elab_post a) =
  DIV_ELAB a
    (fun (state:elab_state) (p:ELAB?.post a) ->
      pre state /\
        (forall (r:elab_result a). pre state /\ post state r ==> p r))

sub_effect ELAB ~> DIV_ELAB {
  lift = fun (a:Type) (rep:elab a) -> rep
}

val modify : f:(elab_state -> Tot elab_state) -> TrivElab unit
let modify f =
  let cur_state = get () in
  let post_state = f cur_state in
  put post_state

(** Attempt a failable operation. *)
val attempt : #a:Type -> #pre:ELAB?.pre -> #post:elab_post a -> (unit -> Elab a pre post) -> Elab (result elab_err a)
  (requires pre)
  (ensures fun state r ->
    (match r with
    | Err _ -> False
    | Ok (state', inner_r) ->
      (match inner_r with
      | Err err -> state == state' /\ post state (Err err)
      | Ok v -> post state (Ok (state', v)))))
let attempt #a #pre #post eff =
  let cur_state = get () in
  let res = reify (eff ()) cur_state in
  match res with
  | Ok (state', v) -> put state'; Ok v
  | Err err -> Err err

(** Initialize a new proof state. *)
val new_proof : global_context -> TrivElab unit
let new_rpoof ctxt =
  let n = mintro "initial" in
  put ({
    global_context = ctxt;
    local_context = [];
    proof_term = DAbs Hole n (DVar n);
    unification_problems = [];
    hole_queue = [n]
  })

val new_term : unit -> TrivElab unit
let new_term () =
  let n = mintro "initial" in
  modify (fun cur_state -> { cur_state with
    proof_term = DAbs Hole n (DVar n);
    unification_problems = [];
    hole_queue = [n]
  })

val focus : n:name -> Elab unit
  (requires fun state -> List.mem n state.hole_queue)
  (ensures fun _ r -> Ok? r)
let focus n =
  let state = get () in
  let queue': UList.t name = n :: (UList.remove n state.hole_queue) in
  put ({ state with hole_queue = queue' })

val unfocus : unit -> Elab unit
  (requires fun state -> not (List.isEmpty state.hole_queue))
  (ensures fun _ r -> Ok? r)
let unfocus () =
  let state = get () in
  let (n :: ns) = state.hole_queue in
  let queue': UList.t name = UList.snoc ns n in
  put ({ state with hole_queue = queue' })

val new_hole : n:name -> Elab unit
  (requires fun state -> not (List.mem n state.hole_queue))
  (ensures fun _ r -> Ok? r)
let new_hole n =
  let state = get () in
  put ({ state with hole_queue = n :: state.hole_queue })

val next_hole : unit -> Elab name
  (requires fun state -> not (List.isEmpty state.hole_queue))
  (ensures fun state r -> Ok? r /\ fst (Ok?.value r) == state)
let next_hole () = List.Tot.hd (get ()).hole_queue

val remove_hole : unit -> Elab unit
  (requires fun state -> not (List.isEmpty state.hole_queue))
  (ensures fun _ r -> Ok? r)
let remove_hole () =
  let state = get () in
  put ({ state with hole_queue = List.Tot.tl state.hole_queue })


