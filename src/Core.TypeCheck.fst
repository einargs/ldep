module Core.TypeCheck

open Core.Fc
open Core.Name
open Core.Ltt
open Core.Tc
open Core.Environment
open Core.Context
open Core.Weaken
open Core.Evaluate

module L = FStar.List.Tot

(** A mapping of the in-scope names to the type that they
    are bound to. *)
private type local_ctxt vars = local_env term vars

private let assert_is_type
  (#vars:list local_name)
  (fl:fc)
  (t:term vars)
  : TcNull unit
  = if Universe? t
    then ()
    else raise (TcTermIsNotAType fl t)

val infer_type : #vars:list local_name
               -> term vars
               -> local_ctxt vars
               -> TcNull (ty:term vars)

val check_type : #vars:list local_name
               -> ty:term vars
               -> t:term vars
               -> local_ctxt vars
               -> TcNull (ty:term vars)

let rec infer_type #vars target envr =
  match target with
  // T-Var
  | Local _ bv -> local_env_lookup_ty term bv envr
  // T-Var
  | Ref fc gn ->
    let gdef: global_def = lookup' fc (GlobalName gn) in
    L.append_l_nil vars;
    weaken_ns term vars gdef.type'
  // T-Type
  | Universe _ -> Universe EmptyFc
  // T-Pi
  | Abs fc n (Pi tyA) tyB ->
    assert_is_type fc (infer_type tyA envr);
    let envr' = ConsEnv (Pi tyA) n envr in
    assert_is_type fc (infer_type tyB envr');
    Universe EmptyFc
  // T-Lam
  | Abs fc n (Lam tyS) body ->
    let envr' = ConsEnv (Lam tyS) n envr in
    let tyT = infer_type body envr' in
    assert_is_type fc tyS;
    Abs EmptyFc n (Pi tyS) tyT
  // T-Let
  | Abs fc n (Let e1 tyS) e2 ->

and check_type #vars ty t envr =

type typed_term (vars:list local_name) =
  | Typed : value:term vars -> ty:term vars{ty == infer_type value} -> typed_term vars
