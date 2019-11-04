module Core.Environment

open Core.Weaken
open Core.Name
open Core.Ltt

module M = FStar.OrdMap

unopteq type local_env (tm:list local_name -> Type) : (vars:list local_name) -> Type =
  | EmptyEnv : local_env tm []
  | ConsEnv : #vars:list local_name
            -> binder (tm vars)
            -> name:local_name // the name bound by the binder
            -> local_env tm vars
            -> local_env tm (name :: vars)

private let rec descend
  (#vars:list local_name)
  (#name:local_name)
  (tm:list local_name -> Type)
  [|weaken tm|]
  (idx:var_index name vars)
  (envr:local_env tm vars)
  : Tot (binder (tm vars))
  = assert (ConsEnv? envr);
    match envr with
    | ConsEnv bnd name' rest ->
      let bnd_vars = List.Tot.tl vars in
      let bnd': binder (tm bnd_vars) =
        if idx = 0 then (
          assert (name = name');
          bnd
        ) else (
          descend #bnd_vars #name tm (idx-1) rest
        ) in
      weaken' #bnd_vars #name' (binder_tm tm) bnd'

let local_env_lookup_binder
  (#vars:list local_name)
  (tm:list local_name -> Type)
  [|weaken tm|]
  (bv:bound_var vars)
  (envr:local_env tm vars)
  : Tot (binder (tm vars))
  = match bv with
  | BoundVar idx -> descend tm idx envr

let local_env_lookup_ty
  (#vars:list local_name)
  (tm:list local_name -> Type)
  [|weaken tm|]
  (bv:bound_var vars)
  (envr:local_env tm vars)
  : Tot (tm vars)
  = binder_ty (local_env_lookup_binder tm bv envr)
