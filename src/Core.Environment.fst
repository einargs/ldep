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

let rec env_lookup
  (#vars:list local_name)
  (tm:list local_name -> Type)
  [|weaken tm|]
  (name:local_name)
  (envr:local_env tm vars)
  : option (binder (tm vars))
  = match envr with
  | EmptyEnv -> None
  | ConsEnv bnd n' rest ->
    let opt_bnd = if n' = name
      then Some bnd
      else env_lookup tm name rest in
    let v :: vs = vars in
    assert (opt_bnd `has_type` option (binder (tm vs)));
    let map_bnd (bnd:binder (tm vs))
      : binder (tm vars) =
      let bnd' = weaken' #vs #v (binder_tm tm) bnd in
      assert (bnd' `has_type` binder (tm vars));
      bnd' in
    match opt_bnd with
    | Some b -> Some (map_bnd b)
    | None -> None
