module Core.Environment

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
private val shave_vars : n:local_name
                       -> l:list local_name{n `List.mem` l}
                       -> Tot (list local_name)
let rec shave_vars n (x::xs) =
  if n = x then xs else shave_vars n xs

(*private val expand_term : #vars:list local_name
                        -> #outer:list local_name
                        -> raw_term vars
                        -> Tot (raw_term (vars @ outer))
let expand_term #vars #outer #tm = function
  | RVar fc n -> RVar fc n
  | RUniverse fc -> RUniverse fc
  | RAbs fc var bnd body -> RAbs fc var bnd body
  | RApp fc l r -> RApp fc l r


type expand_tm (tm:list local_name -> Type) =
  vars:list local_name -> name:local_name ->
  tm vars -> Tot (tm (name :: vars))

private val expand_binder : #tm:(list local_name -> Type)
                          -> #vars:list local_name
                          -> name:local_name
                          -> tm_helper:expand_tm tm
                          -> binder (tm vars)
                          -> Tot (binder (tm (name :: vars)))
let expand_binder #tm #vars name tm_helper = map_binder (tm_helper vars name)*)

val env_lookup : #tm:(list local_name -> Type)
               -> #vars:list local_name
               -> name:local_name
               -> local_env tm vars
               -> Tot (
               option (if name `List.mem` vars
                       then (binder (tm (shave_vars name vars)))
                       else False))
let rec env_lookup #tm #vars name envr =
  match envr with
  | EmptyEnv -> None
  | ConsEnv bnd n' rest ->
    if n' = name then (
      Some bnd
    ) else (
      env_lookup name rest
    )

(*val env_lookup_lemma : #tm:(list local_name -> Type)
                     -> #vars:list local_name
                     -> name:local_name
                     -> envr:local_env tm vars
                     -> Lemma
  (ensures (let res = env_lookup name envr in
           Some? res ==> (name `List.mem` vars /\ res `has_type` binder (tm (shave_vars name vars)))))
let env_lookup_lemma #tm #vars name envr = ()*)

