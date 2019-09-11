module Core.Raw

open Core.Fc
open Core.Name
open Core.Ltt

type raw_term (vars:list local_name) =
  | RVar : fc -> any_name -> raw_term vars
  | RUniverse : fc -> raw_term vars
  | RAbs : fc -> var:local_name
              -> bnd:binder (raw_term vars)
              -> body:raw_term (var :: vars)
              -> raw_term vars
  | RApp : fc -> l:raw_term vars
              -> r:raw_term vars
              -> raw_term vars

type closed_raw_term = raw_term []
