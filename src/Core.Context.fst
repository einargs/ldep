module Core.Context

open Core.Fc
open Core.Name
open Core.Ltt

(** The actual "implementation" of top-level definitions
    (i.e. whether it's a function, or a data constructor).

    Future cases are things like type constructors and
    data constructors. *)
type def =
  | Function : ty:closed_term -> body:closed_term -> def

(** Contains extra context *)
type global_def = {
  location : fc;
  qualified_name : global_name;
  type': closed_term;
  definition: def;
}

(** Create a global definition with no location and with
    `["Main"]` for the namespace. *)
val mk_gdef : string -> closed_term -> def -> Tot global_def
let mk_gdef name ty d = {
  location = EmptyFc;
  qualified_name = {
    namespace = ["Main"];
    local_name = intro name;
  };
  type' = ty;
  definition = d;
}

val body_of_gdef : global_def -> Tot closed_term
let body_of_gdef gdef =
  match gdef.definition with
  | Function _ body -> body

(** Utility function that lifts a predicate over an option type,
    defaulting to `True` if it's `None`. *)
private val pred_over_option : ('a -> Type0)
                     -> option 'a
                     -> Type0
let pred_over_option p = function
  | Some v -> p v
  | None -> True

abstract type definitions_map =
  map:global_name_map global_def{forall n.
    match OrdMap.select n map with
    | Some def -> n = def.qualified_name
    | None -> True
  }

(** An empty `definitions_map`. *)
let empty_definitions_map
  : definitions_map
  = OrdMap.empty

(** Insert a definition into a `definitions_map`. *)
let insert_definition
  (def:global_def)
  (map:definitions_map)
  : Tot definitions_map
  = OrdMap.update def.qualified_name def map

(** Lookup a definition in a `definitions_map`
    based on its qualified name. *)
let get_definition
  (name:global_name)
  (map:definitions_map)
  : Tot (res:option global_def{
    pred_over_option
      (fun def -> def.qualified_name = name)
      res
  })
  = OrdMap.select name map

unopteq type context = {
  definitions: definitions_map
}

(** Initialize a context based on a list of definitions. *)
val init_context : list global_def
                 -> Tot context
let init_context l =
  let f map def = insert_definition def map in
  let definitions = List.Tot.fold_left f empty_definitions_map l in
  { definitions = definitions }

(** Lookup a definition based on its qualified name. *)
val lookup_gdef : name:global_name
                -> context
                -> Pure (option global_def)
  (requires True)
  (ensures (pred_over_option
    (fun def -> def.qualified_name == name)))
let lookup_gdef name ctxt = get_definition name ctxt.definitions
