module Core.Context

open Core.Fc
open Core.Name
open Core.Ltt

(** The actual "implementation" of top-level definitions
    (i.e. whether it's a function, or a data constructor).

    Future cases are things like type constructors and
    data constructors. *)
type def =
  | Function : body:closed_term -> def

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

val term_for_gdef : global_def -> Tot closed_term
let term_for_gdef gdef =
  match gdef.definition with
  | Function body -> body

unopteq type context = {
  content: any_name_map global_def;
}

(** Initialize a context based on a list of names and definitions. *)
val init_context : list (any_name * global_def)
                 -> context
let init_context l =
  let f c (n, d) = OrdMap.update n d c in
  let content = List.Tot.fold_left f OrdMap.empty l in
  { content = content }

val lookup_gdef : any_name -> context -> Tot (option global_def)
let lookup_gdef name ctxt = OrdMap.select name ctxt.content
