module Core.Evaluate

open Core.Ltt
open Core.Tc

(** Notion of equality based on version3 of `pi-forall`.
    
    TODO: review this code; I think there are possible
    problems, primarily with the way variables are handled--
    in version3 `unbind2Plus` from the Unbound library
    is used, and I'm not sure exactly what that's for.
    
    The other potential problem I see is just the fact
    that I don't have a solid understanding of what
    type theory I'm working under, which could introduce
    subtle bugs. *)
val equate : ltt -> ltt -> Tc unit
let equate t1 t2 =
  // if two terms have alpha equality they're
  // equal.
  if alpha_eq t1 t2 then () else 
    let t1' = whnf t1 in
    let t2' = whnf t2 in
    let not_equal = CannotEquate t1' t2' in
    match t1', t2' with
    // Since we currently only have one Universe,
    // they're trivially equal.
    | Universe, Universe -> ()
    
    // Variables are equal if the names are equal.
    //
    // TODO: figure out if this is going to cause
    // bugs. Hopefully the check for alpha equality
    // should ensure that this only comes up if both
    // variables are free.
    | Var x, Var y -> require (x = y)

    // Applications are equal if the left and right
    // sides are equal.
    | App l1 r1, App l2 r2 ->
      equate l1 l2;
      equate r1 r2

    // Equality of abstractions depends on the binding.
    | Abs bnd1 v1 tm1, Abs bnd2 v2 tm2 ->
      match bnd1, bnd2 with
      // Lambdas are equal if the bodies are equal.
      //
      // >>> \x.e = \y.e
      | Lam, Lam -> equate tm1 tm2

      // Pis are the same if the types are the equal
      // and the bodies are the equal.
      //
      // >>> (x:A) -> B = (y:A) -> B
      | Pi ty1, Pi ty2 ->
        equate ty1 ty2;
        equate tm1 tm2

      // If neither matches, the abstractions are
      // not equal.
      | _ -> raise not_equal

    // If none of these cases match, the terms are
    // not equal.
    | _ -> raise not_equal

(** Assert that a value is a function type. *)
val ensurePi : ltt -> Tc (ty: ltt * var: name * body: ltt)
let ensurePi t =
  let t' = whnf t in
  match t' with
  | Abs (Pi ty) var body -> ty * var * body
  | _ -> raise (ExpectedFunctionType t)

(** Put a term into weak head normal form.
    
    Based on version3 of `pi-forall`. *)
val whnf : ltt -> Tc ltt
let rec whnf t =
  match t with
  | Var n ->
    match lookup_def n with
    | Some v -> v
    | None -> t
  | App l r ->
    match l with
    | Abs Lam v body ->
      whnf (subst r v body)
    | _ -> t
  | _ -> t