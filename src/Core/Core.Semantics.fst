module Core.Semantics

open FStar.Tactics

open Core.Ltt

val gt_than_top_name_in : bound_name -> ltt -> GTot bool
let gt_than_top_name_in v t =
  match top_bound_name t with
  | Some v' -> v > v'
  | None -> true

val does_enclose : bound_name -> ltt -> GTot bool
let does_enclose v t = v = enclosing_name_of t

val mk_dump : string -> unit -> Tac unit
let mk_dump str = fun () -> dump str

val bound_names_increase_implies_enclosing_name : t:ltt{Abs? t}
    -> Lemma (ensures ((Abs?.var t) = enclosing_name_of (Abs?.expr t)))
let bound_names_increase_implies_enclosing_name t = ()

val enclosing_name_implies_bound_name:
  bnd:binder
  -> var:bound_name
  -> body:ltt {var = enclosing_name_of body}
  -> Lemma (ensures bound_names_increase (Abs bnd var body))
let enclosing_name_implies_bound_name bnd var body = ()

val has_free_bound_name : v:bound_name -> t:ltt{gt_than_top_name_in v t} -> Tot bool
let rec has_free_bound_name v t =
  match t with
  | Var (Bound v') -> v' = v
  | App l r ->
    assert (bound_names_increase l);
    assert (bound_names_increase r);
    let t_top = top_bound_name t in
    let l_top = top_bound_name l in
    assert (enclosing_name_of t >= enclosing_name_of l);
    assert (gt_than_top_name_in v l);
    assert (gt_than_top_name_in v r);
    has_free_bound_name v l || has_free_bound_name v r
  | Abs bnd _ body ->
    let in_binding = match bnd with
      | Pi ty -> has_free_bound_name v ty
      | Lam -> false in
    in_binding || has_free_bound_name v body
  | _ -> false

val subst : arg:ltt
          -> v:bound_name
          -> body:ltt { gt_than_top_name_in v body }
          -> Tot (ret:ltt { enclosing_name_of ret = if has_free_bound_name v body then enclosing_name_of arg + enclosing_name_of body else enclosing_name_of body}) (decreases body)
let rec subst arg v body =
  let var_bump = (enclosing_name_of arg) in
  match body with
  | Var (Bound v') -> if v = v' then arg else body
  | Var name -> Var name
  | Abs bnd v' body' ->
    assert (bound_names_increase body);
    bound_names_increase_implies_enclosing_name body;
    assert (v' = enclosing_name_of body');
    let new_var = var_bump + v' in
    let new_body: ltt = (subst arg v body') in
    let ret = Abs bnd new_var new_body in
    assert (new_var = enclosing_name_of new_body);
    enclosing_name_implies_bound_name bnd v' new_body;
    assert (bound_names_increase ret);
    ret
  | App l r -> App (subst arg v l) (subst arg v r)
  | Universe n -> Universe n

