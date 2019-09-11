module Core.Name

open FStar.OrdSet

module M = FStar.OrdMap
module O = FStar.Order
module T = FStar.Tactics

(** Represents an identifier.

    If there's a conflict during the capture-avoiding
    substitution process, the `index` value is
    incremented. *)
type base_name = {
  index : nat;
  str : string;
}

(** A series of module names that indicates a namespace. *)
type namespace_path = list string

(** A local (un-qualified) name. *)
type local_name =
  | UserGen : base_name -> local_name
  | MachineGen : base_name -> local_name

(** A global (qualified) name.

    TODO: consider renaming this to `qualified_name`. *)
type global_name = {
  namespace : namespace_path;
  local_name : local_name
}

(** A global or local name. *)
type any_name =
  | LocalName : local_name -> any_name
  | GlobalName : global_name -> any_name

(** Get the base name of a local_name. *)
val get_base_name : local_name -> Tot base_name
let rec get_base_name = function
  | UserGen bn -> bn
  | MachineGen bn -> bn

(** Apply a modification to the base name. *)
val mod_base_name : (base_name -> Tot base_name) -> local_name -> Tot local_name
let rec mod_base_name f = function
  | UserGen bn -> UserGen (f bn)
  | MachineGen bn -> MachineGen (f bn)

(** Introduce a new user-generated local_name.

    Initializes the name with `index` at `0`. *)
val intro : string -> Tot local_name
let intro s = UserGen ({
  str = s;
  index = 0
})

(** Introduce a new machine-generated local_name. *)
val mintro : string -> Tot local_name
let mintro s = MachineGen ({
  str = s;
  index = 0
})

(** Increment the index of a local_name. *)
val inc_name : local_name -> Tot local_name
let inc_name = mod_base_name
  (fun n -> { n with index = n.index+1 })

private type ordering (a:eqtype) = a -> a -> Tot O.order

unfold private let ordering_anti_symmetry (#a:eqtype) (f:ordering a) (x:a) (y:a) =
  f x y = O.Eq ==> x = y

unfold private let ordering_transitivity (#a:eqtype) (f:ordering a) (x:a) (y:a) (z:a): GTot Type0 =
  match f x y, f y z with
  | O.Eq, o -> f x z = o
  | o, O.Eq -> f x z = o
  | o1, o2 -> if o1 = o2 then f x z = o1 else True

unfold private let ordering_totality (#a:eqtype) (f:ordering a) (x:a) (y:a): GTot Type0 =
  match f x y, f y x with
  | O.Eq, O.Eq
  | O.Gt, O.Lt
  | O.Lt, O.Gt -> True
  | _ -> False

private type total_ordering_prop (a:eqtype) (f:ordering a) =
  (forall x y. ordering_anti_symmetry f x y) // anti-symmetry
  /\ (forall x y z. ordering_transitivity f x y z) // transitivity
  /\ (forall x y. ordering_totality f x y) // totality

private val total_order_form : #a:eqtype -> (ordering a) -> Tot (a -> a -> Tot bool)
let total_order_form #a f x y = O.ge (f x y)

private val ordering_is_total : a:eqtype -> (ordering a) -> GTot Type0
let ordering_is_total a f = total_ordering_prop a f
                            /\ total_order a (total_order_form f)

private let order_transitivity (a:eqtype) (g:(a -> a -> Tot bool)) (x:a) (y:a) (z:a) =
  g x y /\ g y z ==> g x z

private val order_transitivity_lemma : #a:eqtype -> g:(a -> a -> Tot bool)
                                     -> Lemma
  (requires forall x y z. order_transitivity a g x y z)
  (ensures forall x y z. g x y /\ g y z ==> g x z)
let order_transitivity_lemma #a g =
  assert_norm ((forall x y z. order_transitivity a g x y z)
         ==> (forall x y z. g x y /\ g y z ==> g x z));
  ()

private val ordering_transitivity_lemma : #a:eqtype -> f:ordering a
                                        -> x:a -> y:a -> z:a
                                        -> Lemma
  (requires ordering_transitivity f x y z)
  (ensures (let g = total_order_form f in g x y /\ g y z ==> g x z))
  [SMTPat (order_transitivity a (total_order_form f) x y z)]
let ordering_transitivity_lemma #a f x y z = ()

private val total_order_derivation_lemma : #a:eqtype -> f:ordering a -> Lemma
  (requires total_ordering_prop a f)
  (ensures total_order a (total_order_form f))
  [SMTPat (total_ordering_prop a f)]
let total_order_derivation_lemma #a f =
  let g = total_order_form f in
  // Prove that anti-symmetry converts
  assert (forall x y. ordering_anti_symmetry f x y ==> (g x y /\ g y x ==> x = y));
  assert (forall x y. g x y /\ g y x ==> x = y);

  // Prove that transitivity converts
  assert (forall x y z. ordering_transitivity f x y z ==> (g x y /\ g y z ==> g x z));
  assert (forall x y z. order_transitivity a g x y z);
  order_transitivity_lemma g;
  assert (forall x y z. g x y /\ g y z ==> g x z);

  // Prove that totality converts
  assert (forall x y. ordering_totality f x y ==> (g x y \/ g y x));
  assert (forall x y. g x y \/ g y x);

  ()

private type total_ordering (a:eqtype) =
  f:(a -> a -> Tot O.order){ordering_is_total a f}

private val compare_string : total_ordering string
let compare_string = admit ();
  fun s1 s2 -> O.order_from_int (String.compare s1 s2)

private val compare_nat_total_lemma : unit -> Lemma
  (ensures total_ordering_prop nat O.compare_int)
let compare_nat_total_lemma () = ()

private val compare_base_name : total_ordering base_name
let compare_base_name b1 b2 =
  match O.compare_int b1.index b2.index with
  | O.Lt -> O.Lt
  | O.Gt -> O.Gt
  | O.Eq -> compare_string b1.str b2.str

private val compare_local_name' : ordering local_name
let compare_local_name' n1 n2 =
  let rank (n:local_name): nat =
    match n with
    | UserGen _ -> 1
    | MachineGen _ -> 0 in

    match n1, n2 with
    | UserGen b1, UserGen b2 -> compare_base_name b1 b2
    | MachineGen b1, MachineGen b2 -> compare_base_name b1 b2
    | _ -> O.compare_int (rank n1) (rank n2)

private val compare_local_name_total_lemma : unit -> Lemma
  (ensures ordering_is_total local_name compare_local_name')
let compare_local_name_total_lemma () = ()

private val compare_local_name : total_ordering local_name
let compare_local_name =
  compare_local_name_total_lemma ();
  compare_local_name'

private val compare_list_anti_symmetry_lemma : #a:eqtype -> g:total_ordering a
                                     -> l1:list a -> l2:list a
                                     -> Lemma
  (ensures (let f = O.compare_list g in
           (ordering_anti_symmetry f l1 l2)))
let rec compare_list_anti_symmetry_lemma #a g l1 l2 =
  let f = O.compare_list g in
  match l1, l2 with
  | [], [] -> ()
  | [], _ -> ()
  | _, [] -> ()
  | x :: xs, y :: ys -> compare_list_anti_symmetry_lemma g xs ys; ()

private val compare_list_totality_lemma : #a:eqtype -> g:total_ordering a
                                     -> l1:list a -> l2:list a
                                     -> Lemma
  (ensures (let f = O.compare_list g in
           (ordering_totality f l1 l2)))
let rec compare_list_totality_lemma #a g l1 l2 =
  let f = O.compare_list g in
  match l1, l2 with
  | [], [] -> ()
  | [], _ -> ()
  | _, [] -> ()
  | x :: xs, y :: ys -> compare_list_totality_lemma g xs ys; ()

private val compare_list_transitivity_lemma : #a:eqtype -> g:total_ordering a
                                            -> l1:list a -> l2:list a -> l3:list a
                                            -> Lemma
  (ensures (let f = O.compare_list g in
           ordering_transitivity f l1 l2 l3))
let rec compare_list_transitivity_lemma #a g l1 l2 l3 =
  let f = O.compare_list g in
  match l1, l2, l3 with
  | x::xs, y::ys, z::zs ->
    compare_list_transitivity_lemma g xs ys zs;
    (match g x y, g y z with
    | O.Eq, o -> assert (g x z = o); ()
    | o, O.Eq -> assert (g x z = o); ()
    | o1, o2 -> if o1=o2
      then (assert (g x z = o1); ())
      else ())
  | _ -> ()

private val compare_list_total_lemma : #a:eqtype -> g:total_ordering a
                                     -> Lemma
  (ensures ordering_is_total (list a) (O.compare_list g))
let compare_list_total_lemma #a g =
  let f = O.compare_list g in
  assert (forall x y. ordering_anti_symmetry (O.compare_list g) x y)
    by (let _ = T.forall_intros () in
       T.apply_lemma (`compare_list_anti_symmetry_lemma));
  assert (forall x y. ordering_totality f x y)
    by (let _ = T.forall_intros () in
       T.apply_lemma (`compare_list_totality_lemma));
  assert (forall x y z. ordering_transitivity f x y z)
    by (ignore (T.forall_intros ());
       T.apply_lemma (`compare_list_transitivity_lemma));
  assert (total_ordering_prop (list a) f);
  ()

private val compare_global_name' : ordering global_name
let compare_global_name' gn1 gn2 =
  match compare_local_name gn1.local_name gn2.local_name with
  | O.Lt -> O.Lt
  | O.Gt -> O.Gt
  | O.Eq ->
    O.compare_list compare_string gn1.namespace gn2.namespace

private val compare_global_name_lemma : unit -> Lemma
  (ensures ordering_is_total global_name compare_global_name')
let compare_global_name_lemma () = compare_list_total_lemma compare_string

private val compare_global_name : total_ordering global_name
let compare_global_name =
  compare_global_name_lemma ();
  compare_global_name'

private val compare_any_name : total_ordering any_name
let compare_any_name an1 an2 =
  match an1, an2 with
  | GlobalName gn1, GlobalName gn2 -> compare_global_name gn1 gn2
  | GlobalName _, LocalName _ -> O.Gt
  | LocalName _, GlobalName _ -> O.Lt
  | LocalName ln1, LocalName ln2 -> compare_local_name ln1 ln2

private unfold let order_map (#t:eqtype) (ordering:total_ordering t) (a:Type) =
  M.ordmap t a (total_order_form ordering)

(** A total ordering on local names.

    Needs to be `abstract` or it causes problems with
    monads. *)
abstract val local_name_order : cmp local_name
let local_name_order = total_order_form compare_local_name

(** A total ordering on global names.

    Needs to be `abstract` or it causes problems with
    monads. *)
abstract val global_name_order : cmp global_name
let global_name_order = total_order_form compare_global_name

(* A total ordering on `any_name`s.

    Needs to be `abstract` or it causes problems with
    monads.
abstract val any_name_order : cmp any_name
let any_name_order = total_order_form compare_any_name *)

(** A type alias for a set of local names.

    Generally used when calculating free variables. *)
let local_name_set: Type0 = ordset local_name local_name_order

(** A type alias for a map from local names to `a`. *)
type local_name_map (a:Type) = M.ordmap local_name a local_name_order

(** A type alias for a map from global names to `a`. *)
type global_name_map (a:Type) = M.ordmap global_name a global_name_order

(** A type alias for a map from global and local names to 'a'. *)
type any_name_map = order_map compare_any_name
