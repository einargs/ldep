module Util.UList

open FStar.List.Tot

module L = FStar.List.Tot
module S = FStar.TSet

private val nem : #a:eqtype -> x:a -> list a -> Tot bool
let nem #a x l = not (mem #a x l)

private val snem : #a:eqtype -> x:a -> S.set a -> Tot Type0
let snem #a x s = ~(S.mem x s)

private val is_ulist : #a:eqtype -> list a -> GTot Type0
let rec is_ulist #a = function
  | [] -> True
  | x :: xs -> not (mem #a x xs) /\ is_ulist xs

type ulist (a:eqtype) = l:list a{is_ulist l}
type t = ulist

private val smem_to_mem : #a:eqtype -> l:list a -> Lemma
  (ensures forall x. mem x l <==> S.mem x (S.as_set' l))
let rec smem_to_mem #a l =
  match l with
  | [] -> ()
  | x :: xs ->
    assert (mem x l <==> S.mem x (S.as_set' l));
    smem_to_mem xs

private val snem_to_nem : #a:eqtype -> x:a -> l:ulist a -> Lemma
  (ensures nem x l <==> snem x (S.as_set' l))
let rec snem_to_nem #a x l =
  match l with
  | [] -> ()
  | y :: ys -> snem_to_nem x ys

private val not_subset_lemma : #a:eqtype -> s1:S.set a -> s2:S.set a -> Lemma
  (requires S.subset s1 s2)
  (ensures forall x. snem x s2 ==> snem x s1)
let not_subset_lemma #a s1 s2 = ()

private val lsubset : #a:eqtype -> l1:ulist a -> l2:ulist a -> Tot Type0
let lsubset #a l1 l2 = S.subset (S.as_set' l1) (S.as_set' l2)

private val nem_lsubset_lemma : #a:eqtype -> x:a -> l1:ulist a -> l2:ulist a -> Lemma
  (requires lsubset l1 l2 /\ nem x l2)
  (ensures nem x l1)
let rec nem_lsubset_lemma #a x l1 l2 =
  let s1 = S.as_set' l1 in
  let s2 = S.as_set' l2 in
  assert (nem x l2);
  snem_to_nem x l2;
  assert (snem x s2);
  assert (snem x s1);
  snem_to_nem x l1;
  assert (nem x l1);
  ()

val remove : #a:eqtype -> x:a -> l:ulist a{mem x l}
  -> Tot (ret:ulist a{lsubset ret l /\ nem x ret})
let rec remove #a x l =
  let (y :: ys) = l in
  assert (nem x l ==> nem x ys);
  if x = y then ys else
    let ys' = remove x ys in
    assert (lsubset ys' ys);
    nem_lsubset_lemma y ys' ys;
    assert (nem y ys');
    y :: ys'

private val sminus : #a:Type -> x:a -> s:S.set a -> Tot (S.set a)
let sminus #a x s = S.intersect (S.complement (S.singleton x)) s

private val sadd : #a:Type -> x:a -> s:S.set a -> Tot (S.set a)
let sadd #a x s = S.union s (S.singleton x)

private val seq_plus : #a:Type -> s1:S.set a -> x:a -> s2:S.set a -> Tot Type0
let seq_plus #a s1 x s2 = S.equal (sadd x s1) s2

private val leq_plus : #a:eqtype -> l1:ulist a -> x:a -> l2:ulist a -> Tot Type0
let leq_plus #a l1 x l2 = seq_plus (S.as_set' l1) x (S.as_set' l2)

private val nem_leq_plus_lemma : #a:eqtype -> y:a -> l1:ulist a -> x:a -> l2:ulist a -> Lemma
  (requires leq_plus l1 x l2 /\ nem y l1 /\ x <> y)
  (ensures nem y l2)
let nem_leq_plus_lemma #a y l1 x l2 =
  let s1 = S.as_set' l1 in
  snem_to_nem y l1;
  assert (snem y s1);
  let s2 = S.as_set' l2 in
  assert (seq_plus s1 x s2);
  let s1' = sadd x s1 in
  assert (S.equal s1' s2);
  assert (snem y s1');
  assert (snem y s2);
  snem_to_nem y l2;
  assert (nem y l2);
  ()

val snoc : #a:eqtype -> l:ulist a -> x:a{nem x l}
  -> Tot (ret:ulist a{leq_plus l x ret})
let rec snoc #a l x =
  match l with
  | [] -> [x]
  | y :: ys ->
    let ys' = snoc ys x in
    assert (nem y ys);
    assert (leq_plus ys x ys');
    nem_leq_plus_lemma y ys x ys';
    assert (nem y ys');
    y :: ys'

private val sdisjoint : s1:S.set 'a -> s2:S.set 'a -> Tot Type0
let sdisjoint s1 s2 = S.intersect s1 s2 `S.equal` S.empty

private val mem_sdisjoint_lemma : #a:eqtype -> x:a -> s1:S.set a -> s2:S.set a -> Lemma
  (requires sdisjoint s1 s2 /\ S.mem x s1)
  (ensures snem x s2)
let mem_sdisjoint_lemma #a x s1 s2 =
  assert (S.mem x s1 /\ S.mem x s2 ==> S.mem x (S.intersect s1 s2));
  ()

private val ldisjoint : #a:eqtype -> l1:ulist a -> l2:ulist a -> Tot Type0
let ldisjoint #a l1 l2 =
  let s1 = S.as_set' l1 in
  let s2 = S.as_set' l2 in
  sdisjoint s1 s2

private val mem_ldisjoint_lemma : #a:eqtype -> x:a -> l1:ulist a -> l2:ulist a -> Lemma
  (requires ldisjoint l1 l2 /\ mem x l1)
  (ensures nem x l2)
let mem_ldisjoint_lemma #a x l1 l2 =
  let s1 = S.as_set' l1 in
  smem_to_mem l1;
  assert (S.mem x s1);
  let s2 = S.as_set' l2 in
  mem_sdisjoint_lemma x s1 s2;
  assert (snem x s2);
  snem_to_nem x l2;
  assert (nem x l2);
  ()

private val lunion : #a:eqtype -> l1:ulist a -> l2:ulist a -> Tot (S.set a)
let lunion #a l1 l2 = S.union (S.as_set' l1) (S.as_set' l2)

private val nem_lunion_lemma : #a:eqtype -> x:a -> l1:ulist a -> l2:ulist a -> Lemma
  (requires nem x l1 /\ nem x l2)
  (ensures snem x (lunion l1 l2))
let nem_lunion_lemma #a x l1 l2 =
  let s1 = S.as_set' l1 in
  let s2 = S.as_set' l2 in
  snem_to_nem x l1;
  snem_to_nem x l2;
  assert (snem x s1 /\ snem x s2);
  ()

val append : #a:eqtype -> l1:ulist a -> l2:ulist a{ldisjoint l1 l2}
  -> Tot (ret:ulist a{S.as_set' ret `S.equal` lunion l1 l2})
let rec append #a l1 l2 =
  match l1 with
  | [] -> l2
  | x :: xs ->
    let xs': ulist a = append xs l2 in
    assert (mem x l1);
    mem_ldisjoint_lemma x l1 l2;
    assert (nem x l2);

    assert (nem x xs);
    assert (nem x l2);
    let s_xs' = S.as_set' xs' in
    assert (s_xs' `S.equal` lunion xs l2);
    nem_lunion_lemma x xs l2;
    assert (snem x s_xs');

    snem_to_nem x xs';
    assert (nem x xs');

    x :: xs'
