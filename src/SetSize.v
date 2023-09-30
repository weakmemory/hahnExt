(* Require Import AuxProp. *)
Require Import IndefiniteDescription.
Require Import PropExtensionality.
Require Import ClassicalDescription.
Require Import Lia.
Require Import Arith.
From hahn Require Import Hahn.

Import ListNotations.
Set Implicit Arguments.

Definition set_size {A: Type} (S: A -> Prop): nat_omega :=
  match (excluded_middle_informative (set_finite S)) with
  | left FIN => (NOnum (length (undup (filterP S (proj1_sig (constructive_indefinite_description _ FIN))))))
  | right _ => NOinfinity
  end. 

Lemma lt_size_of_finite A (s : A -> Prop) d
      (SUB: forall x, s x -> In x d) n :
  lt_size n s <-> n < length (undup (filterP s d)).
Proof using.
  unfold lt_size; split; ins; desf.
    eapply Nat.lt_le_trans, NoDup_incl_length; unfold incl; eauto.
    ins; rewrite in_undup_iff, in_filterP_iff; desf; eauto.
    exists (undup (filterP s d)); splits; ins.
    rewrite in_undup_iff, in_filterP_iff in *; desf; eauto.
Qed.

Lemma set_lt_size {A: Type} (S: A -> Prop) i:
  NOmega.lt_nat_l i (set_size S) <-> lt_size i S.
Proof using.
  unfold set_size. destruct (excluded_middle_informative _).
  2: { simpl. split; auto. ins. by apply lt_size_infinite. }
  destruct (constructive_indefinite_description _).
  simpl. symmetry. by apply lt_size_of_finite.
Qed. 

Lemma enumeratesE' {A : Type} (f : nat -> A) (s : A -> Prop):
  enumerates f s <->
  let dom := fun i => NOmega.lt_nat_l i (set_size s) in
  ⟪INSET: forall i : nat, dom i -> s (f i)⟫ /\
  ⟪INJ: forall i : nat, dom i -> forall j : nat, dom j -> f i = f j -> i = j⟫ /\
  ⟪IND: forall a : A, s a -> exists i : nat, dom i /\ f i = a⟫.
Proof using.
  etransitivity.
  { apply enumeratesE. }
  pose proof (set_lt_size s) as EQUIV. 
  split.
  { ins. desc. splits; ins.
    { by apply RNG, EQUIV. }
    { by apply INJ; [apply EQUIV | apply EQUIV| apply H1]. }
    { apply SUR in H. desc. exists i. split; auto. by apply EQUIV. }
  }
  { ins. desc. splits; ins. 
    { by apply INSET, EQUIV. }
    { by apply INJ; [apply EQUIV | apply EQUIV| ]. }
    { apply IND in IN. desc. exists i. split; auto. by apply EQUIV. }
  }
Qed.

Lemma set_size_equiv {A: Type} (S1 S2: A -> Prop) (EQ: S1 ≡₁ S2):
  set_size S1 = set_size S2.
Proof using.
  cut (S1 = S2); [congruence| ].  
  extensionality a. apply propositional_extensionality.
  by apply set_equiv_exp. 
Qed. 

Lemma set_size_empty {A: Type} (s: A -> Prop):
  set_size s = NOnum 0 <-> s ≡₁ ∅.
Proof.
  split; intros. 
  { unfold set_size in H. destruct excluded_middle_informative; try by vauto.
    destruct constructive_indefinite_description. simpl in *.
    inversion H. apply length_zero_iff_nil in H1.
    destruct (classic (s ≡₁ ∅)) as [? | NEMPTY]; auto. 
    apply set_nonemptyE in NEMPTY. desc.
    specialize (i _ NEMPTY).
    assert (In x0 nil); [| by vauto].
    rewrite <- H1. apply in_undup_iff. apply in_filterP_iff. auto. }
  erewrite set_size_equiv; eauto.
  unfold set_size. destruct excluded_middle_informative.
  2: { destruct n. by exists nil. }
  f_equal. destruct constructive_indefinite_description. simpl in *.
  rewrite (proj2 (filterP_eq_nil ∅ x)); vauto.
Qed. 

Lemma set_size_finite {A} (s : A -> Prop) :
  set_finite s <-> exists n : nat, set_size s = NOnum n.
Proof using.
  split; ins; unfold set_size in *; desf.
  eauto.
Qed.

Lemma set_finite_precise_list {A} (s : A -> Prop)
  (FF : set_finite s) :
  exists l,
    << IN    : forall a, s a <-> In a l >> /\
    << UNDUP : NoDup l >> /\
    << SIZE  : set_size s = NOnum (length l) >>.
Proof using.
  remember FF as AA. clear HeqAA.
  red in AA. desf.
  exists (undup (filterP s findom)).
  splits; ins.
  { split; intros HH.
    { apply in_undup_iff. apply in_filterP_iff. splits; auto. }
    apply in_undup_iff with (l:=filterP s findom) in HH.
    apply in_filterP_iff in HH. desf. }
  unfold set_size. desf.
  f_equal. unfold proj1_sig. desf.
  clear Heq.
  apply Permutation_length, NoDup_Permutation.
  1, 2: by apply nodup_undup.
  ins. 
  etransitivity; [rewrite in_undup_iff; apply in_filterP_iff| ].
  etransitivity; [| symmetry; rewrite in_undup_iff; apply in_filterP_iff].
  intuition. 
Qed.

Lemma set_size_fin_le {A} (s q : A -> Prop) a b
  (SS : set_size s = NOnum a)
  (SQ : set_size q = NOnum b)
  (IN : s ⊆₁ q) :
  a <= b.
Proof using.
  assert (set_finite s /\ set_finite q) as [FS FQ].
  { split; apply set_size_finite; eauto. }
  destruct (set_finite_precise_list FS) as [ls AA].
  destruct (set_finite_precise_list FQ) as [lq BB].
  desf.
  assert (a = length ls); subst.
  { rewrite SS in SIZE0. inv SIZE0. }
  assert (b = length lq); subst.
  { rewrite SQ in SIZE. inv SIZE. }
  apply NoDup_incl_length; auto.
  red. ins. apply IN0. apply IN. now apply IN1.
Qed.

(* TODO: change definition of le, lt, leb, ltb in hahn/HahnOmega.v *)
Definition le_new n m :=
  match n, m with
  | NOnum n, NOnum m => n <= m
  | _,       NOnum m => False
  | _, _ => True
  end.

Theorem le_new_antisymm n m (LENM : le_new n m) (LEMN : le_new m n) :
  n = m.
Proof.
  unfold le_new in *.
  destruct n, m; intuition auto with *.
Qed.

Lemma infinite_set_not_empty : forall (A : Type) (s : A -> Prop), (~set_finite s) ->
  exists x : A, s x.
Proof.
  ins. apply NNPP.
  unfold not.
  ins. apply H.
  unfold set_finite.
  exists nil.
  ins. apply H0.
  by exists x.
Qed.

Lemma undup_filterP_eq {A} (x : A) l (IN : In x l) :
  undup (filterP (eq x) l) = [x].
Proof using.
  induction l; ins; desf; intuition.
  2: { unfold undup. desf; fold undup; intuition.
       exfalso. apply n. apply in_filterP_iff. desf. }
  destruct (classic (In x l)) as [IN|NIN].
  { unfold undup. desf; fold undup.
    { intuition. }
    exfalso. apply n. apply in_filterP_iff. desf. }
  unfold undup. desf; fold undup.
  { exfalso. apply NIN. apply in_filterP_iff in i.
    desf. }
  arewrite (filterP (eq x) l = []); ins.
  apply filterP_eq_nil. ins; desf.
Qed.

Lemma set_size_single {A} (x : A) :
  set_size (eq x) = NOnum 1.
Proof using.
  unfold set_size. desf.
  2: { exfalso. apply n. exists [x]. ins; eauto. }
  unfold proj1_sig. desf.
  f_equal.
  assert (In x (undup (filterP (eq x) x0))) as AA.
  { apply in_undup_iff. apply in_filterP_iff; auto. }
  rewrite undup_filterP_eq; intuition.
Qed.

Lemma set_size_union {A} (s q : A -> Prop) a b
  (SS   : set_size s = NOnum a)
  (SQ   : set_size q = NOnum b) :
  le_new (set_size (set_union s q)) (NOnum (a + b)).
Proof using.
  unfold le_new. desf.
  { unfold set_size, set_finite in *. desf.
    destruct e0 as [ls Els].
    destruct e  as [lq Elq].
    destruct n.
    exists (ls ++ lq).
    unfolder. ins. desf.
    { apply Els in IN. apply in_app_l. done. }
    apply Elq in IN. apply in_app_r. done. }
  assert (set_finite s /\ set_finite q /\ set_finite (s ∪₁ q)) as [FS [FQ FSQ]].
  { splits; apply set_size_finite; eauto. }
  destruct (set_finite_precise_list FS) as [ls AA].
  destruct (set_finite_precise_list FQ) as [lq BB].
  destruct (set_finite_precise_list FSQ) as [lsq CC].
  desf.
  assert (a = length ls); subst.
  { rewrite SS in SIZE1. inv SIZE1. }
  assert (b = length lq); subst.
  { rewrite SQ in SIZE0. inv SIZE0. }
  assert (n = length lsq); subst.
  { rewrite Heq in SIZE. inv SIZE. }
  assert (incl lsq (ls ++ lq)) as II.
  { red. intros a AA. apply IN in AA. apply in_app_iff.
    now destruct AA; [left; apply IN1|right; apply IN0]. }
  clear -II UNDUP.
  rewrite <- app_length.
  apply NoDup_incl_length; auto.
Qed.

Lemma disjoint_undup_l {A} (l l' : list A) :
  disjoint (undup l) l' <-> disjoint l l'.
Proof using.
  split; intros AA a IN IN'.
  all: eapply AA; eauto.
  all: now apply in_undup_iff.
Qed.

Lemma disjoint_undup_r {A} (l l' : list A) :
  disjoint l (undup l') <-> disjoint l l'.
Proof using.
  split; intros AA a IN IN'.
  all: eapply AA; eauto.
  all: now apply in_undup_iff.
Qed.

Lemma disjoint_undup_lr {A} (l l' : list A) :
  disjoint (undup l) (undup l') <-> disjoint l l'.
Proof using. now rewrite disjoint_undup_l, disjoint_undup_r. Qed.

Lemma set_size_union_disjoint {A} (s q : A -> Prop) a b
  (SS   : set_size s = NOnum a)
  (SQ   : set_size q = NOnum b)
  (DISJ : set_disjoint s q) :
  set_size (set_union s q) = NOnum (a + b).
Proof using.
  apply le_new_antisymm.
  { now apply set_size_union. }
  unfold set_size, proj1_sig in *. desf; intuition auto with *.
  rename x into lsq. 
  rename x0 into lq.
  rename x1 into ls. 
  clear Heq Heq0 Heq1.
  red.
  rewrite <- length_app.
  apply NoDup_incl_length.
  { apply nodup_append; try now apply nodup_undup.
    apply disjoint_undup_lr.
    red. ins.
    apply in_filterP_iff in IN1.
    apply in_filterP_iff in IN2.
    desf. eapply DISJ; eauto. }
  red. intros a AA.
  apply in_undup_iff.
  apply in_filterP_iff.
  enough (set_union s q a) as BB by (split; auto).
  apply in_app_iff in AA. destruct AA as [AA|AA]; [left|right].
  all: apply in_undup_iff with (l:=filterP _ _) in AA.
  all: apply in_filterP_iff in AA; desf.
Qed.

Add Parametric Morphism A : (@set_size A) with signature 
  set_subset ==> le_new as set_size_mori.
Proof.
  ins. unfold set_size, proj1_sig.
  desf.
  { apply NoDup_incl_length; unfold incl; auto.
    ins; rewrite in_undup_iff, in_filterP_iff in *; desf; eauto. }
  apply set_finite_mori in H. unfold Basics.impl in H. intuition. 
Qed.

Add Parametric Morphism A : (@set_size A) with signature
  set_equiv ==> eq as set_size_more.
Proof using.
  ins. red in H; desc.
  apply le_new_antisymm; by apply set_size_mori.
Qed.
