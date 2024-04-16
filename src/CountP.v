Require Import Setoid Lia.
From hahn Require Import Hahn.

Definition countP {A} (f: A -> Prop) (l : list A) :=
  length (filterP f l).

Add Parametric Morphism A : (@countP A) with signature
    (@set_subset A) ==> eq ==> le as countP_mori.
Proof using.
  ins. unfold countP.
  induction y0.
  { simpls. }
  ins. desf; simpls.
  1,3: lia.
  exfalso. apply n. by apply H.
Qed.

Add Parametric Morphism A : (@countP A) with signature
    set_equiv ==> eq ==> eq as countP_more.
Proof using.
  ins. unfold countP.
  erewrite filterP_set_equiv; eauto.
Qed.

Lemma countP_strict_mori {A} (e : A) l P P'
      (IN : P ⊆₁ P')
      (INP  : ~ P e)
      (INP' :  P' e)
      (INL  : In e l) :
  countP P l < countP P' l.
Proof using.
  generalize dependent e.
  induction l; simpls.
  ins. desf.
  { unfold countP; simpls. desf. simpls.
    apply PeanoNat.Nat.lt_succ_r. by apply countP_mori. }
  unfold countP; simpls. desf; simpls.
  { apply PeanoNat.Nat.succ_lt_mono with (n:=length (filterP P l)). eapply IHl; eauto. }
  { exfalso. apply n. by apply IN. }
  { apply PeanoNat.Nat.lt_succ_r. by apply countP_mori. }
  by apply IHl with (e:=e).
Qed.

Fixpoint countNatP (p: nat -> Prop) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n =>
    let shift := if excluded_middle_informative (p n)
                 then 1 else 0
    in
    shift + countNatP p n
  end.

Add Parametric Morphism : countNatP with signature
  set_subset ==> eq ==> le as countNatP_mori.
Proof using.
ins. unfold countNatP.
induction y0.
{ simpls. }
ins. desf; simpls.
1,3: lia.
exfalso. apply n. by apply H.
Qed.

Lemma countNatP_lt e n s s' (IN : s ⊆₁ s') (NSE : ~ s e) (SE : s' e) (LE : e < n) :
  countNatP s n < countNatP s' n.
Proof using.
  ins. unfold countNatP.
  generalize dependent e.
  induction n.
  { ins. lia. }
  ins. fold countNatP in *.
  apply PeanoNat.Nat.lt_succ_r with (m:=n) in LE.
  destruct LE as [|m].
  { desf; ins. apply PeanoNat.Nat.lt_succ_r.
    eapply countNatP_mori; auto. }
  apply PeanoNat.Nat.add_le_lt_mono.
  2: { eapply IHn; eauto. lia. }
  destruct (excluded_middle_informative (s (S m))) as [SS|SS].
  2: lia.
  clear -IN SS. desf. exfalso. apply n. by apply IN.
Qed.

Add Parametric Morphism : countNatP with signature
    set_equiv ==> eq ==> eq as countNatP_more.
Proof using.
  ins.
  induction y0.
  { simpls. }
  ins. desf; simpls.
  { by rewrite IHy0. }
  { apply H in x0. desf. }
  apply H in y1. desf.
Qed.

Lemma countNatP_empty n : countNatP ∅ n = 0.
Proof using. induction n; simpls; desf. Qed.

Lemma countNatP_zero s n : countNatP s n = 0 <-> forall m, s m -> n <= m.
Proof using.
  red. split.
  { induction n.
    { ins; lia. }
    unfold countNatP.
    destruct (excluded_middle_informative (s n)) as [HH | nHH].
    { ins; lia. }
    rewrite PeanoNat.Nat.add_0_l.
    intros HH m Sm.
    eapply IHn in HH; eauto.
    destruct HH; intuition auto with *. }
  intros Hm.
  induction n.
  { ins; lia. }
  unfold countNatP.
  destruct (excluded_middle_informative (s n)) as [HH | nHH].
  { specialize (Hm n). intuition auto with *. }
  rewrite PeanoNat.Nat.add_0_l.
  apply IHn.
  intros m Sm.
  specialize (Hm m).
  intuition auto with *.
Qed.

Lemma countNatP_eq m n (LT : m < n) : countNatP (eq m) n = 1.
Proof using.
  generalize dependent m.
  induction n; ins; [lia|].
  destruct (excluded_middle_informative (m = n)) as [HH | nHH].
  { arewrite (countNatP (eq m) n = 0); [|lia].
    eapply countNatP_zero.
    intuition auto with *. }
  rewrite PeanoNat.Nat.add_0_l.
  rewrite PeanoNat.Nat.lt_succ_r in LT.
  destruct LT; intuition auto with *.
Qed.

Lemma countNatP_union (s s' : nat -> Prop) n
      (DISJ : set_disjoint s s') :
  countNatP (s ∪₁ s') n = countNatP s n + countNatP s' n.
Proof using.
  induction n; simpls.
  destruct (excluded_middle_informative ((s ∪₁ s') n)) as [HH | nHH].
  { unfold set_union in HH.
    destruct HH as [S | S'].
    { assert (~ s' n) as nS'.
      { red. ins. by apply (DISJ n). }
      desf; lia. }
    assert (~ s n) as nS.
    { red. ins. by apply (DISJ n). }
    desf; lia. }
  unfold not, set_union in nHH.
  desf; exfalso; auto.
Qed.

Lemma countNatP_lt_eq (s : nat -> Prop) m n (LT : m < n) (HH : forall e (EE : s e), e < m):
  countNatP s n = countNatP s m.
Proof using.
  generalize dependent m.
  induction n; ins.
  { lia. }
  apply PeanoNat.Nat.lt_eq_cases in LT. desf; simpls.
  2: { apply IHn; auto. lia. }
  all: exfalso; apply HH in s0; lia.
Qed.
