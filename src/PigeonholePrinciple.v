Require Import Lia.
From hahn Require Import Hahn.

Set Implicit Arguments.

Lemma pigeonhole_principle_constructive {A}
  (EQA : forall x y : A, {x = y} + {x <> y})
  (f : nat -> A)
  (l : list A)
  (HH : forall i : nat, In (f i) l) :
  exists i j : nat, i < j /\ f i = f j.
Proof using.
  enough (exists i j, i < j <= length l /\ f i = f j).
  { desf; eauto. }
  assert (forall i, i <= length l -> In (f i) l) as YY by ins.
  clear HH. rename YY into HH.
  remember (length l) as ll.
  assert (length l <= ll) as LT by lia.
  clear Heqll.
  generalize dependent l.
  pattern ll. apply Wf_nat.lt_wf_ind.
  clear ll. intros ll LIND; ins.
  destruct (PeanoNat.Nat.eq_dec (length l) 0) as [|NEQ].
  { destruct l; ins. exfalso. eapply HH; eauto. }
  set (ls := List.seq 0 (length l)).
  destruct (in_dec EQA (f (length l)) (map f ls)) as [IN|NAI].
  { apply in_map_iff in IN. destruct IN as [i [FI IN]].
    subst ls. apply in_seq0_iff in IN.
    exists i, (length l). split; auto. }
  remember (f (length l)) as ff.
  assert (In ff l) as INFF.
  { subst. apply HH. lia. }
  set (l':=remove EQA ff l).
  assert (length l' < ll) as SLL.
  { subst l'. eapply (remove_length_lt EQA) in INFF. lia. }
  destruct LIND with (m:=length l') (l:=l')
    as (i & j & IJ & YY); auto.
  2: { exists i, j. split; auto. lia. }
  subst l'. ins. apply in_in_remove; auto.
  2: { apply HH. lia. }
  assert (length (remove EQA ff l) < length l).
  { apply remove_length_lt; auto. }
  subst. intros TT. apply NAI.
  apply in_map_iff. exists i.
  split; auto.
  subst ls. apply in_seq0_iff. lia.
Qed.

Lemma pigeonhole_principle {A}
  (f : nat -> A)
  (l : list A)
  (HH : forall i : nat, In (f i) l) :
  exists i j : nat, i < j /\ f i = f j.
Proof using.
  eapply pigeonhole_principle_constructive; eauto.
  ins. apply excluded_middle_informative.
Qed.
