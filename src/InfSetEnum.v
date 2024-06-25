From hahn Require Import Hahn.
Require Import List.
Import ListNotations.

Require Import SetSize.

Open Scope program_scope.
Open Scope list_scope.

Require Import Lia Program.Basics.

Set Implicit Arguments.

(* TODO: move to HahnExt/SetSize.v *)
Lemma set_size_inf_minus_finite {A} {s s' : A -> Prop}
    (INF : set_size s = NOinfinity)
    (FIN : set_finite s') :
  set_size (s \₁ s') = NOinfinity.
Proof using.
  unfold set_size in *. desf.
  exfalso.
  destruct s0 as [l HH].
  destruct FIN as [l' AA].
  apply n. exists (l ++ l'). ins.
  destruct (classic (s' x)) as [IN'|NIN].
  { apply in_app_r. now apply AA. }
  apply in_app_l. apply HH.
  red. auto.
Qed.

(* TODO: move to HahnExt/SetSize.v *)
Lemma set_finite_singl {A} (a : A) : set_finite (eq a).
Proof using. exists [a]. ins. auto. Qed.

(* TODO: move to HahnExt/SetSize.v *)
Lemma set_size_inf_minus_singl {A} {s : A -> Prop} (a : A)
    (INF : set_size s = NOinfinity) :
  set_size (s \₁ eq a) = NOinfinity.
Proof using.
  apply set_size_inf_minus_finite; auto.
  apply set_finite_singl.
Qed.

Lemma inf_not_empty {A} {s : A -> Prop} (INF : set_size s = NOinfinity) :
  ~s ≡₁ ∅.
Proof using.
  now rewrite <- (set_size_empty s), INF.
Qed.

Lemma grab_first {A} {s} {r}
    (WF : well_founded r)
    (NOT_EMPTY : ~ s ≡₁ ∅) :
  { x : A | s x /\ min_elt (restr_rel s r) x }.
Proof using.
  apply IndefiniteDescription.constructive_indefinite_description.
  destruct (wf_impl_min_elt WF NOT_EMPTY) as (x & IN & MIN). exists x.
  split; auto.
  intros b (REL & B_IN & X_IN). now apply (MIN b).
Qed.

(*
  a function that given a well-founded
  relation provides a mapping from natural numbers
  to set elements
*)
Fixpoint enumerator {A}
    {s : A -> Prop}
    {r : relation A}
    (INF : set_size s = NOinfinity)
    (WF : well_founded r)
    (n : nat) : A :=
  let x := proj1_sig (grab_first WF (inf_not_empty INF)) in
  match n with
  | O => x
  | S n' => enumerator (set_size_inf_minus_singl x INF) WF n'
  end.

Lemma enumerator_in {A} {s : A -> Prop} {r : relation A} (n : nat)
    (INF : set_size s = NOinfinity)
    (WF : well_founded r) :
  s (enumerator INF WF n).
Proof using.
  generalize s INF. clear s INF.
  induction n; intros s INF.
  { simpl. now destruct grab_first. }
  simpl. destruct grab_first as (x & IN & MIN); simpl.
  apply hahn_subset_exp with (s' := s) (s := (s \₁ eq x)).
  { basic_solver. }
  apply IHn.
Qed.

Lemma enumerator_step {A} {s : A -> Prop} {r : relation A}
    (INF : set_size s = NOinfinity)
    (WF : well_founded r)
    (x : A)
    (n : nat) :
  x <> enumerator (set_size_inf_minus_singl x INF) WF n.
Proof using.
  intro F.
  enough (HH : (s \₁ eq x) x) by (unfolder in HH; basic_solver).
  rewrite F at 2. apply enumerator_in.
Qed.

Lemma enumerator_inj {A} {s : A -> Prop} {r : relation A}
    (INF : set_size s = NOinfinity)
    (WF : well_founded r)
    (x y : nat)
    (NEQ : x <> y) :
  enumerator INF WF x <> enumerator INF WF y.
Proof using.
  generalize y NEQ s INF; clear y NEQ s INF.
  induction x; intros y NEQ s INF; simpl.
  { destruct y; try easy. simpl.
    destruct grab_first as (x & XIN & XMIN); simpl.
    apply enumerator_step. }
  destruct y; simpl.
  destruct grab_first as (y & YIN & YMIN); simpl.
  { symmetry.
    apply enumerator_step. }
  apply IHx. congruence.
Qed.

(*
  If a set is ordered by some total well-founded relation
  then enumerator preserves this relation.
*)
Lemma enumerator_ordered {A} {s : A -> Prop} {r : relation A}
    (INF : set_size s = NOinfinity)
    (WF : well_founded r)
    (TOT : is_total s r)
    (x y : nat)
    (LT : x < y) :
  r (enumerator INF WF x) (enumerator INF WF y).
Proof using.
  generalize s y LT TOT INF. clear INF TOT LT s y.
  induction x; ins.
  { destruct (grab_first WF (inf_not_empty INF))
         as (x0 & XIN & XMIN)
         eqn: HEQ.
    assert (HEQ' : x0 = enumerator INF WF 0).
    { ins. rewrite HEQ. ins. }
    destruct TOT with x0 (enumerator INF WF y); auto.
    { apply enumerator_in. }
    { rewrite HEQ'. apply enumerator_inj. lia. }
    exfalso. eapply XMIN. red; splits; eauto.
    apply enumerator_in. }
  destruct y as [| y]; [lia | ins].
  apply IHx; [lia |].
  eapply is_total_mori; eauto.
  { red. basic_solver. }
  basic_solver.
Qed.