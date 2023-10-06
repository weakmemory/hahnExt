Require Import Setoid Lia.
From hahn Require Import Hahn.
Require Import AuxRel.

Export ListNotations.

Set Implicit Arguments.

Lemma pair_inj {A B} (a c : A) (b d : B) (EQ: (a, b) = (c, d)) :
  a = c /\ b = d.
Proof using. ins. inv EQ. Qed.

Lemma pair_congruence {A B} {a1 a2 : A} {b1 b2 : B} :
     (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
Proof using. split; [basic_solver | ins; desf]. Qed.

Lemma some_congruence {T} (a b : T) (EQ : Some a = Some b) :
      a = b.
Proof. inv EQ. Qed.

Definition opt_same_ctor {A B} (a : option A) (b : option B) : Prop :=
  match a, b with
  | None  , None
  | Some _, Some _ => True
  | _, _ => False
  end.

Definition opt_ext {A} (def : A) (a : option A) : A :=
  match a with
  | None => def
  | Some a => a
  end.

Definition opt_to_list {A} (a : option A) : list A :=
  match a with
  | None => []
  | Some a => [a]
  end.

Definition upd_opt {A} {B} (f : A -> B) (a : option A) (b : option B) :=
  match a, b with
  | Some a, Some b => upd f a b
  | _, _ => f
  end.

Fixpoint indexed_list_helper {A} (i : nat) (l : list A) :
  list (nat * A) :=
  match l with
  | nil => nil
  | h :: l => (i, h) :: (indexed_list_helper (S i) l)
  end.

Definition indexed_list {A} (l : list A) : list (nat * A) :=
  indexed_list_helper 0 l.

Fixpoint list_to_fun {A B}
         (DEC : forall (x y : A), {x = y} + {x <> y})
         (def : B) (l : list (A * B)) : A -> B :=
  fun v =>
    match l with
    | nil => def
    | (hv, hf) :: l =>
      if DEC hv v
      then hf
      else list_to_fun DEC def l v
    end.

Lemma In_map_fst {A B} (a : A) (b : B) l (IN : In (a, b) l) :
  In a (map fst l).
Proof using. induction l; inv IN; simpls; eauto. Qed.

Lemma In_map_snd {A B} (a : A) (b : B) l (IN : In (a, b) l) :
  In b (map snd l).
Proof using. induction l; inv IN; simpls; eauto. Qed.

Lemma l2f_in {A B} l (a : A) (b def : B) DEC
      (NODUP : NoDup (map fst l))
      (IN : In (a,b) l) :
  list_to_fun DEC def l a = b.
Proof using.
  induction l; inv IN; simpls; desf.
  { destruct (classic (b0 = b)) as [|NEQ]; auto.
    exfalso.
    eapply NoDup_cons_iff; eauto.
    simpls.
    eapply In_map_fst; eauto. }
  inv NODUP. intuition.
Qed.

Lemma l2f_v {A B} (l : list (A * B)) a def
      (DEC : forall x y : A, {x = y} + {x <> y})
      (NDP : NoDup (map fst l)) :
  (exists b,
      ⟪ BIN : In (a, b) l ⟫) \/
  ((~ exists b, ⟪ BIN : In (a, b) l ⟫) /\
   ⟪ VV  : list_to_fun DEC def l a = def ⟫).
Proof using.
  induction l.
  { right. splits; eauto.
    intros HH. desf. }
  destruct a0 as [a' b'].
  destruct (DEC a' a) as [EQ|NEQ]; subst.
  { left. eexists. splits; eauto.
    constructor. eauto. }
  simpls. inv NDP.
  apply IHl in H2. desf; [left|right].
  { eexists. splits; eauto. }
  splits; eauto. intros HH. desf.
  apply H2. eauto.
Qed.

Lemma l2f_nin {A B} l (a : A) (def : B) DEC
      (NIN : ~ exists b, In (a,b) l) :
  list_to_fun DEC def l a = def.
Proof using.
  induction l; simpls.
  desf.
  2: { apply IHl. intros HH; desf. apply NIN. eauto. }
  exfalso. eapply NIN. eauto.
Qed.

Lemma l2f_codom {A B} (l : list (A * B)) a def DEC :
  In (a, list_to_fun DEC def l a) l \/
  list_to_fun DEC def l a = def.
Proof using.
  generalize dependent l.
  induction l; auto.
  destruct a0.
  simpls.
  destruct (DEC a0 a); basic_solver.
Qed.

Lemma indexed_list_helper_in_to_range {A} a (l : list A) m n
      (IN : In (n, a) (indexed_list_helper m l)) :
  m <= n < m + length l.
Proof using.
  generalize dependent m.
  generalize dependent a.
  induction l; ins; desf.
  { lia. }
  apply IHl in IN.
  lia.
Qed.

Lemma indexed_list_helper_nodup {A} n (l : list A) :
  NoDup (indexed_list_helper n l).
Proof using.
  generalize dependent n.
  induction l; ins.
  constructor.
  2: by intuition.
  intros IN. apply indexed_list_helper_in_to_range in IN. lia.
Qed.

Lemma indexed_list_nodup {A} (l : list A) : NoDup (indexed_list l).
Proof using. apply indexed_list_helper_nodup. Qed.

Lemma indexed_list_helper_fst_eq {A} n (l : list A) x y
      (INX : In x (indexed_list_helper n l))
      (INY : In y (indexed_list_helper n l))
      (EQ : fst x = fst y) :
  x = y.
Proof using.
  generalize dependent y.
  generalize dependent x.
  generalize dependent n.
  induction l; ins; desf.
  3: by eapply IHl; eauto.
  destruct x; simpls; desf.
  2: destruct y; simpls; desf.
  all: match goal with
       | H : In _ _ |- _ => apply indexed_list_helper_in_to_range in H; lia
       end.
Qed.

Lemma indexed_list_fst_eq {A} (l : list A) x y
      (INX : In x (indexed_list l))
      (INY : In y (indexed_list l))
      (EQ : fst x = fst y) :
  x = y.
Proof using. eapply indexed_list_helper_fst_eq; eauto. Qed.

Lemma indexed_list_fst_nodup {A} (l : list A) :
  NoDup (map fst (indexed_list l)).
Proof using.
  apply nodup_map.
  { apply indexed_list_helper_nodup. }
  ins. intros HH.
  eapply indexed_list_fst_eq in HH; eauto.
Qed.

Lemma indexed_list_helper_range {A} (l : list A) m n :
  (exists a, In (n, a) (indexed_list_helper m l)) <->
  m <= n < m + length l.
Proof using.
  split.
  { intros [a HH]. eapply indexed_list_helper_in_to_range; eauto. }
  generalize dependent m.
  induction l; intros m HH; ins; desf.
  { lia. }
  apply NPeano.Nat.lt_eq_cases in HH. desf.
  2: { eexists; eauto. }
  edestruct IHl as [a' AA]; eauto.
  lia.
Qed.

Lemma indexed_list_range {A} (l : list A) n :
  (exists a, In (n, a) (indexed_list l)) <->
  n < length l.
Proof using.
  arewrite (n < length l <-> 0 <= n < 0 + length l).
  2: by apply indexed_list_helper_range.
  lia.
Qed.

Lemma indexed_list_helper_map_snd {A} n (l : list A) :
  map snd (indexed_list_helper n l) = l.
Proof using.
  generalize dependent n.
  induction l; ins.
    by rewrite IHl.
Qed.

Lemma indexed_list_map_snd {A} (l : list A) :
  map snd (indexed_list l) = l.
Proof using. apply indexed_list_helper_map_snd. Qed.

Lemma indexed_list_helper_snd_nodup {A} n a b c (l : list A) (NODUP : NoDup l)
      (INA : In (a, c) (indexed_list_helper n l))
      (INB : In (b, c) (indexed_list_helper n l)) :
  a = b.
Proof using.
  generalize dependent n.
  induction l; ins; desf.
  3: { eapply IHl; eauto. inv NODUP. }
  all: exfalso.
  all: inv NODUP; apply H1.
  apply In_map_snd in INA.
  2: apply In_map_snd in INB.
  all: erewrite <- indexed_list_helper_map_snd; eauto.
Qed.

Lemma indexed_list_snd_nodup {A} a b c (l : list A) (NODUP : NoDup l)
      (INA : In (a, c) (indexed_list l))
      (INB : In (b, c) (indexed_list l)) :
  a = b.
Proof using. eapply indexed_list_helper_snd_nodup; eauto. Qed.

Lemma indexed_list_helper_length {A} n (l : list A) :
  length (indexed_list_helper n l) = length l.
Proof using.
  generalize dependent n.
  induction l; ins. by rewrite IHl.
Qed.

Lemma indexed_list_length {A} (l : list A) :
  length (indexed_list l) = length l.
Proof using.
  unfold indexed_list.
  apply indexed_list_helper_length.
Qed.

Lemma indexed_list_helper_in_exists {A} m a (l : list A) (IN : In a l) :
  exists n, In (n, a) (indexed_list_helper m l).
Proof using.
  generalize dependent m.
  induction l; ins; desf; eauto.
  specialize (IHl IN (S m)). desf. eauto.
Qed.

Lemma indexed_list_in_exists {A} a (l : list A) (IN : In a l) :
  exists n, In (n, a) (indexed_list l).
Proof using. unfold indexed_list. by apply indexed_list_helper_in_exists. Qed.

#[global]
Hint Unfold upd_opt : unfolderDb.

Lemma option_map_same_ctor (A B : Type) (a : option A) (f : A -> B):
  opt_same_ctor (option_map f a) a.
Proof using. unfold option_map. red. destruct a; auto. Qed.

Lemma opt_to_list_none (A : Type) :
  opt_to_list (None : option A) = [].
Proof using. by unfold opt_to_list. Qed.

Lemma opt_to_list_some (A : Type) (a : A) :
  opt_to_list (Some a) = [a].
Proof using. by unfold opt_to_list. Qed.

Lemma opt_to_list_app_singl (A : Type) (a a' : A) (b b' : option A) :
  opt_to_list b ++ [a] = opt_to_list b' ++ [a'] -> a = a' /\ b = b'.
Proof using.
  unfold opt_to_list, app. ins.
  destruct b, b'; inversion H; intuition.
Qed.

Lemma opt_to_list_app_singl_singl (A : Type) (a a' : A) (b : option A) :
  opt_to_list b ++ [a] = [a'] -> a = a' /\ b = None.
Proof using.
  unfold opt_to_list.
  destruct b as [b|];
    unfold app; intros EQ;
    by inversion EQ.
Qed.

Lemma opt_to_list_app_singl_pair (A : Type) (a a' : A) (b : option A) (b' : A) :
  opt_to_list b ++ [a] = [b'; a'] -> a = a' /\ b = Some b'.
Proof using.
  unfold opt_to_list.
  destruct b as [b|];
    unfold app; intros EQ;
    by inversion EQ.
Qed.

Lemma upd_opt_none_l (A B : Type) (f : A -> B) b : upd_opt f None b = f.
Proof using.
  by unfold upd_opt.
Qed.

Lemma upd_opt_none_r (A B : Type) (f : A -> B) a : upd_opt f a None = f.
Proof using.
  destruct a; by unfold upd_opt.
Qed.

Lemma upd_opt_some (A B : Type) (f : A -> B) a b : upd_opt f (Some a) (Some b) = upd f a b.
Proof using.
  by unfold upd_opt.
Qed.

Lemma updo_opt (A B : Type) (f : A -> B) a b x
      (NEQ : ~ eq_opt a x)
      (CTOR : opt_same_ctor a b) :
  upd_opt f a b x = f x.
Proof using.
  unfold upd_opt, eq_opt in *.
  destruct a, b; auto.
  apply updo. auto.
Qed.

Lemma set_collect_updo_opt (A B : Type) (f : A -> B) a b s
      (DISJ : set_disjoint s (eq_opt a))
      (CTOR : opt_same_ctor a b) :
  (upd_opt f a b) ↑₁ s ≡₁ f ↑₁ s.
Proof using.
  unfold upd_opt, eq_opt, set_disjoint in *.
  destruct a, b; auto.
  apply set_collect_updo.
  specialize (DISJ a).
  intuition.
Qed.

Fixpoint first_nat_list (n : nat) : list nat :=
  match n with
  | 0 => []
  | S m => m :: first_nat_list m
  end.

Lemma first_nat_list_In_alt (n m : nat) : In m (first_nat_list n) <-> m < n.
Proof using.
  induction n; simpls.
  { lia. }
  split; intros HH; desf.
  { specialize_full IHn; auto. }
  inversion HH; auto.
Qed.

Lemma nodup_first_nat_list : forall n : nat, NoDup (first_nat_list n).
Proof using.
  induction n.
  { apply NoDup_nil. }
  apply NoDup_cons; auto.
  rewrite first_nat_list_In_alt.
  lia.
Qed.

Lemma split_as_map {A B} (l : list (A * B)) :
  split l = (map fst l, map snd l).
Proof using.
  generalize dependent l.
  induction l; [done|].
  simpls.
  rewrite IHl.
  basic_solver.
Qed.

Lemma combine_split_l {A B} (lA : list A) (lB : list B)
      (LEQ : length lA <= length lB) :
  fst (split (combine lA lB)) = lA.
Proof using.
  generalize dependent lB.
  generalize dependent lA.
  induction lA; [done|].
  intros.
  destruct lB.
  { simpls. lia. }
  simpls. desf.
  arewrite (l = lA); auto.
  rewrite <- (IHlA lB); [|lia].
  unfold fst. basic_solver.
Qed.

Lemma Injective_map_NoDup_dom {A B} (P : A -> Prop) (f : A -> B) (l : list A)
      (IJ : inj_dom P f)
      (PL : Forall P l)
      (NO_DUP: NoDup l) :
  NoDup (map f l).
Proof using.
  generalize dependent NO_DUP.
  induction 1 as [|x l SX N IH]; simpls;
    constructor; apply Forall_cons in PL; desf; auto.
  rewrite in_map_iff. intros (y & E & Y). apply IJ in E.
  { now subst. }
  { eapply Forall_forall; eauto. }
  auto.
Qed.