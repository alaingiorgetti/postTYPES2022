(****************************************************************************)
(* Copyright 2021-2022 Catherine Dubois, Nicolas Magaud and Alain Giorgetti *)
(* Samovar - ICube - FEMTO-ST institute                                     *)
(****************************************************************************)

(****************************************************************************)
(*      This file is distributed under the terms of the                     *)
(*       GNU Lesser General Public License Version 2.1                      *)
(****************************************************************************)

Require Import Arith Lia.
Require Import closable ucs open.

(** * Another definition of closable Motzkin trees in [[BT17]] *)

(** The following definition corresponds to <<isClosable>> in [[BT17]]:
    "We call a Motzkin tree _closable_ if it is the skeleton of at least one
    closed lambda term. The predicate <<isClosable/1>> tests if it exists a 
    closed lambda term having <<X>> as its skeleton. For each lambda binder
    it increments a count <<V>> (starting at 0), and ensures that it is 
    strictly positive for all leaf nodes." [[BT17, section 3]]. *)
(*- BEGINisClosable *)
Fixpoint isClosable2 (mt: motzkin) (V: nat) :=
  match mt with
  | v => V > 0
  | l m => isClosable2 m (S V)
  | a m1 m2 => isClosable2 m1 V /\ isClosable2 m2 V
  end.

Definition isClosable (mt: motzkin) := isClosable2 mt 0.
(*- ENDisClosable *)

(** The former definition corresponds to the Prolog clause

      <<isClosable(X):-isClosable(X,0).>>

    in [[BT17]]. *)


(** * Equivalence between [isClosable] and [is_closable] *)

(*- BEGINisClosable2_S *)
Lemma isClosable2_S : forall m n, isClosable2 m n -> isClosable2 m (S n).
(*- ENDisClosable2_S *)
Proof.
induction m.
  intros; simpl; lia.
simpl.
intros; apply IHm; assumption.
simpl;intros n Hi.
destruct Hi as [Hi1 Hi2].
split.
apply IHm1; apply Hi1.
apply IHm2; apply Hi2.
Qed.

(*- BEGINisClosable_l *)
Lemma isClosable_l : forall m, isClosable (l m).
(*- ENDisClosable_l *)
Proof.
unfold isClosable; simpl; induction m.
simpl; lia.
simpl.
apply isClosable2_S.
assumption.
simpl.
split; assumption.
Qed.

Lemma isClosable_is_closable : forall m, isClosable m -> is_closable m.
Proof.
unfold isClosable; induction m; simpl.
  intros; lia.
  intros;exact I.
  intros Hi; destruct Hi as [Hi1 Hi2].
  split.
  apply IHm1; apply Hi1.
  apply IHm2; apply Hi2.
Qed.

Lemma is_closable_isClosable : forall m, is_closable m -> isClosable m.
Proof.
  induction m. 
  unfold is_closable; simpl; intros; tauto.
  intros; apply isClosable_l.
  unfold is_closable; intros Hi.
  destruct Hi as [Hi1 Hi2].
  split.
  apply IHm1; apply Hi1.
  apply IHm2; apply Hi2.
Qed.

(*- BEGINis_closable_isClosable_eq *)
Lemma is_closable_isClosable_eq : forall (mt: motzkin), is_closable mt <-> isClosable mt.
(*- ENDis_closable_isClosable_eq *)
Proof.
  split.
  apply is_closable_isClosable.
  apply isClosable_is_closable.
Qed.

(** * Equivalence between [isClosable] and the inductive type [closable] *)

(* 'minimal' provable generalization of [isClosable2 m 1] to finish a direct proof
   of [isClosable_lemma]. *)
Lemma isClosable2_pos: forall m n, isClosable2 m (S n).
Proof.
induction m; simpl; auto. intro n. lia.
Qed.

(*- BEGINisClosable_lemma *)
Lemma isClosable_lemma : forall c, isClosable (closable2motzkin c).
(*- ENDisClosable_lemma *)
Proof. (* first proof, obvious, through [is_closable] *)
intro c.
apply is_closable_isClosable_eq.
apply is_closable_lemma.
Restart. (* second proof, direct, less obvious *)
unfold isClosable.
induction c; simpl; auto.
(* It remains to prove [isClosable2 m 1] *)
apply isClosable2_pos.
Qed.

(*- BEGINrecClosable *)
Record recClosable : Type := Build_recClosable {
  Closable_struct : motzkin;
  Closable_prop : isClosable Closable_struct
}.
(*- ENDrecClosable *)

(** * Equivalence between the record [recClosable] and [closable] *)

(** ** From [recClosable] to [closable] *)

Lemma isClosable2closable_aux : forall m, isClosable m -> closable.
Proof.
unfold isClosable.
fix rec 1.
intros m; case m.
+ intro H.
  (* Here the proof differs from the proof of [motzkin2closable_aux] because the tactic [inversion H.]
     cannot be applied directly. *)
  apply False_rect; eapply gt_irrefl; apply H.
+ intros m0 Hm0; apply (La m0).
+ intros m1 m2 [Hm1 Hm2]. apply (Ap (rec m1 Hm1) (rec m2 Hm2)).
Defined.

(*- BEGINisClosable2closable *)
Fixpoint isClosable2closable  (m : motzkin) : isClosable m -> closable :=
  match m as m0 return (isClosable2 m0 0 -> closable) with
   | v => fun H : isClosable2 v 0 => False_rect closable (gt_irrefl 0 H)
   | l m0 => (fun (m1 : motzkin) (_ : isClosable2 (l m1) 0) => La m1) m0
   | a m0 m1 =>
       (fun (m2 m3 : motzkin) (H : isClosable2 (a m2 m3) 0) =>
        match H with
        | conj x x0 => (fun (Hm1 : isClosable2 m2 0) (Hm2 : isClosable2 m3 0) => Ap (isClosable2closable m2 Hm1) (isClosable2closable m3 Hm2)) x x0
        end) m0 m1
  end.
(*- ENDisClosable2closable *)

(*- BEGINrecClosable2closable *)
Definition recClosable2closable m := isClosable2closable (Closable_struct m) (Closable_prop m).
(*- ENDrecClosable2closable *)

(** ** From [closable] to [recClosable] *)
(*- BEGINclosable2recClosable *)
Definition closable2recClosable c :=
  Build_recClosable (closable2motzkin c) (isClosable_lemma c).
(*- ENDclosable2recClosable *)

(*- BEGINclosable2recClosableK_aux *)
Lemma closable2recClosableK_aux : forall (m : motzkin) (Hclo : isClosable m),
  closable2motzkin (isClosable2closable m Hclo) = m.
(*- ENDclosable2recClosableK_aux *)
Proof.
induction m; simpl; intros; auto.
+ inversion Hclo.
+ destruct Hclo as [Hclo1 Hclo2].
  simpl.
  specialize (IHm1 Hclo1).
  specialize (IHm2 Hclo2).
  rewrite IHm1. rewrite IHm2. reflexivity.
Qed.


Lemma proof_irr_isClosable2 :forall x n (p1 p2:isClosable2 x n), p1 = p2.
Proof.
induction x; simpl.
- intros. unfold gt,lt in *. apply le_unique.
- intros. rewrite (IHx (S n) p1 p2). reflexivity.
- intros. destruct p1. destruct p2.
  rewrite (IHx1 n i i1).
  rewrite (IHx2 n i0 i2).
  reflexivity.
Qed.

Lemma proof_irr_isClosable :forall x (p1 p2:isClosable x), p1 = p2.
Proof.
  unfold isClosable.
  intros; apply proof_irr_isClosable2.
Qed.

(*- BEGINrecClosable2closableK *)
Lemma recClosable2closableK : forall x, closable2recClosable (recClosable2closable x) = x.
(*- ENDrecClosable2closableK *)
Proof.
  destruct x.
  unfold closable2recClosable, recClosable2closable; simpl.
generalize (isClosable_lemma (isClosable2closable Closable_struct0 Closable_prop0)); intros p.
revert p.
rewrite closable2recClosableK_aux.
intros.
rewrite (proof_irr_isClosable _ p (Closable_prop0)).
reflexivity.
Qed.

Lemma motzkin_erasure : forall c h,
 (isClosable2closable (closable2motzkin c) h) = c.
Proof.
  induction c; simpl; intros; auto.
  destruct h;rewrite IHc1, IHc2; reflexivity.
Qed.

(*- BEGINclosable2recClosableK *)
Lemma closable2recClosableK : forall c, recClosable2closable (closable2recClosable c) = c.
(*- ENDclosable2recClosableK *)
Proof.
intros; unfold recClosable2closable,closable2recClosable; simpl.
apply motzkin_erasure.
Qed.

(** * Formal proof of Proposition 1 [[BT17]]

   "Proposition 1: The set of terms of size [n] for the size definition 
   {application=2, lambda=1, variable=0} is equal to the set of terms of size [n+1] 
   for the size definition {application=1, lambda=1, variable=1}." [[BT17]] *)

(** ** For Motzkin trees *)

(*- BEGINsize012motzkin *)
Fixpoint size012motzkin (t : motzkin) :=
  match t with
  | v => 0
  | l t => 1 + size012motzkin t
  | a t1 t2 => 2 + size012motzkin t1 + size012motzkin t2
  end.
(*- ENDsize012motzkin *)

(*- BEGINsize111motzkin *)
Fixpoint size111motzkin (t : motzkin) :=
  match t with
  | v => 1
  | l t => 1 + size111motzkin t
  | a t1 t2 => 1 + size111motzkin t1 + size111motzkin t2
  end.
(*- ENDsize111motzkin *)

(*- BEGINproposition1motzkin *)
Proposition proposition1motzkin : forall t : motzkin, size111motzkin t = size012motzkin t + 1.
(*- ENDproposition1motzkin *)
Proof.
induction t; simpl; lia.
Qed.

(** ** For closable Motkzin trees, with the record type *)

(** Thanks to the coercion, it is not necessary to define [size111rec_closable] and [size012rec_closable] *)

(*- BEGINproposition1rec_closable *)
Proposition proposition1rec_closable :
  forall t : rec_closable, size111motzkin t = size012motzkin t + 1.
(*- ENDproposition1rec_closable *)
Proof.
intro t.
apply proposition1motzkin.
Qed.

(** ** For closable Motkzin trees, with the inductive type *)

(*- BEGINsize012closable *)
Fixpoint size012closable (t : closable) :=
  match t with
  | La m => 1 + size012motzkin m
  | Ap t1 t2 => 2 + size012closable t1 + size012closable t2
  end.
(*- ENDsize012closable *)

(*- BEGINsize111closable *)
Fixpoint size111closable (t : closable) :=
  match t with
  | La m => 1 + size111motzkin m
  | Ap t1 t2 => 1 + size111closable t1 + size111closable t2
  end.
(*- ENDsize111closable *)

(*- BEGINproposition1closable *)
Proposition proposition1closable : forall t : closable, size111closable t = size012closable t + 1.
(*- ENDproposition1closable *)
Proof.
induction t; simpl.
- apply f_equal. apply proposition1motzkin.
- lia.
Qed.

(** ** For labeled Motzkin trees *)

(*- BEGINsize012lmt *)
Fixpoint size012lmt (t : lmt) :=
  match t with
  | var _ => 0
  | lam t => 1 + size012lmt t
  | app t1 t2 => 2 + size012lmt t1 + size012lmt t2
  end.
(*- ENDsize012lmt *)

(*- BEGINsize111lmt *)
Fixpoint size111lmt (t : lmt) :=
  match t with
  | var _ => 1
  | lam t => 1 + size111lmt t
  | app t1 t2 => 1 + size111lmt t1 + size111lmt t2
  end.
(*- ENDsize111lmt *)

(*- BEGINproposition1lmt *)
Proposition proposition1lmt : forall t : lmt, size111lmt t = size012lmt t + 1.
(*- ENDproposition1lmt *)
Proof.
induction t; simpl; lia.
Qed.

(** ** For _m_-open terms, with the record type *)

(*- BEGINproposition1rec_open *)
Proposition proposition1rec_open :
  forall m : nat, forall t : rec_open m, size111lmt t = size012lmt t + 1.
(*- ENDproposition1rec_open *)
Proof.
intros m t.
apply proposition1lmt.
Qed.

(** ** For _m_-open terms, with the dependent type *)

(*- BEGINsize012open *)
Fixpoint size012open m (t : open m) :=
  match t with
  | open_var _ _ _ => 0
  | open_lam m0 u => 1 + size012open (S m0) u
  | open_app m0 t1 t2 => 2 + size012open m0 t1 + size012open m0 t2
  end.
(*- ENDsize012open *)

(*- BEGINsize111open *)
Fixpoint size111open m (t : open m) :=
  match t with
  | open_var _ _ _ => 1
  | open_lam m0 u => 1 + size111open (S m0) u
  | open_app m0 t1 t2 => 1 + size111open m0 t1 + size111open m0 t2
  end.
(*- ENDsize111open *)

(*- BEGINproposition1open *)
Proposition proposition1open : forall m (t : open m), size111open m t = size012open m t + 1.
(*- ENDproposition1open *)
Proof.
intros m t; induction t; simpl; lia.
Qed.

(** * Formal proof of [[BT17, Proposition 2]]

"Proposition 2: A Motzkin tree is a skeleton of a closed lambda term if and only if it
exists at least one lambda binder on each path from the leaf to the root." [[BT17]]. *)

(** ** Skeleton of a lambda term

    The skeleton of a lambda term is the Motzkin tree obtained by erasing the 
    labels at its leaves. Specified by <<toMotSkel>> in [[BT17]]. *)
(*- BEGINskeleton *)
Fixpoint skeleton (t: lmt) : motzkin :=
  match t with
  | var _ => v
  | lam t1 => l (skeleton t1)
  | app t1 t2  => a (skeleton t1) (skeleton t2)
  end.
(*- ENDskeleton *)

(** ** Example: *)
Lemma skeleton_ex1 : skeleton lmt_ex2 = mot_ex1.
reflexivity.
Qed.

(** The function [motzkin2lmt0] computes a lambda term from a Motzkin tree by 
    replacing any leaf by a variable labeled with 0, any unary node by an 
    abstraction and any binary node by an application. *)
Fixpoint motzkin2lmt0 mt : lmt :=
  match mt with
  | v => var 0 
  | l m => lam (motzkin2lmt0 m)
  | a m1 m2 => app (motzkin2lmt0 m1) (motzkin2lmt0 m2)
  end.

(** The following lemma proves that [skeleton] is a left inverse of [motzkin2lmt0] *)
Lemma skeleton_motzkin2lmt0 : forall mt, skeleton (motzkin2lmt0 mt) = mt.
Proof.
induction mt ; simpl ; intros; auto.
+ rewrite IHmt; auto.
+ rewrite IHmt1; rewrite IHmt2; auto.
Qed.

(** ** Closed lambda term *)

(** * A closed lambda term is a 0-open term. *)
(*- BEGINis_closed *)
Definition is_closed t := is_open 0 t.
(*- ENDis_closed *)

(*- BEGINis_open_mon *)
Lemma is_open_mon : forall t m, is_open m t -> is_open (S m) t.
(*- ENDis_open_mon *)
Proof.
induction t; simpl; intros.
+ auto.
+ apply IHt; assumption.
+ intuition.
Qed.

Lemma always_closed_lam : forall mt, is_closed (lam (motzkin2lmt0 mt)).
Proof.
unfold is_closed; induction mt.
+ simpl; auto.
+ simpl in *; apply is_open_mon; assumption.
+ simpl in *; split; assumption.
Qed.

Lemma closed_motzkin2lmt0 : forall mt, is_closable mt -> is_closed (motzkin2lmt0 mt).
Proof.
induction mt.
+ simpl; intuition.
+ intros; simpl; apply always_closed_lam.
+ unfold is_closed; simpl in *; intuition.
Qed.

(* only if *)
Lemma is_closable2_skeleton mt : is_closable mt -> exists t, skeleton t = mt /\ is_closed t.
Proof.
intro Hyp.
exists (motzkin2lmt0 mt).
split.
- apply skeleton_motzkin2lmt0.
- apply closed_motzkin2lmt0; auto.
Qed.

Lemma skeleton_inversion_v : forall t, skeleton t = v -> exists n, t = var n.
Proof.
intro t; destruct t; simpl; intros; try (inversion H).
exists n; auto.
Qed.

Lemma skeleton_inversion_l : forall t mt, skeleton t = l mt -> exists t1, t = lam t1.
Proof.
intro t; destruct t; simpl; intros; try (inversion H).
exists t; auto.
Qed.

Lemma skeleton_inversion_a : forall t mt1 mt2,
  skeleton t = a mt1 mt2 -> exists t1, exists t2, t = app t1 t2.
Proof.
intro t; destruct t; simpl; intros; try (inversion H).
exists t1; exists t2; auto.
Qed.

(* if *)
Lemma is_closable2_skeleton_rev : forall mt, 
  (exists t, skeleton t = mt /\ is_closed t) -> is_closable mt.
Proof.
unfold is_closed, is_open in *.
induction mt; simpl; intros; destruct H as [t [Ha Hb]].
+ apply skeleton_inversion_v in Ha. destruct Ha as [n Heq].
  subst. lia.
+ exact I.
+ destruct (skeleton_inversion_a _ _ _ Ha) as[t1 [t2 Heq]].
  subst. simpl in *. split.
  - apply IHmt1. inversion Ha. exists t1; intuition.
  - apply IHmt2. inversion Ha. exists t2; intuition.
Qed.

(** *** Proposition 2 [[BT17]] *)

(*- BEGINproposition2 *)
Proposition proposition2 : forall mt : motzkin,
  (exists t : lmt, skeleton t = mt /\ is_closed t) <-> is_closable mt.
(*- ENDproposition2 *)
Proof.
split.
- apply is_closable2_skeleton_rev.
- apply is_closable2_skeleton.
Qed.

(** * With [rec_closable] and [closable], only one of both implications (from right to left) in
 Proposition 2 [[BT17]] can be formalized: *)

(*- BEGINproposition2rec_closable *)
Proposition proposition2rec_closable : forall r : rec_closable,
  exists t : lmt, skeleton t = closable_struct r /\ is_closed t.
(*- ENDproposition2rec_closable *)
Proof.
destruct r.
apply is_closable2_skeleton.
assumption.
Qed.

Lemma rec_closable1 : forall r: rec_closable, closable2motzkin (rec_closable2closable r) = closable_struct r.
Proof.
unfold rec_closable2closable; intros.
apply closable2rec_closableK_aux.
Qed.

(*- BEGINproposition2closable *)
Proposition proposition2closable : forall c : closable,
  exists t : lmt, skeleton t = closable2motzkin c /\ is_closed t.
(*- ENDproposition2closable *)
Proof. (* Proof using isomorphism with [rec_closable] and the former proposition: *)
intro c.
(* TODO NM: generic tactic for the following steps? *)
rewrite <- (closable2rec_closableK c).
rewrite rec_closable1.
apply (proposition2rec_closable (closable2rec_closable c)).
Qed.

Proposition proposition2closable' : forall c : closable,
  exists t : lmt, skeleton t = closable2motzkin c /\ is_closed t.
Proof. (* Direct proof, without using isomorphism with [rec_closable]: *)
intro c.
induction c.
- exists (lam (motzkin2lmt0 m)).
 simpl. split.
 + apply f_equal. apply skeleton_motzkin2lmt0.
 + apply always_closed_lam.
- destruct IHc1 as [t1 [S1 C1]]. destruct IHc2 as [t2 [S2 C2]].
 exists (app t1 t2); simpl; subst; split.
 + rewrite S1. rewrite S2. apply eq_refl.
 + unfold is_closed. simpl. auto.
Qed.

(** * Formal proof of Proposition 4 [[BT17]]

"Proposition 4: A skeleton is uniquely closable if and only if exactly one lambda binder
 is available above each of its leaf nodes." [[BT17]] *)

(** The proof relies on a characterization [ucs1] of uniquely closable terms with a natural number,
    corresponding to the Prolog predicate <<uniquelyClosable1>> in [[BT17]]:
    "The predicate <<uniquelyClosable1/2>> [...] ensures that for each leaf <<v/0>> exactly 
    one lambda binder is available." [[BT17, section 4]] *)

(*- BEGINucs1 *)
Fixpoint ucs1_aux (t:motzkin) (n:nat) : Prop :=
  match t with
  | v => (1 = n)
  | l m => ucs1_aux m (S n)
  | a m1 m2 => ucs1_aux m1 n /\ ucs1_aux m2 n
  end.
Definition ucs1 (t:motzkin) := ucs1_aux t O.
(*- ENDucs1 *)

(** Examples: *)

Eval compute in ucs1 (v).
Eval compute in ucs1 (l v).
Eval compute in ucs1 (l (l v)).
Eval compute in ucs1 (a (l v) (l v)).
Eval compute in ucs1 (a (l v) (l (l v))).
Eval compute in ucs1 (a (l v) (l (l (l v)))).
Eval compute in ucs1 (a (l v) v).

Lemma ucs1_unique_aux : forall mt m,
  (exists! t, skeleton t = mt /\ is_open m t) -> ucs1_aux mt m.
Proof.
induction mt; simpl; intros; destruct H as [t [[Ha Hb] Huniq]].
+ apply skeleton_inversion_v in Ha. destruct Ha as [p Heq].
  subst. simpl in *.
  case_eq (Arith.Compare_dec.lt_eq_lt_dec m 1); intros Hlt _.
  - destruct Hlt; auto.
    assert (var p = var 0) as Hpb by (apply Huniq; simpl; lia).
    inversion Hpb; lia.
  - assert (var p = var 0) as Hpb0 by (apply Huniq; simpl; intuition).
    assert (var p = var 1) as Hpb1 by (apply Huniq; simpl; intuition).
    congruence.
+ pose proof (skeleton_inversion_l _ _ Ha) as Ht. destruct Ht as [p Heq].
  apply IHmt.
  exists p.
  split.
  - subst. simpl in Ha. intuition. congruence.
  - intros x' H.
    specialize (Huniq (lam x')). subst.
    assert (lam p = lam x') by
     (apply Huniq; simpl in *; destruct H;
      split; [congruence | assumption]).
   congruence.
+ pose proof (skeleton_inversion_a _ _ _ Ha) as Ht1.
  destruct Ht1 as [p1 [p2 Heq]].
  inversion Ha. rewrite Heq in Hb; inversion Hb.
  split.
  - {
    apply IHmt1.
    exists p1. split.
    - subst. simpl in Ha. intuition. congruence.
    - intros.
      specialize (Huniq (app x' p2)). subst.
      assert (app p1 p2 = app x' p2) by
       (apply Huniq ; simpl in *; destruct H2;
        split ; [congruence | tauto]).
      congruence.
  }
  - {
    apply IHmt2.
    exists p2. split.
    - subst. simpl in Ha. intuition. congruence.
    - intros.
    specialize (Huniq (app p1 x')). subst.
    assert (app p1 p2 = app p1 x') by
     (apply Huniq ; simpl in *; destruct H2;
      split ; [congruence | tauto]).
    congruence.
  }
Qed.

Lemma ucs1_unique_aux_rev : forall mt m,
  ucs1_aux mt m -> exists! t, skeleton t = mt /\ is_open m t.
Proof.
induction mt; simpl; intros; auto.
+ exists (var 0). split; simpl.
  - split. reflexivity. lia.
  - intros x' [Hske Hclo].
    apply skeleton_inversion_v in Hske. destruct Hske as [p Hp].
    subst. simpl in Hclo. assert (p = 0) by lia. auto.
+ destruct (IHmt (S m) H) as [t [[Hyp1 Hyp2] Hyp3]].
  exists (lam t). split; simpl.
  - subst; tauto.
  - intros x' [Hske Hclo].
    destruct (skeleton_inversion_l _ _ Hske) as [p Hp].
    subst. simpl in *. inversion Hske.
    rewrite (Hyp3 p); auto.
+ destruct H as [H1 H2].
  destruct (IHmt1 m H1) as [t1 [[Hyp11 Hyp12] Hyp13]].
  destruct (IHmt2 m H2) as [t2 [[Hyp21 Hyp22] Hyp23]].
  exists (app t1 t2). split; simpl.
  - subst; tauto.
  - intros x' [Hske Hclo].
    destruct (skeleton_inversion_a _ _ _ Hske) as [p1 [p2 Hx']].
    subst. simpl in *. inversion Hske.
    destruct Hclo.
    rewrite (Hyp13 p1); auto. rewrite (Hyp23 p2); auto. 
Qed.


(** ** Generalization of Proposition 4, with [ucs1_aux] *)
(*- BEGINproposition4ucs1_aux *)
Lemma proposition4ucs1_aux : forall (mt : motzkin) (m : nat),
  (exists! t, skeleton t = mt /\ is_open m t) <-> ucs1_aux mt m.
(*- ENDproposition4ucs1_aux *)
Proof.
split.
+ apply ucs1_unique_aux.
+ apply ucs1_unique_aux_rev.
Qed.

(** ** Proposition 4 with [ucs1] is a particular case *)
(*- BEGINproposition4ucs1 *)
Corollary proposition4ucs1: forall mt : motzkin,
  (exists! t, skeleton t = mt /\ is_closed t) <-> ucs1 mt.
(*- ENDproposition4ucs1 *)
Proof.
intro mt.
apply proposition4ucs1_aux.
Qed.

(** * Equivalence between [is_ucs] and [ucs1] *)

(** First implication *)

Lemma is_ucs_aux_true_ucs1_aux : forall m, is_ucs_aux m true -> ucs1_aux m 1.
Proof.
induction m; simpl; intros; intuition.
Qed.

Lemma is_ucs_aux_false_ucs1_aux : forall m, is_ucs_aux m false -> ucs1_aux m 0.
Proof.
induction m; simpl; intros.
+ inversion H.
+ apply is_ucs_aux_true_ucs1_aux; auto.
+ intuition.
Qed.

(* AG: altogether, not necessary for final lemma

(* TODO: find in stdlib or define more simply, rename? *)
Definition true2one b : nat :=
  match b with
  | true => 1
  | false => 0
  end.

(* TODO: find in stdlib or define more simply, rename? *)
Definition is_posb n : bool :=
  match n with
  | 0 => false
  | _ => true
  end.

Lemma is_ucs_aux_ucs1_aux_impl_b : forall t b, is_ucs_aux t b -> ucs1_aux t (true2one b).
Proof.
intros t b.
case b; simpl.
+ exact (is_ucs_true_ucs1_aux t).
+ exact (is_ucs_false_ucs1_aux t).
Qed.
*)

(** Second implication *)

Lemma not_ucs1_SS : forall m n, not(ucs1_aux m (S (S n))).
Proof.
induction m; simpl; intros ; intro.
+ lia.
+ specialize (IHm (S n)). contradiction.
+ specialize (IHm1 n). specialize (IHm2 n). intuition. 
Qed.

Lemma ucs1_aux_is_ucs_aux_true : forall m n, ucs1_aux m (S n) -> is_ucs_aux m true.
Proof.
induction m; simpl; intros; auto.
+ pose proof (not_ucs1_SS m n). contradiction.
+ destruct H; split; eauto.
Qed.

Lemma ucs1_aux_is_ucs_aux_false : forall m, ucs1_aux m 0 -> is_ucs_aux m false.
Proof.
induction m; simpl; intros.
+ inversion H.
+ exact (ucs1_aux_is_ucs_aux_true m 0 H).
+ tauto.
Qed.

(* Not necessary for the final lemma

Lemma ucs1_aux_is_ucs_aux_impl : forall t m, ucs1_aux t m -> is_ucs_aux t (is_posb m).
Proof.
intros t m. case m; simpl.
+ exact (ucs1_aux_is_ucs_aux_false t).
+ exact (ucs1_aux_is_ucs_aux_true t).
Qed.

Lemma ucs1_aux_is_ucs_aux_impl_b : forall t b, ucs1_aux t (true2one b) -> is_ucs_aux t b.
Proof.
intros t b. case b; simpl.
+ exact (ucs1_aux_is_ucs_aux_true t 0).
+ exact (ucs1_aux_is_ucs_aux_false t).
Qed.

(*- BEGINucs1_aux_is_ucs_aux_eq *)
Lemma ucs1_aux_is_ucs_aux_eq : forall t b, ucs1_aux t (true2one b) <-> is_ucs_aux t b.
(*- ENDucs1_aux_is_ucs_aux_eq *)
Proof.
split.
+ apply ucs1_aux_is_ucs_aux_impl_b.
+ apply is_ucs_aux_ucs1_aux_impl_b.
Qed.
*)

(*- BEGINucs1_is_ucs_eq *)
Lemma ucs1_is_ucs_eq : forall mt : motzkin, ucs1 mt <-> is_ucs mt.
(*- ENDucs1_is_ucs_eq *)
Proof.
split.
+ exact (ucs1_aux_is_ucs_aux_false mt).
+ exact (is_ucs_aux_false_ucs1_aux mt).
Qed.

(* Not necessary: equivalence for ucs1_aux / is_ucs_aux

Lemma is_ucs_aux_ucs1_aux_impl_m : forall t m, is_ucs_aux t (is_posb m) -> ucs1_aux t m.
Proof.
intros t b.
case b; simpl.
+ exact (is_ucs_false_ucs1_aux t).
+ exact (is_ucs_true_ucs1_aux t).
Qed.

(** ** Generalization of Proposition 4 with [is_ucs_aux] *)

Lemma proposition4generalized_is_ucs_aux : forall mt b,
  (exists! t, skeleton t = mt /\ is_open (true2one b) t) <-> is_ucs_aux mt b.
Proof.
split; intro H.
- {
 apply ucs1_aux_is_ucs_aux_impl_b.
 apply proposition4generalized_ucs1_aux.
 apply H.
}
- {
 apply proposition4generalized_ucs1_aux.
 apply is_ucs_aux_ucs1_aux_impl.
 apply H.
}
Qed.
*)

(** ** Proposition 4 with [is_ucs] is a particular case *)
(*- BEGINproposition4 *)
Proposition proposition4: forall mt : motzkin,
  (exists! t, skeleton t = mt /\ is_closed t) <-> is_ucs mt.
(*- ENDproposition4 *)
Proof.
intro mt.
split.
- intro H. apply (ucs1_is_ucs_eq mt).
  apply proposition4ucs1. apply H.
- intro H. apply (ucs1_is_ucs_eq mt) in H.
  apply proposition4ucs1. apply H.
Qed.
