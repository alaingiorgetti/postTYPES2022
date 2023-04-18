(****************************************************************************)
(* Copyright 2021-2022 Catherine Dubois, Nicolas Magaud and Alain Giorgetti *)
(* Samovar - ICube - FEMTO-ST institute                                     *)
(****************************************************************************)

(****************************************************************************)
(*      This file is distributed under the terms of the                     *)
(*       GNU Lesser General Public License Version 2.1                      *)
(****************************************************************************)

Require Import familyInterface.

(** ** Coq type for Motzkin trees *)

(** "A _Motzkin tree_ (also called binary-unary tree) is a rooted ordered tree 
    built from binary nodes, unary nodes and leaf nodes. Thus the set of 
    Motzkin trees can be seen as the free algebra generated by the 
    constructors <<v/0>>, <<l/1>> and <<a/2>>." [[BT17, section 2]] *)

(*- BEGINmotzkin *)
Inductive motzkin : Set :=
| v : motzkin
| l : motzkin -> motzkin
| a : motzkin -> motzkin -> motzkin.
(*- ENDmotzkin *)

Scheme Equality for motzkin. (* useful for QuickChick *)
(*
motzkin_beq is defined
motzkin_eq_dec is defined
*)

(** *** Examples of Motzkin trees: *)

Definition mot_ex1 := l (a v (l v)).
Definition mot_ex2 := l (a v v).

(** * Closable skeletons *)

(** The following definition corresponds to the following claim in [[BT17]]:
     "closable skeletons [[...]] require at least one lambda on each path,
    with Motzkin trees below" [[BT17, pages 4-5]]. *)

(*- BEGINis_closable *)
Fixpoint is_closable (mt: motzkin) :=
  match mt with
  | v => False
  | l m => True
  | a m1 m2 => is_closable m1 /\ is_closable m2
  end.
(*- ENDis_closable *)

Lemma proof_irr_is_closable :forall x (p1 p2:is_closable x), p1 = p2.
Proof.
induction x; simpl.
- intuition.
- intros Hp1 Hp2.
 case Hp1; case Hp2; reflexivity.
- destruct p1; destruct p2.
  rewrite (IHx1 i i1).
  rewrite (IHx2 i0 i2).
  reflexivity.
Qed.

(** * Example *)

Lemma mot_ex1_closable : is_closable mot_ex1.
Proof. simpl; auto. Defined.

(** ** Record type for closable Motzkin trees *)

(*- BEGINrec_closable *)
Record rec_closable : Type := Build_rec_closable {
  closable_struct :> motzkin;
  closable_prop : is_closable closable_struct
}.
(*- ENDrec_closable *)

(** *** Example *)

Definition rec_closable1 := Build_rec_closable mot_ex1 mot_ex1_closable.

(** * Inductive definition of closable Motzkin trees *)

(** Corresponds to the CF-grammar described by <<closable/2>> in [[BT17]]. *)

(*- BEGINclosable *)
Inductive closable :=
| La : motzkin -> closable
| Ap : closable -> closable -> closable.
(*- ENDclosable *)

Scheme Equality for closable.

Definition closable1 := La (a v (l v)).

(** * Equivalence between the record [rec_closable] and [closable] *)

(** ** From [rec_closable] to [closable] *)

Lemma motzkin2closable_aux : forall m, is_closable m -> closable.
Proof.
fix rec 1.
intros m; case m.
+ intros H; inversion H.
+ intros m0 Hm0; apply (La m0).
+ intros m1 m2 [Hm1 Hm2]; apply (Ap (rec m1 Hm1) (rec m2 Hm2)).
Defined.

(*- BEGINmotzkin2closable *)
Fixpoint motzkin2closable  (m : motzkin) : is_closable m -> closable :=
  match m as m0 return (is_closable m0 -> closable) with
  | v => fun H : is_closable v => let H0 := match H return closable with end in H0
  | l m0 => fun _ : is_closable (l m0) => La m0
  | a m1 m2 => fun H : is_closable (a m1 m2) =>
      match H with
      | conj Hm1 Hm2 => Ap (motzkin2closable m1 Hm1) (motzkin2closable m2 Hm2)
      end
  end.
(*- ENDmotzkin2closable *)

(** *** Example *)

Eval compute in (motzkin2closable mot_ex1 mot_ex1_closable).

(*- BEGINrec_closable2closable *)
Definition rec_closable2closable m := motzkin2closable (closable_struct m) (closable_prop m).
(*- ENDrec_closable2closable *)

(** ** From [closable] to [rec_closable] *)

(*- BEGINclosable2motzkin *)
Fixpoint closable2motzkin c :=
  match c with
  | La m => l m
  | Ap c1 c2 => a (closable2motzkin c1) (closable2motzkin c2)
  end.
(*- ENDclosable2motzkin *)

(** *** Example *)

Eval compute in (closable2motzkin closable1).

(*- BEGINis_closable_lemma *)
Lemma is_closable_lemma : forall c, is_closable (closable2motzkin c).
(*- ENDis_closable_lemma *)
Proof.
induction c; simpl; auto.
Qed.

(*- BEGINclosable2rec_closable *)
Definition closable2rec_closable c :=
  Build_rec_closable (closable2motzkin c) (is_closable_lemma c).
(*- ENDclosable2rec_closable *)

(*- BEGINclosable2rec_closableK_aux *)
Lemma closable2rec_closableK_aux : forall (m : motzkin) (Hclo : is_closable m),
  closable2motzkin (motzkin2closable m Hclo) = m.
(*- ENDclosable2rec_closableK_aux *)
Proof.
induction m; simpl; intros; auto.
+ contradiction.
+ destruct Hclo as [Hclo1 Hclo2].
  simpl.
  specialize (IHm1 Hclo1).
  specialize (IHm2 Hclo2).
  rewrite IHm1. rewrite IHm2. reflexivity.
Qed.

(*- BEGINrec_closable2closableK *)
Lemma rec_closable2closableK : forall x, closable2rec_closable (rec_closable2closable x) = x.
(*- ENDrec_closable2closableK *)
Proof.
  destruct x.
  unfold closable2rec_closable, rec_closable2closable; simpl.
generalize (is_closable_lemma (motzkin2closable closable_struct0 closable_prop0)); intros p.
revert p.
rewrite closable2rec_closableK_aux.
intros.
rewrite (proof_irr_is_closable _ p (closable_prop0)).
reflexivity.
Qed.

Lemma motzkin_erasure : forall c h,
 (motzkin2closable (closable2motzkin c) h) = c.
Proof.
  induction c; simpl; intros; auto.
  destruct h;rewrite IHc1, IHc2; reflexivity.
Qed.

(*- BEGINclosable2rec_closableK *)
Lemma closable2rec_closableK : forall c, rec_closable2closable (closable2rec_closable c) = c.
(*- ENDclosable2rec_closableK *)
Proof.
intros; unfold rec_closable2closable,closable2rec_closable; simpl.
apply motzkin_erasure.
Qed.

Module closable <: family.
  Definition T := motzkin.
  Definition is_P := is_closable.
  Definition P := closable.
  Definition T2P := motzkin2closable.
  Definition P2T := closable2motzkin.
  Definition is_P_lemma := is_closable_lemma.
  Definition P2T_is_P := closable2rec_closableK_aux.
  Definition proof_irr := proof_irr_is_closable.
End closable.

(* Automatically defined in the functor equiv_family:

Definition rec_P := rec_closable.
Definition rec_P2P := rec_closable2closable.
Definition P2rec_P := closable2rec_closable.
Definition rec_P2Pk := closable2rec_closableK.
Definition P2rec_Pk := rec_closable2closableK.
*)
