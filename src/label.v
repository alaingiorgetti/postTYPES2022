(****************************************************************************)
(* Copyright 2021-2022 Catherine Dubois, Nicolas Magaud and Alain Giorgetti *)
(* Samovar - ICube - FEMTO-ST institute                                     *)
(****************************************************************************)

(****************************************************************************)
(*      This file is distributed under the terms of the                     *)
(*       GNU Lesser General Public License Version 2.1                      *)
(****************************************************************************)

Require Import Arith Lia.
Require Import closable open BT17.

(** * Characterization of m-open lambda terms in De Bruijn form with Motzkin trees *)

(** ** Nondeterministic relation [(label m)] between Motzkin trees (without labels) and labeled Motzkin trees *)

(*- BEGINlabel *)
Inductive label : nat -> motzkin -> lmt -> Prop :=
| Lvar : forall m i, i < m -> label m v (var i)
| Llam : forall m mt t, label (S m) mt t -> label m (l mt) (lam t)
| Lapp : forall m mt1 mt2 t1 t2, label m mt1 t1 -> label m mt2 t2
    -> label m (a mt1 mt2) (app t1 t2).
(*- ENDlabel *)

(** *** Useful auxiliary lemma *)

(*- BEGINlabel_mon *)
Lemma label_mon : forall m1 mt t, label m1 mt t -> forall m2, m1 <= m2 -> label m2 mt t.
(*- ENDlabel_mon *)
Proof.
intros m1 mt t H1; induction H1; intros m2 H2.
- apply Lvar. lia.
- apply Llam. apply IHlabel. lia.
- apply Lapp.
 + apply IHlabel1. assumption.
 + apply IHlabel2. assumption.
Qed.

(** *** [(motzkin2lmt0 mt)] provides an image of [mt] by [label 1]: *)

Lemma label_motzkin2lmt0 : forall mt, label 1 mt (motzkin2lmt0 mt).
Proof.
induction mt; simpl.
- apply Lvar. lia.
- apply Llam. apply label_mon with (m1 := 1). assumption. lia.
- apply Lapp; assumption.
Qed.

(** ** Characterization of [m]-open terms as labelings of their skeleton. *)

(*- BEGINskeleton_open *)
Definition skeleton_open (m:nat) (t:lmt) : Prop := label m (skeleton t) t.
(*- ENDskeleton_open *)

(** ** Equivalence between a characterization of [m]-open terms with Motzkin trees 
  and the definition of [m]-open terms *)

Lemma is_open_skeleton_open : forall t m, is_open m t -> skeleton_open m t.
Proof.
unfold skeleton_open.
induction t; simpl; intros m H; try (destruct H); try constructor; auto.
Qed.

Lemma skeleton_open_is_open : forall t m, skeleton_open m t -> is_open m t.
Proof.
unfold skeleton_open.
induction t; simpl; intros m H; inversion H; subst; auto.
Qed.

(*- BEGINskeleton_is_open_eq *)
Lemma skeleton_is_open_eq : forall m t, skeleton_open m t <-> is_open m t.
(*- ENDskeleton_is_open_eq *)
Proof.
split.
apply skeleton_open_is_open.
apply is_open_skeleton_open.
Qed.

(*- BEGINskeleton_labelK *)
Lemma skeleton_labelK : forall m : nat, forall mt : motzkin, forall t : lmt,
  label m mt t -> skeleton t = mt.
(*- ENDskeleton_labelK *)
Proof.
intros m mt t H.
induction H; simpl; subst; auto.
Qed.

(*- BEGINminimal_openness *)
Fixpoint minimal_openness (t : lmt) : nat :=
  match t with
  | var i => i+1
  | lam t => match minimal_openness t with S m => m | _ => 0 end
  | app t1 t2 => max (minimal_openness t1) (minimal_openness t2)
  end.
(*- ENDminimal_openness *)


(* Remark: `label m (skeleton t) t` can be replaced by ` skeleton_open m t` *)
(*- BEGINlabel_skeletonK *)
Lemma label_skeletonK : forall t : lmt, label (minimal_openness t) (skeleton t) t.
(*- ENDlabel_skeletonK *)
Proof.
induction t; simpl.
- constructor. lia.
- constructor.
 case_eq (minimal_openness t).
 + intro E. apply label_mon with (m1 := 0); try lia. rewrite E in IHt. assumption.
 + intros n E. rewrite E in IHt. assumption.
- constructor.
 + apply label_mon with (m1 := minimal_openness t1). assumption. lia.
 + apply label_mon with (m1 := minimal_openness t2). assumption. lia.
Qed.

(*- BEGINlmt_minimal_openness *)
Lemma lmt_minimal_openness : forall t : lmt, is_open (minimal_openness t) t.
(*- ENDlmt_minimal_openness *)
Proof.
intro t.
apply skeleton_is_open_eq.
apply label_skeletonK.
Qed.

(*- BEGINminimality *)
Lemma minimality : forall t : lmt, forall m : nat, is_open m t -> m >= minimal_openness t.
(*- ENDminimality *)
Proof.
intro t. induction t; simpl; intros m H; try lia.
- case_eq (minimal_openness t); intros; subst; try lia. pose proof (IHt _ H). lia.
- destruct H as [H1 H2].
  pose proof (IHt1 _ H1).
  pose proof (IHt2 _ H2).
  lia.
Qed.

Lemma minimality' : forall t : lmt, forall m, m < minimal_openness t -> not (is_open m t).
Proof.
unfold not.
intros t m H1 H2. pose proof (minimality _ _ H2). lia.
Qed.
