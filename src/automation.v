(****************************************************************************)
(* Copyright 2021-2022 Catherine Dubois, Nicolas Magaud and Alain Giorgetti *)
(* Samovar - ICube - FEMTO-ST institute                                     *)
(****************************************************************************)

(****************************************************************************)
(*      This file is distributed under the terms of the                     *)
(*       GNU Lesser General Public License Version 2.1                      *)
(****************************************************************************)

Require Import Arith Lia.
Require Import familyInterface.

Require Import closable ucs open.

(** Tactic to prove automatically the following two lemmas, using the concrete representations of [T], [P] and [is_P]. *)

(*
Parameter is_P_lemma : forall v, is_P (P2T v).
*)

Ltac is_P_lemma_tac := intros; repeat (match goal with c:_ |- _ => red; induction c; simpl; auto end).

Lemma is_closable_lemma : forall v, is_closable (closable2motzkin v).
Proof.
is_P_lemma_tac.
Qed.

Lemma is_ucs_lemma : forall v, is_ucs (ucs2motzkin v).
Proof.
is_P_lemma_tac.
Qed.

(*
Parameter P2T_is_P : forall (m : T) (H : is_P m), P2T (T2P m H) = m.
*)

(** Tactics to prove automatically some roundtrip lemmas. *)

Ltac invert_all := match goal with H:_ |- _ => solve [inversion H] end.
Ltac clear_all := match goal with H:_ |- _ => clear H end.
Ltac induction_cbn m := induction m; simpl; intros; cbn in *.
Ltac destruct_and := repeat (match goal with [ H:_/\ _ |- _ ] => destruct H; cbn in * end).
Ltac f_equals := repeat (apply f_equal || apply f_equal2). 
Ltac cond_rewrite := repeat (match goal with [ H: forall Hclo:_, _ |- _ ] => rewrite (H _) end).
Ltac cond_rewrite_inj := repeat (match goal with [ i:?T, H: forall Hclo:?T, _ |- _ ] =>
  let Hnew:= fresh in
  generalize (H i); clear H; intros Hnew; repeat (injection Hnew; clear Hnew; intros Hnew) end).

Ltac P2T_is_P_tac m := induction_cbn m; destruct_and; f_equals; solve [tauto | invert_all |  cond_rewrite; trivial| cond_rewrite_inj; trivial | clear_all;P2T_is_P_tac m].

Lemma closable2rec_closableK_aux : forall (m : motzkin) (Hclo : is_closable m),
  closable2motzkin (motzkin2closable m Hclo) = m.
Proof.
P2T_is_P_tac m.
Qed.

Lemma uc2muc_K_aux : forall (m : motzkin)
  (Hucs : is_ucs m),
  ucs2motzkin (motzkin2ucs m Hucs) = m.
Proof.
P2T_is_P_tac m.
Qed.

(* The other roundtrip lemma is Lemma rec_P2PK : forall x: P), rec_P2P (P2rec_P x) = x. *)

Ltac destruct_match := try match goal with  [|- (match ?X with conj _ _ => _ end = _ )] => destruct X end.

Ltac proof_irr := repeat (match goal with H:?u ?t ?h = ?v |- ?u ?t ?h' = ?v => rewrite (proof_irr_is_closable _ h' h) end).

Ltac inject_all := 
  repeat (match goal with H:_|- _ => let Hnew:= fresh in injection H; clear H; intros Hnew end).

Ltac rec2ind x := induction_cbn x; try solve [trivial | destruct_match; inject_all; f_equals; proof_irr; trivial].

Lemma rec_closable2closableK :
  forall x: closable, rec_closable2closable (closable2rec_closable x) = x.
Proof.
  rec2ind x.
Qed.

Lemma rec_ucs2Pucs : forall x: ucs, UCS.rec_P2P (UCS.P2rec_P x) = x.
Proof.
  rec2ind x.
  rec2ind c.
Qed.

(* with dependent types? *)

(*
Parameter is_P_lemma : forall (m : U) (t : P m), is_P m (P2T m t).
Parameter P2T_is_P : forall m t H,  P2T m (T2P t m H) = t.
Lemma rec_open2openK : forall m x, rec_open2open m (open2rec_open m x) = x. (* à vérifier *)
*)

Lemma is_open_lemma : forall m t, is_open m (open2lmt m t).
Proof.
  is_P_lemma_tac.
Qed.

Lemma open2lmtK : forall m t H, open2lmt m (lmt2open t m H) = t.
Proof.
  intros m t; revert m.
  P2T_is_P_tac t.
Qed.

Lemma rec_open2openK : forall m x, rec_open2open m (open2rec_open m x) = x.
Proof.
  rec2ind x.
Qed.

