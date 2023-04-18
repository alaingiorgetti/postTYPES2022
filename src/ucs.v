(****************************************************************************)
(* Copyright 2021-2022 Catherine Dubois, Nicolas Magaud and Alain Giorgetti *)
(* Samovar - ICube - FEMTO-ST institute                                     *)
(****************************************************************************)

(****************************************************************************)
(*      This file is distributed under the terms of the                     *)
(*       GNU Lesser General Public License Version 2.1                      *)
(****************************************************************************)

Require Import familyInterface.
Require Export closable.

(*- BEGINis_ucs *)
Fixpoint is_ucs_aux m b :=
  match m with
  | v => b = true
  | l m => if b then False
           else is_ucs_aux m true
  | a m1 m2 => is_ucs_aux m1 b /\ is_ucs_aux m2 b
  end.

Definition is_ucs m := is_ucs_aux m false.
(*- ENDis_ucs *)

Lemma bool_dec : forall a b:bool, (a=b)\/(a <>b).
Proof.
  destruct a; destruct b; try solve [left; trivial | right; intro; discriminate ].
Qed.

Lemma proof_irr_is_ucs_aux : forall x t (p1 p2:is_ucs_aux x t), p1 = p2.
Proof.
  induction x; simpl.
  destruct t.
  intros; apply (@Eqdep_dec.eq_proofs_unicity bool bool_dec true true).
  discriminate.
  destruct t.
  intuition.
  apply IHx.
  intros t [ Hp1 Hp2] [ Hq1 Hq2].
  rewrite (IHx1 t Hp1 Hq1).
  rewrite (IHx2 t Hp2 Hq2).
  reflexivity.
Qed.

Lemma proof_irr_is_ucs : forall x (p1 p2:is_ucs x), p1 = p2.
Proof.
  intros; apply proof_irr_is_ucs_aux.
Qed.

(** * Examples *)

Lemma not_mot_ex1_ucs : not (is_ucs mot_ex1).
Proof. unfold is_ucs; simpl; tauto. Defined.

Lemma mot_ex2_ucs : is_ucs mot_ex2.
Proof. unfold is_ucs; simpl; auto. Defined.

(** ** Record type for uniquely closable Motzkin trees *)

(*- BEGINrec_ucs *)
Record rec_ucs : Type := Build_rec_ucs {
  ucs_struct : motzkin;
  ucs_prop : is_ucs ucs_struct
}.
(*- ENDrec_ucs *)

(** *** Example *)

Definition rec_ucs2 := Build_rec_ucs mot_ex2 mot_ex2_ucs.


(** ** Inductive type for uniquely closable Motzkin trees *)

(** <<ucs> and <<ca>> respectively correspond to the Prolog predicates <<uniquelyClosable/2>>
    and <<closedAbove/2>> and the Haskell datatypes  <<UniquelyClosable>> and 
    <<ClosedAbove>> in [[BT17]]. *)

(*- BEGINucs *)
Inductive ca :=
| V : ca
| B : ca -> ca -> ca.

Inductive ucs :=
| L : ca -> ucs
| A : ucs -> ucs -> ucs.
(*- ENDucs *)

(** * Example *)

Definition ucs_ex1 := L (B V V).

(** * Equivalence between the record [rec_ucs] and [ucs] *)

(*- BEGINis_ucs_aux2ca *)
Lemma is_ucs_aux2ca : forall m : motzkin, is_ucs_aux m true -> ca.
(*- ENDis_ucs_aux2ca *)
Proof.
fix rec 1.
intro m; case m.
- intros; exact V.
- intros; contradiction.
- intros ma mb Hmamb; destruct Hmamb as [Hma Hmb];
  exact (B (rec ma Hma) (rec mb Hmb)).
Defined.

(*- BEGINmotzkin2ucs *)
Fixpoint motzkin2ucs (m : motzkin) : is_ucs m -> ucs :=
  match m as m0 return (is_ucs m0 -> ucs) with
  | v =>
      fun H : is_ucs v =>
      let H0 :=
        match H in (_ = y) return (y = true -> ucs) with
        | eq_refl =>
            fun H0 : false = true =>
            (fun H1 : false = true => let H2 : False := eq_ind false (fun e : bool => if e then False else True) I true H1 in False_rec ucs H2) H0
        end in
      H0 eq_refl
  | l m0 => (fun (m1 : motzkin) (H : is_ucs (l m1)) => L (is_ucs_aux2ca m1 H)) m0
  | a m0 m1 =>
      (fun (ma mb : motzkin) (Hmamb : is_ucs (a ma mb)) =>
       match Hmamb with
       | conj x x0 => (fun (Hma : is_ucs_aux ma false) (Hmb : is_ucs_aux mb false) => A (motzkin2ucs ma Hma) (motzkin2ucs mb Hmb)) x x0
       end) m0 m1
  end.
(*- ENDmotzkin2ucs *)
          
(*- BEGINucs2motzkin *)
Fixpoint ca2motzkin c :=
  match c with
  | V => v
  | B c1 c2 => a (ca2motzkin c1) (ca2motzkin c2)
  end.

Fixpoint ucs2motzkin c :=
  match c with
  | L c => l (ca2motzkin c)
  | A c1 c2 => a (ucs2motzkin c1) (ucs2motzkin c2)
  end.
(*- ENDucs2motzkin *)

(*- BEGINis_ucs_aux_ca2motzkin *)
Lemma is_ucs_aux_ca2motzkin : forall c, is_ucs_aux (ca2motzkin c) true.
(*- ENDis_ucs_aux_ca2motzkin *)
Proof.
induction c; simpl; auto.
Defined.

(*- BEGINis_ucs_ucs2motzkin *)
Lemma is_ucs_ucs2motzkin : forall c, is_ucs (ucs2motzkin c).
(*- ENDis_ucs_ucs2motzkin *)
Proof.
  unfold is_ucs; induction c; simpl.
+ apply is_ucs_aux_ca2motzkin.
+ tauto.
Defined.

Lemma ca2muc_K_aux : forall (m : motzkin)
  (Hucs : is_ucs_aux m true),
  (ca2motzkin (is_ucs_aux2ca m Hucs)) = m.
Proof.
induction m ; simpl ; intros; auto.
+ contradiction.
+ destruct Hucs as [Hucs1 Hucs2].
  simpl.
  specialize (IHm1 Hucs1).
  specialize (IHm2 Hucs2).
  rewrite IHm1. rewrite IHm2. reflexivity.
Qed.

Lemma uc2muc_K_aux : forall (m : motzkin)
  (Hucs : is_ucs m),
  ucs2motzkin (motzkin2ucs m Hucs) = m.
Proof.
induction m ; intros; auto.
+ simpl in Hucs ; inversion Hucs.
+ simpl in Hucs ;  simpl. rewrite ca2muc_K_aux. reflexivity.
+ destruct Hucs as [Hucs1 Hucs2].
  simpl.
  specialize (IHm1 Hucs1).
  specialize (IHm2 Hucs2).
  rewrite IHm1. rewrite IHm2. reflexivity.
Qed.


Module ucs_mod : family
  with Definition T := motzkin
  with Definition is_P := is_ucs
  with Definition P := ucs

  with Definition T2P := motzkin2ucs

  with Definition P2T := ucs2motzkin
  with Definition is_P_lemma := is_ucs_ucs2motzkin

  with Definition P2T_is_P := uc2muc_K_aux.

  Definition T := motzkin.
  Definition is_P := is_ucs.
  Definition P := ucs.

  Definition T2P : forall (x:T), is_P x -> P := motzkin2ucs.

  Definition P2T : P -> T := ucs2motzkin.
  Definition is_P_lemma : forall x:P, is_P (P2T x) := is_ucs_ucs2motzkin.

  Definition P2T_is_P : forall (m : T) (H : is_P m), P2T (T2P m H) = m := uc2muc_K_aux.

  Definition proof_irr := proof_irr_is_ucs.
End ucs_mod.

Module UCS := equiv_family (ucs_mod).

(* Thus you obtain the following lemma for free:
Lemma UCS.P2rec_PK : forall x:UCS.rec_P, UCS.P2rec_P (UCS.rec_P2P x) = x.
*)

(* You can give it a more explicit name: *)
Notation ucs2rec_ucs_left_inverse := UCS.P2rec_PK.

(* You can also import the module: *)

Import UCS.

(* If you declare this lemma with another name, you can prove it generically: *)

Lemma ucs2rec_ucsK : forall x:rec_P, P2rec_P (rec_P2P x) = x.
Proof. apply P2rec_PK. Qed.


Lemma rec_P2PK : forall x:ucs, rec_P2P (P2rec_P x) = x.
Proof.
induction x.
+ unfold P2rec_P, rec_P2P; simpl.
destruct c.
- reflexivity.
- induction c1; induction c2; simpl.
  reflexivity.
  apply f_equal.
  apply f_equal.
  apply f_equal2.
  inversion IHc2_1.
  rewrite H0.
  rewrite H0.
  reflexivity.  
  inversion IHc2_2.
  rewrite H0.
  rewrite H0.
  reflexivity.
  apply f_equal.
  apply f_equal2.
  apply f_equal2.
  inversion IHc1_1.
  rewrite H0.
  rewrite H0.
  reflexivity.
  inversion IHc1_2.
  rewrite H0.
  rewrite H0.
  reflexivity.
  reflexivity.
  apply f_equal.
  apply f_equal2.
  apply f_equal2.
  inversion IHc1_1.
  rewrite H0.
  rewrite H0.
  reflexivity.
  inversion IHc1_2.
  rewrite H0.
  rewrite H0.
  reflexivity.
  inversion IHc1_1.
  apply f_equal2.
  rewrite H1.
  rewrite H1.
  reflexivity.
  rewrite H2.
  rewrite H2.
  reflexivity.
  + unfold P2rec_P, rec_P2P in *; simpl in *.
    apply f_equal2; assumption.
Qed.


