(****************************************************************************)
(* Copyright 2021-2022 Catherine Dubois, Nicolas Magaud and Alain Giorgetti *)
(* Samovar - ICube - FEMTO-ST institute                                     *)
(****************************************************************************)

(****************************************************************************)
(*      This file is distributed under the terms of the                     *)
(*       GNU Lesser General Public License Version 2.1                      *)
(****************************************************************************)

(*- BEGINfamily *)
Module Type family.
  Parameter T : Set.
  Parameter is_P : T -> Prop.
  Parameter P : Set.
  Parameter T2P : forall (x:T), is_P x -> P.
  Parameter P2T : P -> T.
  Parameter is_P_lemma : forall v, is_P (P2T v).
  Parameter P2T_is_P :
    forall (t : T) (H : is_P t), P2T (T2P t H) = t.
  Parameter proof_irr :
    forall x (p1 p2:is_P x), p1 = p2.
End family.
(*- ENDfamily *)

(*- BEGINfunctor *)
Module Type equiv_sig (f:family).
Import f.
Parameter rec_P : Type.
Parameter rec_P2P : rec_P -> P.
Parameter P2rec_P : P -> rec_P.
Parameter P2rec_PK : forall x: rec_P, P2rec_P (rec_P2P x) = x.
End equiv_sig.

Module equiv_family (Import f:family) <: equiv_sig(f).
  Record rrec_P := Build_rrec_P {
    P_struct :> T;
    P_prop : is_P P_struct
  }.

  Definition rec_P := rrec_P.

  Definition rec_P2P m := T2P (P_struct m) (P_prop m).
  Definition P2rec_P (x:P) : rec_P := Build_rrec_P (P2T x) (is_P_lemma x).

  Lemma P2rec_PK : forall x: rec_P, P2rec_P (rec_P2P x) = x.
  Proof.
    unfold rec_P2P, P2rec_P; intros; simpl.
    generalize (is_P_lemma (T2P (P_struct x) (P_prop x))).
    rewrite P2T_is_P.
    intros; destruct x; simpl in *.
    rewrite (proof_irr _ P_prop0 i).
    reflexivity.
  Qed.
End equiv_family.
(*- ENDfunctor *)

  (* Lemma rec_P2PK : forall zx: P), rec_P2P (P2rec_P x) = x. *)
  (* Proof. *)
  (* requires knowing the inductive type P, proof by induction on x:P *)


From QuickChick Require Import QuickChick Tactics.

(*- BEGINgenfamily *)
Module Type family_for_generators (f : family).
  Import f.
  Module facts := equiv_family (f).
  Import facts.
  Parameter is_Pb : T -> bool.
  Parameter is_P_dec : forall x:T, is_P x <-> is_Pb x = true.
  Parameter gen_T : nat -> G T.
  Parameter default_P : T.
  Parameter default_is_P : is_Pb default_P = true.
  Parameter gen_rec_P : nat -> G rec_P.
  Parameter gen_P : nat -> G P.
End family_for_generators.
(*- ENDgenfamily *)

Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200).
End DoNotation.

Import DoNotation.

(*- BEGINgenfunctor *)
Module generators_family (f : family) (g : family_for_generators f).
  Import f.
  Import g.
  Import g.facts.

  Definition filter_max := 100.
  Fixpoint gen_filter_P_aux nb n :=
  match nb with
  | 0 => returnGen default_P
  | S p => do! val <- gen_T n;
           if is_Pb val then returnGen val
           else gen_filter_P_aux p n
  end.
  Definition gen_filter_P : nat -> G T := gen_filter_P_aux filter_max.

  Definition gen_P_from_rec_P n : G P :=
  do! p <- gen_rec_P n;
  returnGen (rec_P2P p).

  Definition gen_rec_P_from_P n : G rec_P :=
  do! p <- gen_P n;
  returnGen (P2rec_P p).
End generators_family.
(*- ENDgenfunctor *)

 (* Test gen_P_struct:
  QuickCheck (sized (fun n => 
    forAll (gen_P_struct n) is_Pb)). *)

(* Another interface to take more dependencies into account *)

(* Alternative module dealing with dependencies *)

Module Type param_family.

  Parameter U:Type.
  Parameter T:Type.
  Parameter is_P : U -> T -> Prop.
  Parameter P: U -> Type.

  Parameter T2P :  forall (t : T) (m : U), is_P m t -> P m.
  Parameter P2T : forall m:U, P m -> T.

  Parameter is_P_lemma : forall (m : U) (t : P m), is_P m (P2T m t).
  Parameter P2T_is_P : forall m t H,  P2T m (T2P t m H) = t.

  Parameter proof_irr : forall x y (p1 p2:is_P x y), p1 = p2.
End param_family.


Module equiv_param_family (Import f:param_family).
  Record rec_P (P_param:U) := {
    P_struct :> T;
    P_prop : is_P P_param P_struct
  }.

  Definition rec_P2P u m := T2P (P_struct u m) u (P_prop u m).
  Definition P2rec_P n (x:P n) : (rec_P n) := Build_rec_P n (P2T n x) (is_P_lemma n x).

  Lemma P2rec_PK : forall n, forall x: rec_P n , P2rec_P _ (rec_P2P n x) = x.
  Proof.
    unfold rec_P2P, P2rec_P; intros; simpl.
    generalize (is_P_lemma _ (T2P (P_struct n x) n (P_prop n x))).
    rewrite P2T_is_P.
    intros; destruct x; simpl in *.
    rewrite (proof_irr _ _ P_prop0 i).
    reflexivity.
  Qed.

End equiv_param_family.

(*- BEGINgen1 *)
Module Type family_for_generators1 (Import f : family).
  Import f.
  Module facts := equiv_family (f).
  Parameter is_Pb : T -> bool.
  Parameter is_P_dec : forall x:T, is_P x <-> is_Pb x = true.
  Parameter gen_T : nat -> G T.
  Parameter default_P : T.
  Parameter default_is_P : is_Pb default_P = true.
End family_for_generators1.

Module generators_family1 (f : family) (g : family_for_generators1 f).
  Import f.
  Import g.
  Import g.facts.

  Definition filter_max := 100.
  Fixpoint gen_filter_P_aux nb n :=
  match nb with
  | 0 => returnGen default_P
  | S p => do! val <- gen_T n;
           if is_Pb val then returnGen val
           else gen_filter_P_aux p n
  end.
  Definition gen_filter_P : nat -> G T := gen_filter_P_aux filter_max.
End generators_family1.
(*- ENDgen1 *)

(*- BEGINgen2 *)
Module Type family_for_generators2 (Import f : family) (Import facts : equiv_sig f).
  Parameter gen_rec_P : nat -> G rec_P.
End family_for_generators2.

Module generators_family2 (Import f : family) (Import facts : equiv_sig f) (Import g : family_for_generators2 f facts) .
 Definition gen_P n : G P :=
  do! p <- gen_rec_P n;
  returnGen (rec_P2P p).
End generators_family2.
(*- ENDgen2 *)

(*- BEGINgen3 *)
Module Type family_for_generators3 (Import f : family).
  Parameter gen_P : nat -> G P.
End family_for_generators3. 

Module generators_family3 (Import f : family) 
 (Import g : family_for_generators3 f) 
 (Import facts : equiv_sig f).
  Definition gen_rec_P n : G rec_P :=
  do! p <- gen_P n;
  returnGen (P2rec_P p).
End generators_family3.
(*- ENDgen3 *)

