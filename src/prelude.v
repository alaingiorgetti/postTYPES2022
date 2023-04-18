(****************************************************************************)
(* Copyright 2021-2022 Catherine Dubois, Nicolas Magaud and Alain Giorgetti *)
(* Samovar - ICube - FEMTO-ST institute                                     *)
(****************************************************************************)

(****************************************************************************)
(*      This file is distributed under the terms of the                     *)
(*       GNU Lesser General Public License Version 2.1                      *)
(****************************************************************************)

Require Import List.
Require Import Permutation.

Definition split {A : Type} (l1 l2 l : list A) := Permutation (l1 ++ l2) l.

Lemma split_length {A : Type} : forall (l1 l2 l : list A), 
  split l1 l2 l -> length l = (length l1) + (length l2).
Proof.
intros. unfold split in H. apply Permutation_length in H. rewrite <- H.
apply List.app_length.
Qed.
