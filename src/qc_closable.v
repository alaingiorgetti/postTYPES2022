(****************************************************************************)
(* Copyright 2021-2022 Catherine Dubois, Nicolas Magaud and Alain Giorgetti *)
(* Samovar - ICube - FEMTO-ST institute                                     *)
(****************************************************************************)

(****************************************************************************)
(*      This file is distributed under the terms of the                     *)
(*       GNU Lesser General Public License Version 2.1                      *)
(****************************************************************************)

Require Import Arith List.
Import ListNotations.
(*Open Scope Z_scope.*)
Set Implicit Arguments.

From QuickChick Require Import QuickChick Tactics.

Require Import closable.
Require Import familyInterface.

(*****************************************)
(** * Random generation of Motzkin trees *)
(*****************************************)

Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200).
End DoNotation.

Import DoNotation.

(** ** Motzkin tree generator *)

(*- BEGINgen_motzkin *)
Derive (Arbitrary, Show) for motzkin.
(*- ENDgen_motzkin *)
  
Definition gen_motzkin n : G motzkin := 
@arbitrarySized _ GenSizedmotzkin n.

(* Sample (gen_motzkin 3).*)


(** ** Closable Motzkin trees *)

Fixpoint isClosable_auxb mt V :=
match mt with
| v => Nat.leb 1 V
| l m => isClosable_auxb m (S V) 
| a m1 m2 => andb (isClosable_auxb m1 V)  
                  (isClosable_auxb m2 V)
end.

(* Corresponds to <<isClosable(X):-isClosable(X,0).>> in [[BT17]] *)
Definition isClosableb X := isClosable_auxb X 0.


Fixpoint is_closableb mt :=
match mt with
| v => false
| l m => true
| a m1 m2 => andb (is_closableb m1) (is_closableb m2)
end.

Lemma is_closable_dec: forall mt, is_closable mt <-> is_closableb mt = true.
Proof.
split ; induction mt; simpl ; intros; simpl ; try tauto.
+ destruct H as [H0 H1] ; apply IHmt1 in H0 ; apply IHmt2 in H1 ; intuition.
+ inversion H.
+ rewrite Bool.andb_true_iff in H. destruct H as [H0 H1] ; apply IHmt1 in H0 ; apply IHmt2 in H1 ; intuition.
Qed.

Import QcNotation.
 (* Line added for compatibility with QC for Coq 8.7, for the notation ==> *)

(* QC (random) generators by filtering, similar to <<closableSkel>> and <<unclosableSkel>> in [[BT17]] (enumerative). *)

Definition closableb_spec mt :=
  is_closableb mt ==> true.
(* QuickChick will generate Motzkin trees,
  check whether the generated [mt] is closable, and, if it is, 
  proceed to check the conclusion. 
  If it is not, it will discard the generated inputs and try again. *)

Fixpoint size_mt (t : motzkin):= match t with
| v => 0
| l t => 1 + size_mt t
| a t1 t2 => 2 + size_mt t1 + size_mt t2
end.

Definition closableb_spec_collect_size mt :=
  collect (size_mt mt) (closableb_spec mt).
  
Definition isClosable_implies_closable_filtering mt :=
  isClosableb mt ==> is_closableb mt.
  
Definition closable_implies_isClosable_filtering mt :=
  is_closableb mt ==> isClosableb mt.

Definition default_closable := l v.

Lemma default_is_closable : is_closableb default_closable = true.
Proof.
auto.
Qed.
  
Definition filter_max := 100.

(*- BEGINgen_filter_closable *)
Fixpoint gen_filter_closable_aux nb n := 
match nb with 
| 0 => returnGen default_closable
| S p => do! val <- gen_motzkin n; 
         if is_closableb val then returnGen val
         else gen_filter_closable_aux p n
end.

Definition gen_filter_closable : nat -> G motzkin := gen_filter_closable_aux filter_max.
(*- ENDgen_filter_closable *)

(* Sample (gen_filter_closable 7). *)

(** ** Generator of closable Motzkin trees; [k] is the number of [l]. *)

(*- BEGINgen_closable_struct *)
Fixpoint gen_closable_struct_aux (k : nat) (n : nat) : G motzkin :=
match n with
| 0 => match k with
       0 => returnGen default_closable
       | _ =>  returnGen v
       end
| S p =>
  match k with
  0 => oneOf [
    (returnGen default_closable);
    (do! mt <- gen_closable_struct_aux (S k) p; returnGen (l mt));
    (do! mt0 <- gen_closable_struct_aux k p; do! mt1 <- gen_closable_struct_aux k p; 
       returnGen(a mt0 mt1)) ]
  | _ => oneOf [
    (returnGen v);
    (do! mt <- gen_closable_struct_aux (S k) p; returnGen (l mt));
    (do! mt0 <- gen_closable_struct_aux k p; do! mt1 <- gen_closable_struct_aux k p; 
       returnGen(a mt0 mt1)) ]
  end
end.

Definition gen_closable_struct : nat -> G motzkin := gen_closable_struct_aux 0.
(*- ENDgen_closable_struct *)

Program Fixpoint gen_rec_closable_aux (k : nat) (n : nat): 
G {mt : motzkin | k = 0 -> is_closable mt} :=
match n with
| 0 =>  match k with
       0 => returnGen (exist _ (l v) _) 
       |_ =>  returnGen (exist _ v _)
       end      
| S p =>  match k with
  0 => oneOf
   [ (returnGen (exist _ (l v) _));
     (do! p0 <- gen_rec_closable_aux (S k) p; 
         returnGen (exist _ (l (proj1_sig p0)) _));
     (do! p0 <- gen_rec_closable_aux k p; 
      do! p1 <- gen_rec_closable_aux k p; 
         returnGen (exist _ (a (proj1_sig p0) (proj1_sig p1)) _))]
 |_ => oneOf
    [(returnGen (exist _ v _ ));
     (do! p0 <- gen_rec_closable_aux (S k) p; 
             returnGen (exist _ (l p0) _ ));
     (do! p0 <- gen_rec_closable_aux k p; 
         do! p1 <- gen_rec_closable_aux k p; 
         returnGen (exist _ (a p0 p1) _))
         ]
  end
end.

Import closable.
Module Import facts_cl := equiv_family (closable).


Definition coerce_2_rec_cmot (p : {mt : motzkin | 0 = 0 -> is_closable mt}) : 
rec_P := (Build_rrec_P (proj1_sig p) 
             ((proj2_sig p) eq_refl)).

Definition gen_rec_closable n : G rec_P := 
do! p <- gen_rec_closable_aux 0 n;
returnGen (coerce_2_rec_cmot p).


(** ** [closable] generator *)

(*- BEGINgen_closable *)
Derive (Arbitrary, Show) for closable. 
(*- ENDgen_closable *)
(* produces GenSizedclosable *)

Definition gen_closable n : G closable := 
@arbitrarySized _ GenSizedclosable n.

(* Sample (gen_closable 2). *)

(** from one generator derive the other one *)


(* Should be omitted if coercion in the record [rec_closable] *)
Definition show_rec_P t :=
show (P_struct t).

Instance showrec_P : Show rec_P :=
{ show := show_rec_P}.

(* Sample (gen_rec_closable_from_closable 2).
*)


(* Use of the generator family functors *)

Module gen_closable1 : family_for_generators1 (closable).
  Import closable.
  Module Import facts := equiv_family (closable).
  Definition is_Pb := is_closableb.
  Definition is_P_dec := is_closable_dec.
  Definition gen_T := gen_motzkin.
  Definition default_P := l v.
  Definition default_is_P := eq_refl true.
End gen_closable1.


Module V1 := generators_family1 closable gen_closable1.

(*Check V1.gen_filter_P.*)


Module gen_closable2 : family_for_generators2 closable facts_cl.
Definition gen_rec_P := gen_rec_closable.
End gen_closable2.

Module V2 := generators_family2 closable facts_cl gen_closable2.
Check V2.gen_P.

(*- BEGINgen_rec_closable *)
Module gen_closable3 : family_for_generators3 (closable).
Definition gen_P := gen_closable.
End gen_closable3.

Module V3 := generators_family3 closable gen_closable3 facts_cl.
(*- ENDgen_rec_closable *)
	     
Check V3.gen_rec_P.

