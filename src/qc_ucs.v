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

Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.

Import DoNotation.

Require Import qc_closable.
Require Import ucs.


Fixpoint is_ucs_auxb m b  := 
match m with
| v =>  Bool.eqb b true
| l m => if b then false
         else is_ucs_auxb m true
| a m1 m2 => andb (is_ucs_auxb m1 b) (is_ucs_auxb m2 b)
end.

Definition is_ucsb m := is_ucs_auxb m false.


Lemma is_ucs_auxb_dec : forall t b, is_ucs_aux t b <-> is_ucs_auxb t b = true.
Proof.
induction t; simpl; intros; split.
+ intro H; rewrite H; auto.
+ case b ; intros; auto. 
+ case b ; intro H. contradiction. apply IHt ; auto.
+ case b ; intro H. inversion H. apply IHt ; auto.
+ intro H; destruct H. 
  replace (is_ucs_auxb t1 b) with true by (symmetry ; apply IHt1; auto).
  replace (is_ucs_auxb t2 b) with true by (symmetry ; apply IHt2; auto). 
  auto.
+ intro H. rewrite Bool.andb_true_iff in H. destruct H. split. apply IHt1; auto. apply IHt2; auto.
Qed.

Lemma is_ucs_dec : forall t, is_ucs t <-> is_ucsb t = true.
Proof.
unfold is_ucs, is_ucsb.
intro t ; exact (is_ucs_auxb_dec t false).
Qed.


(** gen_ucs_struct*)
Definition default_ucs := l v.

Lemma default_is_ucs : is_ucs default_ucs.
Proof.
apply is_ucs_dec ; auto.
Qed.
Hint Resolve default_is_ucs.

Fixpoint gen_ucs_struct_aux (b : bool) (n : nat) : G motzkin :=
match n with
| 0 => match b with
       false => returnGen default_ucs 
       |_ =>  returnGen v
       end
| S p => 
  match b with
  false => oneOf_  (returnGen default_ucs)
   [ (returnGen default_ucs);
     (do! mt <- gen_ucs_struct_aux true p; 
             returnGen (l mt));
     (do! mt0 <- gen_ucs_struct_aux b p; 
         do! mt1 <- gen_ucs_struct_aux b p; 
         returnGen(a mt0 mt1))]
 |true => oneOf_ (returnGen v)
    [(returnGen v);
     (do! mt0 <- gen_ucs_struct_aux b p; 
      do! mt1 <- gen_ucs_struct_aux b p; 
      returnGen(a mt0 mt1))]
  end
  end.
  
Definition gen_ucs_struct : nat -> G motzkin := gen_ucs_struct_aux false.


(** gen_rec_ucs *)
Program Fixpoint gen_rec_ucs_aux (b:bool) (n : nat): 
G {mt : motzkin | is_ucs_aux mt b } :=
match n with
| 0 => match b with
       false => returnGen (exist _ default_ucs _ ) 
       |_ =>  returnGen (exist _ v _ ) 
       end
| S p => 
  match b with
  false => oneOf_  (returnGen (exist _ default_ucs _))
   [ (returnGen (exist _ default_ucs _));
     (do! mt <- gen_rec_ucs_aux true p; 
             returnGen (exist _ (l (proj1_sig mt)) _));
     (do! mt0 <- gen_rec_ucs_aux b p; 
         do! mt1 <- gen_rec_ucs_aux b p; 
         returnGen (exist _ (a (proj1_sig mt0) (proj1_sig mt1)) _ ))]
 |true => oneOf_ (returnGen (exist _ v _ ))
    [(returnGen (exist _ v _ ));
     (do! mt0 <- gen_rec_ucs_aux b p; 
      do! mt1 <- gen_rec_ucs_aux b p; 
         returnGen (exist _ (a (proj1_sig mt0) (proj1_sig mt1)) _ ))]
  end
  end.
Next Obligation.
destruct b ; auto.
Qed.


Definition coerce_2_rec_ucs (p : {mt : motzkin | is_ucs_aux mt false}) : 
UCS.rec_P := 
UCS.Build_rrec_P (proj1_sig p) (proj2_sig p).


Definition gen_rec_ucs n : G UCS.rec_P := 
do! p <- gen_rec_ucs_aux false n;
returnGen (coerce_2_rec_ucs p).


(** ucs **)
Derive (Arbitrary, Show) for ca.
Derive (Arbitrary, Show) for ucs.

Definition gen_ca n : G ca := 
@arbitrarySized _ GenSizedca n.

Definition gen_ucs n : G ucs := 
@arbitrarySized _ GenSizeducs n.

(*Sample (gen_ucs 2).*)


Definition show_rec_ucs t :=
show (UCS.P_struct t).

Instance showrec_ucs  : Show UCS.rec_P := 
{ show := show_rec_ucs}.

(*Sample (gen_rec_ucs_from_ucs 2).*)

