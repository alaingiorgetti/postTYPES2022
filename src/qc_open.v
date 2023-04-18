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


Require Import mathcomp.ssreflect.ssreflect.

Require Import Lia.

Require Import open.

Module DoNotation.
Notation "'do!' X <- A ; B" :=
  (bindGen A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200).
End DoNotation.

Import DoNotation.

(** * [lmt] generator *)

Derive (Arbitrary, Show) for lmt.

Definition gen_lmt n := 
@arbitrarySized _ GenSizedlmt n.

(*Sample (gen_lmt 3). *)


(* Out of scope of Relational_extraction for the moment *)
Fixpoint is_openb ( k : nat) (t: lmt)  : bool :=
match t with
| var n  => Nat.ltb n k
| lam t1 => is_openb (S k) t1
| app t1 t2 => andb (is_openb k t1)  (is_openb k t2)
end.

Lemma is_open_dec : forall k t, is_open k t <-> is_openb k t = true.
Proof.
  intros k t; revert k; induction t; simpl.
  split; apply Nat.ltb_lt.
  intros; apply IHt.
  intros; rewrite Bool.andb_true_iff.
  split; intros.
  split; solve [apply IHt1; tauto | apply IHt2; tauto].
  split; solve [apply IHt1; tauto | apply IHt2; tauto].
Qed.

Fixpoint gen_is_open (k : nat) (size : nat) : G lmt :=
match size with
| 0 => match k with
       0 => returnGen (lam (var 0)) 
       |_ => (do! x <- choose (0, k-1); returnGen (var x))
       end
| S size' => 
  match k with
  0 => oneOf_
   (returnGen (lam (var 0)))
   [ (do! p0 <- gen_is_open (S k) size'; 
             returnGen (lam p0));
     (do! p0 <- gen_is_open k size' ; 
         do! p1 <- gen_is_open k size'; 
         returnGen(app p0 p1))]
 |_ => oneOf_
   (do! p0 <- choose (0, k-1); returnGen (var p0))
    [(do! x <- choose (0, k-1); returnGen (var x));
     (do! p0 <- gen_is_open (S k) size'; 
             returnGen (lam p0));
     (do! p0 <- gen_is_open k size'; 
         do! p1 <- gen_is_open k size'; 
         returnGen(app p0 p1))]
  end
end.

Lemma case1 : is_open 0 (lam (var 0)).
Proof.
constructor.
Qed.


Import OPEN.
 
Program Fixpoint gen_rec_open (k : nat) (size : nat) : 
G (rec_P k) :=
match size with
| 0 => match k with
       0 => returnGen (Build_rec_P _ (lam (var 0)) case1)
       |_ => bindGen' (choose (0, k-1)) (fun x H =>
              returnGen (Build_rec_P _ (var x) _))
       end
| S size' => match k with
  0 => oneOf_
   (returnGen (Build_rec_P _ (lam (var 0)) case1))
   [ (do! p0 <- gen_rec_open (S k) size'; 
             returnGen 
             (Build_rec_P _ (lam (P_struct _ p0)) _));
     (do! p0 <- gen_rec_open k size' ; 
         do! p1 <- gen_rec_open k size'; 
         returnGen 
         (Build_rec_P _ (app (P_struct _ p0) (P_struct _ p1)) _))]
 |_ => oneOf_
   (bindGen' (choose (0, k-1)) (fun p0 H =>
   returnGen (Build_rec_P _ (var p0) _)))
   [(do! p0 <- gen_rec_open (S k) size'; 
             returnGen 
             (Build_rec_P _ (lam (P_struct _ p0)) _));
     (do! p0 <- gen_rec_open k size' ; 
         do! p1 <- gen_rec_open k size'; 
         returnGen 
         (Build_rec_P _ (app (P_struct _ p0) (P_struct _ p1)) _))]
  end
end.
Next Obligation.
apply semChoose in H ; auto.
simpl in H.
assert (le x (k-1)).
rewrite (Bool.reflect_iff (x <= (k-1)) (ssrnat.leq x (k - 1))).
assumption.
apply ssrnat.leP.
lia.
Defined.
Next Obligation.
destruct p0; auto.
Defined.
Next Obligation.
destruct p0 ; destruct p1; auto.
Defined.
Next Obligation.
apply semChoose in H ; auto.
simpl in H.
assert (le p0 (k-1)).
rewrite (Bool.reflect_iff (p0 <= (k-1)) (ssrnat.leq p0 (k - 1))).
assumption.
apply ssrnat.leP.
lia.
Defined.
Next Obligation.
destruct p0 ; auto.
Defined.
Next Obligation.
destruct p0 ; destruct p1; auto.
Defined.


Instance showopenrec_P  (k : nat) : Show (rec_P k) := 
{ show := fun t => show (P_struct _ t) }.

(*Sample   (gen_rec_open 1 3 ).*)


(** * Random generator for the [open] inductive dependent type. *)

Require Import String.
Open Scope string_scope.

Fixpoint show_open (n : nat) (t : open n) :=
  match t with
    | open_var m i _ =>  "Var" ++ show i ++ " _"
    | open_lam m t => "(Lam " ++ show_open t ++ ")" 
    | open_app m t u => "( App " ++ show_open t  ++ show_open  u ++ ")" 
  end.

Instance showOpen (n : nat) : Show (open n) := 
{ show := @show_open n}.

Program Fixpoint gen_open (k : nat) (size : nat) : G (open k) :=
match size with
| 0 => match k with
        0 => returnGen (open_lam 0 (open_var 1 0 _))
       |k => bindGen' (choose (0, k-1)) (fun i H =>
              returnGen ( open_var k i _))
       end
| S size' => match k with
  0 => oneOf_
    (returnGen (open_lam 0 (open_var 1 0 _)))
   [ (do! p0 <- gen_open 1 size'; 
      returnGen (open_lam 0 p0));
     (do! p0 <- gen_open 0 size' ; 
      do! p1 <- gen_open 0 size'; 
         returnGen (open_app 0 p0 p1))]
 |k => oneOf_
   (bindGen' (choose (0, k-1)) (fun i H =>
              returnGen (open_var k i _)))
    [(do! p0 <- gen_open (S k) size'; 
             returnGen (open_lam k p0 ));
     (do! p0 <- gen_open k size' ; 
      do! p1 <- gen_open k size'; 
         returnGen (open_app k p0 p1))]
  end
end.
Next Obligation.
apply semChoose in H;auto.
assert (le i (k0-1)).
rewrite (Bool.reflect_iff (i <= (k0-1)) (ssrnat.leq i (k0 - 1))).
assumption.
apply ssrnat.leP.
lia.
Defined.

Next Obligation.
apply semChoose in H;auto.
assert (le i (k0-1)).
rewrite (Bool.reflect_iff (i <= (k0-1)) (ssrnat.leq i (k0 - 1))).
assumption.
apply ssrnat.leP.
lia.
Defined.

(*Sample (gen_open 2 5).  *)

