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

(** * Coq type for lambda terms in de Bruijn form *)

(** "We define lambda terms in de Bruijn form [[...]] as the free algebra generated
    by the constructors <<l/1>>, and <<a/2>> and leaves labeled with natural numbers 
    wrapped with the constructor <<v/1>>." [[BT17, section 2]]

    Coq constructors have to be unique, so <<v/1>>, <<l/1>> and <<a/2>> are encoded by
    [var], [lam] and [app] in the following type [lmt] for labeled Motzkin trees,
    a tree-like representation of lambda terms in de Bruijn form. *)

(*- BEGINlmt *)
Inductive lmt : Set :=
| var : nat -> lmt
| lam : lmt -> lmt
| app : lmt -> lmt -> lmt.
(*- ENDlmt *)

(*- BEGINex1 *)
Definition ex1 := lam (app (lam (var 1)) (var 0)).
(*- ENDex1 *)
                      
Scheme Equality for lmt.
(*
lmt_beq is defined
lmt_eq_dec is defined
*)

(** *** Examples of lambda terms in de Bruijn form: *)

Definition lmt_ex1 := lam (app (var 0) (lam (var 1))).
Definition lmt_ex2 := lam (app (var 1) (lam (var 1))).

(** * _m_-open terms

  [(is_open m t)] holds iff [t] is a [m]-_open term_, i.e. a lambda term
  with at most [m] distinct free variables. This is a reformulation of 
  <<closedTerm>> in [[BT17]], misleadingly named since [(is_open m t)]
  also holds for terms [t] with free variables, when [m] > 0. *)

(*- BEGINis_open *)
Fixpoint is_open (m: nat) (t: lmt) : Prop :=
  match t with
  | var i  => i < m
  | lam t1 => is_open (S m) t1
  | app t1 t2 => is_open m t1 /\ is_open m t2
  end.
(*- ENDis_open *)

(** ** Examples *)

(** [lmt_ex1] is a 0-open term *)

Lemma lmt_ex1_0open : is_open 0 lmt_ex1.
Proof. simpl; lia. Defined.

(** [lmt_ex2] is a 1-open term *)

Lemma lmt_ex2_1open : is_open 1 lmt_ex2.
Proof. simpl; lia. Defined.

(** [lmt_ex2] is not a 0-open term *)

Lemma not_lmt_ex2_0open : not (is_open 0 lmt_ex2).
Proof. simpl; lia. Defined.

(** ** Record type for _m_-open terms: subtype of labeled Motzkin trees *)

(*- BEGINrec_open *)
Record rec_open (m:nat) : Set := Build_rec_open {
  open_struct :> lmt;
  open_prop : is_open m open_struct
}.
(*- ENDrec_open *)

(** *** Example (ctd): *)

Definition rec_open1 := Build_rec_open 0 lmt_ex1 lmt_ex1_0open.

(** ** Dependent type for _m_-open terms *)

(** [(open m)] is a dependent type for [m]-open terms. 
    [(t: open m)] corresponds to some [t'] such that [(is_open m t')] holds. *)
(*- BEGINopen *)
Inductive open : nat -> Set :=
| open_var : forall (m i:nat), i < m -> open m
| open_lam : forall (m:nat), open (S m) -> open m
| open_app : forall (m:nat), open m -> open m -> open m.
(*- ENDopen *)

(** * Equivalence between the record [rec_open] and the dependent type [open] *)

(** ** From [rec_open] to [open] *)

(** *** As a proof term *)

Lemma lmt2open_lemma : forall (t:lmt) (m:nat), is_open m t -> open m.
Proof.
induction t; simpl; intros.
+ exact (open_var m n H).
+ exact (open_lam m (IHt (S m) H)).
+ destruct H as [Hm1 Hm2].
  exact (open_app m (IHt1 m Hm1) (IHt2 m Hm2)).
Defined.

(** *** Example: *)

Eval compute in (lmt2open_lemma lmt_ex1 0 lmt_ex1_0open).

(** *** As a fixpoint *)

(*- BEGINlmt2open *)
Fixpoint lmt2open (t:lmt) : forall m:nat, is_open m t -> open m :=
  match t as u return (forall m0 : nat, is_open m0 u -> open m0) with
  | var n => fun (m0 : nat) (H : is_open m0 (var n)) => open_var m0 n H
  | lam u => fun (m0 : nat) (H : is_open m0 (lam u)) =>
      open_lam m0 (lmt2open u (S m0) H)
  | app u w =>
      fun (m0 : nat) (H : is_open m0 (app u w)) =>
        match H with
        | conj H0 H1 => open_app m0 (lmt2open u m0 H0) (lmt2open w m0 H1)
        end
end.
(*- ENDlmt2open *)

(*- BEGINrec_open2open *)
Definition rec_open2open (m : nat) (r : rec_open m) :=
  lmt2open (open_struct m r) m (open_prop m r).
(*- ENDrec_open2open *)


(** ** From [open] to [rec_open] *)

(*- BEGINopen2lmt *)
Fixpoint open2lmt (m:nat) (t : open m) : lmt :=
  match t with
  | open_var m i _ => var i
  | open_lam m u  => lam (open2lmt (S m) u)
  | open_app m t1 t2 => app (open2lmt m t1) (open2lmt m t2)
  end.
(*- ENDopen2lmt *)


(*- BEGINis_open_open2lmt *)
Fixpoint is_open_open2lmt m (t : open m) {struct t} : is_open m (open2lmt m t) :=
  match t as u in (open m0) return (is_open m0 (open2lmt m0 u)) with
  | open_var _ _ p => p
  | open_lam m1 u => is_open_open2lmt (S m1) u
  | open_app m2 u w => conj (is_open_open2lmt m2 u) (is_open_open2lmt m2 w)
  end.
(*- ENDis_open_open2lmt *)

(*Check is_open_open2lmt. *) (* forall (m : nat) (t : open m), is_open m (open2lmt m t) *)

(*- BEGINis_open_lemma *)
Lemma is_open_lemma : forall m t, is_open m (open2lmt m t).
(*- ENDis_open_lemma *)
Proof.
exact is_open_open2lmt.
Defined.

(*- BEGINopen2rec_open *)
Definition open2rec_open m t := Build_rec_open m (open2lmt m t) (is_open_lemma m t).
(*- ENDopen2rec_open *)

(*- BEGINrec_open2openK *)
Lemma rec_open2openK : forall m x, rec_open2open m (open2rec_open m x) = x.
(*- ENDrec_open2openK *)
Proof.
unfold open2rec_open, rec_open2open.
intros m x; simpl; induction x.
+ reflexivity.
+ simpl; rewrite IHx; reflexivity.
+ simpl; rewrite IHx1; rewrite IHx2; reflexivity.
Qed.

(*- BEGINopen2lmt_is_open *)
Lemma open2lmt_is_open : forall m t H, open2lmt m (lmt2open t m H) = t.
(*- ENDopen2lmt_is_open *)
Proof.
intros m t; revert m; induction t.
+ intros; simpl; reflexivity.
+ intros; simpl. rewrite IHt; reflexivity.
+ intros; destruct H as [H1 H2]; simpl.
  rewrite IHt1.
  rewrite IHt2.
  reflexivity.
Qed.


Lemma proof_irr_is_open : forall x y, forall p1 p2:is_open x y, p1=p2.
Proof.
  intros x y; revert x ; induction y; simpl.
  intros; unfold lt; apply le_unique.
  intros; apply IHy.
  intros x [Hp1 Hp2] [Hq1 Hq2].
  rewrite (IHy1 x Hp1 Hq1).
  rewrite (IHy2 x Hp2 Hq2).
  reflexivity.
Qed.

(*- BEGINopen2rec_openK *)
Lemma open2rec_openK : forall m r, open2rec_open m (rec_open2open m r) = r.
(*- ENDopen2rec_openK *)
Proof.
  unfold rec_open2open,open2rec_open.
  induction r.
  simpl.
  generalize (is_open_lemma m (lmt2open open_struct0 m open_prop0)); intros Hirr.
  revert Hirr.
  rewrite open2lmt_is_open.
  intros.
  rewrite (proof_irr_is_open _ _ Hirr open_prop0).
  reflexivity.
Qed.

(** ** m-openess is decidable. *)
Fixpoint is_openb (m: nat) (t: lmt) : bool :=
  match t with
    var i   => i <? m
  | lam u   => is_openb (S m) u
  | app u v => andb (is_openb m u) (is_openb m v)
  end.

Lemma is_open_dec1: forall t m, is_open m t -> is_openb m t = true.
Proof.
induction t; simpl; intros.
- apply Nat.ltb_lt. assumption.
- apply IHt. assumption.
- {
 apply Bool.andb_true_iff.
 split.
 - apply IHt1. apply H.
 - apply IHt2. apply H.
}
Qed.

Lemma is_open_dec2: forall t m, is_openb m t = true -> is_open m t.
Proof.
induction t; simpl; intros.
- apply Nat.ltb_lt. assumption.
- apply IHt. assumption.
- {
 apply Bool.andb_true_iff in H.
 split.
 - apply IHt1. apply H.
 - apply IHt2. apply H.
}
Qed.

Lemma is_open_dec: forall t m, is_open m t <-> is_openb m t = true.
Proof.
split. apply is_open_dec1. apply is_open_dec2.
Qed.


(* Using the interface defined in familyInterface.v *)

Module open_mod : param_family
  with Definition U := nat
  with Definition T := lmt
  with Definition is_P := is_open
  with Definition P := open

  with Definition T2P := lmt2open

  with Definition P2T := open2lmt
  with Definition is_P_lemma := is_open_lemma
  
  with Definition P2T_is_P := open2lmt_is_open.

  Definition U:= nat.
  Definition T := lmt.
  Definition is_P := is_open.
  Definition P := open.
  Definition T2P := lmt2open.
  Definition P2T := open2lmt.
  Definition is_P_lemma := is_open_lemma.
  Definition P2T_is_P :=  open2lmt_is_open.
  Definition proof_irr := proof_irr_is_open.
End open_mod.

Module OPEN := equiv_param_family (open_mod).

