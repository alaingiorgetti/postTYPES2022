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

From QuickChick Require Import QuickChick.

Require Import closable qc_closable.
Require Import ucs qc_ucs.

Scheme Equality for motzkin.
(*
motzkin_beq is defined
motzkin_eq_dec is defined
*)


Scheme Equality for ca.
Scheme Equality for ucs.


Definition rec_ucs_beq (r1 r2 : UCS.rec_P) :=
motzkin_beq (UCS.P_struct r1) (UCS.P_struct r2).

(** * Uniquely closable Mtozkin trees *)

(** ** Tests of the generator [gen_ucs_struct] *)

QuickCheck (sized (fun n => forAll (gen_ucs_struct n) is_ucsb)).
(*  +++ Passed 10000 tests (0 discards) *)

QuickCheck (sized (fun n => forAll (gen_rec_ucs n) (fun m =>
is_ucsb (ucs2motzkin (UCS.rec_P2P m))))).


(** ** Test of [is_ucs_ucs2motzkin] *)

QuickCheck (sized (fun n => forAll (gen_ucs n) (fun c =>
is_ucsb (ucs2motzkin c)))).

(** ** Test of the roundtrip lemmas for uniquely closable Motzkin trees *)

(** *** Test of [ucs2rec_ucsK] *)
QuickCheck (sized (fun n => forAll (gen_rec_ucs n) (fun (x : UCS.rec_P) =>
rec_ucs_beq (UCS.P2rec_P (UCS.rec_P2P x)) x))).

(** *** Test of [rec_P2PK] = [rec_ucs2ucsK] *)
QuickCheck (sized (fun n => forAll (gen_ucs n) (fun x =>
ucs_beq (UCS.rec_P2P (UCS.P2rec_P x)) x))).

