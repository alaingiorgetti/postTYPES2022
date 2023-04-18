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

Require Import open qc_open.

Import OPEN.

Definition rec_open_beq m (r1 r2 : OPEN.rec_P m) :=
lmt_beq (OPEN.P_struct _ r1) (OPEN.P_struct _ r2).

Definition open_beq n (t1 t2 : open n) : bool :=
lmt_beq (open2lmt _ t1) (open2lmt _ t2).


(** Check by testing that [gen_closed_lmt_n_ 0] produces closed [lmt]. *)
QuickCheck (sized (fun n => 
  forAll (gen_is_open 0 n) (fun t => 
  is_openb 0 t ))).
(* +++ Passed 10000 tests (0 discards) *)


(** Check by testing that [gen_is_open] produces open terms. *)
QuickCheck (sized (fun n => sized (fun k =>
  forAll (gen_is_open k n) (fun t => 
  is_openb k t )))).
(* +++ Passed 10000 tests (0 discards) *)

(** Check by testing that [gen_is_open] produces truly open terms and closed terms. So there exist counterexamples. *)
QuickCheck (sized (fun n => sized (fun k =>
  forAll (gen_is_open k n) (fun t => 
  is_openb 0 t )))).
(* Finished, 4 targets (0 cached) in 00:00:01.
var 2
*** Failed after 4 tests and 0 shrinks. (0 discards) *)

(** Check by testing that [gen_rec_open] produces open terms. *)
QuickCheck (sized (fun n => sized (fun k =>
  forAll (gen_rec_open k n) (fun t => 
  is_openb k (P_struct _ t) )))).
(* +++ Passed 10000 tests (0 discards) *)

(** Check by testing that [gen_open] produces open terms when transformed to [lmt]. *)
QuickCheck (sized (fun n => sized (fun k =>
  forAll (gen_open k n) (fun t => 
  is_openb k (open2lmt k t) )))).
(* +++ Passed 10000 tests (0 discards) *)

(** Test of [is_open_open2lmt] *)
QuickCheck (sized (fun n => sized (fun k => 
forAll (gen_open k n) (fun c =>
is_openb k (open2lmt k c))))).

(** Test of [P2rec_Pk] *)
QuickCheck (sized (fun n => sized (fun m => 
forAll (gen_rec_open m n) 
(fun (x : OPEN.rec_P m) =>
rec_open_beq (OPEN.P2rec_P _ (OPEN.rec_P2P _  x)) x)))).

(** Test of [rec_P2Pk] *)
QuickCheck (sized (fun n => sized (fun m => 
forAll (gen_open m n) (fun x =>
open_beq (OPEN.rec_P2P _ (OPEN.P2rec_P _ x)) x)))).

