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

Definition rec_closable_beq (r1 r2 : rec_closable) :=
motzkin_beq (closable_struct r1) (closable_struct r2).


(** * Generation of [rec_closable] *)
(* with the generator obtained through the functor 3 *)

(** * Generation of closable Motzkin trees by filtering *)
(* with the generator obtained through the functor 1 *)
QuickChick (sized (fun n =>
  forAll (V1.gen_filter_P n) is_closableb)).

QuickCheck (sized (fun n =>
  forAll (V2.gen_P n) (fun c =>
  closable_beq (rec_closable2closable (closable2rec_closable c)) c))).


(** * Generation of [rec_closable] *)
(* with the generator obtained through the functor 3 *)
QuickChick (sized (fun n =>
  forAll (V3.gen_rec_P n) 
     (fun r => let (s, _) := r in
          is_closableb s))).


(** * Generation of closable Motzkin trees by filtering *)
QuickChick (sized (fun n =>
  forAll (gen_motzkin n) closableb_spec)).
(* +++ Passed 10000 tests (16651 discards) *)

(* same with computation of size *)
QuickChick (sized (fun n =>
  forAll (gen_motzkin n) closableb_spec_collect_size)).
(*
8811 : (Discarded) 0
2932 : 1
980 : 2
970 : (Discarded) 2
663 : 3
638 : (Discarded) 3
546 : 4
415 : 5
415 : (Discarded) 4
361 : (Discarded) 5
311 : (Discarded) 6
298 : 10
290 : 11
286 : 6
283 : (Discarded) 7
282 : 7
270 : 12
258 : 9
251 : 8
242 : 13
241 : (Discarded) 11
238 : (Discarded) 14
237 : (Discarded) 8
234 : 14
234 : (Discarded) 12
230 : 15
228 : (Discarded) 13
228 : (Discarded) 10
221 : (Discarded) 16
220 : (Discarded) 15
213 : (Discarded) 17
198 : (Discarded) 9
196 : 16
194 : (Discarded) 18
188 : 17
183 : (Discarded) 19
164 : (Discarded) 20
157 : 18
157 : (Discarded) 23
151 : 19
149 : 20
145 : (Discarded) 22
140 : (Discarded) 21
135 : (Discarded) 24
127 : 21
114 : 22
113 : (Discarded) 27
112 : (Discarded) 25
106 : (Discarded) 26
94 : (Discarded) 29
93 : 23
84 : 24
76 : (Discarded) 28
75 : (Discarded) 30
74 : 25
73 : (Discarded) 31
65 : 26
65 : (Discarded) 32
61 : 27
57 : (Discarded) 34
53 : (Discarded) 36
50 : 31
49 : 28
45 : (Discarded) 33
44 : 30
43 : 29
42 : (Discarded) 37
39 : (Discarded) 35
35 : (Discarded) 39
34 : (Discarded) 38
29 : 32
28 : (Discarded) 40
26 : 33
23 : (Discarded) 43
23 : (Discarded) 42
20 : (Discarded) 41
19 : (Discarded) 45
17 : 36
17 : (Discarded) 46
16 : 34
16 : (Discarded) 47
15 : (Discarded) 44
13 : 37
13 : (Discarded) 49
12 : 35
12 : (Discarded) 50
11 : 39
11 : (Discarded) 48
10 : 41
10 : 40
10 : 38
10 : (Discarded) 53
9 : (Discarded) 52
8 : (Discarded) 58
7 : (Discarded) 54
6 : (Discarded) 56
6 : (Discarded) 51
5 : 43
5 : (Discarded) 55
4 : 44
3 : 47
3 : 45
3 : 42
3 : (Discarded) 63
2 : 48
2 : (Discarded) 68
2 : (Discarded) 59
1 : 63
1 : 52
1 : 50
1 : 46
1 : (Discarded) 79
1 : (Discarded) 75
1 : (Discarded) 70
1 : (Discarded) 62
1 : (Discarded) 61
1 : (Discarded) 57
+++ Passed 10000 tests (16445 discards)
*)

(** Checking by filtering the equivalence between [isClosable] and [closable] *)

QuickChick (sized (fun n =>
  forAll (gen_motzkin n)
  isClosable_implies_closable_filtering)).
(* +++ Passed 10000 tests (16200 discards) *)
  
QuickChick (sized (fun n =>
  forAll (gen_motzkin n)
  closable_implies_isClosable_filtering)).
(* +++ Passed 10000 tests (16287 discards) *)

(** Checking the equivalence between [isClosable] and [closable] 
 by using the generator of closable Motzkin trees by filtering *)

QuickCheck (sized (fun n => 
  forAll (gen_filter_closable n) isClosableb)).

(** Checking the equivalence between [isClosable] and [closable] 
 by using the dedicated generator of closable Motzkin trees *)

(*- BEGINgen_closable_struct_test *)
QuickCheck (sized (fun n => forAll (gen_closable_struct n) is_closableb)).
(*  +++ Passed 10000 tests (0 discards) *)
(*- ENDgen_closable_struct_test *)

QuickCheck (sized (fun n => 
  forAll (gen_closable_struct n) isClosableb)).
(*  +++ Passed 10000 tests (0 discards) *)


QuickCheck (sized (fun n =>
  forAll (gen_closable n) (fun t =>
  is_closableb (closable2motzkin t) ))).
(*  +++ Passed 10000 tests (0 discards) *)

(** * Tests for the roundtrip lemmas for closable Motzkin trees *)

(* preliminary: checking the generator of closable Motzkin trees with proofs *)
QuickCheck (sized (fun n => 
  forAll (gen_rec_closable_aux 0 n) 
  (fun mt_p => is_closableb (proj1_sig mt_p)))).
(*  +++ Passed 10000 tests (0 discards) *)

(** ** Tests for [closable2rec_closable_K_aux] *)
QuickCheck (sized (fun n => 
  forAll (gen_rec_closable_aux 0 n) 
  (fun p => 
     let m:= proj1_sig p in
     let Hclo := (proj2_sig p) eq_refl in 
     motzkin_beq (closable2motzkin (motzkin2closable m Hclo)) m))).
(*  +++ Passed 10000 tests (0 discards) *)


(** ** Tests for [closable2rec_closableK] *)
QuickCheck (sized (fun n =>
  forAll (gen_closable n) (fun c =>
  closable_beq (rec_closable2closable (closable2rec_closable c)) c))).
(*  +++ Passed 10000 tests (0 discards) *)

(*
(** ** Tests for [rec_closable2closableK] *)
 QuickCheck (sized (fun n =>
  forAll (gen_rec_closable n) (fun x =>
  rec_closable_beq (closable2rec_closable (rec_closable2closable x)) x))).
*)

