Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Rfunctions.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Reals.
Require Import algebra polynomial.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
From mathcomp Require Import tuple.
Section Z_pol.
Instance Z_setoid : Setoid Z.
Proof.
  exists (eq).
  apply Eqsth.
Defined.
Instance Z_comRing : @comSemiRing Z Z_setoid.
Proof.

  exists 0%Z 1%Z (fun x y => (x + y)%Z) (fun x y => (x * y)%Z); unfold equiv,Z_setoid;try (intros; ring);intros a b H c d H0;lia.
Defined.
Instance Z_mpoly0Setoid : Setoid (@mpoly Z 0).
Proof. apply mpoly_setoid. Defined.

Instance Z_mpoly1Setoid : Setoid (@mpoly Z 1).
Proof. apply mpoly_setoid. Defined.

Instance Z_mpoly2Setoid : Setoid (@mpoly Z 2).
Proof. apply mpoly_setoid. Defined.

Instance Z_mpoly0ComRing : @comSemiRing (@mpoly Z 0) _.
Proof.
  apply Z_comRing.
Defined.
Instance Z_mpoly1ComRing : @comSemiRing (@mpoly Z 1) _.
Proof.
  apply mpoly_comSemiRing.
Defined.

Instance Z_mpoly2ComRing : @comSemiRing (@mpoly Z 2) _.
Proof.
  apply mpoly_comSemiRing.
Defined.

Definition p1 : (@mpoly Z 1).
Proof.
  apply [1%Z; 0%Z; 5%Z].
Defined.
Definition p2 : (@mpoly Z 2).
Proof.
  apply [[1%Z]; [1%Z; 2%Z; 0%Z]].
Defined.

Definition x : (@mpoly Z 2) := [[0%Z]; [1%Z]]. 
Definition y : (@mpoly Z 2) := [[0%Z; 1%Z]; [0%Z]]. 
Check @derive_monomial.
Definition p3 := (x*y+y+x*x*x*x+y*y*x*x).



Instance  poly1_dr : (@differentialRing (@mpoly Z 1) _ _).
Proof.
  apply differentialRingPoly.
Defined.
Instance  poly2_dr : (@differentialRing (@mpoly Z 2) _ Z_mpoly2ComRing).
Proof.
  apply differentialRingPoly.
Defined.



End Z_poly.
