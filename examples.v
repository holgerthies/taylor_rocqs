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
Require Import polyapprox.
Section Z_poly.
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

Compute (p3^'^').

End Z_poly.

Require Import QArith.
Require Import Ring.
Section Q_poly.

Open Scope Q_scope.
Instance Q_setoid : Setoid Q.
Proof.
  exists Qeq.
  apply Q_Setoid.
Defined.

Instance Q_semiRing : @comSemiRing Q Q_setoid.
Proof.
  exists 0%Q 1%Q (fun x y => (x + y)%Q) (fun x y => (x * y)%Q);try (intros; unfold SetoidClass.equiv, Q_setoid;ring).
  apply Qplus_comp.
  apply Qmult_comp.
Defined.

Instance Q_Ring :@comRing Q _ Q_semiRing.
Proof.
  exists (fun q => (- q)).
  apply Qopp_comp.
  intros.
  simpl;ring.
Defined.

Instance Q_field :@Field Q _ _ Q_Ring.
Proof.
   exists (fun q p => (1 / q)).
   intros.
   simpl;field.
   contradict p;auto.
Defined.

Instance Q_mpoly0ComRing : @comSemiRing (@mpoly Q 0) _.
Proof.
  apply Q_semiRing.
Defined.

Instance Q_mpoly1Setoid : Setoid (@mpoly Q 1).
Proof. apply mpoly_setoid. Defined.

Instance Q_mpoly2Setoid : Setoid (@mpoly Q 2).
Proof. apply mpoly_setoid. Defined.

Instance Q_mpoly1ComRing : @comSemiRing (@mpoly Q 1)_.
Proof.
  apply mpoly_comSemiRing.
Defined.
Instance Q_mpoly2ComRing : @comSemiRing (@mpoly Q 2) _.
Proof.
  apply mpoly_comSemiRing.
Defined.

Instance  qpoly1_dr : (@differentialRing (@mpoly Q 1) _ Q_mpoly1ComRing).
Proof.
  apply differentialRingPoly.
Defined.

Instance  qpoly2_dr : (@differentialRing (@mpoly Q 2) _ Q_mpoly2ComRing).
Proof.
  apply differentialRingPoly.
Defined.

Add Ring RRing : (@ComSemiRingTheory _ _ Q_mpoly0ComRing).

Instance  qpoly0_dr : (@differentialRing (mpoly 0) _ Q_mpoly0ComRing).
Proof.
  exists (fun x => 0);intros;simpl;ring.
Defined.

Instance qp_da : (@differentialAlgebra Q (@mpoly Q 2) _ _ _  _ _ _ _ qpoly2_dr).
Proof.
  apply (@PolyDifferentialAlgebra Q (@mpoly Q 1) _ _ Q_mpoly1ComRing Q_semiRing _ qpoly1_dr).
  apply (@PolyDifferentialAlgebra Q (@mpoly Q 0) _ _ Q_mpoly0ComRing Q_semiRing  _ qpoly0_dr).
  exists (fun q x => (q * x));intros;simpl;try ring.
  apply Qmult_comp.
Defined.

Definition q2 : (@mpoly Q 2).
Proof.
  apply [[1#2]; [1#2; 2#3]].
Defined.

Definition q11 : (@mpoly Q 1).
Proof.
  apply [0%Q; 0%Q;1%Q].
Defined.
Definition q12 : (@mpoly Q 1).
Proof.
  apply [0%Q; 0%Q;0%Q;1%Q].
Defined.

Instance R_setoid : Setoid R.
Proof. 
  exists eq.
  apply Eqsth.
Defined.
Require Import ClassicalConstructiveReals.
Require Import Coq.setoid_ring.Ring_theory.
Require Import Coq.setoid_ring.Ring.
Require Import Qreals.
Open Scope R_scope.
Instance R_comSemiRing : @comSemiRing R _.
Proof.
  exists 0%R 1%R Rplus Rmult; unfold SetoidClass.equiv;simpl;try (intros a b H0 c d H1;rewrite H0, H1);intros;try ring.
Defined.

Instance R_comRing : @comRing R _ _.
Proof.
  exists Ropp; unfold SetoidClass.equiv;simpl;try (intros a b H0 ;rewrite H0);intros;try ring.
Defined.

Instance R_totalOrder : @TotalOrder R _.
Proof.
  exists Rle;intros;unfold SetoidClass.equiv;simpl;try lra.
Defined.

Definition PM_Q2 : PolynomialModel Q R Q Q2R Q2R 2.
Proof.
   exists [[1%Q]] (fun x y => 0.5%R) 0.5%Q.
   intros.
   simpl.
   destruct (destruct_tuple x0) as [x [tl P]].
   destruct (destruct_tuple tl) as [y [tl' P']].
   unfold eval_mpoly.
   simpl.
   rewrite Q2R_plus.
   rewrite Q2R_mult.
   lra.
Defined.

Definition q1tuple : @tuple 2 (@mpoly Q 1).
Proof.
  exists [q11;q12].
  simpl;lia.
Defined.
Compute (mpoly_composition q2 q1tuple).

End Q_poly.
