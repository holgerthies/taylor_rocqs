Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Section AlgebraicStructures.
  Context {A : Type} `{Setoid A}.
  Class comSemiRing   := {
      zero : A;
      one : A;
      add : A -> A -> A;
      mul : A -> A -> A;

      add_proper :> Proper (equiv ==> equiv ==> equiv) add;
      mul_proper :> Proper (equiv ==> equiv ==> equiv) mul;
      zero_proper :> equiv zero zero;
      one_proper :> equiv one one;

      addA : forall a b c, add (add a b) c == add a (add b c);
      addC : forall a b, add a b == add b a;
      add0 : forall a, add a zero == a; 
      mulA: forall a b c, mul (mul a b) c == mul a (mul b c);
      mulC : forall a b, mul a b == mul b a;
      mul0 : forall a, mul a zero == zero; 
      mul1 : forall a, mul a one == a; 
      distrL : forall a b c, mul a (add b c) == add (mul a b) (mul a c)
    }.

  Class comRing {R_semiRing : comSemiRing} := {
      opp : A -> A;
      opp_proper :> Proper (equiv ==> equiv) opp;
      addI : forall a, add a (opp a) == zero;
  }.

  Class Field `(R_Ring : comRing) := {
      inv : forall {x}, (not (x == zero)) -> A;
      mulI : forall x (p : (not (x == zero))), mul (inv p) x == one
    }.

  Class differentialRing {R_semiRing : comSemiRing} :=
    {
    derivation : A -> A;
    derivation_plus : forall r1 r2, derivation (add r1 r2) == add (derivation r1) (derivation r2);
    derivation_mult : forall r1 r2, derivation (mul r1 r2) == add (mul r2 (derivation r1)) (mul r1  (derivation r2))
    }.
  Class TotalOrder := {
      le : A -> A -> Prop;
      le_refl : forall x, le x x;
      le_anti_sym : forall x y, le x y -> le y x -> x == y;
      le_trans : forall x y z, le x y -> le y z -> le x z;
      le_total : forall x y, le x y \/ le y x
    }.
    
  Definition minus {R_semiRing : comSemiRing}  {R_comRing : comRing} (x y : A)  := add x (opp y).
End AlgebraicStructures. 

Infix "+" := add.
Infix "*" := mul.
Notation "- x" := (opp  x). 
Infix "-" := minus.
Infix "<=" := le.
Notation "0" := zero.
Notation "1" := one.
Notation "p ^'" := (derivation p) (at level 2, left associativity).

Section DifferentialAlgebra.

  Context {K V : Type} {K_setoid : Setoid K} {V_setoid : Setoid V} {R_comRing : @comSemiRing V V_setoid} {K_comSemiRing : @comSemiRing K K_setoid} {K_comRing : @comRing K K_setoid K_comSemiRing} {K_field : @Field K _ K_comSemiRing K_comRing }.

  Class differentialAlgebra `(R_differentialRing : differentialRing) := {
      smult : K -> V -> V;
      smult1 : forall v, smult one v == v;
      smult_proper :> Proper (equiv ==> equiv ==> equiv) smult;
      smult_plus_distr : forall a u v, smult a (u+v) == smult a u + smult a v;
      splus_mult_dist : forall a b v, smult (a+b) v == smult a v + smult b v;
      smult_mult_compat : forall a b v, smult a (smult b v) == smult (a*b) v
    }. 

End DifferentialAlgebra.

Infix "[*]" := smult (at level 2, left associativity).

Section RingTheory.
  Context {A : Type} `{A_comSemiRing : comSemiRing  }.

  Lemma ComSemiRingTheory   : semi_ring_theory 0 1 add mul equiv.
  Proof.
    constructor.
    intro; rewrite addC; apply add0.
    exact addC.
    symmetry; apply addA.
    intro; rewrite mulC; apply mul1.
    intros;rewrite mulC;apply mul0.
    exact mulC.
    symmetry ; apply mulA.
    intros m n p.
    rewrite mulC.
    rewrite (mulC n p).
    rewrite (mulC m p).
    apply distrL.
  Qed.

  Add Ring ARing: ComSemiRingTheory.
  Lemma ComRingTheory {A_comRing : comRing} : ring_theory 0 1 add mul minus opp  equiv.
  Proof.
    constructor; intros;unfold minus; try ring;auto.
    apply addI.
  Qed.
  
  Lemma ring_eq_plus_eq : forall x y x' y', x == x' -> y == y' -> x + y == x' + y'.
  Proof.
    intros x y _ _ <- <-;ring.
  Qed.
  Lemma ring_eq_mult_eq : forall x y x' y', x == x' -> y == y' -> x * y == x' * y'. 
  Proof. intros x y _ _ <- <-;ring. Qed.

End RingTheory.

Section DifferentialAlgebraTheory.

  Context {K V : Type} {V_setoid : Setoid V} {K_setoid : Setoid K } {R_comSemiRing : @comSemiRing V V_setoid} {K_comSemiRing : @comSemiRing K K_setoid} {K_comRing : @comRing K K_setoid K_comSemiRing} {K_field : @Field K K_setoid K_comSemiRing K_comRing } {DR : @differentialRing V V_setoid R_comSemiRing} {DA : @differentialAlgebra K V _ _ _ _ _ _ _ DR}.

  Add Ring RRing: (@ComSemiRingTheory _ V_setoid R_comSemiRing).
  Add Ring RRing: (@ComRingTheory _ K_setoid K_comSemiRing K_comRing).

  Lemma smult_zero  a : a [*] 0 == 0.
  Proof.
    enough (0 [*] 0 == 0).
    rewrite <-H.
    rewrite smult_mult_compat.
    setoid_replace (a*0) with 0 by ring;auto.
    reflexivity.
    rewrite <- (smult1 0) at 2.
    setoid_replace 1 with (0+1) by ring.
    rewrite splus_mult_dist.
    rewrite smult1.
    rewrite add0;reflexivity.
  Qed.

End DifferentialAlgebraTheory.
