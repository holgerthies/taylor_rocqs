Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import polynomial.

Section Symbolic.
Context (A : Type).
Inductive Symbolic 
  :=
  | Szero : Symbolic
  | Sone :  Symbolic
  | Sconst : A -> Symbolic
  | Sadd : Symbolic -> Symbolic -> Symbolic
  | Smul : Symbolic -> Symbolic -> Symbolic
  .
  Inductive symbolic_equiv : Symbolic -> Symbolic -> Prop :=
    | Srefl : forall x, symbolic_equiv x x
    | Ssym : forall x y, symbolic_equiv x y -> symbolic_equiv y x
    | Strans : forall x y z, symbolic_equiv x y -> symbolic_equiv y z -> symbolic_equiv x z
    | SaddC : forall x y, symbolic_equiv (Sadd x y) (Sadd y x) 
    | SaddA : forall x y z, symbolic_equiv (Sadd (Sadd x y) z) (Sadd x (Sadd y z))  
    | SmulC : forall x y, symbolic_equiv (Smul x y) (Smul y x) 
    | SmulA : forall x y z, symbolic_equiv (Smul (Smul x y) z) (Smul x (Smul y z))  
    | SmulD : forall x y z, symbolic_equiv (Smul x (Sadd y z)) (Sadd (Smul x y) (Smul x z)) 
    | Sadd0 : forall x, symbolic_equiv (Sadd x Szero) x
    | Smul0 : forall x, symbolic_equiv (Smul x Szero) Szero 
    | Smul1 : forall x, symbolic_equiv (Smul x Sone) x
    | SaddProper : forall x1 y1 x2 y2, symbolic_equiv x1 y1 -> symbolic_equiv x2 y2 -> symbolic_equiv (Sadd x1 x2) (Sadd y1 y2)
    | SmulProper : forall x1 y1 x2 y2, symbolic_equiv x1 y1 -> symbolic_equiv x2 y2 -> symbolic_equiv (Smul x1 x2) (Smul y1 y2)
  .

  #[global] Instance Proper_symbolic_add :
  Proper (symbolic_equiv ==> symbolic_equiv ==> symbolic_equiv) Sadd.
  Proof.
    intros x1 x2 H1 y1 y2 H2.
    apply SaddProper;auto.
  Defined.

  #[global] Instance Proper_symbolic_mul :
  Proper (symbolic_equiv ==> symbolic_equiv ==> symbolic_equiv) Smul.
  Proof.
    intros x1 x2 H1 y1 y2 H2.
    apply SmulProper;auto.
  Defined.

  #[global] Instance S_setoid : (Setoid Symbolic).
  Proof.
    exists symbolic_equiv.
    constructor.
    intros x;apply Srefl.
    intros x y;apply Ssym.
    intros x y z;apply Strans.
  Defined.
  #[global] Instance S_semiRing : comSemiRing.
  Proof.
    exists Szero Sone Sadd Smul; intros.
    apply Proper_symbolic_add.
    apply Proper_symbolic_mul.
    apply Srefl.
    apply Srefl.
    apply SaddA.
    apply SaddC.
    apply Sadd0.
    apply SmulA.
    apply SmulC.
    apply Smul0.
    apply Smul1.
    apply SmulD.
 Defined.
End Symbolic.

