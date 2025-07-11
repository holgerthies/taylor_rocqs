(*
Interval version of the ODE solver.
Uses coq-interval for operations on floating point intervals.
 *)
From Coq Require Import QArith.
Require Import Qreals.
Require Import combinatorics.
Require Import algebra coqrationals.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
From Coq Require Import Reals Psatz.
From Interval Require Import Tactic Plot.
Require Import Interval.Interval.Float.        
Require Import Interval.Float.Specific_ops.    
Require Import Interval.Float.Specific_bigint. 
Require Import polynomial archimedean.
Require Import tuple.
From Coq Require Import List.
Require Import odebounds.
Require Import realanalytic.
Require Import abstractpowerseries.
Require Import Interval.Real.Xreal.
Require Import Coq.Reals.Rdefinitions.

Require Import Coq.Reals.Raxioms.
Require Import String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import pivp.
Module SFBI2 := SpecificFloat BigIntRadix2.    
Module FI   := FloatInterval SFBI2.         
Definition I := FI.type.
Definition F := SFBI2.type.
Definition print_interval := FI.output true.

Definition Q2Fa (q : Q) : F := (FI.F.div_UP (FI.F.PtoP 30) (SFBI2.fromZ (Qnum q)) (SFBI2.fromZ (Z.pos (Qden q)))).
Coercion Q2Fa : Q >-> F.
Definition Z2I (z : Z) := FI.bnd (SFBI2.fromZ z) (SFBI2.fromZ z).
Definition singleton (f : F) := (FI.bnd f f).
Module Type PRECISION_POS.
  Parameter precision : positive.
End PRECISION_POS.

Module FloatInterval (p : PRECISION_POS).
Definition prec := (FI.F.PtoP p.precision).



Definition Q2I (q : Q) := (FI.div prec (Z2I (Qnum q)) (Z2I (Z.pos (Qden q)))).

Lemma Z2I_spec z : Interval.contains (FI.convert (Z2I z)) (Xreal (IZR z)).
Proof.
  unfold Interval.contains;simpl;rewrite SFBI2.fromZ_correct';lra.
Qed.

Definition Q2F (q : Q) := (FI.F.div_UP prec (SFBI2.fromZ (Qnum q)) (SFBI2.fromZ (Z.pos (Qden q)))).


Lemma Q2I_spec q : Interval.contains (FI.convert (Q2I q)) (Xreal (Q2R q)).
Proof.
  enough ((Xreal (Q2R q)) = ((Xreal (IZR (Qnum q))) / (Xreal (IZR (Z.pos (Qden q)))))%XR) as ->.
  apply FI.div_correct;apply Z2I_spec.
  unfold Q2R.
  simpl.
  unfold Xdiv'.
  rewrite is_zero_false;auto.
Qed.

#[global] Instance I_setoid: Setoid I.
Proof.
  exists (fun x y => x = y).
  split;auto.
  intros a b c -> eq';auto.
Defined.

#[global] Instance F_setoid: Setoid F.
Proof.
  exists (fun x y => x = y).
  split;auto.
  intros a b c -> eq';auto.
Defined.


#[global] Instance I_rawRing: (@RawRing I _).
Proof.
   constructor.
   apply (Z2I 0).
   apply (Z2I 1).
   intros x y.
   apply (FI.add prec x y).
   intros x y.
   apply (FI.mul prec x y).
Defined.

#[global] Instance F_rawRing: (@RawRing F _).
Proof.
   constructor.
   apply  (SFBI2.fromZ 0).
   apply  (SFBI2.fromZ 1).
   intros x y.
   apply (FI.F.add_DN prec x y).
   intros x y.
   apply (FI.F.mul_DN prec x y).
Defined.

#[global] Instance F_rawRingWithOpp: (@RawRingWithOpp F _ _).
Proof.
  constructor.
  apply (SFBI2.neg).
Defined.

#[global] Instance F_rawFieldOps: (@RawFieldOps F _ _ _).
Proof.
  constructor.
  apply Q2F.
  apply (SFBI2.abs).
  apply (SFBI2.max).
  apply (SFBI2.div_DN prec 1 ).
  (* unused for now *)
  apply (fun x => 0).
Defined.

#[global] Instance I_rawRingWithOpp: (@RawRingWithOpp I _ _).
Proof.
  constructor.
  apply FI.neg.
Defined.

#[global] Instance I_rawFieldOps: (@RawFieldOps FI.type _ _ _).
Proof.
  constructor.
  apply Q2I.
  apply FI.abs.
  intros x y.
  apply (singleton (max (FI.upper x) (FI.upper y))).
  apply (FI.inv prec).
  (* unused for now *)
  apply (fun x => 0).
Defined.

Definition Q2Ipoly {d} (p : @mpoly Q d) : @mpoly I d.
Proof.
  induction d.
  apply (Q2I p).
  induction p.
  apply nil.
  apply (cons (IHd a) IHp).
Defined.

Definition Q2Ipolyt {m d} (p :tuple m (@mpoly Q d)) : (tuple m (@mpoly I d)) := (tuple_map Q2Ipoly p).

Lemma Xreal_add a b :  Xreal (a + b) = (Xreal a + Xreal b)%XR.
Proof. reflexivity. Qed.

Lemma Xreal_mul a b :  Xreal (a * b) = (Xreal a * Xreal b)%XR.
Proof. reflexivity. Qed.

Lemma Q2Ipoly_spec1 (p : @mpoly Q 1) xi x : Interval.contains (FI.convert xi) (Xreal (Q2R x)) -> Interval.contains (FI.convert (eval_poly (Q2Ipoly p) (Q2I x))) (Xreal (Q2R (eval_poly p x))).
Proof.
  intros.
  induction p.
  simpl;lra.
  simpl eval_poly.
  rewrite Q2R_plus.
  rewrite Xreal_add.
  apply FI.add_correct; [apply Q2I_spec|].
  rewrite Q2R_mult.
  rewrite Xreal_mul.
  apply FI.mul_correct; [apply Q2I_spec|].
  apply IHp.
Qed.

Definition Q2err (q : Q) := (FI.add prec (FI.bnd FI.F.zero (FI.upper (Q2I q))) (FI.bnd (FI.lower (Q2I (-q))) FI.F.zero)).

Definition F2err (f : F) := (FI.add prec (FI.bnd FI.F.zero f) (FI.bnd (FI.F.sub_DN prec 0 f) FI.F.zero)).

Definition add_errorq (err : Q) (i : I) : I := FI.add prec i (Q2err err).
Definition add_error (err : F) (i : I) : I := FI.add prec i (F2err err).
Definition add_errort {d} (err : F) (i : I^d) : I^d := tuple_map (add_error err) i.

Definition le_zero (t : I) := FI.F'.le (FI.lower t) SFBI2.zero.
End FloatInterval.

