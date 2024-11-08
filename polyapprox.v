Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import polynomial.

Section MultivariateFun.
  Context `{R : Type} `{R_setoid : Setoid R} `{R_semiRing : @comSemiRing R R_setoid}.
  Fixpoint mfun n :=
    match n with
    | 0 => R
    | (S n) => R -> mfun n
    end.


End MultivariateFun.
Section Norm.
Context (A B: Type).
Context (norm : A -> A -> B).
End Norm.
Section Approximation.

Context (base_type target_type error_type : Type).
Context (embed : base_type -> target_type).
Context (embedE : error_type -> target_type).
Context  `{setoidB : Setoid base_type} `{setoidT : Setoid target_type} `{setoidE : Setoid error_type}.  
Context `{semiRingB : comSemiRing base_type} `{semiRingT : comSemiRing target_type} `{semiRingE : comSemiRing error_type}.
Context `{RingT : comRing target_type} `{RingE : comRing error_type}.
Context `{FieldT : Field target_type} `{FieldE : Field error_type}.
Context `{orderE : TotalOrder target_type}.
Definition embed_recursive {n} (f : @mfun target_type n) (x : @tuple n base_type) : target_type.
Proof.
  induction n.
  apply f.
  destruct (destruct_tuple x) as [hd [tl P]].
  pose proof (f (embed hd)) as f0.
   apply (IHn f0 tl).
 Defined.

Class PolynomialModel (d : nat) := {
    p : @mpoly base_type d;
    f : @mfun target_type d;
    err : error_type;
    approx : forall x, (embed p.[x] - embed_recursive f x) <=  embedE err;
  }.
Class PolynomialModelOps  :=
  {
    (* pm_add {d : nat}: @PolynomialModel d -> @PolynomialModel d -> @PolynomialModel d; *)
    (* pm_add_spec {d :nat} p1 p2 : (@f _ (@pm_add d p1 p2)) = (@f _ p1); *)
    (* pm_mul {d : nat}: @PolynomialModel d -> @PolynomialModel d -> @PolynomialModel d; *)
    (* pm_mul_spec {d :nat} p1 p2 : (@f _ (@pm_mul d p1 p2)) = (@f _ p1); *)
    pm_compose {d e: nat}: PolynomialModel d -> @tuple d (@PolynomialModel e) -> @PolynomialModel e;
    pm_integrate {d : nat}: @PolynomialModel d -> @PolynomialModel d -> @PolynomialModel d;
    (* pm_integrate_spec {d :nat} p1 p2 : (@f _ (@pm_integrate d p1 p2)) = (@f _ p1) *)
  }.
End Approximation.

