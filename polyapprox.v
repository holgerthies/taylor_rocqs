Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import polynomial.

Definition tuple_map {n A B} (f : A -> B) (x : @tuple n A) : @tuple n B.
Proof.
  induction n.
  apply nil_tuple.
  destruct (destruct_tuple x) as [hd [tl P]].
  apply (tuple_cons (f hd) (IHn tl)).
 Defined.
Section MultivariateFun.
  Context `{R : Type} `{R_setoid : Setoid R} `{R_semiRing : @comSemiRing R R_setoid}.
  Definition mfun n := (@tuple n R) -> R.

End MultivariateFun.
Section Norm.
Context `{A: Type} `{B : Type}.
Context `{semiRingA : comSemiRing A}.
Context `{FieldB : Field B}.
Context `{orderE : TotalOrder B}.
Class metric (metric_distance : A -> A -> B )  := {
    metric_proper : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) metric_distance;
    metric_zero : forall x y, metric_distance x y == 0 <-> x == y;
    metric_sym : forall x y, metric_distance x y == metric_distance y x;
    metric_triangle : forall x y z, metric_distance x y <= metric_distance x z + metric_distance z y
  }.
End Norm.

Class ApproximationStructure (base_type : Type) (target_type : Type) (error_type : Type) `{semiRingB : comSemiRing base_type} `{fieldT : Field target_type} `{semiRingE : comSemiRing error_type}  `{orderE : TotalOrder target_type}  := {
    embed : base_type -> target_type;
    embed_proper : Proper (SetoidClass.equiv ==> SetoidClass.equiv) embed;
    embedE : error_type -> target_type;
    embedE_proper : Proper (SetoidClass.equiv ==> SetoidClass.equiv) embedE;
    dist : target_type -> target_type -> target_type;
    metricd : (metric dist)
  }.
Section Approximation.
  Context {base_type : Type} {target_type : Type} {error_type : Type} `{semiRingB : comSemiRing base_type} `{fieldT : Field target_type} `{semiRingE : comSemiRing error_type}   `{orderE : TotalOrder target_type}.
  Class PolynomialModel (approx : ApproximationStructure base_type target_type error_type) (d : nat) := {
    pm_p : @mpoly base_type d;
    pm_f : @mfun target_type d;
    pm_err : error_type;
    pm_spec : forall x, (approx.(dist) (approx.(embed) pm_p.[x]) (pm_f (tuple_map embed x))) <=  embedE pm_err;
  }.
  Definition eval_pm {a : ApproximationStructure base_type target_type error_type} {d} (p : PolynomialModel a d) (t : @tuple d base_type) : base_type * error_type.
  Proof.
    destruct p.
    apply (pm_p0.[t], pm_err0).
  Defined.
Class PolynomialModelAddition {a : ApproximationStructure base_type target_type error_type} {d} (pm_add : PolynomialModel a d -> PolynomialModel a d -> PolynomialModel a d)  :=
  {
    pm_add_spec p1 p2 x : ((pm_add p1 p2).(pm_f) x) == p1.(pm_f) x + p2.(pm_f) x;
  }.
(* Context (base_type target_type error_type : Type). *)
(* Context (embed : base_type -> target_type). *)
(* Context  *)
(* Context (). *)
(* Context (d : nat). *)
(* Context  `{setoidB : Setoid base_type} `{setoidT : Setoid target_type} `{setoidE : Setoid error_type}.   *)
(* Context `{semiRingB : comSemiRing base_type} `{semiRingT : comSemiRing target_type} `{semiRingE : comSemiRing error_type}. *)
(* Context `{RingT : comRing target_type} `{RingE : comRing error_type}. *)
(* Context `{FieldT : Field target_type} `{FieldE : Field error_type}. *)
(* Context `{orderE : TotalOrder target_type}. *)
(* Context `{metricd : (metric  _ _ dist)}. *)
(* Class PolynomialModel := { *)
(*     pm_p : @mpoly base_type d; *)
(*     pm_f : @mfun target_type d; *)
(*     pm_err : error_type; *)
(*     pm_spec : forall x, (dist (embed pm_p.[x]) (pm_f (embed_tuple x))) <=  embedE pm_err; *)
(*   }. *)

(*     (* pm_mul {d : nat}: @PolynomialModel d -> @PolynomialModel d -> @PolynomialModel d; *) *)
(*     (* pm_mul_spec {d :nat} p1 p2 : (@f _ (@pm_mul d p1 p2)) = (@f _ p1); *) *)
(*     (* pm_compose {d e: nat}: PolynomialModel d -> @tuple d (@PolynomialModel e) -> @PolynomialModel e; *) *)
(*     (* pm_integrate {d : nat}: @PolynomialModel d -> @PolynomialModel d -> @PolynomialModel d; *) *)
(*     (* pm_integrate_spec {d :nat} p1 p2 : (@f _ (@pm_integrate d p1 p2)) = (@f _ p1) *) *)
(*   }. *)
End Approximation.

