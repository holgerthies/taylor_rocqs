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

  Instance Proper_symbolic_add :
  Proper (symbolic_equiv ==> symbolic_equiv ==> symbolic_equiv) Sadd.
  Proof.
    intros x1 x2 H1 y1 y2 H2.
    apply SaddProper;auto.
  Defined.

  Instance Proper_symbolic_mul :
  Proper (symbolic_equiv ==> symbolic_equiv ==> symbolic_equiv) Smul.
  Proof.
    intros x1 x2 H1 y1 y2 H2.
    apply SmulProper;auto.
  Defined.

  Instance S_setoid : (Setoid Symbolic).
  Proof.
    exists symbolic_equiv.
    constructor.
    intros x;apply Srefl.
    intros x y;apply Ssym.
    intros x y z;apply Strans.
  Defined.
  Instance S_semiRing : comSemiRing.
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

Section Interval.
  Context `{R : Type} `{R_setoid : Setoid R} `{R_semiRing : @comSemiRing R R_setoid}.
  
  Definition mfun n := (@tuple n R) -> R.

End Interval.
Section Norm.
Context `{A: Type} `{B : Type}.
Context `{semiRingA : comSemiRing A}.
Context `{FieldB : Field B}.
Context `{orderE : TotalOrder B}.
Class MetricSpace  := {
    metric_distance : A -> A -> B ;
    metric_proper :> Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) metric_distance;
    metric_zero : forall x y, metric_distance x y == 0 <-> x == y;
    metric_sym : forall x y, metric_distance x y == metric_distance y x;
    metric_triangle : forall x y z, metric_distance x y <= metric_distance x z + metric_distance z y
  }.
End Norm.

Class ApproximationStructure (base_type : Type) (target_type : Type) (error_type : Type) `{semiRingB : comSemiRing base_type} `{fieldT : Field target_type} `{semiRingE : comSemiRing error_type}  `{orderE : TotalOrder target_type}  := {
    embed : base_type -> target_type;
    embed_proper :> Proper (SetoidClass.equiv ==> SetoidClass.equiv) embed;
    embedE : error_type -> target_type;
    embedE_proper :> Proper (SetoidClass.equiv ==> SetoidClass.equiv) embedE;
  }.
Section Approximation.
  Context {base_type : Type} {target_type : Type} {error_type : Type} `{semiRingB : comSemiRing base_type} `{fieldT : Field target_type} `{semiRingE : comSemiRing error_type}   `{orderT : TotalOrder target_type} `{metricT : MetricSpace target_type target_type}.
  Definition embed_poly {d : nat} (a : ApproximationStructure base_type target_type error_type) : @mpoly base_type d -> @mpoly target_type d. 
  Proof.
    intros.
    induction d.
    apply (a.(embed) X).
    apply (map IHd X).
   Defined.
  Class ExactPolynomialModel  (d : nat) (dom : @tuple d (target_type * target_type)) := {
    epm_p : @mpoly target_type d;
    epm_f : @mfun target_type d;
    pme_err : target_type;
    pme_spec : forall x, in_hypercube dom x -> (metricT.(metric_distance) epm_p.[x] (epm_f x)) <=  pme_err;
  }.
  Class PolynomialModel (approx : ApproximationStructure base_type target_type error_type) (d : nat) (dom : @tuple d (target_type * target_type)) := {
    pm_p : @mpoly base_type d;
    pm_f : @mfun target_type d;
    pm_err : error_type;
    pm_spec : forall x, in_hypercube dom x -> (metricT.(metric_distance) (embed_poly approx pm_p).[x] (pm_f x)) <=  embedE pm_err;
  }.
  Definition eval_pm {a : ApproximationStructure base_type target_type error_type} {d} {dom} (p : PolynomialModel a d dom) (t : @tuple d base_type) :  base_type * error_type.
  Proof.
    destruct p.
    apply (pm_p0.[t], pm_err0).
  Defined.
Class PolynomialModelAddition {a : ApproximationStructure base_type target_type error_type} {d dom} (pm_add : PolynomialModel a d dom -> PolynomialModel a d dom -> PolynomialModel a d dom)  :=
  {
    pm_add_spec p1 p2 x : ((pm_add p1 p2).(pm_f) x) == p1.(pm_f) x + p2.(pm_f) x;
  }.
Class PolynomialModelMultiplication {a : ApproximationStructure base_type target_type error_type} {d dom} (pm_mul : PolynomialModel a d dom -> PolynomialModel a d dom -> PolynomialModel a d dom)  :=
  {
    pm_mul_spec p1 p2 x : ((pm_mul p1 p2).(pm_f) x) == p1.(pm_f) x * p2.(pm_f) x;
  }.
Definition apply_recursive {A B d} (fs : @tuple d (A -> B)) (x : A) : (@tuple d B).
Proof.
  induction d.
  apply nil_tuple.
  destruct (destruct_tuple fs) as [f [fs' Ps]].
  apply (tuple_cons (f x) (IHd fs')).
Defined.

Definition pm_f_composition {a : ApproximationStructure base_type target_type error_type} {d e dom1 dom2} (p : PolynomialModel a d dom1) (qs : @tuple d (PolynomialModel a e dom2)) : (@tuple e target_type -> target_type).
Proof.
   intros.
   apply  (p.(pm_f) (apply_recursive (tuple_map (fun p => p.(pm_f)) qs) X)).
Defined.

Class PolynomialModelComposition {a : ApproximationStructure base_type target_type error_type} {d e dom1 dom2} (pm_comp : PolynomialModel a d dom1 -> @tuple d (PolynomialModel a e dom2) -> PolynomialModel a e dom2)  :=
  {
    pm_comp_spec p1 p2 x : ((pm_comp p1 p2).(pm_f) x) == pm_f_composition p1 p2 x;
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

