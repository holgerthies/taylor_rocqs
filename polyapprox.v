Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import polynomial.
Require Import intervalpoly.
Require Import symbolic.

Definition tuple_map {n A B} (f : A -> B) (x : @tuple n A) : @tuple n B.
Proof.
  induction n.
  apply nil_tuple.
  destruct (destruct_tuple x) as [hd [tl P]].
  apply (tuple_cons (f hd) (IHn tl)).
 Defined.

Section MultivariateFun.
  Context `{R : Type}.
  Definition mfun n := (@tuple n R) -> R.

End MultivariateFun.
Class ApproximationStructure (base_type : Type)  (target_type : Type) `{setoidB : Setoid base_type} `{rawRingB : RawRing (A := base_type)}   `{fieldT : TotallyOrderedField target_type}    := {
    embed : base_type -> target_type;
    embed_proper :> Proper (SetoidClass.equiv ==> SetoidClass.equiv) embed;
  }.
Definition eval_symbolic  `{a : ApproximationStructure } (x : Symbolic base_type) : base_type.
   Proof.
    induction x.
    apply 0.
    apply 1.
    apply a0.
    apply ((IHx1) + (IHx2)).
    apply ((IHx1) * (IHx2)).
  Defined.

Definition embed_poly `{a : ApproximationStructure } {d : nat} : @mpoly base_type d -> @mpoly target_type d.
  Proof.
    intros.
    induction d.
    apply (a.(embed) X).
    apply (map IHd X).
   Defined.
Section Approximation.
  Context {base_type : Type} {target_type : Type}.
     Context `{comSemiRing (A:=target_type)}  `{normT : NormedSemiRing (A:=target_type) (B := target_type)  (H := H) (H0 := H) (R_rawRing := R_rawRing) (R_rawRing0 := R_rawRing)}.
   Context `{a : ApproximationStructure base_type target_type (H := H) (R_rawRing := R_rawRing) (R_TotalOrder := R_TotalOrder)}.

  Definition dist x y:= normT.(norm) (x-y).
  Add Ring Tring: ComRingTheory.
  Lemma metric_distance_plus x y u v: dist  (x+y) (u+v) <= dist x u + dist y v.
Proof.
  unfold dist.
  setoid_replace (x+y - (u+v)) with ((x-u) + (y-v)) by ring.
  apply norm_triangle.
  Qed.
  #[global] Instance dist_proper : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) dist.
  Proof.
  intros a0 b P0 c d P1.
  apply norm_proper.
  rewrite P0,P1;reflexivity.
  Defined.
  Class PolynomialModel  (d : nat) `(dom : @tuple d (@cinterval target_type)) := {
    pm_p : @mpoly base_type d;
    pm_f : @mfun target_type d;
    pm_err : base_type;
    pm_spec : forall x, in_cintervalt x dom -> (dist (embed_poly pm_p).[x] (pm_f x)) <=   embed pm_err;
  }.

  Definition embed_tuple {n} (x : (@tuple n base_type)) :=  (tuple_map a.(embed) x).
  Definition embed_interval (i : base_type * base_type) := (a.(embed) (fst i),(a.(embed) (snd i))).
  Class PolynomialModelEvaluation (d : nat)  (dom : @tuple d (@cinterval target_type)):= {
      pm_eval : PolynomialModel d dom -> (@tuple d base_type) -> base_type * base_type;
      pm_eval_spec p (x : (@tuple d base_type)) : forall x, in_cintervalt (embed_tuple x) dom -> in_cinterval (p.(pm_f) (embed_tuple x)) (embed_interval (pm_eval p x))
    }.

Class PolynomialModelAddition (d : nat) (dom : @tuple d (@cinterval target_type))  :=
  {
    pm_add : PolynomialModel d dom -> PolynomialModel d dom -> PolynomialModel d dom;
    pm_add_spec p1 p2 x : ((pm_add p1 p2).(pm_f) x) == p1.(pm_f) x + p2.(pm_f) x;
  }.
(* Class PolynomialModelMultiplication {a : ApproximationStructure base_type target_type error_type} {d dom} (pm_mul : PolynomialModel a d dom -> PolynomialModel a d dom -> PolynomialModel a d dom)  := *)
(*   { *)
(*     pm_mul_spec p1 p2 x : ((pm_mul p1 p2).(pm_f) x) == p1.(pm_f) x * p2.(pm_f) x; *)
(*   }. *)
Definition apply_recursive {A B d} (fs : @tuple d (A -> B)) (x : A) : (@tuple d B).
Proof.
  induction d.
  apply nil_tuple.
  destruct (destruct_tuple fs) as [f [fs' Ps]].
  apply (tuple_cons (f x) (IHd fs')).
Defined.

Definition pm_vec d e dom :=  @tuple e (PolynomialModel d dom).

(* Definition eval_pm_vec {d e dom} (p : pm_vec d e dom) (t : @tuple d base_type) :  @tuple e (base_type * target_type). *)
(* Proof. *)
(*   induction e. *)
(*   apply nil_tuple. *)
(*   destruct (destruct_tuple p) as [p0 [pr P]]. *)
(*   apply (tuple_cons (eval_pm p0 t) (IHe pr)). *)
(* Defined. *)

Definition pm_f_composition  {d e dom1 dom2} (p : PolynomialModel d dom1) (qs :pm_vec e d dom2) : (@tuple e target_type -> target_type).
Proof.
   intros.
   apply  (p.(pm_f) (apply_recursive (tuple_map (fun p => p.(pm_f)) qs) X)).
Defined.

Class PolynomialModelComposition  {d e dom1 dom2} (pm_comp : PolynomialModel d dom1 -> @tuple d (PolynomialModel e dom2) -> PolynomialModel e dom2)  :=
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

