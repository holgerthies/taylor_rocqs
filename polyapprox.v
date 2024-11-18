Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import polynomial.
Require Import symbolic.

Definition tuple_map {n A B} (f : A -> B) (x : @tuple n A) : @tuple n B.
Proof.
  induction n.
  apply nil_tuple.
  destruct (destruct_tuple x) as [hd [tl P]].
  apply (tuple_cons (f hd) (IHn tl)).
 Defined.
Definition in_hypercube {A : Type} `{T : TotalOrder A} {d : nat} (t : @tuple d (A*A)) (x : @tuple d A): Prop.
Proof.
  induction d.
  apply True.
  destruct (destruct_tuple x) as [xh [xt xP]].
  destruct (destruct_tuple t) as [th [tt tP]].
  apply (((fst th) <= xh) /\ (xh <= (snd th) ) /\ (IHd tt xt)).
Defined.

Section MultivariateFun.
  Context `{R : Type} `{R_setoid : Setoid R} `{R_semiRing : @comSemiRing R R_setoid}.
  Definition mfun n := (@tuple n R) -> R.

End MultivariateFun.

Class ApproximationStructure (base_type : Type)  (target_type : Type) (error_type : Type) `{setoidB : Setoid base_type}  `{setoidE : Setoid error_type} `{fieldT : Field target_type}  `{orderE : TotalOrder target_type}  := {
    embed : base_type -> target_type;
    embed_proper :> Proper (SetoidClass.equiv ==> SetoidClass.equiv) embed;
    embedE : error_type -> target_type;
    embedE_proper :> Proper (SetoidClass.equiv ==> SetoidClass.equiv) embedE;
    ASzero : base_type;
    ASone : base_type;
    addition : base_type -> base_type -> base_type;
    multiplication : base_type -> base_type -> base_type
  }.
Section Approximation.
  Context {base_type : Type} {target_type : Type} {error_type : Type} `{normT : NormedSemiRing target_type target_type}.
   Context `(a : ApproximationStructure base_type target_type error_type).

   Definition eval_symbolic (x : Symbolic base_type) : base_type.
   Proof.
    induction x.
    apply (a.(ASzero)).
    apply (a.(ASone)).
    apply a0.
    apply (a.(addition) (IHx1) (IHx2)).
    apply (a.(multiplication) (IHx1) (IHx2)).
  Defined.

  Definition embed_poly {d : nat} : @mpoly (Symbolic base_type) d -> @mpoly target_type d. 
  Proof.
    intros.
    induction d.
    apply (a.(embed) (eval_symbolic X)).
    apply (map IHd X).
   Defined.

  Definition dist x y:= normT.(norm) (x-y).


  Class PolynomialModel  (d : nat) (dom : @tuple d (target_type * target_type)) := {
    pm_p : @mpoly (Symbolic base_type) d;
    pm_f : @mfun target_type d;
    pm_err : error_type;
    pm_spec : forall x, in_hypercube dom x -> (dist (embed_poly pm_p).[x] (pm_f x)) <=  embedE pm_err;
  }.
  Definition eval_pm  {d} {dom} (p : PolynomialModel d dom) (t : @tuple d base_type) :  base_type * error_type.
  Proof.
    destruct p.
    apply (eval_symbolic pm_p0.[tupleToSymbolic t], pm_err0).
  Defined.
(* Class PolynomialModelAddition {a : ApproximationStructure base_type target_type error_type} {d dom} (pm_add : PolynomialModel a d dom -> PolynomialModel a d dom -> PolynomialModel a d dom)  := *)
(*   { *)
(*     pm_add_spec p1 p2 x : ((pm_add p1 p2).(pm_f) x) == p1.(pm_f) x + p2.(pm_f) x; *)
(*   }. *)
(* Class PolynomialModelMultiplication {a : ApproximationStructure base_type target_type error_type} {d dom} (pm_mul : PolynomialModel a d dom -> PolynomialModel a d dom -> PolynomialModel a d dom)  := *)
(*   { *)
(*     pm_mul_spec p1 p2 x : ((pm_mul p1 p2).(pm_f) x) == p1.(pm_f) x * p2.(pm_f) x; *)
(*   }. *)
(* Definition apply_recursive {A B d} (fs : @tuple d (A -> B)) (x : A) : (@tuple d B). *)
(* Proof. *)
(*   induction d. *)
(*   apply nil_tuple. *)
(*   destruct (destruct_tuple fs) as [f [fs' Ps]]. *)
(*   apply (tuple_cons (f x) (IHd fs')). *)
(* Defined. *)

(* Definition pm_f_composition {a : ApproximationStructure base_type target_type error_type} {d e dom1 dom2} (p : PolynomialModel a d dom1) (qs : @tuple d (PolynomialModel a e dom2)) : (@tuple e target_type -> target_type). *)
(* Proof. *)
(*    intros. *)
(*    apply  (p.(pm_f) (apply_recursive (tuple_map (fun p => p.(pm_f)) qs) X)). *)
(* Defined. *)

(* Class PolynomialModelComposition {a : ApproximationStructure base_type target_type error_type} {d e dom1 dom2} (pm_comp : PolynomialModel a d dom1 -> @tuple d (PolynomialModel a e dom2) -> PolynomialModel a e dom2)  := *)
(*   { *)
(*     pm_comp_spec p1 p2 x : ((pm_comp p1 p2).(pm_f) x) == pm_f_composition p1 p2 x; *)
(*   }. *)
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

