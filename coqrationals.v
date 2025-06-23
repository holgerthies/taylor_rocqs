Require Import combinatorics.
Require Import algebra archimedean.
Require Import polynomial.
Require Import functions.
Require Import ode.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
From Coq Require Import QArith.
Require Import tuple.

From Coq Require Import Psatz.
From Coq Require Import List.
Require Import QOrderedType Qabs.
(* Require Import examples. *)

Import ListNotations.

  #[global] Instance Q_rawRing : (@RawRing Q _).
  Proof.
    constructor.
    apply 0.
    apply 1.
    apply Qplus.
    apply Qmult.
Defined.


#[global] Instance Q_rawRingWithOpp: (@RawRingWithOpp Q _ _).
Proof.
  constructor.
  apply Qopp.
Defined.

 #[global] Instance Q_rawFieldOps: (@RawFieldOps Q _ _ _).
Proof.
  constructor.
  apply (fun x => x).
  apply Qabs.
  apply Qminmax.Qmax.
  apply Qinv.
Defined.

  #[global] Instance R_comSemiRing : SemiRing (A := Q).
  Proof.
    constructor;simpl;intros; try ring.
    apply Qplus_comp.
    apply Qmult_comp.
 Defined.

  #[global] Instance R_comRing : Ring (A := Q).
  Proof.
    constructor;intros;simpl;try ring.
    apply Qopp_comp.
  Defined.
  Definition Q_inv' x : (not (x == 0)) -> Q.
  Proof.
    intros.
    apply (Qinv x).
  Defined.

  (* Lemma lt_neq : forall x y,( CRlt R x y) -> (not (CReq R x y)). *)
  (* Proof. *)
  (*    destruct (CRltLinear R) as [[p1 _] _]. *)
  (*    intros x y H H0. *)
  (*    rewrite H0 in H. *)
  (*    apply (p1 y y);auto. *)
  (* Qed. *)

    #[global] Instance Q_partialOrder : (archimedean.PartialOrder (A :=Q)).
  Proof.
    exists (fun x y => (x <= y)%Q).
    intros a b eq1 c d eq2.
    rewrite eq1, eq2;reflexivity.
    
    intros.
    apply Qle_refl.
    intros.
    apply QOrder.le_antisym;auto.
    intros;apply (Qle_trans _ y);auto.
  Defined.

   #[global] Instance Q_embedQ : (QEmbedding (A:=Q)).
   Proof.
   constructor;simpl;intros;try reflexivity;auto.
    intros a b eq.
    rewrite eq;reflexivity.
  Defined.

   #[global] Instance R_hasAbs : HasAbs.
   Proof.
   constructor.
    - intros a b ->;reflexivity.
    - intros;apply Qabs_pos;auto.
    - intros;apply Qabs_neg;auto.
    - intros;apply Qabs_Qmult;auto.
    - intros;apply Qabs_triangle.
    - intros; apply Qabs_nonneg.
    - intros.
      simpl.
      apply Qabs_case;intros;split;intros;auto;lra.
  Defined.

   #[global] Instance Q_ArchimedeanField : ArchimedeanField.
   Proof.
     constructor;simpl;intros; try lra.
    - intros;apply Qmult_le_0_compat;auto.
    - intros.
      destruct (Qarchimedean x).
      exists (Pos.to_nat x0).
      rewrite <-ntimes_embed.
      simpl.
      rewrite positive_nat_Z.
      apply Qlt_le_weak.
      apply q.
   Defined.


  Transparent Qabs.



  
    



