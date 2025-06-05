Require Import combinatorics.
Require Import algebra.
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

  #[global] Instance Q_setoid : @Setoid Q.
  Proof.
    exists Qeq.
    apply Q_Setoid.
  Defined.

  #[global] Instance Q_rawRing : (@RawRing Q _).
  Proof.
    constructor.
    apply 0.
    apply 1.
    apply Qplus.
    apply Qmult.
Defined.


  #[global] Instance R_comSemiRing : SemiRing (A := Q).
  Proof.
    constructor;simpl;intros; try ring.
    apply Qplus_comp.
    apply Qmult_comp.
 Defined.

  #[global] Instance R_comRing : Ring (A := Q).
  Proof.
    exists Qopp;intros;simpl;try ring.
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

  #[global] Instance Q_field : Field (A := Q).
  Proof.
    exists Q_inv'.
    intros.
    unfold Q_inv';simpl.
    field;auto.
    simpl;auto.
    compute.
    discriminate.
  Defined.

  Lemma Q_total (x y : Q): (x <= y) \/ (y <= x). 
  Proof.
     lra.
  Qed.

  #[global] Instance Q_totalOrder : TotalOrder.
  Proof.
    exists (fun x y => (x <= y)); intros;simpl;try lra.
    apply Qle_comp.
  Defined.

  #[global] Instance Q_totallyOrderedField : TotallyOrderedField.
  Proof.
    constructor;simpl;intros; try lra.
    apply Qmult_le_0_compat;auto.
  Defined.


  Lemma ntimes_Q : (forall m, ntimes m 1 == (inject_Z (Z.of_nat m))).
  Proof.
    intros.
    induction m.
    simpl; try reflexivity.
    simpl.
    rewrite IHm.
    replace 1%Q with (inject_Z 1%Z) by auto.
    rewrite <-inject_Z_plus.
    apply inject_Z_injective.
    lia.
  Qed.

  #[global] Instance invSn : Sn_invertible.
  Proof.
    exists (fun n => Qinv (inject_Z (Z.of_nat (S n)))).
    intros.
    rewrite ntimes_Q.
    simpl.
    rewrite Qmult_inv_r;try reflexivity.
    unfold Qeq;simpl;lia.
  Defined.

  Lemma Qabs_zero x :   Qabs x == zero <-> x == zero.
  Proof.
  simpl.
  apply Qabs_case;intros;lra.
  Qed.

  Opaque Qabs.
  #[global] Instance Q_norm : NormedSemiRing (A := Q) (B := Q) (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := Q_totalOrder). 
  Proof.
    exists (Qabs);intros;simpl.
    apply Qabs_wd_Proper.
    apply Qabs_nonneg.
    apply Qabs_zero.
    apply Qabs_triangle.
    rewrite Qabs_Qmult.
    lra.
  Defined.

 #[global] Instance ArchimedeanFieldQ : algebra.ArchimedeanField (A := Q).
  Proof.
    unshelve eapply algebra.Build_ArchimedeanField.
    - intros.
      simpl.
      apply Qabs_pos;auto.
   -  intros.
      apply Qabs_neg;auto.
   -  intros.
      simpl.
      destruct (Qarchimedean x).
      exists (Pos.to_nat x0).
      rewrite ntimes_Q.
      rewrite positive_nat_Z.
      apply Qlt_le_weak.
      apply (QOrder.lt_le_trans q).
      rewrite Qmake_Qdiv.
      field_simplify.
      rewrite <-Zle_Qle.
      lia.
  Defined.

  Transparent Qabs.



  
    



