Require Import combinatorics.
Require Import Coq.Reals.Abstract.ConstructiveReals.
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
From Coq Require Import ConstructiveRcomplete.
From Coq Require Import ConstructiveLimits.
From Coq Require Import Reals.Abstract.ConstructiveMinMax.
(* From Coq Require Import Classical. *)

(* Require Import examples. *)
Require Import ConstructiveAbs.
Import ListNotations.
Section ConstructiveReals.
  Context {R : ConstructiveReals}.
  Open Scope ConstructiveReals.
  Close Scope algebra_scope.
  Require Import ConstructiveLUB.
  #[global] Instance R_setoid : @Setoid (CRcarrier R).
  Proof.
    exists (CReq R).
    apply CReq_rel.
  Defined.
  #[global] Instance R_rawRing : (@RawRing (CRcarrier R) _).
  Proof.
    constructor.
    apply 0.
    apply 1.
    apply CRplus.
    apply CRmult.
Defined.
  Definition CR_upper (x : CRcarrier R): nat.
  Proof.
    destruct (CR_archimedean _ x).
    apply (Pos.to_nat x0).
  Defined.
#[global] Instance R_rawRingWithOpp: (@RawRingWithOpp (CRcarrier R) _ _).
Proof.
  constructor.
  apply CRopp.
Defined.

  Definition CR_inv_approx :  CRcarrier R -> CRcarrier R.
  Proof.
    intros x.
    assert (CRapart R (CRmax 1 x) (CR_of_Q R 0) ).
    {
      right.
      apply (CRlt_le_trans _ _ _ (CRzero_lt_one R)).
      apply CRmax_l.
    }
    apply (CRinv R _ H).
  Defined.
 #[global] Instance R_rawFieldOps: (@RawFieldOps (CRcarrier R) _ _ _).
Proof.
  constructor.
  apply (CR_of_Q R).
  apply (CRabs R).
  apply CRmax.
  apply CR_inv_approx.
  apply CR_upper.
Defined.

  #[global] Instance R_comSemiRing : SemiRing (A := (CRcarrier R)).
  Proof.
    constructor; try reflexivity.
    apply CRplus_morph_Proper.
    apply CRmult_morph_Proper.
    apply CRplus_assoc.
    apply CRplus_comm.
    apply CRplus_0_r.
    apply CRmult_assoc.
    apply CRmult_comm.
    apply CRmult_0_r.
    apply CRmult_1_r.
    apply CRmult_plus_distr_l.
 Defined.

  #[global] Instance R_comRing : Ring (A := (CRcarrier R)).
  Proof.
    constructor.
    apply CRopp_morph_Proper.
    apply CRplus_opp_r.
  Defined.

  (* Definition CR_inv' x : (not (x == 0)) -> (CRcarrier R). *)
  (* Proof. *)
  (*   intros. *)
  (*   apply (CRinv R x). *)
  (*   apply neq_apart;auto. *)
  (* Defined. *)

  Lemma lt_neq : forall x y,(CRlt R x y) -> (not (CReq R x y)).
  Proof.
     destruct (CRltLinear R) as [[p1 _] _].
     intros x y H H0.
     rewrite H0 in H.
     apply (p1 y y);auto.
  Qed.

  #[global] Instance R_partialOrder : archimedean.PartialOrder.
  Proof.
    exists (fun x y => (x <= y)).
    intros a b eq1 c d eq2.
    rewrite eq1, eq2;reflexivity.
    
    intros.
    apply CRle_refl.
    intros;split;auto.
    intros.
    apply (CRle_trans _ y);auto.
  Defined.

   #[global] Instance R_embedQ : QEmbedding.
   Proof.
     constructor; simpl;try reflexivity.
     - intros a b eq.
       rewrite eq;reflexivity.
    - intros;rewrite CR_of_Q_plus;reflexivity.
    - intros;rewrite CR_of_Q_mult;reflexivity.
    - intros;rewrite CR_of_Q_opp;reflexivity.
    - intros;apply (eq_inject_Q (R := R));auto.
    - intros;apply CR_of_Q_le;auto.
  Defined.

   #[global] Instance R_hasAbs : HasAbs.
   Proof.
    constructor.
    - intros a b ->;reflexivity.
    - intros;apply CRabs_right;auto.
    - intros;apply CRabs_left;auto.
    - intros;apply CRabs_mult;auto.
    - intros;apply CRabs_triang.
    - intros; apply CRabs_pos.
    - intros.
      split;intros.
      destruct H as [_ H].
      apply CRabs_def2 in H.
      destruct H.
      rewrite CRopp_0 in H0.
      split;auto.
      rewrite H.
      unfold abs.
      unfold R_rawFieldOps.
      rewrite CRabs_right;[reflexivity | apply CRle_refl].
  Defined.

   #[global] Instance R_ArchimedeanField : ArchimedeanField.
   Proof.
     constructor;simpl.
     - intros H0.
       apply eq_inject_Q in H0.
       lra.
    - intros;apply CRplus_le_compat_r;auto.
    - intros;apply CRmult_le_0_compat;auto.
    - intros.
      unfold CR_upper.
      destruct (CR_archimedean _ x).
      rewrite <-ntimes_embed.
      simpl.
      rewrite positive_nat_Z.
      apply CRlt_asym.
      apply c.
   - intros.
     apply CRmax_l.
   - intros.
     apply CRmax_r.
   Defined.



  
    
End ConstructiveReals.



(** A few more things needed for working with the Cauchy reals **)
(** As the modulus definitons in our reals and the Cauchy reals are different we need to relate them **)
(** Most of the things are admitted for now **)

Require Import odebounds.
Require Import realanalytic.
From Coq.Reals Require Import ConstructiveCauchyReals.
From Coq.Reals.Cauchy Require Import ConstructiveRcomplete.
Require Import ConstructiveCauchyAbs.
Require Import Qpower.
Require Import Qabs.
Require Import Qround.
Require Import QArith.
Section CauchyReals.
Print CRealLt.

Definition q (x : Z) (y : positive) := ({| Qnum := x; Qden := y |}).
(* Need to relate our definition of fast Cauchy sequence to the modulus definition *)
(* Admitted for now *)
Definition RQ := CRcarrier CRealConstructive.
Lemma cauchy_neighbor_helper (xn : nat -> RQ) : fast_cauchy_neighboring xn ->  forall k (i j : nat),(Nat.log2 (Pos.to_nat (k + 1)) <= i)%nat -> (Nat.log2 (Pos.to_nat (k + 1)) <= j)%nat -> (CReal_abs (xn i - xn j) <= inject_Q (q 1 k))%CReal.
 Admitted.

Lemma cauchy_neighboring_to_mod   (xn : nat -> RQ) : fast_cauchy_neighboring xn ->  (Un_cauchy_mod xn).
Proof.
   intros H k.
   exists (Nat.log2 ((Pos.to_nat (k+1)))).
   intros.
   apply cauchy_neighbor_helper;auto.
 Defined.

 (* Archimedean for Q seems to be opaque, so we built our own for now (correctness admitted for now) *)
  Local Lemma magic : False.
  Admitted.

 (* #[global] Instance ArchimedeanFieldRQ : ArchimedeanField (A := RQ). *)
 (*  Proof. *)
 (*    unshelve eapply Build_ArchimedeanField. *)
 (*    contradict magic. *)
 (*    contradict magic. *)
 (*    contradict magic. *)
 (*   -  intros. *)
 (*      exists (Z.to_nat (Qceiling (seq x (-1))+1)). *)
 (*      contradict magic. *)
 (*  Defined. *)


  #[global] Instance constrComplete : (ConstrComplete (A := RQ)).
  Proof.
    constructor.
    intros.
    exists (CReal_from_cauchy  xn (cauchy_neighboring_to_mod _ H)).
    intros.
    generalize dependent xn.
    generalize dependent n.
    contradict magic.
   Defined.
End CauchyReals.
