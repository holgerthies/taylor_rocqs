Require Import combinatorics.
Require Import Coq.Reals.Abstract.ConstructiveReals.
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
From Coq Require Import ConstructiveRcomplete.
From Coq Require Import ConstructiveLimits.
From Coq Require Import Classical.

(* Require Import examples. *)
Require Import ConstructiveAbs.
Import ListNotations.
Section ConstructiveReals.
  Context {R : ConstructiveReals}.
  Open Scope ConstructiveReals.
  Close Scope algebra_scope.
Lemma neq_apart : forall x y,(not (CReq R x y)) -> (CRlt R x y) + (CRlt R  y x).
Proof.
  intros.
  apply CRltDisjunctEpsilon.
  unfold CReq in H.
  apply Classical_Prop.not_and_or in H.
  destruct H.
  left.
  apply Classical_Prop.NNPP.
  intros Hp.
  contradict H.
  intros H0.
  contradict Hp.
  apply CRltForget;auto.
  right.
  apply Classical_Prop.NNPP.
  intros Hp.
  contradict H.
  intros H0.
  contradict Hp.
  apply CRltForget;auto.
Defined.
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
    exists (CRopp R).
    apply CRopp_morph_Proper.
    apply CRplus_opp_r.
  Defined.
  Definition CR_inv' x : (not (x == 0)) -> (CRcarrier R).
  Proof.
    intros.
    apply (CRinv R x).
    apply neq_apart;auto.
  Defined.

  Lemma lt_neq : forall x y,(CRlt R x y) -> (not (CReq R x y)).
  Proof.
     destruct (CRltLinear R) as [[p1 _] _].
     intros x y H H0.
     rewrite H0 in H.
     apply (p1 y y);auto.
  Qed.

  #[global] Instance R_field : Field (A := (CRcarrier R)).
  Proof.
    exists CR_inv'.
    intros.
    apply CRinv_l.
    apply lt_neq.
    apply CRzero_lt_one.
  Defined.

  (* requires classical reasoning in Prop*)
  Lemma R_total (x y : (CRcarrier R)): (x <= y) \/ (y <= x). 
  Proof.
    destruct (classic (x == y)).
    left.
    rewrite H.
    apply CRle_refl.
    destruct (neq_apart _ _ H).
    left.
    apply CRlt_asym;auto.
    right.
    apply CRlt_asym;auto.
  Qed.

  #[global] Instance R_totalOrder : TotalOrder.
  Proof.
    exists (fun x y => (x <= y)).
    intros a b eq1 c d eq2.
    rewrite eq1, eq2;reflexivity.
    
    intros.
    apply CRle_refl.
    intros;split;auto.
    intros.
    apply (CRle_trans _ y);auto.
    intros.
    apply R_total.
  Defined.

  #[global] Instance R_totallyOrderedField : TotallyOrderedField.
  Proof.
    constructor.
    intros.
    simpl.
    apply CRplus_le_compat_r;auto.
    intros; simpl.
    apply CRmult_le_0_compat;auto.
  Defined.

  Definition p1 : (@mpoly (CRcarrier R) 1).
  Proof.
     unfold mpoly.
     apply [0;1].
   Defined.

  Definition p2 : (@mpoly (CRcarrier R) 2).
  Proof.
     unfold mpoly.
     apply [[0;1]; [0;1]].
   Defined.

  #[global] Instance invSn : Sn_invertible.
  Proof.
    exists (fun n => CR_of_Q R ( / inject_Z (Z.of_nat (S n)))).
    intros.
    enough (forall m, ntimes m 1 == CR_of_Q R (inject_Z (Z.of_nat m))) as ->.
    {
      simpl.
      rewrite <-CR_of_Q_mult.
      rewrite Qmult_inv_r;try reflexivity.
      unfold Qeq;simpl;lia.
    }
    intros.
    induction m.
    simpl; try reflexivity.
    simpl.
    rewrite IHm.
    rewrite <-CR_of_Q_plus.
    apply CR_of_Q_morph.
    replace 1%Q with (inject_Z 1%Z) by auto.
    rewrite <-inject_Z_plus.
    apply inject_Z_injective.
    lia.
  Defined.

  Lemma CRabs_zero x :   CRabs R x == zero <-> x == zero.
  Proof.
    split.
    intros.
    - destruct (le_total x 0).
      simpl in H0.
      rewrite CRabs_left in H;auto.
      rewrite <-CRopp_involutive.
      rewrite H.
      apply CRopp_0.
      rewrite CRabs_right in H;auto.
   - intros.
     rewrite H.
     rewrite CRabs_right;auto.
     reflexivity.
     apply CRle_refl.
  Qed.

  #[global] Instance R_norm : NormedSemiRing (A := CRcarrier R) (B := CRcarrier R) (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := R_totalOrder). 
  Proof.
    exists (CRabs R).
    intros.
    apply ConstructiveAbs.CRabs_morph_prop_Proper.
    intros.
    apply CRabs_pos.
    intros.
    apply CRabs_zero.
    intros.
    apply CRabs_triang.
    intros.
    simpl.
    rewrite CRabs_mult.
    apply CRle_refl.
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
  Lemma archimedean_bound (x : RQ) : algebra.le x (algebra.ntimes (Z.to_nat (Qceiling (seq x (-1)) + 1)) algebra.one).
  Admitted.

 #[global] Instance ArchimedeanFieldRQ : algebra.ArchimedeanField (A := RQ).
  Proof.
    unshelve eapply algebra.Build_ArchimedeanField.
    - intros.
      simpl.

      apply CReal_abs_right.
      apply H.
   -  intros.
      simpl.
      apply CReal_abs_left;auto.
   -  intros.
      exists (Z.to_nat (Qceiling (seq x (-1))+1)).
      apply archimedean_bound.
  Defined.


  Lemma  completeness_helper xn H0 n:  @algebra.le RQ (@R_setoid CRealConstructive) (@R_totalOrder CRealConstructive)
    (@algebra.norm RQ RQ (@R_setoid CRealConstructive) (@R_rawRing CRealConstructive)
       (@R_setoid CRealConstructive) (@R_rawRing CRealConstructive) (@R_totalOrder CRealConstructive)
       (@R_norm CRealConstructive)
       (@algebra.minus RQ (@R_setoid CRealConstructive) (@R_rawRing CRealConstructive)
          (@R_comSemiRing CRealConstructive) (@R_comRing CRealConstructive)
          (CReal_from_cauchy xn (cauchy_neighboring_to_mod xn H0)) (xn n)))
    (@algebra.npow RQ (@R_setoid CRealConstructive) (@R_rawRing CRealConstructive)
       (@combinatorics.inv2 RQ (@R_setoid CRealConstructive) (@R_rawRing CRealConstructive)
          (@R_comSemiRing CRealConstructive) (@invSn CRealConstructive)) n).
  Proof.
  Admitted.

  #[global] Instance constrComplete : (ConstrComplete (A := RQ)).
  Proof.
    constructor.
    intros.
    exists (CReal_from_cauchy  xn (cauchy_neighboring_to_mod _ H)).
    intros.
    apply completeness_helper.
   Defined.
End CauchyReals.
