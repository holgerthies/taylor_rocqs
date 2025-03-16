Require Import combinatorics.
Require Import Coq.Reals.Abstract.ConstructiveReals.
Require Import algebra.
Require Import polynomial.
Require Import functions.
Require Import ode.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import QArith.
Require Import tuple.

Require Import Psatz.
Require Import List.
Require Import ConstructiveRcomplete.
Require Import ConstructiveLimits.

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

  Lemma R_total (x y : (CRcarrier R)): (x <= y) \/ (y <= x). 
  Proof.
  Admitted.

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
  Admitted.

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
  Open Scope fun_scope.

  Require Import odebounds.
  Lemma cauchy_neighboring_to_mod_helper  xn k i j : fast_cauchy_neighboring xn ->   (Nat.log2_up (Pos.to_nat (k+1)) <= i)%nat -> (Nat.log2_up (Pos.to_nat (k+1)) <= j)%nat ->  CRabs R (xn i - xn j)%ConstructiveReals  <=  CR_of_Q R {| Qnum := 1; Qden := k |}.
  Admitted.

  Lemma cauchy_neighboring_to_mod   xn : fast_cauchy_neighboring xn ->  (CR_cauchy R xn).
  Proof.
    intros.
    intros k.
    exists (Nat.log2_up ((Pos.to_nat (k+1)))).
    intros.
    apply cauchy_neighboring_to_mod_helper;auto.
 Defined.

  Lemma npow_inv2 n :  npow (CR_of_Q R (/ inject_Z 2)) n == CR_of_Q R (2^(- Z.of_nat n))%Q.
  Proof.
  Admitted.

  Lemma fast_cauchy_fast_limit xn x n : CR_cv R xn x -> fast_cauchy_neighboring xn -> norm (x - xn n) <= npow inv2 n.
  Admitted.

  #[global] Instance R_complete : ConstrComplete (A := CRcarrier R).
  Proof.
    constructor.
    intros.
    destruct (CR_complete _ xn).
    apply cauchy_neighboring_to_mod;auto.
    intros.
    exists x.
    intros.
    apply fast_cauchy_fast_limit;auto.
  Qed.
    
End ConstructiveReals.






