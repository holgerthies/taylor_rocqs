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
Require Import examples.
Require Import ConstructiveAbs.
Import ListNotations.
Section ConstructiveReals.
  Context {R : ConstructiveReals}.
  Open Scope ConstructiveReals.

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
  Open Scope algebra_scope.
  Open Scope fun_scope.

  Lemma y_in_dom {d} (f : ((mpoly d)^d)) (y0 : (mpoly 0)^d) :  y0 \in_dom f.
  Proof.
    intros n P.
    simpl;auto.
  Defined.

  Definition PIVP_T {d} (f : @tuple d (mpoly d)) y0 := ivp_taylor_poly f y0 (y_in_dom f y0).
 Definition exp_series := PIVP_T (tuple_cons p1 nil_tuple) (tuple_cons 1 nil_tuple). 
End ConstructiveReals.






