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
  - intros.
    unfold CR_inv_approx.
    rewrite CRinv_morph.
    2: (apply CRmax_right;auto).
    apply CRinv_r.
    Unshelve.
    apply CRabs_appart_0.

    apply (CRlt_le_trans _ x).
    2: apply CRle_abs.
    apply (CRlt_le_trans _ 1);auto.
    apply CRzero_lt_one.
   Defined.



  
    
End ConstructiveReals.


(** Some of the operations in ConstructiveReals appear to be declared
opaque and thus block computation. In particular, this is true for
the completeness result CR_complete.
We therefore need to instantiate completeness explicitly for the Cauchy reals to enable compuation
 **)


Require Import odebounds.
Require Import realanalytic.
From Coq.Reals Require Import ConstructiveCauchyReals.
From Coq.Reals.Cauchy Require Import ConstructiveRcomplete.
Require Import ConstructiveCauchyAbs ConstructiveCauchyRealsMult.
Require Import Qpower.
Require Import Qabs.
Require Import Qround.
Require Import QArith.
From Coq Require Import micromega.Lqa.
Section CauchyReals.
Print CRealLt.

Definition q (x : Z) (y : positive) := ({| Qnum := x; Qden := y |}).
Definition RQ := CRcarrier CRealConstructive.

Lemma inv2_npow_spec n : (npow (inv2 :RQ) n == inject_Q (2^(-Z.of_nat n)))%CReal.
Proof.
  induction n.
  simpl;reflexivity.
  simpl npow.
  rewrite IHn.
  replace (inv2) with (inject_Q (q 1 2)) by auto.

  rewrite <-inject_Q_mult.
  apply inject_Q_morph.
  rewrite !Qpower_opp.

  rewrite Nat2Z.inj_succ.
  unfold Z.succ.
  rewrite Qpower_plus';try lia.
  rewrite Qinv_mult_distr.
  simpl.
  setoid_replace (q 1 2) with (/ 2)%Q by reflexivity.
  rewrite Qmult_comm.

  apply Qmult_inj_l;try reflexivity.
  rewrite <-Qinv_power.
  enough ((/ 2) ^ (Z.of_nat n) > 0)%Q by lra.
  apply Qpower_0_lt.
  apply Qinv_lt_0_compat.
  lra.
Qed.

Lemma inject_Q_pow2_split n : (inject_Q (2 ^ (- Z.of_nat n)) == inject_Q (2 ^ (- Z.of_nat (S n)))+inject_Q (2 ^ (- Z.of_nat (S n))))%CReal.
Proof.
  rewrite <-inject_Q_plus.
  apply inject_Q_morph.
  rewrite !Nat2Z.inj_succ.
  unfold Z.succ.
  rewrite !Z.opp_add_distr.
  rewrite !Qpower_plus; try lra.
  simpl.
  field.
Qed.

Lemma fast_cauchy_neighboring_ij (xn : nat -> RQ) : fast_cauchy_neighboring xn -> forall i j, (CReal_abs (xn i - xn j) <= inject_Q (2^(- Z.of_nat (Nat.min i j))))%CReal.
Proof.
 unfold fast_cauchy_neighboring.
 setoid_rewrite inv2_npow_spec.
 intros H.
 enough (forall k i, CReal_abs (xn i - xn (i + k)%nat) <= inject_Q (2^(- Z.of_nat i)))%CReal.
 {
     intros.
     assert (i <= j \/ j <= i)%nat by lia.
     destruct H1.
     replace j with (i + (j - i))%nat by lia.
     rewrite Nat.min_l;try lia.
     apply H0.
     replace i with (j + (i - j))%nat by lia.
     rewrite CReal_abs_minus_sym.
     rewrite Nat.min_r;try lia.
     apply H0.
 }
 intros k. 
 induction k;intros.
 replace (i+0)%nat with i by lia.
 setoid_replace (xn i - xn i)%CReal with (inject_Q 0) by ring.
 rewrite <-Qabs_Rabs.
 apply inject_Q_le.
 simpl.
 apply Qpower_0_le;lra.
 setoid_replace (xn i - xn (i+S k)%nat)%CReal with ((xn i - xn (S i)) + (xn (S i) - xn (i + S k)%nat))%CReal by ring.
 replace (i + S k)%nat with (S i + k)%nat by lia.
 rewrite inject_Q_pow2_split.
 apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _ )).
 apply CReal_plus_le_compat.
 rewrite CReal_abs_minus_sym.
 apply H.
 apply IHk.
Qed.

Local Lemma Pos_of_nat_le n m: (n <= m)%nat -> (Pos.of_nat n <= Pos.of_nat m)%positive.
Proof. lia. Qed.

Lemma cauchy_neighbor_helper (xn : nat -> RQ) : fast_cauchy_neighboring xn ->  forall k (i j : nat),(Nat.log2_up (Pos.to_nat k) <= i)%nat -> (Nat.log2_up (Pos.to_nat k) <= j)%nat -> (CReal_abs (xn i - xn j) <= inject_Q (q 1 k))%CReal.
Proof.
  intros.
  apply (CReal_le_trans _ _ _ (fast_cauchy_neighboring_ij _ H _ _)).
  apply inject_Q_le.
  apply (Qle_trans _ (2^-(Z.of_nat (Nat.log2_up (Pos.to_nat k))))).
  apply Qpower_le_compat_l; [lia|lra].
  rewrite ClassicalDedekindReals.Qpower_2_neg_eq_natpow_inv.
  unfold q,Qle.
  simpl.
  apply Pos2Z.pos_le_pos.
  rewrite <-Pos2Nat.id at 1.
  apply Pos_of_nat_le.
  destruct (Pos.to_nat k).
  lia.
  destruct n.
  simpl.
  lia.
  apply Nat.log2_up_spec.
  lia.
Qed.

Lemma cauchy_neighbor_helper2 (xn : nat -> RQ) : fast_cauchy_neighboring xn ->  forall k (i j : nat),(Pos.to_nat (Pos.size k) <= i)%nat -> (Pos.to_nat (Pos.size k) <= j)%nat -> (CReal_abs (xn i - xn j) <= inject_Q (q 1 k))%CReal.
Proof.
  intros.
  apply (CReal_le_trans _ _ _ (fast_cauchy_neighboring_ij _ H _ _)).
  apply inject_Q_le.
  apply (Qle_trans _ (2^-(Z.of_nat (Pos.to_nat (Pos.size k))))).
  apply Qpower_le_compat_l; [lia|lra].
  rewrite ClassicalDedekindReals.Qpower_2_neg_eq_natpow_inv.
  unfold q,Qle.
  simpl.
  apply Pos2Z.pos_le_pos.
  replace (2)%nat with (Pos.to_nat 2) by auto.
  rewrite <-Pos2Nat.inj_pow.
  rewrite Pos2Nat.id.
  pose proof (Pos.size_gt k).
  lia.
Qed.

Lemma CReal_abs_eq0 (x y : RQ) : (CReal_abs (x-y) == inject_Q 0)%CReal -> x == y. 
Proof.
  intros.
  destruct H.
  apply CReal_abs_def2 in H0.
  destruct H0.
  rewrite CReal_opp_0 in H1.
  split.
  apply (CReal_plus_le_reg_r (-y)).
  setoid_replace (y + (-y))%CReal with (inject_Q 0) by ring.
  exact H1.
  apply (CReal_plus_le_reg_r (-y)).
  ring_simplify.
  exact H0.
Qed.

Lemma cauchy_neighboring_to_mod   (xn : nat -> RQ) : fast_cauchy_neighboring xn ->  (Un_cauchy_mod xn).
Proof.
   intros H k.
   exists (Pos.to_nat (Pos.size k)).
   intros.
   apply cauchy_neighbor_helper2;auto.
 Defined.

(* Lemma cauchy_neighboring_to_mod   (xn : nat -> RQ) : fast_cauchy_neighboring xn ->  (Un_cauchy_mod xn). *)
(* Proof. *)
(*    intros H k. *)
(*    exists (Nat.log2_up ((Pos.to_nat k))). *)
(*    intros. *)
(*    apply cauchy_neighbor_helper;auto. *)
(*  Defined. *)

  Lemma pos_size_pow2 n :  (n > 0)%nat -> Pos.size (2 ^ Pos.of_nat n) = Pos.succ (Pos.of_nat n).
  Proof.
    induction n.
    lia.
    intros.
    destruct n.
    simpl.
    reflexivity.
    rewrite Nat2Pos.inj_succ;try lia.
    rewrite Pos.pow_succ_r.

    simpl Pos.size.
    destruct n.
    simpl;reflexivity.
    rewrite <-Nat2Pos.inj_succ; try lia.
  Qed.

  Local Lemma CReal_from_cauchy_seq (xn : nat -> RQ) H n:  (n > 0)%nat -> seq (CReal_from_cauchy xn (cauchy_neighboring_to_mod _ H)) (Z.neg (Pos.of_nat n)) = seq (xn (n+3)%nat) (Zneg (Pos.of_nat n+2)).
  Proof.
    intros.
    unfold CReal_from_cauchy.
    simpl.
    unfold CReal_from_cauchy_seq.
    simpl.
    f_equal.
    rewrite pos_size_pow2;auto.
    f_equal.
    lia.
  Qed.

  Lemma CReal_from_cauchy_lim (xn : nat -> RQ) (H : fast_cauchy_neighboring xn): forall n, (CReal_abs ((CReal_from_cauchy _ (cauchy_neighboring_to_mod _ H)) - xn (S n)) <=  inject_Q (2^(-Z.of_nat n)))%CReal.
  Proof.
     intros.
     remember (CReal_from_cauchy xn (cauchy_neighboring_to_mod xn H)) as x.
     remember (Z.neg (Pos.of_nat (n+3)%nat)) as p.
     assert (CReal_abs (inject_Q (seq x p) - (inject_Q (seq (xn (S n)) p))) <= inject_Q (2^(p+1)) + inject_Q (2^(-Z.of_nat (S n))))%CReal.
     {
       rewrite Heqx, Heqp.
       rewrite CReal_from_cauchy_seq; try lia.
       rewrite <-Heqp.
       replace (n+3+3)%nat with (n+6)%nat by lia.
       replace (Pos.of_nat (n+3) + 2)%positive with (Pos.of_nat (n+5)) by lia.
       remember (Z.neg (Pos.of_nat (n+5))) as p'.
       remember (inject_Q (seq (xn (n+6)%nat) p')) as a.
       remember (inject_Q (seq (xn (S n)) p)) as b.
       setoid_replace (a - b)%CReal with ((a - (xn (n+6)%nat)) +  (xn (S n) - b ) + (xn (n+6)%nat - xn (S n)) )%CReal by ring.
       apply (CReal_le_trans _ _ _ (CReal_abs_triang _  _)).
       apply CReal_plus_le_compat.
       - apply (CReal_le_trans _ _ _ (CReal_abs_triang _  _)).
         rewrite Heqa, Heqb.
         rewrite CReal_abs_minus_sym.
         apply (CReal_le_trans _ _ _ (CReal_plus_le_compat _ _ _ _ (CReal_cv_self' _ _) (CReal_cv_self' _ _))).
         rewrite <-inject_Q_plus.
         apply inject_Q_le.
         rewrite Qpower_plus;try lra.
         setoid_replace (2^p * 2^1) with (2^p + 2^p) by (simpl;lra).
         apply Qplus_le_l.
         apply Qpower_le_compat_l;[lia|lra].
       - apply (CReal_le_trans _ _ _ (fast_cauchy_neighboring_ij xn H _ _ )).
         apply inject_Q_le;apply Qpower_le_compat_l;[lia|lra].
     }
     setoid_replace (x - xn (S n))%CReal with ((x - inject_Q (seq x p)) + ((inject_Q (seq x p)) - (inject_Q (seq (xn (S n)) p))+ ((inject_Q (seq (xn (S n)) p))- xn (S n))))%CReal by ring.
     apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
     apply (CReal_le_trans _ _ _ (CReal_plus_le_compat_l _ _ _ (CReal_abs_triang _ _))).

     apply (CReal_le_trans _ _ _ (CReal_plus_le_compat _ _ _ _ (CReal_cv_self' _ _) (CRealLe_refl  _))).
     rewrite CReal_plus_comm, CReal_plus_assoc.
     apply (CReal_le_trans _ _ _ (CReal_plus_le_compat _ _ _ _ H0 (CRealLe_refl  _))).
     rewrite CReal_plus_comm, CReal_plus_assoc.
     rewrite CReal_abs_minus_sym.
     apply (CReal_le_trans _ _ _ (CReal_plus_le_compat _ _ _ _ (CReal_cv_self' _ _) (CRealLe_refl  _))).
     rewrite <-!inject_Q_plus.
     apply inject_Q_le.
     replace (-Z.of_nat (S n))%Z with (p+2)%Z by lia.
     rewrite !Qpower_plus; try lra.
     replace (2^2)%Q with 4%Q by reflexivity.
     replace (2^1)%Q with 2%Q by reflexivity.
     setoid_replace (2 ^ p + (2 ^ p + (2 ^ p*2 + 2 ^ p * 4))) with (8 * 2^p) by (simpl;lra).
     rewrite  Heqp. 
     replace 8 with (2^3) by reflexivity.
     rewrite <-Qpower_plus; try lra.
     apply Qpower_le_compat_l;[lia|lra].
  Qed.

  Lemma fast_cauchy_S (xn : nat -> RQ) : fast_cauchy_neighboring xn -> fast_cauchy_neighboring (fun n => (xn (S n))).
  Proof.
    intros.
    intros n.
    simpl.
    apply (CReal_le_trans _ _ _ (H (S n))).
    simpl.
    unfold inv2.
    simpl.
    rewrite <-CReal_mult_assoc.
    apply CReal_mult_le_compat_r.
    pose proof (npow_pos (A:=RQ) (inject_Q (q 1 2)) n).
    apply H0.
    simpl.
    unfold q.
    apply inject_Q_le;lra.
    rewrite <-inject_Q_mult.
    apply inject_Q_le.
    lra.
  Qed.

  
  #[global] Instance constrComplete : (ConstrComplete (A := RQ)).
  Proof.
    constructor.
    intros.
    exists (CReal_from_cauchy _ (cauchy_neighboring_to_mod _ H)).
    intros.
    rewrite inv2_npow_spec.
    pose proof (CReal_from_cauchy_lim xn H).
    simpl.
    remember  (CReal_from_cauchy xn (cauchy_neighboring_to_mod xn H)) as x.
    assert (forall p, CReal_abs (x - xn n) <=inject_Q (2 ^ (- Z.of_nat p)) + inject_Q (2 ^ (- Z.of_nat n)))%CReal.
    {
        intros.
        remember (Nat.max p n) as p'.
        setoid_replace (x - xn n)%CReal with ((x - xn (S p')) + (xn (S p') - xn n) )%CReal by ring.
        apply (CReal_le_trans _ _ _ (CReal_abs_triang _ _)).
        apply CReal_plus_le_compat.
        apply (CReal_le_trans _ _ _ (H0 _)).
        apply inject_Q_le.
        apply Qpower_le_compat_l; [lia|lra].
        apply (CReal_le_trans _ _ _ (fast_cauchy_neighboring_ij xn H  _ _)).
        apply inject_Q_le.
        apply Qpower_le_compat_l; [lia|lra].
    }

    assert (forall p, CReal_abs (x - xn n) <=inject_Q (2 ^ p) + inject_Q (2 ^ (- Z.of_nat n)))%CReal.
    {
       intros.
       assert (p <= 0 \/ 0 < p)%Z by lia.
       destruct H2.
       replace p with (-Z.of_nat (Z.to_nat (-p)))%Z by lia.
       apply H1.
       apply (CReal_le_trans _ _ _ (H1 0%nat)).
       apply CReal_plus_le_compat;apply inject_Q_le;try lra.
       apply Qpower_le_compat_l;[lia|lra].
    }
    clear H1.
    apply CRealLe_not_lt.
    intros p.
    specialize (H2 p).
    rewrite <-inject_Q_plus in H2.
    apply (CReal_abs_Qabs _ _ p) in H2.
    simpl.
    unfold CReal_abs_seq.
    setoid_replace (2 * 2 ^ p) with (2^p + 2 ^ p) by (simpl;lra).
    apply (Qplus_le_l _ _ (- 2^(-Z.of_nat n))) in H2.
    apply (Qle_trans _ _ _ H2).
    lra.
 Defined.
End CauchyReals.

