Require Import combinatorics.
Require Import algebra.
From Coq Require Import Setoid.
Require Import
  CoRN.model.totalorder.QposMinMax
  CoRN.metric2.Metric
  CoRN.metric2.Complete
  CoRN.reals.faster.ARexp
  CoRN.reals.faster.ARbigD
  CoRN.reals.faster.ARQ
  CoRN.reals.faster.ARabs.


Require Import Coq.Classes.SetoidClass.
Require Import Psatz.
#[global] Instance AR_setoid: Setoid ARbigD.
Proof.
  exists canonical_names.equiv.
  split;auto.
Defined.

#[global] Instance AR_rawRing: (@RawRing ARbigD _).
Proof.
   constructor.
   apply 0.
   apply 1.
   intros x y.
   apply (x+y).
   intros x y.
   apply (x*y).
Defined.

Add Ring ARR : (rings.stdlib_ring_theory ARbigD).

Opaque msp_car.
#[global] Instance AR_semiRing: (algebra.SemiRing (A := ARbigD)).
Proof.
  split;intros; simpl; try ring.
  intros a b eqH c d eqH'.  
  rewrite eqH, eqH';auto.
  intros a b eqH c d eqH'.  
  rewrite eqH, eqH';auto.
Defined.

#[global] Instance AR_Ring: (algebra.Ring (A := ARbigD)).
Proof.
  exists (fun (x : ARbigD) => (-x));intros;simpl; try ring.
  intros a b eqH.
  rewrite eqH;auto.
Defined.

(* Lemma neg_apart x y : (not (x == y)) -> apart x y.  *)
(* Proof. *)
(*  unfold apart, ARapart. *)
(*  intros. *)
(* Admitted. *)

(* Definition AR_recip' (x : ARbigD) : (not (x == 0)) -> ARbigD. *)
(* Proof. *)
(*   intros. *)
(* Admitted. *)

#[global] Instance AR_field: (algebra.Field (A := ARbigD)).
Proof.
Admitted.

  Lemma AR_total (x y : ARbigD): (ARle x  y) \/ (ARle y x). 
  Proof.
  Admitted.

  #[global] Instance AR_totalOrder : algebra.TotalOrder.
  Proof.
    exists (fun x y => (ARle x y)); intros;simpl;auto.
    intros a b Heq c d Heq';rewrite Heq, Heq';split;auto.
     apply ARtoCR_preserves_le;auto.
     apply orders.dec_from_lt_dec_obligation_1;auto.
     apply ARtoCR_preserves_le;auto.
     apply AR_total.
  Defined.

  #[global] Instance AR_totallyOrderedField : TotallyOrderedField.
  Proof.
    constructor;simpl;intros;auto.
    apply ARplus_le_compat_r;auto.
    apply AR_mult_0_le_compat;auto.
  Defined.


  Definition inv_Sn_ARbigD (n : nat) : ARbigD :=  (inject_Q_AR ( / inject_Z (Z.of_nat (S n)))).
  #[global] Instance invSn : Sn_invertible.
  Proof.
    exists inv_Sn_ARbigD.
    intros.
    enough (forall m, ntimes m 1 == inject_Q_AR (inject_Z (Z.of_nat m))) as ->.
    {
      simpl.
      unfold inv_Sn_ARbigD.
      rewrite <-inject_Q_AR_1.
      rewrite <-inject_Q_AR_mult.
      apply inject_Q_AR_wd.
      rewrite Qmult_inv_r;try reflexivity.
      unfold Qeq;simpl;lia.
    }
    intros.
    induction m.
    simpl;rewrite inject_Q_AR_0;reflexivity.
    simpl.
    rewrite IHm.
    rewrite <-inject_Q_AR_1.
    rewrite <-inject_Q_AR_plus.
    apply inject_Q_AR_wd.
    replace 1%Q with (inject_Z 1%Z) by auto.
    rewrite <-inject_Z_plus.
    apply inject_Z_injective.
    lia.
  Defined.

Transparent msp_car.

  Lemma ARabs_zero (x : ARbigD) :   ARabs x == 0 -> x == 0.
  Proof.
  Admitted.

Lemma magic : False.
Admitted.

  #[global] Instance AR_norm : NormedSemiRing (A := ARbigD).
  Proof.
    exists (ARabs);contradict magic.

   (* Opaque msp_car ARabs. *)
   (*  intros;simpl. *)
   (*  intros a b Heq. *)
   (*  rewrite Heq;auto. *)
   (*  intros. *)
   (*  simpl. *)
  Defined.

 #[global] Instance ArchimedeanFieldQ : algebra.ArchimedeanField (A := ARbigD).
  Proof.
    unshelve eapply algebra.Build_ArchimedeanField.
    - intros.
      simpl.
      simpl in H.
      contradict magic.
   - contradict magic.
   - intros.
     exists 3%nat.
     contradict magic.
  Defined.

Require Import polynomial.
Require Import examples.
Require Import tuple.
From Coq Require Import List.
Require Import odebounds.
Require Import realanalytic.
Require Import abstractpowerseries.
Require Import CoRN.metric2.Complete.
Require Import String.
Require Import Decimal DecimalString.
Definition to_string (d : bigD) : string.
Proof.
  destruct d.
  remember (NilZero.string_of_int  (Z.to_int (fast_integers.BigZ_Integers.inject_ZType_Z mant))) as m.
  remember (NilZero.string_of_int  (Z.to_int (fast_integers.BigZ_Integers.inject_ZType_Z expo))) as e.
  apply (append m (append "* 2 ^" e)).
Defined.

  Definition q (x : Z) (y : positive) : Q := ({| Qnum := x; Qden := y |}).
Definition approx_index (e : Q)  := S (Z.to_nat (Qdlog.Qdlog2 (Qinv e))).

  Lemma approx_index_spec (u : nat -> ARbigD) (e : Q) : fast_cauchy_neighboring u ->
    ∀ m n, (m ≥ approx_index e) → (n ≥ approx_index e) →
            ball e (u m) (u n).
  Proof.
  Admitted.

  Definition to_reg (u : nat -> ARbigD) (e: Qpos) : (AQ_as_MetricSpace (AQ := bigD))  := approximate (u (approx_index (`e))) (Qpos_mult e (QabsQpos (q 1 2))) . 

  Lemma fast_cauchy_reg u : fast_cauchy_neighboring u -> is_RegularFunction_noInf _ (to_reg  u).
  Proof.
    unfold is_RegularFunction_noInf, approx.
    intros.
    unfold to_reg.
    Admitted.

  #[global] Instance constrComplete : (ConstrComplete (A := ARbigD)).
  Proof.
    constructor.
    intros. 
    exists (mkRegularFunction (canonical_names.zero) (fast_cauchy_reg _ H)).
    contradict magic.
 Defined.

Open Scope algebra_scope.
Section examples.


Definition exp_example := exp_ivp (A := ARbigD).

Definition exp_analytic  := analytic_poly exp_example.(pf) exp_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 20 approximation *)
Definition exp_taylor := taylor_poly exp_analytic 0 5.
(*evaluate at 1/2 *)
Definition exp_approx1 : ARbigD := (eval_poly exp_taylor (inv_Sn_ARbigD 1)).
Check approximate.
Definition test := (approximate exp_approx1 (Qpos2QposInf (QabsQpos (q 1 1)))).
Eval vm_compute in test.

 Definition exp_cont1  := analytic_poly exp_example.(pf) t(exp_approx1).

Definition exp_taylor2 := taylor_poly exp_cont1 0 5.
Definition exp_approx2 := (eval_poly exp_taylor2 (inv_Sn_ARbigD 1)).
  
Definition test2 := (approximate exp_approx2 (Qpos2QposInf (QabsQpos (q 1 1)))).
 Definition  approx_tuple {d} (p : (ARbigD * tuple d ARbigD))  (n : positive): string * list string.
 Proof.
   destruct p as [t v].
   destruct v.
   remember (Qpos2QposInf (QabsQpos (q 1 n))) as prec.
   apply (to_string (approximate t prec) , (map (fun x => (to_string (approximate x prec))) x)).
 Defined.

 Definition  approx_trajectory {d} (p : list (ARbigD * tuple d ARbigD))   z :=  map (fun p => approx_tuple p z) p.

Eval vm_compute in test2.
    
(* now with guaranteed error bound  at max time *)
Definition exp_exact := (ivp_solution_max exp_analytic).
Definition app := (approx_tuple exp_exact 1000).
Definition a := (ivp_r_max exp_analytic).
Definition b := (proj1_sig  (analytic_solution_r exp_analytic)).

Eval vm_compute in app.



