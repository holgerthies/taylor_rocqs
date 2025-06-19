From Coq Require Import QArith.
Require Import combinatorics.
Require Import algebra archimedean.
From Coq Require Import Setoid.
Require Import
  CoRN.reals.Q_in_CReals
  CoRN.reals.fast.CRFieldOps
  CoRN.reals.fast.CRArith
  CoRN.algebra.CFields
  CoRN.model.totalorder.QposMinMax
  CoRN.metric2.Metric
  CoRN.metric2.Complete
  CoRN.reals.faster.ARexp
  CoRN.reals.faster.ARbigD
  CoRN.reals.faster.ARQ
  CoRN.reals.faster.ARabs
  CoRN.reals.faster.ARArith
  CoRN.reals.CReals.


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


    #[global] Instance AR_partialOrder : (archimedean.PartialOrder (A :=ARbigD)).
  Proof.
    exists (fun x y => (ARle x y)); intros;simpl;auto.
    intros a b Heq c d Heq';rewrite Heq, Heq';split;auto.
     apply ARtoCR_preserves_le;auto.
     apply orders.dec_from_lt_dec_obligation_1;auto.
     apply ARtoCR_preserves_le;auto.
  Defined.

   Transparent msp_car.
  Lemma inject_Q_AR_opp x :   inject_Q_AR (AQ := bigD) (- x) = - inject_Q_AR (AQ := bigD) x.
  Proof.
  Admitted.

  Lemma inject_Q_AR_inj x y :   inject_Q_AR (AQ := bigD) x = inject_Q_AR (AQ := bigD) y -> (x == y)%Q.
  Admitted.

   #[global] Instance AR_embedQ : (QEmbedding (A:=ARbigD)).
   Proof.
   exists inject_Q_AR; simpl;intros;try reflexivity;auto.
   - intros a b eq.
     apply inject_Q_AR_wd;auto.
  - apply inject_Q_AR_0.
  - apply inject_Q_AR_1.
  - apply inject_Q_AR_plus.
  - apply inject_Q_AR_mult.
  - apply inject_Q_AR_opp.
  - apply inject_Q_AR_inj;auto.
   - apply inject_Q_AR_le;auto.
  Defined.
   Lemma ARabs_mult (x y : ARbigD) : ARabs (x * y) == ARabs x * ARabs y. 
   Proof.
   Admitted.

   Lemma ARabs_triangle (x y : ARbigD) : le (ARabs (x + y)) (ARabs x + ARabs y).
   Proof.
   Admitted.
   Lemma ARabs_nonneg (x : ARbigD) : le 0 (ARabs x).
   Proof.
   Admitted.

   Lemma ARabs_zero (x : ARbigD) : ARabs x == 0 <-> x == 0.
   Proof.
   Admitted.

   #[global] Instance AR_hasAbs : (HasAbs (A := ARbigD)).
   Proof.
   exists ARabs.
    - intros a b ->;reflexivity.
    - intros;apply ARabs_pos;auto.
    - intros;apply ARabs_neg;auto.
    - intros;apply ARabs_mult;auto.
    - intros;apply ARabs_triangle.
    - intros; apply ARabs_nonneg.
    - intros;apply ARabs_zero.
  Defined.

   Lemma AR_0_1_distinct : not (0 == 1).
   Proof.
   Admitted.

   Definition AR_b' (x : ARbigD) : Q :=  ('(approximate x (QabsQpos 1)) + 1).
   Lemma AR_b_spec (x : ARbigD) : ARle x (inject_Q_AR (AR_b' x)).
   Proof.
      unfold AR_b'.
   Admitted.


   #[global] Instance AR_ArchimedeanField : ArchimedeanField.
   Proof.
     constructor;simpl;intros; try lra.
     - apply AR_0_1_distinct.
     - apply ARplus_le_compat_r;auto.
     - apply AR_mult_0_le_compat;auto.
     - exists (Z.to_nat (Qround.Qceiling (AR_b' x))).
     rewrite <-ntimes_embed.
     rewrite embNatQ.
     simpl.
     apply (ARle_trans _ (inject_Q_AR (AR_b' x))).
     apply AR_b_spec.
     apply inject_Q_AR_le.
     apply (Qle_trans _ ((Qround.Qceiling (AR_b' x)))%Q).
     apply Qround.Qle_ceiling.
     rewrite <-Q.Zle_Qle.
     enough (forall z, (z <= Z.to_nat z)%Z) by auto.
     intros.
     destruct (Z.le_ge_cases z 0).
     rewrite Z.Zto_nat_nonpos;auto.
     rewrite Z2Nat.id;auto;lia.
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
Definition approx_index (e : Q)  := 4%nat. (* S (Z.to_nat (Qdlog.Qdlog2 (Qinv e))). *)

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

  Lemma magic : False.
  Admitted.

  #[global] Instance constrComplete : (ConstrComplete (A := ARbigD)).
  Proof.
    constructor.
    intros. 
    exists (mkRegularFunction (canonical_names.zero) (fast_cauchy_reg _ H)).
    contradict magic.
 Defined.

Open Scope algebra_scope.
(* Section examples. *)

Definition  approx_poly {d} (p : (tuple d (list ARbigD)))  (n : positive):  list (list string).
   destruct p as [t v].
   destruct v.
   remember (Qpos2QposInf (QabsQpos (q 1 n))) as prec.
   induction t.
   apply nil.
   apply (cons (map (fun x => (to_string (approximate x prec))) a)  IHt). 
Defined.

  Definition Fi_fast {d} (f : (tuple (S d) (@mpoly ARbigD (S d)))) (n i : nat) : list (@mpoly ARbigD (S d)).
  Proof.
    induction n.
    apply (cons (cons 0 (cons 1 nil)) nil).
    apply (cons (sum (fun j =>  (tuple_nth j f 0) * (D[j] (hd 0 IHn))) (S d))  IHn).
  Defined.
  
Definition Fi_to_taylor {d} (l : list (@mpoly ARbigD (S d))) (y0 : (tuple (S d) ARbigD)) : @poly ARbigD.
Proof.
  induction l.
  apply nil.
  apply (IHl ++ (cons (![Datatypes.length IHl] * eval_tuple a y0) nil)).
Defined.

Definition exp_example := exp_ivp (A := ARbigD).

Definition exp10 := (Fi_fast exp_example.(pf) 5 0).

Definition exp_taylor10 := Fi_to_taylor exp10 exp_example.(py0).

Definition exp_approx0 : ARbigD :=(ARcompress  (eval_poly exp_taylor10 (inv_Sn 1))).

Fixpoint exp_continue0 (n : nat) := match n with
                          | 0%nat => (ARcompress (eval_poly exp_taylor10 (inv_Sn 1)))
                          | (S n') => (ARcompress (eval_poly (Fi_to_taylor exp10 (tuple_cons (exp_continue0 n') nil_tuple)) (inv_Sn 1)))
                                       end.
Definition test0 := (approximate exp_approx0 (Qpos2QposInf (QabsQpos (q 1 100)))).
Time Eval vm_compute in test0.


Definition testc0 := (approximate (exp_continue0 2) (Qpos2QposInf (QabsQpos (q 1 3)))).

Time Eval vm_compute in testc0.
Require Import CoRN.ode.Picard.
Require Import CoRN.ode.FromMetric2.
Require Import CoRN.model.metric2.Qmetric.
Notation sx := (sig (@ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig rx) x0)).
Program Definition half : sx := q 1 2.
Next Obligation.
apply mspc_ball_Qabs_flip. unfold x0. rewrite negate_0, plus_0_r.
rewrite abs.abs_nonneg; [reflexivity |].
change (0 <= 1 # 2)%Q. auto with qarith.
Qed.
Check (picard_iter 2 (inv_Sn_ARbigD 1)).

Definition exp_analytic  := analytic_poly exp_example.(pf) exp_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 20 approximation *)
Definition exp_taylor := taylor_poly exp_analytic 0 20.
(*evaluate at 1/2 *)
Definition exp_approx1 : ARbigD :=(ARcompress  (eval_poly exp_taylor (inv_Sn_ARbigD 1))).
Definition test := (approximate exp_approx1 (Qpos2QposInf (QabsQpos (q 1 100)))).
Time Eval vm_compute in test.

 Definition exp_cont1  := analytic_poly exp_example.(pf) t(exp_approx1).

Definition exp_taylor2 := taylor_poly exp_cont1 0 10.
Definition exp_approx2 := (ARcompress ((eval_poly exp_taylor2 (inv_Sn_ARbigD 1)))).
  
Definition test2 := (approximate exp_approx2 (Qpos2QposInf (QabsQpos (q 1 100)))).

  Fixpoint eval_poly' (a : poly) (x : ARbigD) :=
    match a with
    | nil => 0
    | h :: t => ARcompress h + x * (ARcompress (eval_poly t x))
    end.



Check (exp_example.(pf)).

Fixpoint exp_continue (n : nat) := match n with
                          | 0%nat => (ARcompress (eval_poly' (taylor_poly (analytic_poly exp_example.(pf) exp_example.(py0)) 0 5) (inv_Sn_ARbigD 1)))
                          | (S n') => (ARcompress (eval_poly' (taylor_poly (analytic_poly exp_example.(pf) t(exp_continue n')) 0 5) (inv_Sn_ARbigD 1)))
                                       end.


Definition test3 := (approximate (exp_continue 1) (Qpos2QposInf (QabsQpos (q 1 100)))).
Time Eval vm_compute in test3.

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
Check pivp_trajectory.
   Definition pivp_trajectory {d} (p : (tuple (S d) (@mpoly ARbigD (S d)))) (t0 : ARbigD) (y0 : (tuple (S d) ARbigD)) (steps : nat) :  list (ARbigD * (tuple (S d) ARbigD)).
   Proof.
     revert t0 y0.
     induction steps;intros.
     apply (cons (ARcompress t0,tuple_map ARcompress y0) nil).
     pose proof (pivp_solution_max p y0).
     apply (cons (ARcompress t0, tuple_map ARcompress y0) (IHsteps (ARcompress (t0 + fst X)) (tuple_map ARcompress (snd X)))).
   Defined.
Definition exp_trajectory := (pivp_trajectory exp_example.(pf) canonical_names.zero exp_example.(py0) 2).
Eval vm_compute in (approx_trajectory exp_trajectory 1).

End examples.

Recursive Extraction test3.
