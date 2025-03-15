Require Import algebra ode polynomial functions.
Require Import Psatz. 
Require Import tuple.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import combinatorics.
Section IVP_Examples.
  Open Scope fun_scope.
  Context `{AbstractFunctionSpace }.
  Context `{Ring (A := A 0) (H := (H 0)) (R_rawRing := (H0 0)) (R_semiRing := (H1 0))}.
  Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat))}.
  (* one-dimensional examples *)

  Notation "\x_ i" := (comp1 i) (at level 2).
  Definition exp_ivp : (IVP  (d := 1) (A := A)).
  Proof.
    exists t(\x_0) t(1).
    intros n P.
    replace n with 0%nat by lia.
    simpl f.
    rewrite tuple_nth_cons_hd.
    apply dom_id.
  Defined.


  Definition tan_ivp : (IVP  (d := 1) (A := A)).
  Proof.
    exists t(1 [+] \x_0*\x_0 ) t(0).
    intros n P.
    replace n with 0%nat by lia.
    simpl f.
    rewrite tuple_nth_cons_hd.
    apply dom_plus.
    apply const_dom.
    apply dom_mult;apply dom_id.
  Defined.

  (* two-dimensional examples *)
  Lemma in_dom2  f0 f1 t0 t1: t(t0;t1) \in_dom (t(f0;f1) : (A 2)^2) <->   t(t0;t1) \in_dom f0 /\ t(t0;t1) \in_dom f1.
  Proof.
    assert (f0 == (tuple_nth 0 t(f0;f1) 0)) by (simpl;reflexivity).
    assert (f1 == (tuple_nth 1 t(f0;f1) 0)) by (simpl;reflexivity).
    split;intros.
    split;[rewrite (dom_change_f  _ _ _ H7)|rewrite (dom_change_f  _ _ _ H8)];apply H9;lia.
    intros i Hi.
    assert (i = 0 \/ i = 1)%nat by lia.
    destruct H10;rewrite H10;auto.
    rewrite <-(dom_change_f  _ _ _ H7);apply H9.
    rewrite <-(dom_change_f  _ _ _ H8);apply H9.
  Qed.   

  Definition sin_cos_ivp : (IVP (d := 2) (A := A)).
    exists t(\x_1;(opp 1) [*] \x_0) t(0;1).
    apply in_dom2.
    split; [|apply dom_mult;try apply const_dom ];try apply dom_id.
  Defined.

  Definition vdp_ivp (mu : A 0) : (IVP (d := 2) (A := A)).
    exists t(\x_1;mu [*] (1 [+] ((opp 1) [*] \x_0 *\x_0)) * \x_1 + (opp 1) [*] \x_0) t(0;1).
    apply in_dom2.
    split; try apply dom_id.
    apply dom_plus; apply dom_mult;try apply dom_id; try apply const_dom.
    apply dom_mult; try apply const_dom.
    apply dom_plus; try apply dom_mult;try apply dom_id; try apply const_dom.
    apply dom_mult;apply dom_id.
  Defined.
End IVP_Examples.
(* Require Import Psatz. *)
(* Require Import List. *)
(* Require Import ZArith. *)
(* Import ListNotations. *)
(* Require Import Coq.Reals.Rdefinitions. *)
(* Require Import Coq.Reals.Raxioms. *)
(* Require Import Rfunctions. *)
(* Require Import Coq.Reals.RIneq. *)
(* Require Import Coq.Reals.Reals. *)
(* Require Import algebra polynomial. *)
(* Require Import Setoid. *)
(* Require Import Coq.Classes.SetoidClass. *)
(* Require Import polyapprox. *)
(* Require Import intervalpoly. *)
(* Require Import symbolic. *)
(* Require Import powerseries. *)
(* Section Z_poly. *)
(* Instance Z_setoid : Setoid Z. *)
(* Proof. *)
(*   exists (eq). *)
(*   apply Eqsth. *)
(* Defined. *)
(* Instance Z_rawRing : RawRing (A := Z). *)
(* Proof. *)
(*   constructor; [apply 0%Z | apply 1%Z | apply (fun x y => (x + y)%Z) | apply (fun x y => (x * y)%Z)]. *)
(* Defined. *)

(* Instance Z_comRing : comSemiRing (A := Z). *)
(* Proof. *)
(*    constructor;unfold equiv,Z_setoid;simpl;try (intros; ring);intros a b H c d H0;lia. *)
(* Defined. *)

(* Instance Z_mpoly0Setoid : Setoid (@mpoly Z 0). *)
(* Proof. apply mpoly_setoid. Defined. *)

(* Instance Z_mpoly1Setoid : Setoid (@mpoly Z 1). *)
(* Proof. apply mpoly_setoid. Defined. *)

(* Instance Z_mpoly2Setoid : Setoid (@mpoly Z 2). *)
(* Proof. apply mpoly_setoid. Defined. *)


(* Definition p1 : (@mps Z 1). *)
(* Proof. *)
(*   intros n. *)
(*   apply 1. *)
(* Defined. *)

(* Definition p2 : (@mps Z 1). *)
(* Proof. *)
(*   intros n. *)
(*   destruct n. *)
(*   apply 0. *)
(*   apply 1. *)
(* Defined. *)

(* Definition mp1 : (@mps Z 2). *)
(* Proof. *)
(*   intros n. *)
(*   intros m. *)
(*   apply (Z.of_nat (n+m+1)). *)
(* Defined. *)

(* Definition poly1 : (@mps Z 2). *)
(* Proof. *)
(*   intros n. *)
(*   apply match n with 0 => 0 | 1 => 0 | 2 => 1 | _ => 0 end. *)
(* Defined. *)

(* Definition print_mp1 (a : @mps Z 1) n:= map a (seq 0 (S n)). *)
(* Definition print_mp2 (a : @mps Z 2) n:= map (fun j => print_mp1 (a j) n) (seq 0 (S n)). *)

(* Definition x : (@mpoly Z 2) := [[0%Z]; [1%Z]].  *)
(* Definition y : (@mpoly Z 2) := [[0%Z; 1%Z]; [0%Z]].  *)
(* Definition p3 := (x*y+y+x*x*x*x+y*y*x*x). *)

(* Compute p3. *)
(* Compute (poly_pdiff 1 p3). *)

(* End Z_poly. *)

(* Require Import QArith. *)
(* Require Import Ring. *)
(* Section Q_poly. *)

(* Open Scope Q_scope. *)
(* Instance Q_setoid : Setoid Q. *)
(* Proof. *)
(*   exists Qeq. *)
(*   apply Q_Setoid. *)
(* Defined. *)

(* Instance Q_rawRing : RawRing (A := Q). *)
(* Proof. *)
(*   constructor; [apply 0%Q | apply 1%Q | apply (fun x y => (x + y)%Q) | apply (fun x y => (x * y)%Q)]. *)
(* Defined. *)

(* Instance Q_semiRing : comSemiRing. *)
(* Proof. *)
(*   constructor;try (intros; unfold SetoidClass.equiv, Q_setoid;simpl;ring). *)
(*   apply Qplus_comp. *)
(*   apply Qmult_comp. *)
(* Defined. *)

(* Instance Q_Ring :comRing. *)
(* Proof. *)
(*   exists (fun q => (- q)). *)
(*   apply Qopp_comp. *)
(*   intros. *)
(*   simpl;ring. *)
(* Defined. *)

(* Instance Q_field :Field. *)
(* Proof. *)
(*    exists (fun q p => (1 / q)). *)
(*    intros. *)
(*    simpl;field. *)
(*    contradict p;auto. *)
(*    simpl. *)
(*    intros H. *)
(*    symmetry in H. *)
(*    apply Q_apart_0_1;auto. *)
(* Defined. *)

(* Add Ring RRing : (ComSemiRingTheory (A := (mpoly 0))). *)


(* Definition q2 : (@mpoly Q 2). *)
(* Proof. *)
(*   apply [[1#2]; [1#2; 2#3]]. *)
(* Defined. *)

(* Definition q11 : (@mpoly Q 1). *)
(* Proof. *)
(*   apply [0%Q; 0%Q;1%Q]. *)
(* Defined. *)
(* Definition q12 : (@mpoly Q 1). *)
(* Proof. *)
(*   apply [0%Q; 0%Q;0%Q;1%Q]. *)
(* Defined. *)

(* Instance R_setoid : Setoid R. *)
(* Proof.  *)
(*   exists eq. *)
(*   apply Eqsth. *)
(* Defined. *)
(* Require Import ClassicalConstructiveReals. *)
(* Require Import Coq.setoid_ring.Ring_theory. *)
(* Require Import Coq.setoid_ring.Ring. *)
(* Require Import Qreals. *)
(* Open Scope R_scope. *)
(* Instance R_rawRing : RawRing (A := R). *)
(* Proof. *)
(*   constructor; [apply 0%R  | apply 1%R | apply Rplus | apply Rmult]. *)
(* Defined. *)

(* Instance R_comSemiRing :comSemiRing. *)
(* Proof. *)
(*   constructor; unfold SetoidClass.equiv;simpl;try (intros a b H0 c d H1;rewrite H0, H1);intros;try ring. *)
(* Defined. *)

(* Instance R_comRing : comRing. *)
(* Proof. *)
(*   exists Ropp; unfold SetoidClass.equiv;simpl;try (intros a b H0 ;rewrite H0);intros;try ring. *)
(* Defined. *)

(* Instance R_totalOrder : TotalOrder. *)
(* Proof. *)
(*   exists Rle;intros;unfold SetoidClass.equiv;simpl;try lra. *)
(*   intros a b H c d H0. *)
(*   lra. *)
(* Defined. *)

(* Instance Q_totalOrder : TotalOrder (A:=Q). *)
(* Proof. *)
(*   exists Qle; intros;try lra. *)
(*   intros a b H a0 b0 H0;rewrite H,H0;reflexivity. *)
(*   apply Qle_antisym;auto. *)
(* Defined. *)
(* Instance Q_totallyOrderedField : TotallyOrderedField. *)
(* Proof. *)
(*   constructor;unfold le;simpl;intros;try lra. *)
(*   apply Qmult_le_0_compat;auto. *)
(* Defined. *)

(* Lemma Q_abs_zero x : Qabs.Qabs x == 0%Q <-> x == 0%Q.  *)
(* Proof. *)
(* Admitted. *)

(* Instance Q_normed : NormedSemiRing (A:=Q) (B:=Q). *)
(* Proof. *)
(*   exists Qabs.Qabs;intros. *)
(*   intros a b ->;reflexivity. *)
(*   apply Qabs.Qabs_nonneg. *)
(*   split;intros; [| rewrite H;reflexivity]. *)
(*   simpl in H. *)
(*   apply Q_abs_zero;auto. *)
(*   apply Qabs.Qabs_triangle. *)
(*   rewrite Qabs.Qabs_Qmult. *)
(*   apply le_refl. *)
(* Defined. *)

(* Compute (proj1_sig (boundPoly q2 t[(3,1);(5,1)]%Q)). *)
(* (* Instance Rdist_metric : MetricSpace. *) *)
(* (* Proof. *) *)
(* (*    exists Rdist. *) *)
(* (*    intros a b H c d H0. *) *)
(* (*    rewrite H, H0; reflexivity. *) *)
(* (*    apply Rdist_refl. *) *)
(* (*    apply Rdist_sym. *) *)
(* (*    apply Rdist_tri. *) *)
(* (* Defined. *) *)

(* Instance R_Field : Field. *)
(* Proof. *)
(*    exists (fun q p => (1 / q)). *)
(*    intros. *)
(*    unfold SetoidClass.equiv in *. *)
(*    simpl in *. *)
(*    field;auto. *)
(*    unfold SetoidClass.equiv;simpl;lra. *)
(* Defined. *)


(* Instance R_TotallyOrderedField : TotallyOrderedField. *)
(* Proof. *)
(*   constructor;simpl;intros; try lra. *)
(*   nra. *)
(* Defined. *)

(* Instance approx_RQ : ApproximationStructure Q R Q. *)
(* Proof. *)
(*   exists Q2R Q2R; try (intros a b ->;reflexivity). *)
(*   apply 0%Q. *)
(*   apply 1%Q. *)
(*   apply Qplus. *)
(*   apply Qmult. *)
(* Defined. *)

(* Instance normR : NormedSemiRing. *)
(* Proof. *)
(*   exists Rabs;intros. *)
(*   intros a b ->;reflexivity. *)
(*   apply Rabs_pos. *)
(*   simpl. *)
(*   split;intros; [| rewrite H;rewrite Rabs_R0;reflexivity]. *)
(*   enough (not (x0 <> 0)) by tauto. *)
(*   intros H0. *)
(*   contradict H. *)
(*   apply Rabs_no_R0;auto. *)
(*   apply Rabs_triang. *)
(*   rewrite Rabs_mult. *)
(*   apply le_refl. *)
(* Defined. *)

(* Definition PM_Q2 : PolynomialModel approx_RQ 2 t[(0,1);(0,1)]. *)
(* Proof. *)
(*    exists [[Sconst _ 1%Q]] (fun t => 0.5%R) 0.5%Q. *)
(*    intros. *)
(*    simpl. *)
(*    destruct (destruct_tuple x0) as [x [tl P]]. *)
(*    destruct (destruct_tuple tl) as [y [tl' P']]. *)
(*    unfold eval_mpoly. *)
(*    simpl. *)
(*    rewrite RMicromega.Q2R_1. *)
(*    unfold Rdist. *)
(*    apply Rabs_le. *)
(*    split;lra. *)
(* Defined. *)

(* Lemma ntimes_Q n q: ntimes n q == (inject_Z (Z.of_nat n) * q)%Q. *)
(* Proof. *)
(*    induction n.  *)
(*    simpl;unfold inject_Z;lra. *)
(*    simpl. *)
(*    rewrite IHn. *)
(*    rewrite Zpos_P_of_succ_nat. *)
(*    unfold Z.succ;simpl. *)
(*    rewrite inject_Z_plus. *)
(*    ring. *)
(* Qed. *)

(* Lemma q_char0 : forall n, (not (ntimes (S n) 1%Q == 0%Q)). *)
(* Proof. *)
(*   intros n. *)
(*   rewrite ntimes_Q. *)
(*   intros H. *)
(*   ring_simplify in H. *)
(*   replace 0%Q with (inject_Z 0) in H by auto. *)
(*   rewrite inject_Z_injective in H. *)
(*   lia. *)
(* Qed.  *)

(* Definition embed_add_compat p q : embed_poly approx_RQ (add p q) = add (embed_poly approx_RQ p) (embed_poly approx_RQ q).   *)
(* Proof. *)
(*   simpl. *)
(*   revert q;induction p;[simpl;auto|]. *)
(*   intros. *)
(*   destruct q;simpl;auto. *)
(*   rewrite IHp. *)
(*   f_equal. *)
(*   revert m;induction a;[simpl;auto|]. *)
(*   intros. *)
(*   destruct m;simpl;auto. *)
(*   rewrite IHa. *)
(*   f_equal. *)
(*   rewrite Q2R_plus;auto. *)
(* Defined. *)
(* Definition pmq_add {dom}: PolynomialModel approx_RQ 2 dom -> PolynomialModel approx_RQ 2 dom -> PolynomialModel approx_RQ 2 dom.  *)
(* Proof. *)
(*   intros p1 p2. *)
(*   destruct p1,p2. *)
(*   exists (@add _ Q_mpoly2Setoid Q_mpoly2ComRing pm_p pm_p0) (fun t => pm_f t + pm_f0 t) (pm_err + pm_err0)%Q. *)
(*   intros. *)
(*   rewrite embed_add_compat. *)
(*   rewrite mpoly_add_spec. *)
(*   setoid_replace (add (embed_poly approx_RQ pm_p).[x0] (embed_poly approx_RQ pm_p0).[x0]) with ((embed_poly approx_RQ pm_p).[x0] + (embed_poly approx_RQ pm_p0).[x0])%R; [|simpl;ring]. *)
(*   unfold le, R_totalOrder. *)
(*   rewrite !Q2R_plus. *)
(*   rewrite Rdist_plus. *)
(*   apply Rplus_le_compat;[apply pm_spec | apply pm_spec0];try apply H. *)
(* Defined. *)

(* Instance pmq_add_addition {dom}: PolynomialModelAddition (@pmq_add dom). *)
(* Proof. *)
(*   split. *)
(*   intros. *)
(*   simpl. *)
(*   destruct p4,p5;simpl. *)
(*   ring. *)
(* Qed. *)


(* Definition pmq_composition {dom1 dom2}: PolynomialModel approx_RQ 1 dom1 -> @tuple 1 (PolynomialModel approx_RQ 2 dom2) -> PolynomialModel approx_RQ 2 dom2. *)
(* Proof. *)
(*   assert (forall x, in_hypercube dom (tuple_map embed x) -> Rdist ()). *)
(*   intros p qs. *)
(*   destruct (destruct_tuple qs) as [q [n N]]. *)
(*   destruct p as [p f err P]. *)
(*   destruct q as [q g err' Q]. *)
(*   exists (p \o (tuple_cons q nil_tuple)) (fun x => (f (tuple_cons (g x) nil_tuple))) err. *)
(*   intros. *)
(*   rewrite (mpoly_composition_spec p (tuple_cons q nil_tuple)). *)
(*   setoid_replace (eval_tuple_rec (tuple_cons q nil_tuple) x0) with (tuple_cons q.[x0] nil_tuple) by simpl;auto. *)
(*  setoid_replace (tuple_cons (g (tuple_map embed x0)) nil_tuple) with (tuple_map embed (tuple_cons q.[x0] nil_tuple)). *)
(*   apply P. *)
(*   admit. *)
  
(* End Q_poly. *)
