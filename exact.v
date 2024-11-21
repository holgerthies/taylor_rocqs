Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import polynomial polyapprox intervalpoly.
Class ExactApproximationStructure `{a : ApproximationStructure} := {

    embed_0: a.(embed) 0 == 0;
    embed_1: a.(embed) 1 == 1;
    embed_add_compat: forall (p q: base_type),  a.(embed) (p + q) == a.(embed) p + a.(embed) q;
    embed_mul_compat: forall (p q: base_type),  a.(embed) (p * q) == a.(embed) p * a.(embed) q
   

  }.

Section Exact.
     Context {base_type target_type : Type}.
     Context `{comSemiRing (A:=target_type)}  `{normT : NormedSemiRing (A:=target_type) (B := target_type)  (H := H) (H0 := H) (R_rawRing := R_rawRing) (R_rawRing0 := R_rawRing)}.
   Context `{a_exact : ExactApproximationStructure base_type target_type (H := H) (R_rawRing := R_rawRing) (R_TotalOrder := R_TotalOrder)}.
   Add Ring TRing: ComRingTheory.

  Lemma embed_poly_add_compat {d : nat} (p q : (mpoly d)) : embed_poly (a := a) (add p q) == add (embed_poly p) (embed_poly  q).  
Proof.
  simpl.
  induction d.
  simpl.
  apply embed_add_compat.
  revert q. induction p;[simpl;reflexivity|].
  intros.
  destruct q;simpl;try reflexivity.
  apply eqlistA_cons.
  apply IHd.
  apply IHp.
 Defined.

  Lemma embed_poly_mul_compat {d : nat} (p q : (mpoly d)) : embed_poly (a := a) (mul p q) == mul (embed_poly p) (embed_poly  q).  
  Admitted.

  Lemma embed_poly0 {d}: embed_poly (d := d) (a := a) 0 == 0.
  Proof.
    induction d.
    simpl.
    apply embed_0.
    reflexivity.
  Qed.

  Lemma embed_const_to_mpoly_compat d x : const_to_mpoly d (a.(embed) x) == embed_poly (const_to_mpoly d x).
  Proof.
    induction d; try reflexivity.
    simpl.
    rewrite IHd.
    reflexivity.
  Qed.

  Lemma embed_poly_eval_compat {d : nat} (p : (mpoly d)) x : (embed_poly (a:=a) p).[embed_tuple x] == a.(embed) (p.[x]).
  Proof.
    induction d;[simpl;reflexivity|].
    simpl.
    destruct (destruct_tuple x) as [x0 [xr X]].
    rewrite destruct_tuple_cons.
    enough ((map embed_poly p) .{ a.(embed) x0} == (embed_poly (p.{x0}))).
    rewrite meval_proper;try apply H1.
    apply IHd.
    induction p.
    unfold eval_mpoly.
    simpl.
    rewrite embed_poly0;reflexivity.
    simpl.
    unfold eval_mpoly.
    simpl.
    rewrite !embed_poly_add_compat, !embed_poly_mul_compat.
    apply ring_eq_plus_eq;try reflexivity.
    rewrite IHp.
    apply ring_eq_mult_eq; try reflexivity.
    apply embed_const_to_mpoly_compat.
  Qed.
  Lemma mult0_iff0 (x y: target_type) :  (not (x == 0)) -> x * y == 0 -> y == 0.  
  Proof.
     intros.
     setoid_replace y with (1*y) by ring.
     rewrite <-(mulI _ H1).
     rewrite mulA.
     rewrite H2.
     ring.
 Qed.

 Lemma norm_1 : normT.(norm) 1 == 1.
  Proof.
    enough (normT.(norm) 1 * (normT.(norm) 1  -  1) == 0).
    setoid_replace (normT.(norm) 1) with ((normT.(norm) 1 - 1) + 1) by ring.
    apply mult0_iff0 in H1.
    rewrite H1;ring.
    intros H2.
    rewrite norm_zero in H2.
    symmetry in H2.
    contradict H2.
    apply distinct_0_1.
    unfold minus.
    rewrite distrL.
    rewrite <- norm_mult.
    setoid_replace (1*1 : target_type) with (1 : target_type) by ring.
    ring.
  Qed.


  Lemma norm_opp1 : normT.(norm) (opp 1) == 1.
  Proof.
    enough ((normT.(norm) (opp 1) + 1) * (normT.(norm) (opp 1) - 1) == 0).
    apply mult0_iff0 in H1.
    setoid_replace (normT.(norm) (opp 1)) with ((normT.(norm) (opp 1) -1 )+1) by ring.
    rewrite H1;ring.
    intros H2.
    assert (normT.(norm) (opp 1) == (opp 1)).
    setoid_replace (opp 1) with (0 + (opp 1)) at 2 by ring.
    rewrite <-H2;ring.
    pose proof (normT.(norm_nonneg) (opp 1)).
    rewrite H3 in H4.
    apply (le_plus_compat _ _ 1) in H4.
    ring_simplify in H4.
    assert (0 <= 1).
    rewrite <-norm_1.
    apply norm_nonneg.
    pose proof (le_anti_sym _ _ H4 H5).
    symmetry in H6.
    contradict H6.
    apply distinct_0_1.
    ring_simplify.
    rewrite <- norm_mult.
    setoid_replace (opp 1 * opp 1) with (1 : target_type) by ring.
    rewrite norm_1.
    unfold minus. rewrite addI.
    reflexivity.
  Qed.
  
   Lemma norm_opp x : normT.(norm) (opp x) == normT.(norm) (x).
   Proof.
     setoid_replace (opp x) with (opp 1 * x) by ring.
     rewrite norm_mult.
     rewrite norm_opp1.
     ring.
   Qed.

   Lemma dist_sym x y : normT.(norm) (x-y) == normT.(norm) (y-x).
   Proof.
     rewrite <-norm_opp.
     setoid_replace (- (x - y)) with (y - x) by ring.
     reflexivity.
   Qed.

   Instance pme_evaluation {dim dom} : PolynomialModelEvaluation (a := a) dim dom.
   Proof.
     exists (fun (p : (PolynomialModel (a:=a) dim dom)) x => (p.(pm_p).[x], p.(pm_err))).
     intros.
      unfold embed_interval; simpl.
      unfold in_cinterval.
      simpl.
      rewrite <-embed_poly_eval_compat.
      rewrite dist_sym.
      apply p.(pm_spec);auto.
   Defined.

  Definition pme_add {dim dom} : PolynomialModel (a :=a) dim dom -> PolynomialModel (a := a) dim dom -> PolynomialModel (a := a) dim dom. 
Proof.
  intros p1 p2.
  destruct p1,p2.
  exists (pm_p + pm_p0) (fun t => pm_f t + pm_f0 t) (pm_err + pm_err0).
  intros.
  rewrite meval_proper; try apply embed_poly_add_compat.
  rewrite mpoly_add_spec.
  apply (le_trans _ _ _ (metric_distance_plus _ _ _ _ )).
  rewrite embed_add_compat.
  apply le_le_plus_le;auto.
Defined.

Instance pme_addition {d dom}: (PolynomialModelAddition (a :=a) d dom).
Proof.
  exists pme_add.
  intros.
  unfold pm_f, pme_add;simpl.
  destruct p1,p2;reflexivity.
Defined.

Lemma dist_tri x y z: dist x y <= dist x z + dist z y. 
Admitted.
Definition pm_f_diff_bound {d dom} (p : PolynomialModel (a := a) d dom) eps : {b | forall x y, in_cintervalt x dom -> in_cintervalt y dom -> is_eps_close x y eps -> dist (p.(pm_f) x) (p.(pm_f) y) <= (a.(embedE) b)}.  
Proof.
  destruct (boundPolyDiff (embed_poly (p.(pm_p))) dom eps) as [b B].
  assert ({e : error_type | a.(embedE) p.(pm_err) + (b + a.(embedE) p.(pm_err))  <= a.(embedE) e}) as [e E].
  admit.
  exists e.
  intros.
  apply (le_trans _ (embedE p.(pm_err) + (b + a.(embedE) p.(pm_err))));auto.
  destruct p.
  simpl.
  apply (le_trans _ _ _ (dist_tri _ _ (embed_poly pm_p).[x])).
  apply le_le_plus_le;[rewrite dist_sym;apply pm_spec;auto|].
  apply (le_trans _ _ _ (dist_tri _ _ (embed_poly pm_p).[y])).
  apply le_le_plus_le;[apply B|];auto.
Admitted.  

Definition pm_image_contained {d dom m} (ps : (@tuple m (PolynomialModel (a := a) d dom))) (D : @tuple m (@cinterval target_type)) := forall x, in_cintervalt x dom -> (in_cintervalt (tuple_map (fun p => (embed_poly p.(pm_p)).[x]) ps) D) /\ (in_cintervalt (apply_recursive (tuple_map (fun p => (p.(pm_f))) ps) x) D).
Definition pme_compose {d dom1 dom2} (p0 : PolynomialModel (a := a) 1 dom1) (p1 :  @tuple 1 (PolynomialModel (a := a) d dom2)) : pm_image_contained p1 dom1 -> PolynomialModel (a := a) d dom2.
Proof.
  intros.
  destruct (destruct_tuple p1) as [p10 [p1' P1]] eqn:E.
  destruct (pm_f_diff_bound p0 (embedE p10.(pm_err))) as [b B].
  exists (p0.(pm_p) \o (tuple_cons p10.(pm_p) nil_tuple)) (fun x => pm_f_composition p0 p1 x) (a.(additionE) p0.(pm_err) b).
  intros.
  rewrite embed_poly_comp_compat.
  rewrite mpoly_composition_spec.
  
  assert (pm_f_composition p0 p1 x = (p0.(pm_f) (tuple_cons (p10.(pm_f) x) nil_tuple))) as ->.
  {
    unfold pm_f_composition.
    f_equal.
    replace (tuple_map (fun p  => p.(pm_f)) p1) with (tuple_cons (p10.(pm_f)) nil_tuple).
    simpl;reflexivity.
    simpl.
    rewrite E.
    reflexivity.
  }
   unfold pm_image_contained in H1.
   simpl in H1.
   rewrite E in H1.
  apply (le_trans _ _ _ (dist_tri _ _ (p0.(pm_f) (tuple_cons (embed_poly p10.(pm_p)).[x] nil_tuple)))).
  rewrite embedE_add_compat.
  apply le_le_plus_le.
   apply p0.(pm_spec).
   apply H1;auto.
   apply B.
   apply H1;auto.
   apply H1;auto.
   simpl.
   split;auto.
   apply (p10.(pm_spec));auto.
Defined.
