Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import polynomial polyapprox.

Section Exact.

Context {base_type : Type} {target_type : Type} {error_type : Type}  `{semiRingB : comSemiRing base_type}  `{TotallyOrderedFieldT : TotallyOrderedField target_type} `{semiRingE : comSemiRing error_type}.
  Add Ring TRing: ComRingTheory.
  Context `{normT : @NormedSemiRing target_type target_type  _ _ _ _ _}.

  Context {approx : (ApproximationStructure base_type target_type error_type)}.
  Lemma embed_add_compat (p q: base_type) :  embed (p+q) = embed p + embed q.
  Admitted.

  Lemma embedE_add_compat (p q: error_type) :  approx.(embedE) (p+q) = approx.(embedE) p + approx.(embedE) q.
  Admitted.

  Lemma embed_poly_add_compat {d : nat} (p q : (mpoly d)) : embed_poly approx (add p q) = add (embed_poly approx p) (embed_poly approx q).  
Proof.
  simpl.
  induction d.
  simpl.
  apply embed_add_compat.
  revert q. induction p;[simpl;auto|].
  intros.
  destruct q;simpl;auto.
  f_equal.
  apply IHd.
  apply IHp.
Defined.
Lemma metric_distance_plus a b c d: dist (a+b) (c+d) <= dist a c + dist b d.
Proof.
  unfold dist.
  setoid_replace (a+b - (c+d)) with ((a-c) + (b-d)) by ring.
  apply norm_triangle.
  Qed.

  #[global] Instance dist_proper : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) dist.
  Proof.
  intros a b P0 c d P1.
  apply norm_proper.
  rewrite P0,P1;reflexivity.
  Defined.
Definition pme_add {dim dom} : PolynomialModel approx dim dom -> PolynomialModel approx dim dom -> PolynomialModel approx dim dom. 
Proof.
  intros p1 p2.
  destruct p1,p2.
  exists (@add _ _ _ pm_p pm_p0) (fun t => pm_f t + pm_f0 t) (pm_err + pm_err0).
  intros.
  rewrite embed_poly_add_compat.
  rewrite mpoly_add_spec.
  rewrite embedE_add_compat.
  apply (le_trans _ _ _ (metric_distance_plus _ _ _ _ )).
  apply le_le_plus_le;auto.
Defined.
