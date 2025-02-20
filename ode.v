Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.

Require Import powerseries.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import Classical.




 Lemma tuple_nth_ext {n A} (x y : @tuple n A) d : (forall n, tuple_nth n x d = tuple_nth n y d) -> x = y.
 Proof.
   intros.
   destruct x, y.
   simpl in H.
   apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
   apply (nth_ext _ _ d d);auto;lia.
 Qed.


Section PIVP.
  Context `{CompositionalDiffAlgebra} .

 Definition derive_tuple {d} (y : @tuple d (A 1)) :  @tuple d (A 1).
 Proof.
   induction d.
   apply nil_tuple.
  destruct (destruct_tuple y) as [hd [tl P]].
   apply (tuple_cons (pdiff 0 hd) (IHd tl)).
 Defined.


 Definition nth_derivative {d} (y : @tuple d (A 1)) (n : nat) :  @tuple d (A 1).
 Proof.
   induction n.
   apply y.
   apply (derive_tuple IHn).
 Defined.


 Lemma derive_tuple_cons {m} x (y : @tuple m (A 1)) : derive_tuple (tuple_cons x y) = tuple_cons (pdiff 0 x) (derive_tuple y).

 Proof.
   induction m.
   destruct y;apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;auto.
   simpl.
   destruct (destruct_tuple (tuple_cons x y)) as [hd [tl P]].
   rewrite proj1_sig_tuple_cons in P.
   injection P;intros.
   rewrite H5.
   f_equal;auto.
   enough (y = tl) as -> by auto.
   apply eq_sig_hprop;auto.
   intros.
   apply proof_irrelevance. 
 Qed.

 Lemma derive_tuple_nth {m} n (y : @tuple m (A 1)) d   : (n < m)%nat -> tuple_nth n (derive_tuple y) d = pdiff 0 (tuple_nth n y d).
  Proof.
     intros.
     revert dependent n.
     induction m;intros; try lia.
     destruct (destruct_tuple y) as [hd [tl P]].
     replace y with (tuple_cons hd tl) by (destruct y;destruct tl;apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;auto).
     rewrite derive_tuple_cons.
     destruct n.
     rewrite !tuple_nth_cons_hd;auto.
     rewrite !tuple_nth_cons_tl;auto.
     rewrite IHm;auto;lia.
  Qed.

  Definition is_IVP_solution_series {d} f (y : @tuple d (A 1)) := derive_tuple y = multi_composition f y.

   Definition tuple_choice_P {T d} P (Hp : (forall i, (i < d)%nat -> {x : T  | P x i})): forall x, {t : (@tuple d T) | forall i (lt : (i < d)%nat), tuple_nth i t x =  proj1_sig (Hp i lt) }.
   Proof.
     intros.
     revert dependent P.
     induction d;intros.
     exists nil_tuple.
     intros;lia.
     assert (forall i, i < d -> (S i) < (S d)) by lia.
     enough {t : (tuple d) | forall i (lt' : i < d), tuple_nth i t x = proj1_sig (Hp (S i) (H4 _ lt'))} as [t0 T0].
     {
       assert (0 < S d)%nat by lia.
       exists (tuple_cons (proj1_sig (Hp 0%nat H5)) t0).
       intros.
       destruct i.
       rewrite tuple_nth_cons_hd;simpl.
       replace H5 with lt by apply proof_irrelevance;auto.
       rewrite tuple_nth_cons_tl.
       assert (i < d)%nat by lia.
       rewrite (T0 _ H6).
       replace (H4 i H6) with lt by apply proof_irrelevance;auto.
     }
     assert (Hp' : forall i, i < d -> {x : T | forall lt', proj1_sig (Hp (S i) (H4 i lt')) = x}).
     {
       intros.
       destruct (Hp (S i) (H4 _ H5)) eqn:E.
       exists x0.
       intros.
       replace lt' with H5 by apply proof_irrelevance.
       rewrite E;auto.
     }
     destruct (IHd _ Hp').
     exists x0.
     intros.
     rewrite (e _ lt').
     destruct (Hp' i lt').
     simpl; rewrite e0;auto.
   Qed.

   Lemma tuple_nth_nth_derivative_S {d} n m (t : tuple d) x : (n < d)%nat -> tuple_nth n (nth_derivative t (S m)) x = pdiff 0 (tuple_nth n (nth_derivative t m) x).
   Proof.
     intros.
     simpl.
     rewrite derive_tuple_nth;auto.
   Defined.

   Fixpoint IVP_Di {d} (f : @tuple d (A d)) (n i : nat) :=
     match n with
     | 0%nat => (comp1 i)
     | (S n') => (sum (fun j => tuple_nth j f 0 * (D[j] (IVP_Di f n' i))) d)
   end.

   Definition IVP_Di_spec {d} f n: forall i y,  (i < d)%nat ->  @is_IVP_solution_series d f y -> ((IVP_Di f n i) \o y ) == tuple_nth i (nth_derivative y n) 0.
   Proof.
     intros.
     induction n.
     simpl.
     apply composition_id.
     rewrite tuple_nth_nth_derivative_S;auto.
     destruct d; try lia.
     pose proof (pdiff_chain (IVP_Di f n i) y (d := 0)).
     simpl.
     rewrite <-IHn.
     rewrite H6.
     rewrite composition_sum_comp.
     apply sum_ext; intros.
     rewrite composition_mult_comp.
     rewrite <- derive_tuple_nth; try lia.
     rewrite H5.
     rewrite tuple_nth_multicomposition;try lia.
     reflexivity.
  Defined.

   Definition IVP_D {d} (f :@tuple d (A d)) (n :nat) : @tuple d (A d).
   Proof.
     destruct (seq_to_tuple (IVP_Di f n) d (def := 0)).
     apply x.
   Defined.

   Lemma IVP_D_nth {d} f n i : i < d -> tuple_nth i (@IVP_D d f n) 0 = IVP_Di f n i. 
   Proof.
     intros.
     unfold IVP_D.
     destruct (seq_to_tuple _ _ ).
     rewrite e;auto.
   Qed.

  Definition IVP_D_spec {d} f :  forall n y, @is_IVP_solution_series d f y -> nth_derivative y n == (IVP_D f n) \o\ y.
  Proof.
     intros.
     apply (tuple_nth_ext' _ _ 0 0).
     intros.
     rewrite tuple_nth_multicomposition;try lia.
     unfold IVP_D.
     destruct (seq_to_tuple _ _).
     rewrite e;try lia.
     rewrite IVP_Di_spec;auto.
     reflexivity.
   Qed.
  

End PIVP.


Section OdeBounds.
  Context `{AbstractFunction }.
  Context `{TotallyOrderedField (A := (A 0%nat)) (H := (H 0%nat)) (R_rawRing := (H0 0%nat)) (R_semiRing := (H1 0%nat))}. 
  Context `{normK : (NormedSemiRing (A 0) (A 0) (H := (H 0)) (H0 := (H 0)) (R_rawRing := (H0 0%nat)) (R_rawRing0 := (H0 0%nat)) (R_TotalOrder := R_TotalOrder))}.
(* {domain : @tuple d (@cinterval (A 0))}  *)
  Context {d : nat} (f : A[d;d])  (y0 : A[d;0%nat]) (dom_f : y0 \in_dom f).

  Definition inv_factorial (n : nat) : (A 0).
  Proof.
    induction n.
    apply 1.
    apply (inv (char0 n) * IHn).
  Defined.

  Notation "![ n ]" := (inv_factorial n).

  Lemma dom_D : forall n, y0 \in_dom (IVP_D f n).
  Proof.
    intros.
    induction n;intros i Hi;rewrite IVP_D_nth;auto;[apply dom_id|].
    simpl.
    destruct d; try lia.
    apply dom_sum;intros.
    apply dom_mult.
    apply dom_f;lia.
    apply dom_diff.
    rewrite <- IVP_D_nth;try lia.
    apply IHn;lia.
  Qed.

  Definition ivp_solution_taylor (n : nat) : A[d;0%nat] := ![n] ** ([IVP_D f n](y0; (dom_D n))).

  Definition is_IVP_solution y (Hy : 0 \in_dom y) := is_IVP_solution_series f y  /\ [y](0;Hy) == y0.
   
  Lemma  is_IVP_solution_deriv_dom {y Hy}: is_IVP_solution y Hy -> forall n, 0 \in_dom (nth_derivative y n). 
  Proof.
    intros.
    induction n;[apply Hy|].
    intros i Hi.
    rewrite tuple_nth_nth_derivative_S;auto.
    apply dom_diff.
    apply IHn;auto.
  Qed.

  Lemma ivp_solution_taylor_spec n y Hy (S :  is_IVP_solution y Hy) : ivp_solution_taylor n == ![n] ** ([nth_derivative y n](0;(is_IVP_solution_deriv_dom S n))).
  Proof.
    unfold ivp_solution_taylor.
    setoid_replace (([IVP_D f n](y0; dom_D n))) with ([nth_derivative y n](0; is_IVP_solution_deriv_dom S n));try reflexivity.
    destruct S.
    pose proof (IVP_D_spec _ n _ i).
    assert (0 \in_dom (IVP_D f n) \o\ y).
    {
      apply (dom_composition _ y 0 Hy _ e).
      apply dom_D.
    }
    rewrite (meval_proper _ _ _ _ (is_IVP_solution_deriv_dom (conj i e) n) H8 H7);try reflexivity.
    assert (([y](0; Hy)) \in_dom (IVP_D f n)).
    {
      rewrite e.
      apply dom_D.
    }
    rewrite (eval_composition_compat  _ _ _ Hy H9).
    apply meval_proper;try rewrite e;reflexivity.
  Qed.
End OdeBounds.
