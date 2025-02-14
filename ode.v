Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import Classical.


Definition tuple_map {n A B} (f : A -> B) (x : @tuple n A) : @tuple n B.
Proof.
  induction n.
  apply nil_tuple.
  destruct (destruct_tuple x) as [hd [tl P]].
  apply (tuple_cons (f hd) (IHn tl)).
 Defined.



 Lemma tuple_nth_ext {n A} (x y : @tuple n A) d : (forall n, tuple_nth n x d = tuple_nth n y d) -> x = y.
 Proof.
   intros.
   destruct x, y.
   simpl in H.
   apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
   apply (nth_ext _ _ d d);auto;lia.
 Qed.

 Lemma eqlistA_nth_ext {A} {A_setoid : Setoid A} l1 l2 d1 d2 : (eqlistA SetoidClass.equiv l1 l2) <-> (length l1 = length l2 /\ forall n, n < length l1 -> nth n l1 d1 == nth n l2 d2).
 Proof.
   intros.
   split;intros;[split|].
   - apply (@eqlistA_length A SetoidClass.equiv);auto.
   - intros.
     generalize dependent n.
     induction H.
     intros.
     simpl in H0;lia.
     destruct n.
     simpl;auto.
     intros.
     simpl.
     apply IHeqlistA.
     simpl in H1;lia.
  - destruct H.
    generalize dependent l1.
    induction l2;intros.
    + simpl in H.
      apply length_zero_iff_nil in H.
      rewrite H.
      reflexivity.
    + destruct l1.
      simpl in H.
      lia.
      apply eqlistA_cons.
      specialize (H0 0%nat).
      simpl in H0.
      apply H0;lia.
      apply IHl2.
      simpl in H;lia.
      intros.
      specialize (H0 (S n)).
      simpl in H0.
      apply H0.
      lia.
  Qed.

 Lemma tuple_nth_ext' {n A} {A_setoid : Setoid A} (x y : @tuple n A) d1 d2 : (forall i, (i < n) -> tuple_nth i x d1 == tuple_nth i y d2) -> x == y.
 Proof.
   intros.
   destruct x, y.
   simpl in H.
   unfold SetoidClass.equiv.
   simpl.
   rewrite eqlistA_nth_ext;split;try lia.
   intros.
   apply H;lia.
 Qed.

Section PIVP.
  Context `{CompositionalDiffAlgebra} .
  Definition multi_composition {n m r} (ps : (@tuple r (A n))) (qs : @tuple n (A m)) : (@tuple r (A m)).
Proof.
  induction r.
  apply nil_tuple.
  destruct (destruct_tuple ps) as [hd [tl P]].
  apply (tuple_cons (hd \o qs) (IHr tl)).
  Defined.

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

 Lemma tuple_nth_nil {T} n (t : (@tuple 0 T)) d : (tuple_nth n t d) = d.
 Proof.
   destruct t.
   simpl.
   apply nth_overflow.
   lia.
 Defined.
 Lemma tuple_nth_cons_hd {T m} (hd : T) (t : (@tuple m T)) d : (tuple_nth 0 (tuple_cons hd t) d) = hd.
 Proof.
   destruct t;simpl;auto.
 Defined.

 Lemma tuple_nth_cons_tl {T m} n (hd : T) (t : (@tuple m T)) d : (tuple_nth (S n) (tuple_cons hd t) d) = tuple_nth n t d.
 Proof.
   destruct t;simpl;auto.
 Defined.

 Lemma tuple_nth_multicomposition {n m r} i d (ps : (@tuple r (A n))) (qs : @tuple n (A m)) : (i < r)%nat -> tuple_nth i (multi_composition ps qs) d = (tuple_nth i ps 0) \o qs.
 Proof.
   revert i.
  induction r;intros; try lia.
  simpl.
  destruct (destruct_tuple ps) as [hd [tl P]].
  destruct ps.
  destruct i.
  rewrite tuple_nth_cons_hd.
  simpl in *.
  rewrite P;auto.
  rewrite tuple_nth_cons_tl.
  rewrite IHr; try lia.
  simpl in *.
  rewrite P.
  destruct tl; simpl;auto.
 Qed.

 Lemma proj1_sig_tuple_cons {T n} x (y: @tuple n T) : proj1_sig (tuple_cons x y) = x :: (proj1_sig y).
 Proof.
   destruct y.
   simpl;auto.
 Qed.

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

  Definition IVP_solution_derivatives {d} f y : @is_IVP_solution_series d f y -> forall n,  {fn | nth_derivative y n == multi_composition fn y}.
  Proof.
     intros.
     enough (forall i, (i < d)%nat -> {fi  | (fi \o y ) == tuple_nth i (nth_derivative y n) 0}).
     {
       destruct (tuple_choice_P _ X 0).
       exists x.
       apply (tuple_nth_ext' _ _ 0 0).
       intros.
       rewrite tuple_nth_multicomposition;try lia.
       rewrite (e _ H5).
       destruct (X i H5);rewrite e0;reflexivity.
     }
     intros.
     induction n.
     simpl.
     exists (comp1 i).
     apply composition_id.
     rewrite tuple_nth_nth_derivative_S;auto.
     destruct IHn as [fn P].
     exists (sum (fun i => tuple_nth i f 0 * (D[i] fn)) d).
     destruct d; try lia.
     pose proof (pdiff_chain fn y (d := 0)).
     rewrite <-P.
     rewrite H6.
     rewrite composition_sum_comp.
     apply sum_ext; intros.
     rewrite composition_mult_comp.
     rewrite <- derive_tuple_nth; try lia.
     rewrite H4.
     rewrite tuple_nth_multicomposition;try lia.
     reflexivity.
   Defined.
End PIVP.

