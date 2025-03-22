Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import abstractpowerseries.
Require Import functions.
Require Import polynomial.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import Classical.
Require Import tuple.
Require Import combinatorics.
Require Import ode.
Require Import polynomial.

 Open Scope algebra_scope.

Section Bounds.

  Context `{AbstractPowerSeries}.
  Context `{ArchimedeanField (A:=A) (H:=_) (R_rawRing := _) (R_semiRing := _) (invSn := _)}.

  (* Context `{TotallyOrderedField (A := A) (H := _) (R_rawRing := _) (R_semiRing := H0)}. *)
 (* Context `{normK : (NormedSemiRing A A (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }. *)
  
  (* Context `{norm_abs : forall x, 0 <= x -> norm x == x}. *)

  Lemma norm1 : norm 1 == 1.  
  Proof.
    apply norm_abs.
    apply le_0_1.
  Qed.

 Add Ring KRing: (ComRingTheory (A := A)).

(* First the single-variate case *)
 Definition mps_bound {d} (a : (nat^d -> A)) (b : (nat^1 -> A)) := forall n, norm (a n) <= (b t(order n)).
 Notation "| a | <= b" := (mps_bound a b) (at level 70).
 Definition mps_tuple_bound {d} {e} (a : (nat^d -> A )^e) (b : (nat^1 -> A)):=  forall i, i < e -> |a\_i| <= b.

 #[global]Instance mps_bound_proper d : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (@mps_bound d).
   Proof.
     intros a b eq a0 b0 eq'.
     split.
     intros.
     unfold mps_bound.
     intros.
     rewrite index_proper; try rewrite <-eq; try reflexivity.
     symmetry in eq'.
     rewrite (index_proper b0 a0 eq' t(order n)); try reflexivity.
     apply H7.
     unfold mps_bound.
     intros.
     rewrite index_proper; try rewrite eq; try reflexivity.
     rewrite (index_proper a0 b0 eq' t(order n)); try reflexivity.
     apply H7.
   Defined.

   Definition partial_eval {d} (a : nat^(S d) -> A) (n : nat) := (fun k => a (tuple_cons n k)).

   Definition partial_eval_ps1 {d} (a : nat^(S d) -> A) k  (n : nat^1) := (partial_eval a n\_0 k).

   Lemma partial_eval_ps1_spec {d} (a : nat^(S d) -> A) n k : partial_eval a n k = partial_eval_ps1 a k t(n).
   Proof.
     unfold partial_eval_ps1.
     rewrite tuple_nth_cons_hd.
     reflexivity.
   Qed.

   Instance partial_eval_proper {d} : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (partial_eval (d := d)).
   Proof.
     intros a b eq a' b' eq'.
     unfold partial_eval.
     simpl.
     intros k.
     apply index_proper;auto.
     rewrite eq'.
     reflexivity.
   Qed.

   
   Lemma partial_eval_bound {d} (a :  nat^(S d) -> A) (b : (nat^1 -> A)): (forall i, mps_bound (partial_eval a i) (fun n => (b (t(i)+n))))  <-> mps_bound a b.
  Proof.
    split.
    - intros P2 k.
      simpl.
      destruct (destruct_tuple_cons k) as [hd [tl ->]].
      specialize (P2 hd tl).
      simpl in P2.
      apply P2.
   -  intros P1.
      intros i k.
      specialize (P1 (tuple_cons i k)).
      simpl in P1.
      destruct (destruct_tuple_cons (tuple_cons i k)) as [hd' [tl' P']].
      apply tuple_cons_ext in P'.
      destruct P' as [-> ->].
      apply P1.
  Qed.


  Lemma partial_eval_nil  (a : nat^1->A) i (k : nat^0): partial_eval a i k == a t(i).
  Proof.
    unfold partial_eval.
    apply index_proper;try reflexivity.
    rewrite zero_tuple_zero.
    reflexivity.
  Qed.

  Lemma partial_eval_mul_nil  (a : nat^0->A) b (k : nat^0): (a * b) k == a 0  * b 0 .
  Proof.
     rewrite index_proper; try rewrite zero_tuple_zero;try reflexivity.
     rewrite ps_mul0.
     reflexivity.
  Qed.


  Lemma mul_convolution {d} (a b : nat^(S d) -> A) n : partial_eval (a*b) n == sum (fun i => (partial_eval a i) * (partial_eval b (n-i)%nat)) (S n).
  Proof.
    unfold partial_eval.
    intros k.
    apply cauchy_product.
  Qed.

  Lemma partial_eval_mul0 {d} (a b : nat^(S d) -> A) : partial_eval (a*b) 0 == partial_eval a 0 * partial_eval b 0.
  Proof.
    rewrite mul_convolution.
    rewrite sum_1.
    replace (0 - 0)%nat with 0%nat by lia.
    reflexivity.
  Qed.

  Lemma partial_eval_mul0_k {d} (a b : nat^(S d) -> A) k : partial_eval (a*b) 0 k == (partial_eval a 0 * partial_eval b 0) k.
  Proof.
    apply index_proper;try reflexivity.
    apply partial_eval_mul0.
  Qed.

  Lemma partial_eval_S {d} (a : nat^(S d) -> A) n k : partial_eval a (S n) k == (inv_Sn n) * partial_eval (D[0] a) n k.
  Proof.
    unfold partial_eval.
    rewrite deriv_next_backwards.
    apply ring_eq_mult_eq;try reflexivity.
  Qed.

  Lemma partial_eval_D_prod {d} (a b : nat^(S d) -> A) n k : partial_eval (D[0] (a*b)) n k ==  partial_eval (b * D[0] a ) n k + partial_eval (a * D[0] b) n k.
  Proof.
    transitivity (partial_eval (b*D[0] a + a * D[0]b) n k).
    apply partial_eval_proper; try reflexivity.
    apply pdiff_mult.
    unfold partial_eval.
    rewrite index_plus.
    reflexivity.
  Qed.

  Lemma exchange_index {d} (a : nat^d -> A) k k': k == k' -> a k == a k'. 
  Proof.
    apply index_proper;reflexivity.
  Qed.

  Definition coeff_shift1 {d} (a : nat^(S d) ->A ) := (fun n => inv_Sn (n\_0) * (D[0] a n)).
  Definition coeff_shift_inner {d} (a : nat^(S d) ->A ) : coeff_shift1 a ==  D[0] (fun n => inv_Sn (pred (n\_0)) * a n).
  Proof.
    unfold coeff_shift1.
    intros k.
    destruct (destruct_tuple_cons k) as [h [t ->]].
    rewrite (deriv_next (fun n => inv_Sn (pred n\_0) * _)).
    rewrite !(tuple_nth_cons_hd).
    replace (pred (h+1)) with h by lia.
    rewrite deriv_next.
    ring.
  Qed.
  Lemma coeff_shift1_spec {d} (a : nat^(S d) ->A ) n k  : partial_eval (coeff_shift1 a) n k  == partial_eval a (S n) k.  
  Proof.
  rewrite partial_eval_S.
  unfold partial_eval.
  unfold coeff_shift1.
  simpl.
  rewrite tuple_nth_cons_hd.
  reflexivity.
 Qed.

  Lemma coeff_shift1_bound {d} (a : nat^(S d) ->A ) (B: nat^1 -> A) : |a| <= B -> |(coeff_shift1 a)| <= coeff_shift1 B.
  Proof.
    intros.
    apply partial_eval_bound.
    intros i k.
    rewrite index_proper; try rewrite coeff_shift1_spec;try reflexivity.
    rewrite <-partial_eval_bound in H7.
    apply (le_trans _ _ _ (H7 _ _)).
    rewrite !index1_add.
    replace (coeff_shift1 B t( i + order k)) with ((partial_eval (coeff_shift1 B) (i+order k)%nat) nil_tuple) by reflexivity.
    rewrite coeff_shift1_spec.
    setoid_replace (S i + order k)%nat with (S (i+order k))%nat by (simpl;lia).
    unfold partial_eval.
    apply le_refl.
  Qed.

  Lemma coeff_shift1_p {d} {a : nat^(S d) -> A} i : partial_eval (coeff_shift1 a) i == partial_eval a (S i).
  Proof.
    intros k.
    apply coeff_shift1_spec.
  Qed.

  Lemma coeff_shift_mul {d} (a b : nat^(S d) ->A ) i : partial_eval (a*b) (S i)  == partial_eval ((coeff_shift1 a)*b) i + partial_eval a 0 * partial_eval b (S i).
    setoid_replace (a * b) with (b * a) by apply mulC.
    setoid_replace (coeff_shift1 a * b) with (b * coeff_shift1 a) by apply mulC.
    rewrite !mul_convolution.
    rewrite sum_S.
   replace (S i - S i)%nat  with 0%nat by lia.
    apply ring_eq_plus_eq;[|rewrite mulC;reflexivity].
    apply sum_ext.
    intros.
    apply ring_eq_mult_eq;try reflexivity.
    replace (S i - n)%nat with (S (i-n))%nat by lia.
    rewrite coeff_shift1_p.
    reflexivity.
  Qed.

  Lemma coeff_shift_mul1  (a b : nat^1 ->A ) i : (a*b) t(S i)  == ((coeff_shift1 a)*b) t(i) +  a 0 * b t(S i).
  Proof.
    rewrite <-!(partial_eval_nil _ _ 0).
    rewrite index_proper; try apply coeff_shift_mul;try reflexivity.
    rewrite index_plus.
    rewrite ps_mul0.
    reflexivity.
  Qed.

  (* Lemma coeff_shift_mul1  (a b : nat^1 ->A ) i : (a*b) t(S i)  == ((coeff_shift1 a)*b) t(i) +  ((coeff_shift1 b)*a) t(i). *)
  (* Proof. *)
  (*   replace ((a*b) t(S i)) with (partial_eval (a*b) (S i) 0) by auto. *)
  (*   replace (((coeff_shift1 a) * b) t(i)) with (partial_eval ((coeff_shift1 a)*b) i 0) by auto. *)
  (*   replace (((coeff_shift1 b) * a) t(i)) with (partial_eval ((coeff_shift1 b)*a) i 0) by auto. *)
  (*   rewrite index_proper; try apply coeff_shift_mul;try reflexivity. *)
  (*   rewrite index_plus. *)
  (*   reflexivity. *)
  (* Qed. *)

  Lemma mul_convolution1  (a b : nat^1 -> A) n : (a*b) t(n) == sum (fun i =>  a t(i) * (b t(n-i)%nat)) (S n).
  Proof.
    rewrite <-(partial_eval_nil _ _ 0).
    rewrite index_proper; try apply mul_convolution; try reflexivity.
    rewrite index_sum.
    apply sum_ext.
    intros.
    rewrite ps_mul0.
    reflexivity.
  Qed.

 Lemma le_eq x y : (x == y) -> (x <= y).
 Proof.
   intros ->.
   apply le_refl.
 Qed.

   Lemma destruct_tuple1 (k : nat^1) : {h | k = t(h)}.
   Proof.
     destruct (destruct_tuple_cons k) as [h [tl P]].
     exists h.
     rewrite P.
     enough (tl = 0) as -> by auto.
     destruct tl.
     simpl.
     destruct (t()).
     apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
     assert (x0 = []) as ->; (apply length_zero_iff_nil;auto).
   Qed.

  Lemma sum_norm : forall f i, norm (sum f i) <= sum (fun n => (norm (f n))) i.
  Proof.
    intros.
    induction i.
    unfold sum;simpl.
    rewrite (proj2 (norm_zero 0)); try apply le_refl;try reflexivity.
    rewrite !sum_S.
    apply (le_trans _ _ _ (norm_triangle _ _)).
    apply le_plus_compat.
    apply IHi.
  Qed.

  Lemma mult_monotone1  (a b : nat^1 -> A) (A1 B1 : nat^1 -> A) : (|a| <= A1) -> |b| <= B1 -> |a*b| <= A1*B1.
  Proof.
    intros.
    intros k.
    destruct (destruct_tuple1 k) as [i ->].
    generalize dependent A1.
    generalize dependent a.
    induction i;intros.
    - simpl order.
      rewrite !ps_mul0.
      apply (le_trans _ _ _ (norm_mult _ _ )).
      apply (mul_le_le_compat_pos); try apply norm_nonneg;auto.
    - simpl order.
      rewrite !coeff_shift_mul1.
      apply (le_trans _ _ _ (norm_triangle  _ _ )).
      apply le_le_plus_le.
      specialize (IHi (coeff_shift1 a) (coeff_shift1 A1)).
      simpl order in IHi.
      apply IHi.
      apply coeff_shift1_bound;apply H7.
      apply (le_trans _ _ _ (norm_mult _ _ )).
      apply (mul_le_le_compat_pos); try apply norm_nonneg;auto.
   Qed.

  (* Lemma mult_monotone {d} (a b : nat^d -> A) (A1 B1 : nat^1 -> A) : (|a| <= A1) -> |b| <= B1 -> |a*b| <= A1*B1. *)
  (* Proof. *)
  (*   intros. *)
  (*   generalize dependent B1. *)
  (*   generalize dependent A1. *)
  (*   generalize dependent b. *)
  (*   generalize dependent a. *)
  (*   induction d;intros. *)
  (*   - intros k. *)
  (*     rewrite index_proper; [|reflexivity|apply zero_tuple_zero]. *)
  (*     assert (t(order k) == 0) by (rewrite (zero_tuple_zero k);rewrite zero_order;reflexivity). *)
  (*     setoid_rewrite (index_proper (A1*B1) (A1*B1) _ t(order k) 0); [|reflexivity|apply H9]. *)
  (*     rewrite !ps_mul0. *)
  (*     apply (le_trans _ _ _ (norm_mult _ _)). *)
  (*     apply mul_le_le_compat_pos; try apply norm_nonneg. *)
  (*     apply H7. *)
  (*     apply H8. *)
  (*   - intros. *)
  (*     apply partial_eval_bound. *)
  (*     intros i. *)
  (*     rewrite !mul_convolution. *)
  (*     intros k. *)
  (*     rewrite index_sum. *)
  (*     assert (sum_norm : forall f i, norm (sum f i) <= sum (fun n => (norm (f n))) i). *)
  (*     admit. *)
  (*     assert (sum_monotone : forall f g i, (forall j, j < i -> f j <= g j) ->  (sum f i) <= sum g i). *)
  (*     admit. *)
  (*     assert (forall j, j < (S i) -> (norm ((partial_eval a j * (partial_eval b (i-j))) k)) <= ((fun k0 => (A1 (t(j)%nat + k0))) * (fun (k0 : nat^1) => (B1 (t(i-j)%nat + k0)))) t(order k)). *)
  (*     admit. *)
  (*     apply (le_trans _ _ _ (sum_norm _ _)). *)
  (*     apply (le_trans _ _ _ (sum_monotone _ _ _ H9)). *)
  (*     rewrite index1_add. *)
  (*     apply le_eq. *)
  (*     apply ps_mul1_shift. *)
  (*     generalize dependent B1. *)
  (*     generalize dependent A1. *)
  (*     induction (order k);intros. *)
  (*     { *)
  (*       enough (forall j, (((fun k => A1 (t(j) + k ))) * (fun k => B1 (t(i-j)%nat + k))) t(0) == A1 t(j) * B1 t(i-j)%nat  ). *)
  (*       rewrite sum_ext; try (intros;apply H7;auto). *)
  (*       rewrite <-mul_convolution1. *)
  (*       setoid_replace (i+0)%nat with i by (simpl;lia). *)
  (*       reflexivity. *)
  (*       intros. *)
  (*       rewrite ps_mul0. *)
  (*       rewrite index_proper; try apply add0;try reflexivity. *)
  (*       rewrite (exchange_index B1); try apply add0. *)
  (*       reflexivity. *)
  (*     } *)
  (*     assert (forall j, (((fun k => A1 (t(j) + k ))) * (fun k => B1 (t(i-j)%nat + k))) t(S n) == (((fun k => (coeff_shift1 A1) (t(j) + k ))) * (fun k => B1 (t(i-j)%nat + k))) t(n) +  A1 t(j) * B1 t(i-j + S n)%nat). *)
  (*     { *)
  (*       intros. *)
  (*       rewrite coeff_shift_mul1. *)
  (*       apply ring_eq_plus_eq. *)
  (*       apply index_proper; try reflexivity. *)
  (*       apply ring_eq_mult_eq; try reflexivity. *)
  (*       intros k0. *)
  (*       destruct (destruct_tuple1 k0) as [n0  ->]. *)
  (*       rewrite index1_add. *)
  (*       rewrite <-!(partial_eval_nil _ _ 0). *)
  (*       rewrite !coeff_shift1_spec. *)
  (*       rewrite !partial_eval_nil. *)
  (*       rewrite index1_add. *)
  (*       setoid_replace (j + S n0)%nat with (S (j + n0))%nat by (simpl;lia). *)
  (*       reflexivity. *)
  (*       rewrite index1_add. *)
  (*       setoid_replace ((i-j)+S n)%nat with (i-j + S n)%nat by (simpl;lia). *)
  (*       apply ring_eq_mult_eq; try reflexivity. *)
  (*       apply index_proper;try rewrite add0; try reflexivity. *)
  (*     } *)
  (*     rewrite sum_ext; try (intros;apply H7). *)
  (*     assert (sum_sum : forall f f1 f2 n , (forall j, j < i -> f j == f1 j + f2 j) -> sum f n == sum f1 n + sum f2 n). *)
  (*     admit. *)
  (*     rewrite (sum_sum _ (fun j => ((fun k => ((coeff_shift1 A1 (t(j) + k )))) * (fun k => B1 (t(i-j)%nat + k))) t(n)) (fun j => A1 t(j) * B1 (t(i-j+S n)%nat)));[|intros;reflexivity]. *)
  (*     rewrite IHn. *)
  (*     setoid_replace (i + S n)%nat with (S (i+n))%nat by (simpl;lia). *)
  (*     rewrite coeff_shift_mul1. *)
  (*     apply ring_eq_plus_eq; try reflexivity. *)
      
  (*     rewrite sum_S. *)
  (*     rewrite <-(partial_eval_nil _ _ 0). *)
  (*     Check mul_convolution. *)
  (*     simpl add. *)
  (*     rewrite (mul_convolution A1 B1 (i+order k) 0). *)
      
  (*     generalize dependent B1. *)
  (*     generalize dependent A1. *)
  (*     generalize dependent b. *)
  (*     generalize dependent a. *)
  (*     induction i;intros. *)
  (*     {        *)
  (*       rewrite partial_eval_mul0. *)
  (*      specialize (IHd (partial_eval a 0) (partial_eval b 0)). *)
  (*      assert ((fun n => (A1 * B1) (t(0)+n)) == A1*B1) as ->. *)
  (*      { *)
  (*        intros n. *)
  (*        apply index_proper; try reflexivity. *)
  (*        setoid_rewrite <-zero_tuple1. *)
  (*        rewrite addC,add0;reflexivity. *)
  (*      } *)
  (*      apply IHd;auto. *)
  (*       + intros k. *)
  (*         apply (le_trans _ _ _ (H7 _)). *)
  (*         rewrite order_cons. *)
  (*         replace (0+order k)%nat with (order k) by lia. *)
  (*         apply le_refl. *)
  (*       + intros k. *)
  (*         apply (le_trans _ _ _ (H8 _)). *)
  (*         rewrite order_cons. *)
  (*         replace (0+order k)%nat with (order k) by lia. *)
  (*         apply le_refl. *)
  (*     } *)
  (*     rewrite coeff_shift_mul. *)
  (*     intros k. *)
  (*     rewrite index1_add. *)
  (*     setoid_replace (S i + order k)%nat with (S (i+order k)%nat) by (simpl;lia). *)
  (*     rewrite coeff_shift_mul1. *)
  (*     rewrite index_plus. *)
  (*     apply (le_trans _ _ _ (norm_triangle _ _ )). *)
  (*     apply le_le_plus_le. *)
  (*   + specialize (IHi _  _ _ (coeff_shift1_bound _ _ H7) _ H8 k). *)
  (*     apply (le_trans _ _ _ IHi). *)
  (*     rewrite index1_add. *)
  (*     apply le_refl. *)
  (*   + apply (le_trans  _ _ _ (coeff_shift0 _ _ _ _)). *)
  (*     pose proof (proj2 (partial_eval_bound a A1) H7 0). *)
  (*     pose proof (proj2 (partial_eval_bound b B1) H8 (S i)). *)
  (*     specialize (IHd (partial_eval a 0) (partial_eval b (S i)) _ H9 _ H10 k). *)
  (*     apply (le_trans _ _ _ IHd). *)
  (*     (* assert (((fun n => A1 (t( 0) + n)) *(fun n => B1 (t( S i) + n))) t( order k) == A1 * (fun B1 t(S ))) *) *)
  (*     clear H9 IHi IHd. *)
  (*     induction (order k). *)
  (*     rewrite ps_mul0. *)
  (*     apply le_refl. *)
  (*     rewrite coeff_shift_mul1. *)
  (*     rewrite <-(add0 ((A1 0) *_)). *)
  (*     rewrite (addC ((A1 0) *_)). *)
  (*     apply le_plus_compat. *)
      
  (*     specialize (IHi _  _ _ (coeff_shift1_bound _ _ H8) _ H7 k). *)
  (*     apply (le_trans _ _ _ IHi). *)
  (*     rewrite index1_add. *)
  (*     apply le_refl. *)
  (*   Qed. *)

  
    Lemma norm_zero_eq : norm 0 == 0.
    Proof.
        setoid_replace (norm 0) with 0 by (rewrite norm_zero;reflexivity).
        apply reflexivity.
     Qed.

   Lemma sum_monotone {d} (a : nat -> nat^d ->A ) (b: nat -> nat^1 -> A) N : (forall n, (n < N) -> |a n| <= b n) -> |(sum a N)| <= sum b N.
   Proof.
     intros.
     induction N.
     unfold sum.
     simpl.
     intros k.
     rewrite !ps0.
     rewrite norm_zero_eq.
     apply le_refl.
     rewrite !sum_S.
     intros k.
     rewrite !index_plus.
     apply (le_trans _ _ _ (norm_triangle _ _)).
     apply le_le_plus_le.
     apply IHN.
     intros;apply H7;lia.
     apply H7.
     lia.
   Qed.

   Lemma sum_same {d} (a : nat -> (nat^d -> A)) (b: (nat^1 -> A)) N : (forall n, (n < N) -> |a n| <= b) -> |(sum a N)| <= ntimes N b. 
   Proof.
     intros.
     enough (ntimes N b == sum (fun _ => b) N) as ->.
     apply sum_monotone.
     apply H7.
     induction N.
     simpl.
     intros.
     unfold sum.
     simpl.
     reflexivity.
     rewrite !sum_S.
     Opaque add.
     simpl ntimes.
     rewrite IHN.
     rewrite addC.
     reflexivity.
     intros.
     apply H7.
     lia.
     Transparent add.
  Qed.

    Lemma Fi_S {d :nat} (a : (nat ^d -> A)^d) (i n : nat) : (Fi (H3:=H4) a (S n) i) == (sum (fun j => (tuple_nth j a 0) * (D[j] (Fi (H3 := H4) a n i))) d).
    Proof.
      simpl;auto.
      reflexivity.
    Qed.

  Lemma norm_n_le_n n : norm (ntimes n 1) <= ntimes n 1.
  Proof.
    induction n.
    simpl.
    assert (norm 0 == 0) as -> by (apply norm_zero;reflexivity).
    apply le_refl.
    simpl.
    apply (le_trans _ _ _ (norm_triangle _ _ )).
    rewrite norm1.
    apply le_le_plus_le;auto.
    apply le_refl.
  Qed.

  Lemma norm_ntimes_le n x : norm (ntimes n x) <= ntimes n 1 * norm x.
  Proof.
    induction n.
    simpl.
    assert (norm 0 == 0) as -> by (apply norm_zero;reflexivity).
    ring_simplify.
    apply le_refl.
    simpl.
    apply (le_trans _ _ _ (norm_triangle _ _ )).
    ring_simplify.
    rewrite addC.
    apply le_plus_compat.
    rewrite mulC.
    apply IHn.
  Qed.
  Lemma norm_ntimes_le_ntimes_norm n x : norm (ntimes n x) <= ntimes n (norm x).
  Proof.
    apply (le_trans _ _ _ (norm_ntimes_le _ _)).
    rewrite mulC, <-ntimes_mult.
    rewrite mul1.
    apply le_refl.
  Qed.

  Lemma ntimes_monotone  n m: (n <= m)%nat -> (# n <= # m). 
  Proof.
    simpl.
    induction m.
    intros.
    assert (n = 0)%nat as -> by lia.
    apply le_refl.
    intros.
    assert (n <= m \/ n = S m)%nat by lia.
    destruct H8.
    simpl.
    setoid_replace (#n) with (0 + #n) by ring.
    apply le_le_plus_le.
    apply le_0_1.
    apply IHm;auto.
    rewrite H8.
    apply le_refl.
  Qed.

  Lemma ntimes_pos_monotone  n m x : (0 <= x) ->  (n <= m)%nat -> (ntimes n x <= ntimes m x). 
  Proof.
    intros.
    setoid_replace (x) with (x*1) by ring.
    rewrite !ntimes_mult.
    apply mul_le_compat_pos;auto.
    apply ntimes_monotone;auto.
  Qed.

  Lemma ntimes_monotone2  n x y :  (x <= y) -> (ntimes n x <= ntimes n y). 
  Proof.
    simpl.
    intros.
    setoid_replace (x) with (x*1) by ring.
    setoid_replace (y) with (y*1) by ring.
    rewrite !ntimes_mult.
    rewrite (mulC x), (mulC y).
    apply mul_le_compat_pos;try apply ntimes_nonneg;try apply le_0_1;auto.
  Qed.

  Lemma diff0_monotone {d} (a : (nat^(S d) ->A)) b : |a| <= b ->  (|pdiff 0 a| <=  pdiff 0 b).
  Proof.
       intros Hb.
       intros k.
       destruct (destruct_tuple_cons k) as [hd [tl ->]].
       rewrite !deriv_next.
       apply (le_trans _ _ _ (norm_mult _ _)).
       apply (mul_le_le_compat_pos); try apply ntimes_nonneg; try apply le_0_1; try apply norm_nonneg.
       apply (le_trans _ _ _ (norm_n_le_n _)).
       apply ntimes_monotone.
       rewrite order_cons.
       lia.
       replace (order (tuple_cons hd tl) + 1)%nat with (order (tuple_cons (hd+1) tl))%nat  by (rewrite !order_cons;lia).
       apply Hb.
 Qed.


  Lemma bound_nonneg {d} (a : (nat^(S d) -> A )) b : (|a| <= b) -> forall i, 0 <= (b i). 
  Proof.
    intros.
    destruct (destruct_tuple_cons i) as [h [tl P]].
    enough ({t : nat^(S d) | order t = h}) as [t T].
    {
      specialize (H7 t).
      rewrite T in H7.
      apply (le_trans _ _ _ (norm_nonneg  (a t))).
      apply (le_trans _ _ _ H7).
      rewrite P.
      apply le_eq.
      apply index_proper;try reflexivity.
      enough (tl == 0) as ->.
      reflexivity.
      apply zero_tuple_zero.
    }
    clear a b H7.
    induction d.
    exists (tuple_cons h nil_tuple).
    simpl;lia.
    destruct IHd.
    exists (tuple_cons 0%nat x).
    rewrite order_cons.
    lia.
  Qed.



    (* Lemma F_monotone {d :nat} (a : (nat^d -> A)^d) (b : (nat^1 -> A)^1) n : (mps_tuple_bound a b\_0) -> (mps_tuple_bound (F a n) (tuple_nth 0 (F (ntimes d b) n) 0)). *)
    (* Proof. *)
    (*    intros. *)
    (*    induction n;intros i ile. *)
    (*    - simpl. *)
    (*      pose proof (id_nth (d:=d) i). *)
    (*      rewrite H8;auto. *)
    (*      apply comp1_bound. *)
    (*    - rewrite !(F_nth (H3 := H4));try lia;auto. *)
    (*      assert (0 < 1)%nat by lia. *)
    (*      pose proof (F_nth (ntimes d b) (S n) _ H8). *)
    (*      intros k. *)
    (*      pose proof (index_proper _ _ H9 t(order k) t(order k)). *)
    (*      rewrite <-H10;try reflexivity. *)
    (*      rewrite index_proper; try apply Fi_S; try reflexivity. *)
    (*      enough (forall j, j < d -> |(tuple_nth j a 0) * (D[j] (Fi (H3 := H4) a n i))| <= (tuple_nth 0 b 0 * D[0] (Fi  (H3 := H4) (ntimes d b) n 0))). *)
    (*      { *)
    (*        pose proof (sum_same (fun j => tuple_nth j a 0 * D[j] (Fi (H3:=H4) a n i)) _ d H11). *)
    (*        apply (le_trans _ _ _ (H12 _)). *)
           
    (*        rewrite (index_proper _ _ (F_nth  _ _ _ H8) t(order k) t(order k)); try reflexivity. *)
    (*        rewrite (index_proper _ _ (Fi_S  _ _ _) t(order k) t(order k)); try reflexivity. *)
    (*        unfold sum. *)
    (*        Opaque add zero pdiff order tuple_cons. *)
    (*        simpl fold_right. *)
    (*        apply le_eq. *)
    (*        apply index_proper; try reflexivity. *)
    (*        rewrite add0. *)
    (*        setoid_rewrite  <-(ntimes_nth b);auto. *)
    (*        rewrite (mulC (ntimes _ _)). *)
    (*        rewrite <-ntimes_mult. *)
    (*        rewrite (mulC (D[0] _ )). *)
    (*        reflexivity. *)
    (*        Transparent add zero pdiff order tuple_cons. *)
    (*      } *)
    (*      intros. *)
    (*      intros l. *)
    (*      apply mult_monotone. *)
    (*      intros k';apply H7;auto. *)
    (*      apply diff_monotone;auto. *)
    (*      intros i0. *)
    (*      specialize (IHn i ile i0). *)
    (*      rewrite index_proper in IHn; try apply (F_nth (H3 := H4)); try reflexivity;auto. *)
    (*      apply (le_trans _ _ _ IHn). *)
    (*      apply le_eq. *)
    (*      apply index_proper;try reflexivity. *)
    (*      rewrite (F_nth (H3 := H4));try lia. *)
    (*      reflexivity. *)
    (*  Qed. *)

  Definition f_bound C r k := C * npow r k.
  Definition g_bound C n r k := C * [(k+1)!2*n+1] * npow r k.
  Definition fg_bound C1 C2 r n k := inv_Sn (2*n+1)  *  C1*C2 *  [(k+1)!2*n+2] * npow r k.

   Lemma f_bound_S r C : (fun n => (f_bound C r (S n))) == (f_bound (C*r) r).
   Proof.
       intros n.
       unfold f_bound.
       simpl.
       ring.
   Qed.

   Definition to_ps (f : nat -> A) (k : nat^1) := f k\_0.

   Notation "| a | <= b" := (mps_bound  a b) (at level 70).

  (* Lemma ps_mult_monotone (a b : nat^1 -> A) (a' b' : nat^1 ->A) : (|a| <= a') -> |b| <= b' -> |a*b| <= a' * b'. *)
  (* Proof. *)
  (*  intros. *)
  (*  generalize  dependent a'. *)
  (*  generalize  dependent a. *)
  (*  induction k;intros. *)
  (*  simpl. *)
  (*  unfold mult_ps, powerseries.convolution_coeff;simpl. *)
  (*  ring_simplify. *)
  (*  rewrite add0. *)
  (*  apply (le_trans _ _ _ (norm_mult _ _)). *)
  (*  apply (mul_le_le_compat_pos);try apply norm_nonneg;auto. *)
  (*  simpl. *)
  (*  rewrite !mult_ps_S. *)
  (*  apply (le_trans _ _ _ (norm_triangle _ _ )). *)
  (*  apply le_le_plus_le;auto. *)
  (*  apply (le_trans _ _ _ (norm_mult _ _)). *)
  (*  apply (mul_le_le_compat_pos);try apply norm_nonneg;auto. *)
  (*  apply IHk. *)
  (*  intros;auto. *)
  (* Qed. *)

   Lemma order1d k: order (t(k)) = k.
   Proof. simpl; lia. Qed.

   Lemma to_ps_simpl a k : to_ps a t(k) = a k.
   Proof.
     simpl;auto.
   Qed.

   Lemma to_ps_simpl0 a : to_ps a 0 = a 0.
   Proof.
     simpl;auto.
   Qed.

   Lemma to_ps_simpl2 a k k' : to_ps a (tuple_cons k k') = a k.
   Proof.
     simpl;auto.
     destruct (destruct_tuple1 (tuple_cons k k')) as [k0 E].
     apply tuple_cons_ext in E.
     destruct E as [_ ->].
     apply to_ps_simpl.
   Qed.

   Lemma f_shift1 C1 r : (coeff_shift1 (to_ps (f_bound C1 r))) == (to_ps (f_bound (C1*r) r)).
   Proof.
     intros k.
     destruct (destruct_tuple_cons k) as [hd [tl ->]].
     pose proof (coeff_shift1_spec (to_ps (f_bound C1 r)) hd tl).
     rewrite H7.
     unfold partial_eval.
     rewrite !to_ps_simpl2.
     apply f_bound_S.
   Qed.

   Lemma shift1_to_ps f : (coeff_shift1 (to_ps f)) == (to_ps (fun n => f (S n))).
   Proof.
     intros k.
     destruct (destruct_tuple_cons k) as [hd [tl ->]].
     pose proof (coeff_shift1_spec (to_ps f) hd tl).
     rewrite H7.
     unfold partial_eval.
     rewrite !to_ps_simpl2.
     reflexivity.
   Qed.

  Lemma mul_ps_S  (a b : nat^1 -> A) n :  (a*b) t(S n) == (a t(0)) * b t((S n)) + ((coeff_shift1 a) * b) t(n).
  Proof.
    pose proof (coeff_shift_mul1 a b n).
    rewrite H7.
    rewrite addC.
    reflexivity.
  Qed.

   Lemma fg_bounded (a b : nat^1 -> A ) C1 C2 r n : |a| <= to_ps (f_bound C1 r) -> |b| <= to_ps (g_bound C2 n r )-> |a*b| <= to_ps (fg_bound C1 C2 r n).
   Proof.
     intros.
     pose proof (mult_monotone1  _ _ _ _ H7 H8).
     intros k.
     destruct (destruct_tuple1 k).
     rewrite e.
     apply (le_trans _ _ _ (H9 _)).
     apply le_eq.
     clear H7 H8 H9 e k.
     rename x into k.
     rewrite order1d.
     rewrite to_ps_simpl.
     generalize dependent C1.
     induction k;intros.
     - rewrite ps_mul0.
       rewrite !to_ps_simpl0.
       unfold f_bound, g_bound, fg_bound.
       simpl.
       ring_simplify.
       replace  (n + (n+0)+2)%nat with (S (2*n+1))%nat by lia.
       replace  (n + (n+0)+1)%nat with ((2*n + 1))%nat by lia.
       rewrite rising_factorial_sn.
       replace (0+(2*n+1)+1)%nat with (S (2*n+1)) by lia.
       rewrite !mulA.
       rewrite <-(mulA (inv_Sn _ )).
       rewrite (mulC (inv_Sn _ )).
       rewrite inv_Sn_spec.
       ring.
     - rewrite !mul_ps_S.
       pose proof  (f_shift1 C1 r).
       assert ( to_ps (g_bound C2 n r) == to_ps (g_bound C2 n r)) by reflexivity.
       pose proof (mul_proper _ _ H7 _ _ H8 t(k)).
       rewrite H9.
       rewrite IHk.
       rewrite !to_ps_simpl.
      unfold f_bound, g_bound, fg_bound.
      Opaque Nat.mul.
      simpl.
      ring_simplify.
      replace (2 * n + 2)%nat with (S (2*n +1))%nat by lia.
      enough ([S (k+1)!2*n+1] + inv_Sn (2*n+1) * [k+1!S (2*n+1)] ==  inv_Sn (2 * n + 1) * [S (k + 1) ! S (2 * n + 1)]) by (rewrite !mulA, <-H10;ring).
      rewrite !rising_factorial_sn.
      replace (S (2*n+1)) with ((2*n+1)+1)%nat by lia.
      rewrite rising_factorial_s.
      ring_simplify.
      replace (k+2)%nat with (S (k+1)) by lia.
      replace (k+1 + (2*n+1)+1)%nat with (S (2*n + k +2)) by lia.
      rewrite !mulA.
      enough (1 + inv_Sn (2 * n + 1) * # (k + 1) ==  inv_Sn (2 * n + 1) * # (S (2 * n + k + 2))) as <- by ring.
      setoid_replace 1 with (#1) at 1 by (simpl;ring).
      rewrite rat_plus1.
      replace (1*(2*n+1+1) + (k+1))%nat with (S (2*n+k+2)) by lia.
      ring.
   Qed.
   Definition Fn_bound M r n k := npow inv2 n * ![n] * [k+1!2*n]* npow M (n+1) * npow r (n + k).
   Definition DFn_bound M r n k :=  npow (inv2) n * ![n] * [(k+1)!2*n+1]* npow M (n+1) * npow r (n + (k + 1)).
 
   Lemma DFn_bound_spec M r (a : nat^1 -> A) n : |a| <= to_ps (Fn_bound M r n) -> |D[0] a| <= to_ps (DFn_bound M r n).
   Proof.
   intros.
   simpl.
   intros k.
   destruct (destruct_tuple1 k) as [k0 ->].
   rename k0 into k.
   rewrite deriv_next.
   rewrite to_ps_simpl.
   rewrite order1d.
   unfold DFn_bound.
   (* setoid_replace (a t(k+1)%nat) with ((a t(k+1)%nat) *1 ) by (rewrite mul1;reflexivity). *)
   apply (le_trans _ _ _  (norm_mult _ _)).
   rewrite mulC.
   apply (le_trans _ _ _  (mul_le_compat_pos (norm_nonneg _ ) (norm_n_le_n _ ))). 
   rewrite rising_factorial_s.
   rewrite mulC.
   rewrite !mulA.
   rewrite (mulC (npow _ _)).
   rewrite !mulA.
   rewrite (mulC ![n]).
   rewrite !mulA.
   apply mul_le_compat_pos.
   apply ntimes_nonneg.
   apply le_0_1.
   rewrite <-mulA.
   replace (k+2)%nat with ((k+1)+1)%nat by lia.
   apply (le_trans _ _ _ (H7 _)).
   rewrite to_ps_simpl.
   rewrite order1d.
   unfold Fn_bound.
   apply le_eq.
   ring.
 Qed.

   Lemma DFn_boundg M r n : DFn_bound M r n == g_bound (npow (inv2) n * ![n] * (npow M (n+1)) * npow r (n+1) ) n r. 
   Proof.
     intros k.
     unfold DFn_bound, g_bound.
     replace (n+(k+1))%nat with ((n +1) + k)%nat by lia.
     rewrite !npow_plus.
     ring.
  Qed.

   Lemma DFn_bound_spec' (a : nat^1 -> A) M r n : |a| <= to_ps (Fn_bound M r n) -> |D[0] a| <= to_ps (g_bound (npow (inv2) n * ![n] * (npow M (n+1)) * npow r (n+1) ) n r).
   Proof.
     intros.
     intros k.
     destruct (destruct_tuple1 k) as [k0 ->].
     rewrite to_ps_simpl.
     rewrite order1d.
     rewrite <-(DFn_boundg _ _ n k0).
     pose proof (DFn_bound_spec M r a n H7 t(k0)).
     rewrite order1d, to_ps_simpl in H8.
     apply H8.
  Qed.

  Lemma bound_prod  M r (a b : nat^1 -> A) n : |a| <= to_ps (f_bound M r) -> |b| <= (to_ps (Fn_bound M r n)) -> |a * (D[0] b) | <= to_ps (Fn_bound M r (n+1)). 
  Proof.
   intros P1 P2.
   pose proof (DFn_bound_spec'  b M r n P2) as P3.
   pose proof (fg_bounded _ _ _ _ _ _ P1 P3) as P4.
   intros k.
   apply (le_trans _ _ _ (P4 _)).
   apply le_eq.
   destruct (destruct_tuple1 k) as [k0 ->].
   rename k0 into k.
   rewrite order1d, !to_ps_simpl.
   unfold fg_bound, Fn_bound.
   setoid_replace M with (npow M 1) at 1 by (simpl;ring).
   rewrite !npow_plus.
   replace (2*(n+1))%nat with (2*n+2)%nat by lia.
   replace (n+1)%nat with (S n) by lia.
   ring_simplify.
   rewrite !mulA.
   enough (npow inv2 1 * ![ S n] == inv_Sn (2*n + 1) * ![n]) as -> by ring.
   simpl.
   ring_simplify.
   enough (inv2 * inv_Sn n == inv_Sn (2*n+1)) as <- by ring.
   apply inv_Sn_unique.
   replace (S (2*n+1)) with (2 * (S n))%nat by lia.
   rewrite nat_mult_compat.
   setoid_replace (#2 * # (S n) * (inv2 * inv_Sn n)) with ((#2 * inv2 ) * (# (S n) * inv_Sn n)) by ring.
   unfold inv2.
   rewrite !inv_Sn_spec.
   ring.
 Qed.

 Lemma npow_inv m n : npow #(S m) n * npow (inv_Sn m) n == 1.
 Proof.
   induction n.
   simpl.
   ring.
   setoid_replace (npow # (S m) (S n) * npow (inv_Sn m) (S n)) with (# (S m) * inv_Sn m * ((npow (# (S m)) n) * (npow (inv_Sn m) n))) by (simpl;ring).
   rewrite IHn.
   ring_simplify.
   rewrite inv_Sn_spec.
   ring.
 Qed.

 Lemma Fn_bound0 M r : (0 <= M) -> (0 <= r) -> forall n, Fn_bound M r n 0 <= [n]! *  M * npow (#2*M*r) n.
 Proof.
   intros Mp rp n.
   unfold Fn_bound.
   simpl.
   replace (n+0)%nat with n by lia.
   rewrite !npow_mult, npow_plus.
   simpl.
   ring_simplify.
   assert (  npow inv2 n * ![ n] * [1 ! 2 * n] * npow M n * M * npow r n ==  npow M n * M * npow r n * (npow inv2 n * ![ n] * [1 ! 2 * n] )) as -> by ring.
   rewrite !mulA.
   apply mul_le_compat_pos;try apply npow_pos;auto.
   apply mul_le_compat_pos;auto.
   apply mul_le_compat_pos;try apply npow_pos;auto.
   rewrite rising_factorial1.
   pose proof (npow_inv 1 n).
   rewrite (mulC [n]!).
   setoid_replace (npow inv2 n) with (npow #2 n * npow inv2 n * npow inv2 n) by (rewrite npow_inv;ring).
   rewrite !mulA.
   apply mul_le_compat_pos; try (apply npow_pos;apply ntimes_nonneg;apply le_0_1).
   rewrite <-!mulA.
   rewrite <-npow_plus.
   rewrite (mulC _ ![n]).
   clear H7.
   induction n.
   - simpl.
     replace (2*0)%nat with 0%nat by lia.
     simpl;ring_simplify.
     apply le_refl.
  - replace (S n + S n)%nat with (S (S (n+n))) by lia.
    replace (2*S n)%nat with (S (S (2*n))) by lia.
    setoid_replace (![S n] * npow inv2 (S (S (n+n))) * [S(S (2 *n))]!) with (((![n] * npow inv2 (n+n) * [2*n]!)) * (inv2 * inv2 * # (S (S (2 *n))) *# (S (2 * n)) * inv_Sn n)) by (simpl;ring).
    setoid_replace [S n]! with ([n]! * #(S n)) by (simpl;ring).
    apply mul_le_le_compat_pos.
    apply mul_pos_pos;try apply fact_pos.
    apply mul_pos_pos;try apply invfact_pos;apply npow_pos;apply inv_Sn_pos.
    apply mul_pos_pos; try apply mul_pos_pos; try apply mul_pos_pos; try apply ntimes_nonneg; try apply le_0_1; try apply inv_Sn_pos.
    apply mul_pos_pos; apply inv_Sn_pos.
    apply IHn.
    replace (S (S (2 *n))) with (2*(S n))%nat by lia. 
    rewrite nat_mult_compat.
    rewrite <-mulA.
    rewrite (mulC _ #2).
    rewrite <-mulA.
    unfold inv2.
    rewrite inv_Sn_spec.
    ring_simplify.
    setoid_replace (inv_Sn 1 * #(S n) * #(S(2*n)) * inv_Sn n) with ((#(S n) * inv_Sn n) * (inv_Sn 1 * #(S(2*n)))) by ring.
    rewrite inv_Sn_spec.
    ring_simplify.

    apply (le_trans _ (inv_Sn 1 * # (2*(S n)))).
    apply mul_le_compat_pos;try apply inv_Sn_pos.
    apply ntimes_monotone;lia.
    rewrite nat_mult_compat.
    rewrite <-mulA.
    rewrite (mulC _ (#2)).
    rewrite inv_Sn_spec.
    ring_simplify.
    apply le_refl.
  Qed.

  Definition a_bound_series M r: (nat^1 -> A)  := to_ps (fun n => M * (npow r n)).

  Lemma Fn_bound_spec d M r n k : (0 <= M) -> (0 <= r) ->  norm (Fi (H3 := H4) (ntimes d t(a_bound_series M r))  (S n) 0 t(k)) <= Fn_bound (ntimes d M) r n k.
 Proof.
   intros Mgt0 rgt0.
   revert k.
   induction n; intros.
   - assert (Fi (H3 := H4) (ntimes d t(a_bound_series M r)) 1 0 ==  (ntimes d (to_ps ( fun n : nat => M * npow r n)))).
     {
       rewrite Fi_S.
       rewrite sum_1.
       simpl Fi.
       rewrite diff_id_same; try lia.
       rewrite mul1.
       rewrite <-ntimes_nth;try lia.
       rewrite tuple_nth_cons_hd.
       reflexivity.
     }
     rewrite index_proper; try apply H7; try reflexivity.
     rewrite ntimes_index.
     rewrite to_ps_simpl.
     unfold Fn_bound.
     simpl.
     ring_simplify.
     simpl.
     rewrite rising_factorial0.
     ring_simplify.
     apply (le_trans _ _ _ (norm_ntimes_le_ntimes_norm _ _)).
     rewrite norm_abs.
     rewrite mulC.
     rewrite ntimes_mult.
     rewrite mulC;apply le_refl.
     apply mul_pos_pos;auto.
     apply npow_pos;auto.
   - pose proof (Fi_S (d:=1)  (ntimes d t(a_bound_series M r)) 0 (S n) ).
     rewrite index_proper; try apply H6; try reflexivity.
     rewrite index_proper;try apply sum_1; try reflexivity.
     replace (S n) with (n+1)%nat by lia.
     assert (| (ntimes d t( a_bound_series M r)) \_ 0 | <= to_ps (f_bound (ntimes d M) r)).
     { intros.
       unfold f_bound.
       intros j.
       destruct (destruct_tuple1 j) as [j0 ->].
       rewrite index_proper; try (rewrite <-ntimes_nth;try lia;rewrite tuple_nth_cons_hd;reflexivity ); try reflexivity.
       unfold a_bound_series.
       rewrite ntimes_index.
       apply (le_trans _ _ _ (norm_ntimes_le_ntimes_norm _ _)).
       rewrite order1d.
       rewrite to_ps_simpl.
       rewrite norm_abs; [rewrite mulC,ntimes_mult,mulC; apply le_refl|].
       apply mul_pos_pos;auto.
       apply npow_pos;auto.
     }

     assert ( | Fi (ntimes d t( a_bound_series M r)) (n + 1) 0 | <= to_ps (Fn_bound (ntimes d M) r n)).
     {
      intros j.
       destruct (destruct_tuple1 j) as [j0 ->].
      replace (n+1)%nat with (S n) by lia.
      rewrite order1d, to_ps_simpl.
       apply IHn.
     }
     pose proof (bound_prod _ _ _ _ n H8 H9 t(k)).
     rewrite order1d, to_ps_simpl in H10.
     apply H10.
  Qed.

 
  Lemma Fn_bound_spec1 M r n k : (0 <= M) -> (0 <= r) ->  norm (Fi (H3 := H4) t(a_bound_series M r)  (S n) 0 t(k)) <= Fn_bound M r n k.
  Proof.
    intros.
    assert (M == (ntimes 1 M)) by (simpl;ring).
    assert (t(a_bound_series M r) == (ntimes 1 t(a_bound_series M r))).
    unfold ntimes;rewrite add0;reflexivity.

    (* apply Fn_bound_spec;auto. *)
    (* unfold ntimes. *)
  Admitted.

  (** multivariate case **)

  (* Definition sum_coeff_order {d} (a : nat^(S d) -> A) (n : nat) : A. *)
  (* Proof. *)
  (*   induction n. *)
  (*   - apply (a 0). *)
  (*   - apply (sum (fun i =>  partial_eval a ) *)
  (* Definition sum_bound {d} (a : nat^(S d) -> A) (b : nat^1 -> A) : Prop. *)
  (* Proof. *)
  (*   induction d; [apply True|]. *)
  (*   apply (forall n, IHd (sum (fun n => partial_eval a n) (fun k =>  b)). *)
  (* Admitted. *)
  Definition inv_ncr (n r : nat) : A.
  Admitted.

  Lemma inv_ncr_nonneg n r: (0 <= inv_ncr n r).
  Admitted.

  Definition sum_order {d} (a : nat^d -> A ) (n : nat) : A.
  Proof.
    revert n.
    induction d;intros.
    apply (norm (a t())).
    destruct d.
    apply (norm (a t(n))).
    apply (sum (fun j => (IHd (partial_eval a j) (n-j)%nat)) (S n)).
  Defined.

  (* Definition strong_bound {d} (a : nat^d -> A) (b : nat^1 -> A):= |a| <= (fun k => (inv_ncr (k\_0+d-1)%nat (d-1)%nat) * (b k)). *)

  Definition strong_bound {d} (a : nat^d -> A) (b : nat^1 -> A):= forall n, sum_order a n <= b t(n).

 #[global]Instance sum_order_proper d : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (@sum_order d).
 Proof.
   intros a b eq a0 b0 eq'.
   simpl in eq'.
   rewrite eq'.
   clear eq'.
   revert b0.
   induction d;intros.
   simpl.
   apply norm_proper.
   apply index_proper;auto;try reflexivity.
   simpl.
   destruct d.
   apply norm_proper.
   apply index_proper;auto;try reflexivity.
   apply sum_ext.
   intros.
   apply IHd.
   rewrite eq.
   reflexivity.
 Defined.
 
 #[global]Instance strong_bound_proper d : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (@strong_bound d).
   Proof.
     intros a b eq a0 b0 eq'.
     unfold strong_bound.
     split.
     - intros.
       rewrite <-eq.
       symmetry in eq'.
       rewrite (index_proper b0 a0 eq' t(n) t(n));try reflexivity;auto.
     - intros.
       rewrite eq.
       rewrite (index_proper a0 b0 eq' t(n) t(n));try reflexivity;auto.
   Defined.

  Notation "| a | << b" := (strong_bound a b) (at level 70).

  Lemma index_to_eval {d} (a : nat^(S d) -> A) hd tl: (a (tuple_cons hd tl)) = partial_eval a hd tl.
  Proof.
    reflexivity.
  Qed.

  Lemma mult_monotone {d} (a b : nat^d -> A) (A1 B1 : nat^1 -> A) : (|a| << A1) -> |b| << B1 -> |(a * b)| << (A1 * B1).
  Proof.
    intros.
    induction d.
    - intros n.
      simpl.
      rewrite !ps_mul0.
      specialize (H7 n).
      admit.
    - unfold strong_bound.
      intros.
   Admitted.

   Lemma sum_monotone_strong {d} (a : nat -> nat^d ->A ) (b: nat -> nat^1 -> A) N : (forall n, (n < N) -> |a n| << b n) -> |(sum a N)| << sum b N.
   Admitted.

  (* Lemma sum_order_0 {d}: forall k, sum_order (d:=d) 0 k == 0. *)
  (* Proof. *)
  (*   intros. *)
  (*   induction d. *)
  (*   simpl. *)
  (*   rewrite ps0;reflexivity. *)
  (*   simpl. *)
  (*  Admitted. *)


   (* Lemma sum_monotone_strong {d} (a : nat -> nat^d ->A ) (b: nat -> nat^1 -> A) N : (forall n, (n < N) -> |a n| << b n) -> |(sum a N)| << sum b N. *)
   (*   intros. *)
   (*   induction N. *)
   (*   - unfold sum. *)
   (*     simpl. *)
   (*     intros k. *)
   (*     rewrite sum_order_0. *)
   (*     rewrite !ps0. *)
   (*     apply le_refl. *)
   (*   - intros k. *)
   (*   rewrite norm_zero_eq. *)
   (*   ring_simplify. *)
   (*   apply le_refl. *)
   (*   unfold strong_bound. *)
   (*   rewrite !sum_S. *)
   (*   intros k. *)
   (*   rewrite !index_plus. *)
   (*   apply (le_trans _ _ _ (norm_triangle _ _)). *)
   (*   assert (forall n, n < N -> |a n| << b n). *)
   (*   intros;apply H7;lia. *)
   (*   specialize (IHN H8 k). *)
   (*   pose proof (index_proper (sum b (S N))  _ (sum_S _ _) t(order k) t(order k)). *)
   (*   rewrite H9;try reflexivity. *)
   (*   rewrite index_plus. *)
   (*   ring_simplify. *)
   (*   apply le_le_plus_le. *)
   (*   apply IHN. *)
   (*   apply H7;lia. *)
   (* Qed. *)

   Lemma sum_same_strong {d} (a : nat -> (nat^d -> A)) (b: (nat^1 -> A)) N : (forall n, (n < N) -> |a n| << b) -> |(sum a N)| << ntimes N b.
   Proof.
     intros.
     enough (ntimes N b == sum (fun _ => b) N) as ->.
     apply sum_monotone_strong.
     intros.
     apply H7;auto.
     induction N.
     simpl.
     intros.
     unfold sum.
     simpl.
     reflexivity.
     rewrite !sum_S.
     Opaque add.
     simpl ntimes.
     rewrite IHN.
     rewrite addC.
     reflexivity.
     intros.
     apply H7.
     lia.
     Transparent add.
  Qed.

  Lemma partial_eval_D_S {d} (a: nat^(S d) -> A) n k i : partial_eval (D[S i] a) n k == (D[i] (partial_eval a n)) k.
  Proof.
    intros.
  Admitted.

  Lemma diff0_strong_monotone {d} (a : (nat^(S d) ->A)) b : |a| << b ->  (|pdiff 0 a| <<  pdiff 0 b).
  Proof.
       intros Hb.
       intros k.
       (* destruct (destruct_tuple_cons k) as [hd [tl ->]]. *)
       (* rewrite !deriv_next. *)
       (* apply (le_trans _ _ _ (norm_mult _ _)). *)
       (* apply (mul_le_le_compat_pos); try apply ntimes_nonneg; try apply le_0_1; try apply norm_nonneg. *)
       (* apply (le_trans _ _ _ (norm_n_le_n _)). *)
       (* apply ntimes_monotone. *)
       (* rewrite order_cons. *)
       (* lia. *)
       (* replace (order (tuple_cons hd tl) + 1)%nat with (order (tuple_cons (hd+1) tl))%nat  by (rewrite !order_cons;lia). *)
       (* apply Hb. *)
 Admitted.

  Lemma diff_monotone {d} (a : nat^d -> A) b i : (i <d) -> (|a| <= b) -> (|pdiff i a| <= pdiff 0 b).
    generalize dependent i .
    generalize dependent b .
    induction d;try lia.
    intros.
    revert H8.
    destruct i; [apply diff0_monotone|].
    intros H8 k.
    apply partial_eval_bound.
    intros hd tl.
    rewrite partial_eval_D_S.
    assert (i < d)%nat by lia.
    pose proof (proj2 (partial_eval_bound a b)  H8 hd).
    rewrite index1_add.
    specialize (IHd _ _ _ H9 H10 tl).
    apply (le_trans _ _ _ IHd).
    rewrite !deriv_next.

    simpl.
    replace (hd + (order tl +1))%nat with (hd + order tl + 1)%nat by (simpl;lia).

    apply mul_le_le_compat_pos; try apply ntimes_nonneg; try apply le_0_1;try apply (bound_nonneg a);auto.
    apply ntimes_pos_monotone; try apply le_0_1.
    lia.
    apply le_refl.
  Qed.

  Lemma diff_monotone_strong {d} (a : nat^d -> A) b i : (i <d) -> (|a| << b) -> (|pdiff i a| << pdiff 0 b).
    (* generalize dependent i . *)
    (* generalize dependent b . *)
    (* induction d;try lia. *)
    (* intros. *)
    (* revert H8. *)
    (* destruct i. *)
    (* apply diff0_strong_monotone. *)
    (* intros H8 k. *)
    (* apply partial_eval_bound. *)
    (* intros hd tl. *)
    (* rewrite partial_eval_D_S. *)
    (* assert (i < d)%nat by lia. *)
    (* pose proof (proj2 (partial_eval_bound a b)  H8 hd). *)
    (* rewrite index1_add. *)
    (* specialize (IHd _ _ _ H9 H10 tl). *)
    (* apply (le_trans _ _ _ IHd). *)
    (* rewrite !deriv_next. *)

    (* simpl. *)
    (* replace (hd + (order tl +1))%nat with (hd + order tl + 1)%nat by (simpl;lia). *)

    (* apply mul_le_le_compat_pos; try apply ntimes_nonneg; try apply le_0_1;try apply (bound_nonneg a);auto. *)
    (* apply ntimes_pos_monotone; try apply le_0_1. *)
    (* lia. *)
    (* apply le_refl. *)
  Admitted.

    Lemma comp1_order {d : nat} i k : (order k > 1) ->  comp1 (m:=d) i k == 0.
    Proof.
      intros.
      rewrite ps_property_backwards.
      induction d.
      assert (k == 0) by (rewrite zero_tuple_zero;reflexivity).
      simpl.
      unfold derive_rec.
      simpl.
      rewrite comp1_0.
      ring.
      destruct (destruct_tuple_cons k) as [hd [tl ->]].
  Admitted.
   Lemma comp1_bound {d : nat} i :  |comp1 (m:=d) i| << (comp1 0).
    Proof.
      intros k.
      rewrite ps_property_backwards.
    Admitted.

   Lemma npow_Sn_times x n m: npow x (S n * m) == npow x m * npow x (n*m) .  
   Proof.
     replace (S n * m)%nat with (n*m + m)%nat by lia.
     rewrite npow_plus.
     ring.
   Qed.
    Lemma mul_nonneg (a b : nat^1 -> A) : (forall k, 0 <= a k) -> (forall k, 0 <= b k) -> (forall k, 0 <= (a*b) k).
    Admitted.

   Definition tuple_bound_strong {d} {e} (a : (nat^d -> A )^e) (b : (nat^1 -> A)):=  forall i, i < e -> |a\_i| << b.


    Lemma F_monotone {d :nat} (a : (nat^d -> A)^d) (b : (nat^1 -> A)^1) n  :  forall i, i<d ->  (tuple_bound_strong a b\_0) -> |Fi a n i| << (Fi (ntimes d b) n 0).
    Proof.
       intros.
       induction n.
       - apply comp1_bound. 
       - intros k.
         rewrite index_proper; try apply Fi_S; try reflexivity.
         enough (forall j, j < d -> |(tuple_nth j a 0) * (D[j] (Fi (H3 := H4) a n i))| <<  ( b\_0 * D[0] (Fi  (H3 := H4) (ntimes d b) n 0))).
         {
           rewrite index_proper; try apply Fi_S; try reflexivity. 
          (* rewrite index_sum.  *)
           (* apply (le_trans _ _ _ (sum_norm _ _)).  *)
           pose proof (sum_same_strong (fun j => a\_j * D[j] (Fi (H3:=H4) a n i )) _ d  H9 k).
           apply (le_trans _ _ _ H10).
           rewrite index_sum.
           rewrite sum_1.
           apply le_eq.
           rewrite !ntimes_index.
           (* apply ntimes_proper. *)
           rewrite <-ntimes_index.
           apply index_proper; try reflexivity.
           setoid_rewrite  <-(ntimes_nth b);auto.
           rewrite mulC.
           rewrite ntimes_mult.
           rewrite (mulC (D[0] _ )).
           reflexivity.
         }
         intros.
         intros l.
         apply mult_monotone.
          apply H8;lia. 
         apply diff_monotone_strong;auto.
     Qed.

       
    Lemma strong_bound1d (a : nat^1 -> A) (b : nat^1 -> A) : |a| << b -> |a| <= b. 
    Proof.
      intros.
      intros k.
      destruct (destruct_tuple1 k) as [k0 -> ].
      specialize (H7 k0).
      rewrite order1d.
      simpl in H7.
      apply H7.
    Qed.

    Lemma sum_order0 {d} (a : (nat^d -> A)): sum_order a 0 == norm (a 0). 
    Proof.
      induction d.
      simpl.
      reflexivity.
      destruct d.
      simpl.
      reflexivity.
      Opaque tuple_cons.
      simpl.
      rewrite sum_1.
      destruct d.
      admit.
      rewrite sum_1.
    Admitted.

    Lemma F_bound {d :nat} (a : (nat^d -> A)^d) (b : (nat^1 -> A)^1) n  : forall i, i<d -> (tuple_bound_strong a b\_0) -> norm ((Fi a n) i 0) <=  (Fi (ntimes d b) n 0 0).
    intros.
    pose proof (F_monotone a b n i H7 H8 0).
    rewrite sum_order0 in H9.
    apply H9.
   Qed.
  (* Definition Fn_bound_mv M r d n k :=  #d * (npow #2 (n * (k + d -1))) * (Fn_bound M r n k). *)

  (* Lemma Fn_bound_spec_mv M r d n k : (0 <= M) -> (0 <= r) ->   norm (#d * (npow #2 ((S n) * (k + d -1))) * (Fi (H3 := H4) t(a_bound_series M r)  (S n) 0 t(k))) <= (Fn_bound_mv M r  d n k). *)
  (* Admitted. *)

  (*   Lemma npow_mul_pow  x n m: npow x (n*m) == npow (npow x m) n. *)
  (*   Admitted. *)

   (*  Lemma F_monotone {d :nat} (a : (nat^d -> A)^d) (b : (nat^1 -> A)^1) n : (mps_tuple_bound a b\_0) -> (mps_tuple_bound (F a n) (tuple_nth 0 (F (ntimes d b) n) 0)). *)
   (* Admitted. *)
   (*  Lemma Fn_bound_mv0  M r d : (0 <= M) -> (0 <= r) -> (0 < d) -> forall n, Fn_bound_mv M r  d n 0 <= [n]! *  (#d*M) * npow ((npow #2 d)*M*r) n. *)
   (*  Proof. *)
   (*    intros. *)
   (*    unfold Fn_bound_mv. *)
   (*    pose proof (Fn_bound0 _ _ H7 H8 n). *)
   (*    replace ((n*(0+d-1))%nat) with (n*(d-1))%nat by lia. *)
   (*    rewrite npow_mul_pow. *)
   (*    rewrite mulA. *)
   (*    assert ((npow (npow #2 d *  M * r) n) == npow ((npow #2 ((d-1)%nat) * (#2 * M * r))) n) as ->. *)
   (*    { *)
   (*      apply npow_proper. *)
   (*      replace (d) with (S (d -1))%nat at 1 by lia. *)
   (*      simpl;ring. *)
   (*    } *)
   (*    rewrite npow_mult. *)
   (*    setoid_replace ([n ]! * (# d * M) * ((npow (npow #2 (d-1)) n) * (npow (#2 * M * r) n))) with (# d * ((npow (npow #2 (d-1)) n) * ([n ]! * ( M) * npow (# 2 * M * r) n))) by ring. *)
   (*    apply mul_le_compat_pos; try apply ntimes_nonneg;try apply le_0_1. *)
   (*    apply mul_le_compat_pos; try apply npow_pos; try apply npow_pos; try apply ntimes_nonneg; try apply le_0_1. *)
   (*    apply H10. *)
   (* Qed. *)
End Bounds.

Section Bounded_PS.

  Context `{AbstractPowerSeries}.
  Context `{ArchimedeanField (A:=A) (H:=_) (R_rawRing := _) (R_semiRing := _) (invSn := _)}.

  Context {d : nat} {f : (nat^(S d) -> A)^(S d)}.
  Context {M r : A} {Mpos : 0 <= M} {rpos : 0 <= r}.
  Context {f_bounded : tuple_bound_strong f t(a_bound_series M r)\_0}.

  Add Ring TRing: (ComRingTheory (A := A)). 

  Definition y   := (yt (f := f)).

  Lemma y0_spec i : i < (S d) -> (y\_i 0) == 0.
  Proof.
    intros.
    unfold y.
    rewrite vec0_cons.
    rewrite yt_spec;auto.
    unfold y_i.
    simpl inv_factorial.
    ring_simplify.
    simpl.
    rewrite comp1_0;reflexivity.
  Defined.

  Lemma y_bound_Fn i n: i < (S d) -> norm ((y\_i) t(S n))  <= ![S n] * Fn_bound (ntimes (S d) M) r n 0.  
  Proof.
   intros.
   pose proof (F_bound  _ _ (S n) i H7 f_bounded).
   (* pose proof (F_monotone  _ _ (S n) i H7 f_bounded). *)
   pose proof (Fn_bound_spec  (S d) M r n 0 Mpos rpos).
   unfold y.
   rewrite yt_spec;auto.
   unfold y_i.
   apply (le_trans _ _ _ (norm_mult _ _)).
   rewrite norm_abs;try apply invfact_pos.
   apply mul_le_compat_pos;try apply invfact_pos.
   apply (le_trans _ _ _ (H8)).
   rewrite norm_abs in H9;auto.
   apply (le_trans _ (norm (Fi (H3:=H4) f (S n) i 0)));try apply norm_nonneg;auto.
 Qed.

Lemma y_bound i n: i < (S d) -> norm (y\_i t(S n)) <= ntimes (S d) M  * npow (ntimes 2 1 * ntimes (S d) M * r) n.
  Proof.
     intros.
     apply (le_trans _ _ _ (y_bound_Fn _ _ H7)).
     assert (0 <= ntimes (S d) M )by (apply ntimes_nonneg;auto).
    pose proof (mul_le_compat_pos (invfact_pos (S n)) (Fn_bound0 (ntimes (S d) M) r H8 rpos n)).
       apply (le_trans _ _ _ H9).
       rewrite <-!mulA.
       enough (![ S n] * [n ]! * ntimes (S d) M * npow (ntimes 2 1 * ntimes (S d) M * r) n  <= ( [S n ]! * ![ S n]) * ntimes (S d) M * npow (ntimes 2 1 * ntimes (S d) M * r) n ).
       {
         apply (le_trans _ _ _ H10).
         rewrite fact_invfact.
         ring_simplify.
         apply le_refl.
       }
       setoid_replace (([S n ]! * ![ S n]) * ntimes (S d) M * npow (ntimes 2 1 * ntimes (S d) M * r) n ) with (![ S n] * ([S n ]! * (ntimes (S d) M * npow (ntimes 2 1 * ntimes (S d) M * r) n ))) by ring.
       rewrite !mulA.
       apply mul_le_compat_pos; try apply invfact_pos.
       rewrite mulC.
       rewrite (mulC [S n]!).
       apply mul_le_compat_pos; try apply invfact_pos.
       apply mul_pos_pos.
       apply ntimes_nonneg;auto.
       apply npow_pos.
       apply mul_pos_pos;auto.
       apply mul_pos_pos; apply ntimes_nonneg;auto.
       apply le_0_1.
       simpl.
       rewrite mulC.
       setoid_replace ([n]!) with ([n]!*1) at 1 by ring.
       apply mul_le_compat_pos.
       apply fact_pos.
       rewrite addC.
       setoid_replace 1 with (0 + 1) at 1 by ring.
       apply le_plus_compat.
       apply ntimes_nonneg.
       apply le_0_1.
   Qed.


 End Bounded_PS. 

Section Modulus.
  Context `{AbstractPowerSeries}.
  Context `{ArchimedeanField (A:=A) (H:=_) (R_rawRing := _) (R_semiRing := _) (invSn := _)}.
  Add Ring TRing: (ComRingTheory (A := A)). 

   Definition fast_cauchy_neighboring (a : nat -> A) := forall n, norm (a (S n) - a n) <= npow inv2 (S n).

    Definition partial_sum (a : nat^1 -> A) (x : A) (N : nat) := sum (fun n => a t(n) * npow x n) N.

    Lemma partial_sum_neighboring (a : nat^1 -> A) (x : A) (N : nat) : norm (partial_sum a x (S N) - partial_sum a x N) == norm (a t(N) * npow x N).
    Proof.
      unfold partial_sum.
      rewrite sum_S.
      apply norm_proper.
      ring.
   Qed.
      
    Lemma npow_norm_le x n : norm (npow x n) <= npow (norm x) n.
    Proof.
      induction n.
      simpl.
      rewrite norm_abs; try reflexivity;try apply le_0_1; try apply le_refl.
      simpl.
      apply (le_trans _ _ _ (norm_mult _ _)).
      apply mul_le_compat_pos; try apply norm_nonneg.
      apply IHn.
    Qed.

    Lemma npow_monotone x y n : (0 <= x) -> (x <= y) -> npow x n <= npow y n.
    Proof.
      intros.
      induction n.
      simpl.
      apply le_refl.
      simpl.
      apply mul_le_le_compat_pos;auto.
      apply npow_pos;auto.
    Qed.

    Lemma inv2_pos : 0 <= inv2.
    Proof.
      apply inv_Sn_pos.
    Qed.

    Lemma npow1 x n : x == 1 -> npow x n == 1.
    Proof.
      intros.
      induction n.
      simpl.
      reflexivity.
      simpl.
      rewrite IHn, H7.
      ring.
    Qed.
    Lemma ps_modulus_helper x r n m :  norm x <= r -> norm (npow x (n + m)) <= npow r n * npow r m. 
    Proof.   
      intros.
      rewrite npow_plus.
      apply (le_trans _ _ _ (norm_mult _ _)).
      apply mul_le_le_compat_pos; try apply norm_nonneg;apply (le_trans _ _ _ (npow_norm_le _ _)).
      apply npow_monotone; try apply norm_nonneg;auto.
      apply npow_monotone; try apply norm_nonneg;auto.
    Qed.

    Definition bps_modulus logM n := (n+1+logM)%nat.
    Definition bps_radius invr := inv2 * invr.

    Lemma bounded_ps_modulus_spec  (a : nat^1 -> A) (M r : A) invr logM x: (r * invr == 1) -> (M <= npow (#2) logM) ->  norm x <= (bps_radius invr) -> (mps_bound a (a_bound_series M r)) -> fast_cauchy_neighboring (fun n => (partial_sum a x) (bps_modulus logM n)). 
    Proof.
      unfold bps_modulus, bps_radius.
      intros.
      unfold fast_cauchy_neighboring.
      intros.
      replace ((S n + 1) + logM)%nat with (S (n+1+logM))%nat by lia.
      rewrite partial_sum_neighboring.
      apply (le_trans _ _ _ (norm_mult _ _)).
      rewrite mulC.
        
      apply (le_trans _ _ _ (mul_le_compat_pos (norm_nonneg _) (H10 _))).
      rewrite mulC.
      pose proof (bound_nonneg a (a_bound_series M r) H10).
      apply  (le_trans _ _ _ (mul_le_compat_pos  (H11 _) (ps_modulus_helper _ _ _ logM H9))).
      unfold a_bound_series.
      rewrite order1d.
      rewrite to_ps_simpl.
      rewrite !npow_mult.
      ring_simplify.
      setoid_replace (M * npow r (n + 1 + logM) * npow inv2 (n+1) * npow invr (n+1) * npow inv2 logM *npow invr logM) with ((npow inv2 (n+1)) * (M * npow inv2 logM) * ( npow r (n+1+logM) * npow invr (n+1) * npow invr logM)) by ring.
      rewrite (npow_plus r).
      setoid_replace  (npow r (n + 1) * npow r logM * npow invr (n + 1) * npow invr logM)  with ((npow r (n+1) * npow invr (n+1)) * ((npow r logM) * (npow invr logM))) by ring.
      rewrite <-!npow_mult.
      setoid_replace ((npow (r * invr) (n + 1))) with 1 by apply npow1;auto.
      setoid_replace ((npow (r * invr) (logM))) with 1 by apply npow1;auto.
      ring_simplify.
      replace (n+1)%nat with (S n) by lia.
      setoid_replace ( npow inv2 (S n)) with ( npow inv2 (S n) * 1) at 2 by ring.
      rewrite mulA.
      apply mul_le_compat_pos.
      apply npow_pos.
      apply inv2_pos.
      rewrite mulC.
      apply (le_trans _ _ _ (mul_le_compat_pos (npow_pos _ _ (inv2_pos)) H8)).
      rewrite mulC.
      rewrite <-npow_mult.
      unfold inv2.
      apply le_eq.
      apply npow1.
      apply inv_Sn_spec.
   Qed.

  
End Modulus.

