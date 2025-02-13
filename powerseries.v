Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import polynomial.

 Instance seq_A_setoid {A} {A_setoid : Setoid A} : Setoid (nat -> A).
 Proof.
   exists (fun x y => forall n, x n == y n).
   split.
   intros a b; apply setoid_equiv.
   intros a b H n.
   apply setoid_equiv;auto.
   intros a b c H1 H2  n.
   rewrite H1;apply H2.
 Defined.
Section Powerseries.
Context `{A_comRing : comSemiRing}.
Add Ring ARing: ComSemiRingTheory.
Definition ps := nat -> A.
Definition derive_ps (a : ps) := fun n => (ntimes (n+1) (a (n+1)%nat)).
Definition sum_ps (a b : ps) : ps := fun n => (a n)+(b n).
Fixpoint convolution_coeff_rec (a b : ps) n i :=
     (a (n-i)%nat) * (b i%nat) + match i with
     | 0 => 0
     | S i' => convolution_coeff_rec a b n i'
    end.
 Definition convolution_coeff a b  n := convolution_coeff_rec a b n n.

 Definition mult_ps (a b : ps) : ps := fun n => convolution_coeff a b n.

 Definition zero_ps : ps := (fun n => 0).
 Definition one_ps : ps := (fun n => match n with | 0%nat => 1 | _ => 0 end).

  #[global] Instance ps_rawRing: RawRing (A := ps).
  Proof.
    constructor.
    apply zero_ps. apply one_ps. apply (sum_ps). apply (mult_ps).
  Defined.

 #[global] Instance convolution_coeff_rec_proper : forall n m, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun a b => convolution_coeff_rec a b n m)).
 Proof.
   intros n m a b H0 c d H1.
   simpl in H0, H1.
   induction m.
   simpl.
   rewrite H0, H1; ring.
   simpl.
   rewrite IHm.
   rewrite H0, H1; ring.
  Defined.

 #[global] Instance convolution_coeff_proper : forall n, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun a b => convolution_coeff a b n)).
 Proof.
   intros n a b H0  c d H1.
   unfold convolution_coeff; apply convolution_coeff_rec_proper;auto.
  Defined.

   Lemma convolution_coeff_rec_S a b n i  : (i <= n)%nat -> convolution_coeff_rec a b (S n) i == convolution_coeff_rec (fun n => (a (S n))) b n i.
  Proof.
   intros.
   induction i.
   - simpl.
     rewrite Nat.sub_0_r;unfold nth;simpl.
     ring.
   - simpl.
     assert (i < n)%nat by lia.
     destruct (n-i)%nat eqn: E; [lia|].
     rewrite IHi; try lia.
     assert ((n - S i)%nat = n0) as -> by lia.
     ring.
 Qed. 


  
 Lemma convolution_coeff_S a b n : convolution_coeff a b (S n) == (a 0%nat) * (b (S n)) + convolution_coeff (fun n=> (a (S n))) b n.
 Proof.
   unfold convolution_coeff.
   simpl.
   destruct (n-n)%nat eqn:E;rewrite convolution_coeff_rec_S;try lia;auto.
   ring.
 Qed.

 Lemma convolution_coeff_rec_inv_S a b n i : (i < n)%nat -> convolution_coeff_rec a b n (n-i) == convolution_coeff_rec a b n (n - S i) +  a i * b (n-i)%nat. 
 Proof.
   simpl.
   destruct (n-i)%nat eqn:E.
   lia.
   intros.
   simpl.
   rewrite <-E.
   replace (n - (n-i))%nat with i by lia.
   destruct (n - S i)%nat eqn:E'.
   replace n0 with 0%nat by lia.
   ring.
   replace n0 with (S n1) by lia.
   ring.
 Qed.

 Lemma convolution_coeff_rec_opp a b n i: (i < n)%nat -> convolution_coeff_rec a b n n == convolution_coeff_rec a b n (n-S i)%nat + convolution_coeff_rec b a n i.
 Proof.
   intros.
   induction i.
   - destruct n; try lia.
     simpl.
     rewrite Nat.sub_diag.
     rewrite Nat.sub_0_r.
     ring.
   - rewrite IHi; try lia.
     rewrite convolution_coeff_rec_inv_S.
     simpl.
     ring.
     lia.
Qed.

 Lemma convolution_coeff_sym a b n : convolution_coeff a b n == convolution_coeff b a n.
 Proof.
  unfold convolution_coeff.
  destruct n; [simpl; ring | ].
  rewrite (convolution_coeff_rec_opp _ _ _ (n-1)%nat);try lia.
  destruct n; [simpl;ring|].
  replace (S (S n) - S (S n - 1))%nat with 1%nat by lia.
  simpl.
  rewrite Nat.sub_0_r, Nat.sub_diag.
  ring_simplify.
  destruct n.
  ring.
  replace (S n - n)%nat with 1%nat by lia.
  ring.
 Qed.

  Lemma convolution_coeff_add a b c n : convolution_coeff (fun m =>  a m +  b m) c n == convolution_coeff a c n + convolution_coeff b c n.
  Proof.
    revert a b c.
    induction n; intros.
    unfold convolution_coeff;simpl.
    ring.
    rewrite !convolution_coeff_S.
    ring_simplify.
    rewrite IHn.
    ring.
  Qed.

  Lemma convolution_coeff_smult a b x n : convolution_coeff (fun m =>  x * a m) b n == x * convolution_coeff a b n.
  Proof.
   revert a.
   induction n; intros.
   unfold convolution_coeff; simpl;ring.
   rewrite !convolution_coeff_S.
   rewrite IHn.
   ring.
  Qed.

  Lemma mult_ps_assoc a b c:  mult_ps (mult_ps a b) c == mult_ps a (mult_ps b c).
  Proof.
      intros n.
      unfold mult_ps.
      revert a b c.
      induction n;intros.
      - unfold convolution_coeff.
        simpl.
        ring.
      - rewrite !convolution_coeff_S.
        ring_simplify.
        enough (convolution_coeff (fun n => convolution_coeff a b (S n)) c n == a 0%nat * convolution_coeff (fun n => b (S n)) c n + convolution_coeff (fun n => a (S n)) (fun n => convolution_coeff b c n) n) as -> by (unfold convolution_coeff; simpl;ring).
        rewrite convolution_coeff_proper;try apply convolution_coeff_S; try reflexivity;try (intros m;apply convolution_coeff_S).
        rewrite <-IHn.
        rewrite convolution_coeff_add.
        rewrite convolution_coeff_smult.
        apply add_proper; try ring.
        apply convolution_coeff_proper;try reflexivity.

   Qed.
  #[global] Instance ps_comSemiRing :  comSemiRing (A := ps).
  Proof.
  constructor; intros.
  - intros a b H0 c d H1 n.
    apply A_comRing;auto.
  - intros a b H0 c d H1 n.
    apply convolution_coeff_proper;auto.    
  - intros n;simpl;unfold zero_ps;ring.
  - intros n;simpl;unfold one_ps;ring.
  - intros n; simpl; unfold sum_ps;ring.
  - intros n; simpl; unfold sum_ps;ring.
  - intros n; simpl; unfold sum_ps, zero_ps;ring.
  - apply mult_ps_assoc.
  - simpl; apply convolution_coeff_sym.
  - intros n; simpl; unfold zero_ps, mult_ps.
    revert a.
    induction n;intros.
    unfold convolution_coeff;simpl;ring.
    rewrite convolution_coeff_S.
    rewrite IHn.
    ring.
  - intros n; simpl; unfold one_ps, mult_ps.
    revert a.
    induction n;intros.
    unfold convolution_coeff;simpl;ring.
    rewrite convolution_coeff_S.
    rewrite IHn.
    ring.
  - intros n.
    simpl; unfold mult_ps,sum_ps.
    rewrite convolution_coeff_sym,  convolution_coeff_add.
    rewrite !(convolution_coeff_sym _ a).
    ring.
  Defined.

  Fixpoint power_ps (a : ps) (n : nat) :=
    match n with
    | 0 => one_ps
    | (S n') => a * power_ps a n'
    end.

  Definition ps_composition (a b : ps) : ps.
  Proof.
    intros n.
    apply (fold_right add 0 (map (fun i => a i * (power_ps b i) n) (seq 0 (S n)))).
  Defined.

  Lemma ps_product_rule a b n :  derive_ps (mult_ps a b) n == sum_ps (mult_ps a (derive_ps b)) (mult_ps b (derive_ps a)) n.
  Proof.
    revert b.
    induction n.
    - intros;simpl.
      unfold derive_ps, mult_ps, sum_ps, convolution_coeff.
      simpl.
      ring.
    - intros.
      unfold derive_ps, mult_ps, sum_ps, convolution_coeff.
      simpl.
      
      destruct a0.
      {
        remember (r0 :: r1 :: b) as p1.
        rewrite derive_poly_cons.
        rewrite derive_const.
        apply (nth_ext_A _ _ 0 0).
        rewrite Heqp1.
        unfold mult_polyf.
        rewrite derive_poly_length, length_sum_coefficients, !length_mult_coefficients.
        unfold sum_polyf.
        destruct (derive_poly (r0 :: r1 :: b)) eqn:E.
        apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia.
        rewrite <-E; clear E.
        remember mult_coefficients as f.
        simpl.
        rewrite Heqf.
        rewrite !length_mult_coefficients, derive_poly_length;simpl.
        destruct (length b + 1)%nat eqn:e; simpl; try lia.
        intros.
        rewrite derive_poly_nth, sum_coefficient_nth, !mult_polyf_convolution,<-!mult_coefficients_convolution.
        rewrite ntimes_proper; [|apply nth_proper_list;apply mult_coefficient_cons';rewrite Heqp1;discriminate].
        rewrite (nth_proper_list n);[|apply mult_coefficient_cons';try (rewrite Heqp1;rewrite <-length_zero_iff_nil; rewrite derive_poly_length;simpl;lia )].

        rewrite !sum_coefficient_nth.
        assert ( nth n (mult_coefficients p1 (sum_polyf [r] [0])) 0
 ==  nth n (mult_coefficients (sum_polyf [r] [0]) p1) 0) as -> by (rewrite nth_proper_list; try apply mult_coefficients_sym;ring).
        simpl.
        rewrite !mult_coefficients_single.
        rewrite !derive_poly_nth.
        destruct n;simpl;try ring.
        rewrite mult_coefficients_single.
        rewrite !derive_poly_nth.
        simpl.
        rewrite !ntimes_plus, !ntimes_mult.
        ring.
      }
      remember (r1 :: b) as b1.
      remember (r2 :: a0) as a1.
      rewrite mult_poly_cons.
      rewrite poly_sum_rule.
      rewrite sum_coefficients_proper; [|apply poly_scalar_mult_deriv | reflexivity].
      rewrite mult_polyf_shift_switch.
      rewrite IHa.
            pose proof (mult_poly_cons a (r :: a1)).

      rewrite (sum_poly1_proper (mult_polyf (r0::b1) _ )); try apply H0.

      rewrite sum_poly_assoc.
      apply sum_coefficients_proper; try reflexivity.
      rewrite (derive_poly_const_independent a).
      rewrite sum_poly1_proper; [| apply mult_poly2_proper;try apply derive_poly_cons].
      rewrite (sum_poly2_proper (mult_polyf (0 :: r :: a1) _)); [| apply mult_poly2_proper;try apply derive_poly_cons].
      rewrite sum_poly1_proper; [| apply mult_poly_distr].
      rewrite !mult_poly_distr.
      rewrite <-(sum_poly_assoc (mult_polyf (0 :: _) _)).
      rewrite (sum_poly1_proper (mult_polyf (r0 :: b1) _));try apply (sum_poly_sym _ (mult_polyf (r0 :: b1) (r :: a1))).
      rewrite !sum_poly_assoc.
      apply sum_coefficients_proper.
      rewrite mult_poly_sym;reflexivity.
      rewrite Heqb1.
      apply sum_coefficients_proper.
      destruct (derive_poly (r0 :: r1 :: b)) eqn:E.
      apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia.
      clear E.
      rewrite <-mult_polyf_shift_switch;reflexivity.
      rewrite Heqa1.
      destruct (derive_poly (r :: r2 :: a0)) eqn:E.
      apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia.
      rewrite mult_polyf_shift_switch;reflexivity.
  Qed.
  #[global] Instance differentialRingPs : differentialRing (A := ps).
  Proof.
    exists (derive_ps).
    - intros a b n.
      simpl.
      unfold derive_ps, sum_ps.
      rewrite ntimes_plus;ring.
   - intros a b n.
     admit.
  Admitted.
  
    
End Powerseries.

Section MultiPowerseries.
  Context `{A_comRing : comSemiRing}.

  Fixpoint mps n :=
    match n with
    | 0 => A
    | (S n) => @ps (mps n)
    end.

  #[global] Instance mps_setoid n : Setoid (mps n).
  Proof.
    intros.
    induction n.
    apply H.
    apply seq_A_setoid.
.
  Defined.

  Fixpoint const_to_mps n x : (mps n) := 
    match n with
    | 0 => x
    | (S n) => (fun m => match m with | 0 => const_to_mps n x | _ => 0 end)
   end.

  Definition multips_composition {n m} (a : mps n) (bs : @tuple n (mps (S m))) : (mps (S m)).
  Proof.
    revert a bs.
    induction n;ggintros.
    apply (const_to_mps (S m) a).
    destruct (destruct_tuple bs) as [hd [tl P]].
    apply ((fun n => (fold_right add 0 (map (fun i => ((IHn (a i) tl) * (power_ps hd i)) n)  (seq 0 (S n))))) : (mps (S m))).
  Defined.
End MultiPowerseries.

