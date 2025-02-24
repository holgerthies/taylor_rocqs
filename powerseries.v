Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import tuple.

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
Definition derive_ps (a : ps) : ps := fun n => (ntimes (n+1) (a (n+1)%nat)).
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
 Definition comp_one_ps : ps := (fun n => match n with | 0%nat => 0 | 1 => 1 | _ => 0 end).

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

 Lemma mult_ps_S a b n : mult_ps a b (S n) == (a 0%nat)*(b (S n)) + mult_ps (fun n => (a (S n))) b n.
 Proof.
   unfold mult_ps.
   apply convolution_coeff_S.
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

  Lemma mult_ps_comm a b:  mult_ps a b  == mult_ps b a.
  Proof.
    unfold mult_ps.
    intros n.
    rewrite convolution_coeff_sym;reflexivity.
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

  Lemma ps_product_rule a b n :  derive_ps (mult_ps a b) n == sum_ps (mult_ps b (derive_ps a)) (mult_ps a (derive_ps b)) n.
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
      
 (*      destruct a0. *)
 (*      { *)
 (*        remember (r0 :: r1 :: b) as p1. *)
 (*        rewrite derive_poly_cons. *)
 (*        rewrite derive_const. *)
 (*        apply (nth_ext_A _ _ 0 0). *)
 (*        rewrite Heqp1. *)
 (*        unfold mult_polyf. *)
 (*        rewrite derive_poly_length, length_sum_coefficients, !length_mult_coefficients. *)
 (*        unfold sum_polyf. *)
 (*        destruct (derive_poly (r0 :: r1 :: b)) eqn:E. *)
 (*        apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia. *)
 (*        rewrite <-E; clear E. *)
 (*        remember mult_coefficients as f. *)
 (*        simpl. *)
 (*        rewrite Heqf. *)
 (*        rewrite !length_mult_coefficients, derive_poly_length;simpl. *)
 (*        destruct (length b + 1)%nat eqn:e; simpl; try lia. *)
 (*        intros. *)
 (*        rewrite derive_poly_nth, sum_coefficient_nth, !mult_polyf_convolution,<-!mult_coefficients_convolution. *)
 (*        rewrite ntimes_proper; [|apply nth_proper_list;apply mult_coefficient_cons';rewrite Heqp1;discriminate]. *)
 (*        rewrite (nth_proper_list n);[|apply mult_coefficient_cons';try (rewrite Heqp1;rewrite <-length_zero_iff_nil; rewrite derive_poly_length;simpl;lia )]. *)

 (*        rewrite !sum_coefficient_nth. *)
 (*        assert ( nth n (mult_coefficients p1 (sum_polyf [r] [0])) 0 *)
 (* ==  nth n (mult_coefficients (sum_polyf [r] [0]) p1) 0) as -> by (rewrite nth_proper_list; try apply mult_coefficients_sym;ring). *)
 (*        simpl. *)
 (*        rewrite !mult_coefficients_single. *)
 (*        rewrite !derive_poly_nth. *)
 (*        destruct n;simpl;try ring. *)
 (*        rewrite mult_coefficients_single. *)
 (*        rewrite !derive_poly_nth. *)
 (*        simpl. *)
 (*        rewrite !ntimes_plus, !ntimes_mult. *)
 (*        ring. *)
 (*      } *)
 (*      remember (r1 :: b) as b1. *)
 (*      remember (r2 :: a0) as a1. *)
 (*      rewrite mult_poly_cons. *)
 (*      rewrite poly_sum_rule. *)
 (*      rewrite sum_coefficients_proper; [|apply poly_scalar_mult_deriv | reflexivity]. *)
 (*      rewrite mult_polyf_shift_switch. *)
 (*      rewrite IHa. *)
 (*            pose proof (mult_poly_cons a (r :: a1)). *)

 (*      rewrite (sum_poly1_proper (mult_polyf (r0::b1) _ )); try apply H0. *)

 (*      rewrite sum_poly_assoc. *)
 (*      apply sum_coefficients_proper; try reflexivity. *)
 (*      rewrite (derive_poly_const_independent a). *)
 (*      rewrite sum_poly1_proper; [| apply mult_poly2_proper;try apply derive_poly_cons]. *)
 (*      rewrite (sum_poly2_proper (mult_polyf (0 :: r :: a1) _)); [| apply mult_poly2_proper;try apply derive_poly_cons]. *)
 (*      rewrite sum_poly1_proper; [| apply mult_poly_distr]. *)
 (*      rewrite !mult_poly_distr. *)
 (*      rewrite <-(sum_poly_assoc (mult_polyf (0 :: _) _)). *)
 (*      rewrite (sum_poly1_proper (mult_polyf (r0 :: b1) _));try apply (sum_poly_sym _ (mult_polyf (r0 :: b1) (r :: a1))). *)
 (*      rewrite !sum_poly_assoc. *)
 (*      apply sum_coefficients_proper. *)
 (*      rewrite mult_poly_sym;reflexivity. *)
 (*      rewrite Heqb1. *)
 (*      apply sum_coefficients_proper. *)
 (*      destruct (derive_poly (r0 :: r1 :: b)) eqn:E. *)
 (*      apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia. *)
 (*      clear E. *)
 (*      rewrite <-mult_polyf_shift_switch;reflexivity. *)
 (*      rewrite Heqa1. *)
 (*      destruct (derive_poly (r :: r2 :: a0)) eqn:E. *)
 (*      apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia. *)
 (*      rewrite mult_polyf_shift_switch;reflexivity. *)
  Admitted.
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

  Add Ring ARing : ComSemiRingTheory.
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
  Defined.

  #[global] Instance mps_rawRing n : RawRing (A := mps n).
  Proof.
    induction n.
    apply R_rawRing.
    apply ps_rawRing.
  Defined.

  #[global] Instance mps_comSemiRing n : comSemiRing (A := mps n).
  Proof.
    induction n.
    apply A_comRing.
    apply ps_comSemiRing.
  Defined.

   Fixpoint const_to_mps n x : (mps n) := 
      
    match n with
    | 0 => x
    | (S n) => (fun m => match m with | 0 => const_to_mps n x | _ => 0 end)
   end.

  Definition multips_composition {n m} (a : mps n) (bs : @tuple n (mps (S m))) : (mps (S m)).
  Proof.
    revert a bs.
    induction n;intros.
    apply (const_to_mps (S m) a).
    destruct (destruct_tuple bs) as [hd [tl P]].
    apply ((fun n => (fold_right add 0 (map (fun i => ((IHn (a i) tl) * (power_ps hd i)) n)  (seq 0 (S n))))) : (mps (S m))).
  Defined.


  #[global] Instance const_to_mps_proper : forall n, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (const_to_mps n)).
  Proof.
    intros n a b H0.
    induction n.
    simpl;auto.
    simpl;intros.
    destruct n0;[apply IHn|reflexivity].
  Defined.

  #[global] Instance multips_composition_proper : forall n m, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (@multips_composition m n)).
  Proof.
    intros.
    intros a b H0 c d H1.
    induction m.
    replace (  multips_composition a c)  with (const_to_mps (S n) a) by auto.
    replace (  multips_composition b d)  with (const_to_mps (S n) b) by auto.
    rewrite H0;reflexivity.
  Admitted.
  Definition multips_pdiff {m : nat} (n : nat) (a : mps m)  : mps m.
  Proof.
    revert a n.
    induction m.
    - intros.
      apply 0.
    - intros.
      destruct n.
      apply (derive_ps a).
      apply ((fun i => (IHm (a i) n)) : (mps (S m))).
   Defined.

  #[global] Instance multips_pdiff_proper : forall m n, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (@multips_pdiff m n)).
  Proof.
    intros m.
    induction m;intros.
    intros a b H0.
    simpl;ring.
    intros a b H0.
    destruct n.
    simpl.
    intros; unfold derive_ps;apply ntimes_proper;apply H0.
    simpl; intros.
    apply IHm;auto.
  Defined.
  Lemma mps_plus_diff {m} (a b : mps m) n : multips_pdiff n (a + b) ==  multips_pdiff n a +  multips_pdiff n b.
  Proof.
      revert a b n.
      induction m;intros; [simpl;rewrite add0;reflexivity|].
      destruct n.
      simpl;intros;unfold derive_ps, sum_ps; rewrite ntimes_plus;reflexivity.
      simpl;intros.
      apply IHm.
  Qed.

  Lemma mps_mult_diff {m} (a b : mps m) n : multips_pdiff n (a * b) == b * multips_pdiff n a +  a * multips_pdiff n b.
  Proof.
    revert a b n.
    induction m.
    intros;simpl;ring.
    intros.
    destruct n; intros.
    simpl;apply ps_product_rule.
    simpl; intros i.
    revert a b.
    induction i;intros.
    - setoid_replace (mult_ps a b 0%nat) with (a 0%nat * b 0%nat).
      rewrite IHm.
      unfold mult_ps,sum_ps,convolution_coeff;simpl.
      rewrite !add0;reflexivity.
      unfold mult_ps,sum_ps,convolution_coeff;simpl; rewrite add0;reflexivity.
    - rewrite mult_ps_S.
      rewrite mps_plus_diff.
      rewrite IHi.
      unfold sum_ps.
      rewrite (mult_ps_S a).
      rewrite <-addA.
      rewrite (addC _ ((a 0%nat) * _)).
      rewrite addA.
      rewrite IHm.
      rewrite (addC (b (S i) * _)).
      rewrite addA.
      enough (b (S i) * multips_pdiff n (a 0%nat)  + (mult_ps b (fun i0 : nat => multips_pdiff n (a (S i0))) i +
   mult_ps (fun n0 : nat => a (S n0)) (fun i0 : nat => multips_pdiff n (b i0)) i)  ==  (mult_ps b (fun i0 : nat => multips_pdiff n (a i0)) (S i) +mult_ps (fun n0 : nat => a (S n0)) (fun i0 : nat => multips_pdiff n (b i0)) i)) as -> by reflexivity.
      unfold mult_ps at 3.
      rewrite (convolution_coeff_sym b).
      rewrite convolution_coeff_S.
      rewrite (convolution_coeff_sym ).
      rewrite mulC.
      rewrite addA;reflexivity.
  Qed.

  Lemma mps_diff0 {m} n : @multips_pdiff m n 0 == 0.
  Proof.
    revert n.
    induction m;intros.
    simpl;reflexivity.
    destruct n;simpl;intros.
    unfold derive_ps, zero_ps;simpl.
    rewrite ntimes_zero;reflexivity.
    apply IHm.
  Qed.

  Lemma mps_diff_ntimes {m} (a : mps m) n d : multips_pdiff d (ntimes n a) == (ntimes n (multips_pdiff d a)).  
  Proof.
    induction n.
    simpl.
    apply mps_diff0.
    simpl.
    rewrite mps_plus_diff.
    rewrite IHn;reflexivity.
  Qed.

  Lemma mps_diff_diff {m} (a : mps m) n1 n2 :   multips_pdiff n1 (multips_pdiff n2 a) == multips_pdiff n2 (multips_pdiff n1 a).
  Proof.
    revert a n1 n2.
      induction m;intros; [simpl;ring|].
      destruct n1;destruct n2.
      simpl;intros;reflexivity.
      simpl;intros;unfold derive_ps;rewrite mps_diff_ntimes;reflexivity.
      simpl;intros;unfold derive_ps;rewrite mps_diff_ntimes;reflexivity.
      simpl;intros.
      apply IHm.
   Qed.

  #[global] Instance multips_differentialring {m} : PartialDifferentialRing (A := (mps m)).
  Proof.
    exists multips_pdiff.
    - intros; apply mps_plus_diff.
    - intros; apply mps_mult_diff.
    - intros;apply mps_diff_diff.
    - apply multips_pdiff_proper.
  Defined.

  Definition mps_comp1 m : nat -> (mps m).
  Proof.
    induction m;intros n.
    apply 0.
    destruct n.
    apply comp_one_ps.
    apply ((fun n => match n with 0%nat => (IHm n) | _ => 0 end) : (mps (S m))).
  Defined.

  #[global] Instance multips_diffalgebra  : CompositionalDiffAlgebra.
  Proof.
    exists @multips_composition mps_comp1.
    (* - intros. *)
    (*   apply (const_to_mps _ X). *)
    - intros;apply multips_composition_proper.
    - intros.
      induction m.
      simpl;intros.
      admit.
      destruct i.
      simpl mps_comp1.
      admit.
      admit.
  Admitted.
End MultiPowerseries.



