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

  #[global] Instance differentialRingPoly : differentialRing (A := ps).
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
  Defined.

  #[global] Instance mps_rawRing n: RawRing (A := (mps n)).
  Proof.
    induction n.
    apply R_rawRing.
    apply ps_rawRing.
  Defined.
  
  #[global] Instance mps_comSemiRing n:  comSemiRing (A := (mps n)).
  Proof.
    intros.
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
End MultiPowerseries.


