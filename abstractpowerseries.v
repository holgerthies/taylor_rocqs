From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Require Import algebra archimedean.
Require Import functions.
Require Import polynomial.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
From Coq Require Import Classical.
Require Import tuple.
Require Import combinatorics.
Require Import Psatz.
Open Scope algebra_scope.
Section SequenceSetoid.
Context `{SemiRing}.

  #[global] Instance single_ps_set : Setoid (nat -> A).
  Proof.
      intros.
      exists (fun x y => (forall k, x k == y k)).
      constructor; intros a b; try reflexivity.
      intros eq k.
      rewrite eq;reflexivity.
      intros.
      rewrite H1.
      rewrite H2.
      reflexivity.
  Defined.

  #[global] Instance ps_set : forall d, Setoid (nat^d -> A).
  Proof.
    intros.
    exists (fun x y => (forall k, x k == y k)).
    constructor; intros a b; try reflexivity.
    intros eq k.
    rewrite eq;reflexivity.
    intros.
    rewrite H1.
    rewrite H2.
    reflexivity.
 Defined.
End SequenceSetoid.

  #[global] Instance derive_helper_proper_full `{PartialDifferentialRing } {d}  i : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (derive_rec_helper (d:=d) i).
  Proof.
    intros a b eq k1 k2 eq'.
    revert i.
    induction d;intros;simpl.
    rewrite eq;reflexivity.
    destruct (destruct_tuple_cons k1) as [hd [tl ->]].
    destruct (destruct_tuple_cons k2) as [hd' [tl' ->]].
    apply tuple_cons_equiv in eq'.
    destruct eq'.
    enough (hd = hd') as ->.
    apply nth_derivative_proper.
    setoid_rewrite IHd;try reflexivity;auto.
    simpl in H1;auto.
  Defined.

  #[global] Instance derive_rec_proper_full `{PartialDifferentialRing } {d} : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (derive_rec (d:=d)).
  Proof.
    unfold derive_rec.
    apply derive_helper_proper_full.
  Defined.

  Lemma deriv_rec_next_pdiff `{PartialDifferentialRing }  {m} f (k : nat^m) i : i<m -> (derive_rec (pdiff i f) k) == (derive_rec f (k + nth1 m i)).
  Proof.
    intros.
    unfold derive_rec.
    rewrite deriv_next_helper.
    enough (forall j , D[i+j] (derive_rec_helper j f k) == derive_rec_helper j f (k+nth1 m i)).
    replace i with (i+0)%nat at 1 by lia.
    apply H2;try lia.
    generalize dependent i;induction m;intros; try lia.
    destruct (destruct_tuple_cons k) as [k0 [kt ->]].
    destruct i.
    - replace (0+j)%nat with j%nat by lia.
      simpl nth1.
      setoid_rewrite tuple_cons_plus.
      replace (k0 +1)%nat with (S k0) by lia.
      rewrite add0.
      rewrite !derive_rec_helper_next.
      rewrite nth_derivative_S.
      rewrite nth_deriv_independent.
      reflexivity.
    - simpl nth1.
      setoid_rewrite tuple_cons_plus.
      replace (k0 +0)%nat with k0 by lia.
      rewrite !derive_rec_helper_next.
      rewrite <-nth_deriv_independent.
      apply nth_derivative_proper.
      replace (S i + j)%nat with (i + S j)%nat by lia.
      apply IHm; try lia.
  Qed.
Section AbstractPowerSeries.
  Context `{ArchimedeanField}.
  Definition ps d := nat^d -> A.

  Add Ring ARing: (ComRingTheory (A := A)). 
  Definition zero_ps d : ps d:= (fun (n : nat^d) => 0).
  Definition one_ps d (n : nat ^d) := if is_zero_tuple n then 1 else 0.
  Definition ps_plus {d} (a b : ps d) : ps d := (fun n =>  a n + b n).
  Definition ps_mult {d} (a b : ps d) : ps d.
  Proof.
    induction d.
    intros k.
    apply (a k * b k).
    intros nk.
    destruct (destruct_tuple_cons nk) as [n [k P]].
    apply (fold_right ps_plus (zero_ps d) (map (fun i => (IHd (fun k0 => a (tuple_cons i k0)) (fun k0 => b (tuple_cons (n-i)%nat k0)))) (seq 0 (S n))) k).
  Defined.

  #[global] Instance ps_rawRing {d}: RawRing (A := ps d).
  Proof.
    constructor.
    apply zero_ps.
    apply (one_ps d : ps d).
    apply (ps_plus (d := d)).
    apply (ps_mult (d:=d)).
  Defined.

  Lemma ps_mult_cons {d} (a b : nat^(S d) -> A) n k : (a*b) (tuple_cons n k) = sum (fun i => (fun k0 => a (tuple_cons i k0)) * (fun k0 => b (tuple_cons (n-i)%nat k0))) (S n) k.
  Proof.
    simpl.
    destruct (destruct_tuple_cons (tuple_cons n k)) as [n0 [k0 P]].
    unfold sum.
    apply tuple_cons_ext in P.
    destruct P as [-> ->].
    simpl.
    f_equal.
 Qed.

  Lemma index_equiv_eq d (n m : nat^d) : n == m -> n = m.
  Proof.
    intros.
    induction d.
    destruct n, m.
    apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
    clear H1.
    rewrite length_zero_iff_nil in e.
    rewrite length_zero_iff_nil in e0.
    rewrite e, e0;auto.
    destruct (destruct_tuple_cons n) as [n0 [n1 ->]].
    destruct (destruct_tuple_cons m) as [m0 [m1 ->]].
    apply tuple_cons_equiv in H1;simpl in H1.
    f_equal;try apply H1.
    apply IHd.
    apply H1.
  Qed.

  Lemma ps_mult_d0  (a b : nat^0 -> A) k : (a*b) k = (a k) * (b k).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma ps0 : forall d  (k : nat^d), (zero_ps d k) == 0.
  Proof.
    intros.
    unfold zero_ps.
    reflexivity.
  Qed.

  Lemma ps_add0 : forall d (a b : (nat^d -> A)) , (a + b) 0 == a 0 + b 0.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.


  #[global] Instance index_proper : forall {d}, Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun (a : nat^d -> A) n => a n).
  Proof.
    intros.
    intros a b eq n m eq'.
    apply index_equiv_eq in eq'.
    rewrite eq'.
    apply eq.
  Defined.
    
  #[global] Instance ps_add_proper : forall {d}, Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (ps_plus (d := d)).
  Proof.
    intros.
    intros a b eq a' b' eq'.
    intros k.
    unfold ps_plus.
    rewrite index_proper; try apply eq; try reflexivity.
    apply ring_eq_plus_eq; try reflexivity.
    rewrite index_proper; try apply eq'; try reflexivity.
  Qed.

  Lemma ps_mul0 : forall d (a b : (nat^d -> A)) , (a * b) 0 == a 0 * b 0.
  Proof.
    intros.
    induction d.
    simpl.
    reflexivity.
    rewrite vec0_cons.
    rewrite ps_mult_cons.
    simpl.
    unfold sum;simpl.
    setoid_rewrite ps_add0.
    setoid_rewrite IHd.
    rewrite ps0.
    rewrite add0.
    reflexivity.
 Qed.

  Lemma index_plus {m} (g1 g2 : nat^m -> A) (k : nat^m): (g1 + g2 ) k == g1 k + g2 k.
  Proof.
    simpl.
    reflexivity.
  Qed.   

  Lemma index_sum {m} (g: (nat -> (nat^m -> A))) (k : nat^m) N: (sum g N) k == (sum (fun i => (g i k)) N).
  Proof.
    generalize dependent g.
    induction N;intros.
    unfold sum;simpl.
    unfold zero_ps;reflexivity.
    setoid_rewrite sum_S_fun.
    rewrite index_proper; try apply sum_S_fun; try reflexivity.
    setoid_rewrite index_plus.
    rewrite IHN.
    reflexivity.
  Qed.


  #[global] Instance ps_mult_proper : forall {d}, Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (ps_mult (d := d)).
  Proof.
    intros.
    intros a b eq a' b' eq'.
    intros k.
    induction d.
    setoid_rewrite ps_mult_d0.
    rewrite index_proper; try apply eq; try reflexivity.
    apply ring_eq_mult_eq; try reflexivity.
    rewrite index_proper; try apply eq'; try reflexivity.
    destruct (destruct_tuple_cons k) as [k0 [k1 ->]].
    setoid_rewrite ps_mult_cons.
    rewrite !index_sum.
    apply sum_ext.
   intros n Hn.
   apply IHd.
   intros k;apply eq.
   intros k;apply eq'.
  Qed.
  Lemma mult_ps_comm {d} (a b : ps d) :   a * b  == b * a.
  Proof.
    induction d.
    intros k.
    setoid_rewrite ps_mult_d0;ring.
    intros k.
    destruct (destruct_tuple_cons k) as [k0 [k1 ->]].
    setoid_rewrite ps_mult_cons.
    rewrite !index_sum.
    rewrite sum_backwards.
    apply sum_ext.
    intros.
    simpl.
    replace (k0 - (k0 -n))%nat with n by lia.
    apply IHd.
  Qed.

  Lemma mult_ps_0 {d} (a : ps d) : a * 0 == 0.
  Proof.
    intros k.
    induction d.
    rewrite ps_mult_d0.
    rewrite ps0;ring.
    destruct (destruct_tuple_cons k) as [k0 [k1 ->]].
    setoid_rewrite ps_mult_cons.
    rewrite index_sum.
    apply sum_zero.
    intros.
    apply IHd.
  Qed.

  Lemma is_zero_tuple_next {d} (k : nat ^d ) : is_zero_tuple (tuple_cons 0 k) = is_zero_tuple k.
  Proof.
    destruct (is_zero_tuple k) eqn:E.
    - apply is_zero_tuple_spec.
      rewrite vec0_cons.
      apply tuple_cons_equiv_equiv; try reflexivity.
      apply is_zero_tuple_spec;auto.
   - destruct (is_zero_tuple (tuple_cons 0 k)) eqn:E';auto.
     apply is_zero_tuple_spec in E'.
     rewrite vec0_cons in E'.
     apply tuple_cons_equiv in E'.
     destruct E'.
     apply is_zero_tuple_spec in H2.
     rewrite E in H2.
     discriminate H2.
  Qed.

  Lemma mult_ps_1 {d} (a : ps d) : a * 1 == a.
  Proof.
    intros k.
    induction d.
    rewrite ps_mult_d0.
    simpl.
    unfold one_ps.
    simpl.
    ring.
    destruct (destruct_tuple_cons k) as [k0 [k1 ->]].
    setoid_rewrite ps_mult_cons.
    rewrite index_sum.
    rewrite sum_S.
    rewrite sum_zero.
    - ring_simplify.
      enough ( (fun k2 : nat ^ d => 1 (tuple_cons (k0 - k0)%nat k2)) == (1 : ps d)).
      {
        rewrite index_proper;try rewrite H1; try reflexivity. 
        apply IHd.
      }
      replace (k0 - k0)%nat with 0%nat by lia.
      intros k2.
      simpl.
      unfold one_ps.
      rewrite is_zero_tuple_next;reflexivity.
   - intros.
     enough ((fun k => 1 (tuple_cons (k0 -i)%nat k)) == (0 : ps d)).
     rewrite index_proper; try rewrite H2; try apply mult_ps_0;try reflexivity.
     intros k.
     simpl.
     unfold one_ps.
     destruct (is_zero_tuple (tuple_cons (k0 - i)%nat k)) eqn:E; try reflexivity.
     apply is_zero_tuple_spec in E.
     rewrite vec0_cons in E.
     apply tuple_cons_equiv in E.
     destruct E.
     simpl in H2.
     lia.
  Qed.

  Lemma ps_plus_index {d} (a b : ps d) k : (a + b) k == a k + b k.
  Proof.
    simpl;unfold ps_plus;ring.
  Qed.

  Lemma mult_ps_distr {d} (a b c: ps d) : a * (b+c) == a *b +  a * c.
  Proof.
    induction d;intros k.
    simpl;unfold ps_plus;ring.
    destruct (destruct_tuple_cons k) as [k0 [k1 ->]].
    rewrite ps_plus_index.
    setoid_rewrite ps_mult_cons.
    rewrite !index_sum.
    rewrite sum_plus.
    apply sum_ext.
    intros.
    apply IHd.
  Qed.

  Lemma mult_ps_cons_ps {d} (a b : ps (S d)) n :  (fun k => (a * b) (tuple_cons n k)) ==  sum (fun i => (fun k => a (tuple_cons i k)) *  (fun k => b (tuple_cons (n-i)%nat k))) (S n).
  Proof.
    intros k.
    setoid_rewrite ps_mult_cons.
    reflexivity.
  Qed.

  Definition partial_index {d} (a : ps (S d)) n : ps d := fun k => a (tuple_cons n k).

  #[global] Instance partial_index_proper {d} : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (partial_index (d:=d)).
  Proof.
    intros a b eq n m eq'.
    simpl in eq'.
    rewrite eq'.
    simpl.
    intros k.
    unfold partial_index.
    apply index_proper;auto; try reflexivity.
  Defined.

  Lemma partial_index_equiv {d} (a b : ps (S d)) : (forall n, partial_index a n == partial_index b n) <-> a == b.
  Proof.
    split;intros.
    intros k.
    destruct (destruct_tuple_cons k) as [k0 [k1 ->]].
    apply H1.
    intros k.
    apply H1.
  Qed.

  Lemma partial_index_mult_0 {d} (a b : ps (S d)): partial_index (a*b) 0 == partial_index a 0 * partial_index b 0. 
  Proof.
    intros k.
    unfold partial_index.
    setoid_rewrite ps_mult_cons.
    rewrite index_sum.
    unfold sum.
    simpl.
    rewrite add0.
    reflexivity.
  Qed.

  Definition coeff_shift1 {d} (a : ps d) := (fun k => a (k+nth1 d 0)).
  Lemma coeff_shift1_spec {d} (a : ps (S d)) n : partial_index (coeff_shift1 a) n == partial_index a (S n).
  Proof.
    unfold partial_index.
    unfold coeff_shift1.
    intros k.
    apply index_proper; try reflexivity.
    apply (tuple_nth_ext' _ _ 0  0).
    intros.
    rewrite vec_plus_spec;auto.
    destruct i.
    rewrite nth1_spec1; try lia.
    rewrite !tuple_nth_cons_hd; simpl;try lia.
    rewrite nth1_spec0;try lia.
    rewrite !tuple_nth_cons_tl.
    simpl;lia.
  Qed.

  Lemma partial_index_mult_S {d} (a b : ps (S d)) n: partial_index (a*b) (S n) == partial_index a 0 * partial_index b (S n) + partial_index ((coeff_shift1 a) * b) n.
  Proof.
    intros k.
    setoid_rewrite ps_mult_cons.
    rewrite index_sum.
    setoid_rewrite sum_S_fun.
    apply ring_eq_plus_eq.
    replace (S n - 0)%nat with (S n) by lia;reflexivity.
    unfold partial_index.
    rewrite ps_mult_cons.
    rewrite index_sum.
    apply sum_ext.
    intros.
    apply index_proper; try reflexivity.
    replace (S n - S n0)%nat with (n - n0)%nat by lia.
    apply ps_mult_proper; try reflexivity.
    clear k.
    intros k.
    unfold coeff_shift1.
    apply index_proper;try reflexivity.
    apply (tuple_nth_ext' _ _ 0  0).
    intros.
    rewrite vec_plus_spec;auto.
    destruct i.
    rewrite nth1_spec1; try lia.
    rewrite !tuple_nth_cons_hd; simpl;try lia.
    rewrite nth1_spec0;try lia.
    rewrite !tuple_nth_cons_tl.
    simpl;lia.
 Qed.
  
  Lemma add_ps_assoc {d} (a b c: ps d) : (a + b) + c == a + (b  + c).
  Proof.
    intros;simpl;intros k;unfold ps_plus;ring.
  Qed.

  Definition to_mps {d} (a : nat -> ps d) : ps (S d).
  Proof.
    intros k.
    destruct (destruct_tuple_cons k) as [k0 [kt P]].
    apply (a k0 kt).
  Defined.

  Lemma to_mps_spec {d} (a : nat -> ps d) n : partial_index (to_mps a) n == a n.
  Proof.
    intros k.
    unfold partial_index.
    unfold to_mps.
    destruct (destruct_tuple_cons (tuple_cons n k)) as [n' [k' P]].
    apply tuple_cons_ext in P.
    destruct P as [-> ->].
    reflexivity.
  Qed.

  Lemma partial_index_plus {d} {a b : ps (S d)} n : partial_index (a+b) n == partial_index a n + partial_index b n.
  Proof.
    unfold partial_index.
    intros k.
    apply ps_plus_index.
  Qed.

  Lemma partial_index0 {d} n : partial_index (d := d) 0 n == 0. 
  Proof.
     unfold partial_index.
     intros k.
     simpl.
     unfold zero_ps.
     reflexivity.
  Qed.
  Lemma const_ps_shift0 {d} (x : ps d) : coeff_shift1 (to_mps (fun k => match k with 0 => x | _ => 0 end)) == 0.
  Proof.
       apply partial_index_equiv.
       intros.
       rewrite coeff_shift1_spec.
       rewrite to_mps_spec.
       reflexivity.
  Qed.

  Lemma to_mps_smult {d} (a : nat -> ps d) (x : ps d) : to_mps (fun k => x * a k) == to_mps (fun k => match k with 0 => x | _ => 0 end) * to_mps a.
  Proof.
    apply partial_index_equiv.
    intros.
    rewrite !to_mps_spec.
    induction n.
    - rewrite partial_index_mult_0.
      rewrite !to_mps_spec;reflexivity.
   - rewrite partial_index_mult_S.
     rewrite !to_mps_spec.
     rewrite const_ps_shift0.
     setoid_rewrite mult_ps_comm.
     rewrite mult_ps_0.
     rewrite partial_index0.
     intros k.
     rewrite ps_plus_index.
     simpl.
     unfold zero_ps.
     ring.
  Qed.

  Lemma partial_index_mult_const {d} (a : ps (S d)) x n : partial_index ((to_mps (fun k => match k with 0 => x | _ => 0 end)) * a) n == x * partial_index a n.
  Proof.
    destruct n.
    - rewrite partial_index_mult_0.
      rewrite to_mps_spec.
      reflexivity.
    - rewrite partial_index_mult_S.
      rewrite to_mps_spec.
      rewrite const_ps_shift0.
       setoid_rewrite mult_ps_comm.
       rewrite mult_ps_0.
       rewrite partial_index0.
       intros k.
       rewrite ps_plus_index.
       simpl.
       unfold zero_ps.
       ring.
   Qed.

  Lemma to_mps_partial_index {d} (a : ps (S d)) : to_mps (partial_index a) == a.
  Proof.
    apply partial_index_equiv.
    intros n.
    apply to_mps_spec.
  Qed.

  Lemma mult_ps_assoc {d} (a b c: ps d) : (a * b) * c == a * (b  * c).
  Proof.
    induction d.
    intros k.
    rewrite !ps_mult_d0;ring.
    apply partial_index_equiv.
    intros.
    generalize dependent a.
    generalize dependent b.
    induction n;intros.
    - rewrite !partial_index_mult_0.
      apply IHd.
    - rewrite !partial_index_mult_S.
      rewrite partial_index_mult_0.
      rewrite !mult_ps_distr.
      rewrite add_ps_assoc.
      rewrite IHd.
      apply ps_add_proper;try reflexivity.
      rewrite <-IHn.
      assert (coeff_shift1 (a*b) == (to_mps (fun k => partial_index a 0 * partial_index (coeff_shift1 b) k) + to_mps (fun k => partial_index ((coeff_shift1 a) * b) k))) as ->.
      {
          apply partial_index_equiv.
          intros.
          rewrite coeff_shift1_spec.
          rewrite partial_index_mult_S.
          rewrite partial_index_plus.
          rewrite !to_mps_spec.
          rewrite coeff_shift1_spec.
          reflexivity.
      }
      rewrite to_mps_smult.
      setoid_rewrite mult_ps_comm.
      rewrite mult_ps_distr.
      rewrite partial_index_plus.
      apply ps_add_proper.
      + rewrite mult_ps_comm.
        rewrite IHn.
        rewrite partial_index_mult_const.
        rewrite to_mps_partial_index.
        rewrite mult_ps_comm.
        reflexivity.
      + apply partial_index_proper; try reflexivity.
        apply ps_mult_proper; try reflexivity.
        apply partial_index_equiv.
        intros;rewrite to_mps_spec;reflexivity.
  Qed.

  #[global] Instance ps_SemiRing {d} :  SemiRing (A := ps d).
  Proof.
    constructor.
    - apply ps_add_proper.
    - apply ps_mult_proper.
    - intros;simpl;intros k;unfold ps_plus;ring.
    - intros;simpl;intros k;unfold ps_plus;ring.
    - intros;simpl;intros k;unfold ps_plus; rewrite ps0;ring.
    - apply mult_ps_assoc.
    - apply mult_ps_comm.
    - apply mult_ps_0.
    - apply mult_ps_1.
    - apply mult_ps_distr.
 Defined.

  (* Context `{invSn : Sn_invertible (A := A) (H := _) (R_rawRing := _) (H0 := _)}. *)
  Definition tuple_derive {d} (a : ps d) (k : nat^d) : ps d := (fun (j : nat^d) => t[j+1!k] * a (k+j)).   
  Definition ps_pdiff {d} i (a : ps d)  : ps d := match  (d - i)%nat with 0 => 0 | _ => tuple_derive a (nth1 d i) end.

  Definition ps_smul {d}  x (a : ps d)  : ps d := fun k => x * a k.
  Infix "[*]" := ps_smul.
  Definition ps_pdiff_first {d} (a : ps (S d)) n :  partial_index (ps_pdiff 0 a) n ==  partial_index (ps_smul #(S n) a)  (S n).
  Proof.
   unfold ps_smul.
    intros.
    intros k.
    unfold partial_index, ps_pdiff, tuple_derive.
    apply ring_eq_mult_eq.
    - rewrite rising_factorialt_unfold.
      setoid_replace (tuple_cons n k + nth1 (S d) 0) with (tuple_cons (S n) k).
      rewrite factt_S.
      rewrite mulA.
      rewrite fact_invfactt.
      replace (n+1)%nat with (S n) by lia.
      ring.
      apply (tuple_nth_ext' _ _ 0 0).
      intros.
      destruct i; rewrite vec_plus_spec;auto; [rewrite nth1_spec1,!tuple_nth_cons_hd | rewrite nth1_spec0,!tuple_nth_cons_tl ]; simpl; try lia.
   -  apply index_proper; try reflexivity.
      simpl nth1.
      rewrite tuple_cons_plus.
      rewrite addC, add0.
      apply tuple_cons_equiv_equiv;try reflexivity; simpl;try lia.
    Qed.

  Definition ps_pdiff_next {d} i (a : ps (S d)) n :  partial_index (ps_pdiff (S i) a) n == ps_pdiff i (partial_index a n).
  Proof.
     intros.
     unfold partial_index, ps_pdiff, tuple_derive.
     replace (S d - S i)%nat with (d - i)%nat by lia.
     destruct (d-i)%nat; try reflexivity.
     intros k.
     apply ring_eq_mult_eq.
    - rewrite !rising_factorialt_unfold.
      enough (tuple_cons n k + nth1 (S d)  (S i) == tuple_cons n (k + nth1 d i)) as ->.
      rewrite !factt_cons, !inv_factt_cons.
      rewrite (mulC ![n]), <-!mulA, mulC, <-!mulA, (mulC ![n]).
      rewrite fact_invfact.
      ring.
      simpl nth1.
      rewrite tuple_cons_plus.
      replace (n+0)%nat with n by lia.
      reflexivity.
   -  apply index_proper; try reflexivity.
      simpl nth1.
      rewrite tuple_cons_plus.
      replace (0+n)%nat with n by lia.
      reflexivity.
  Qed.

  Lemma ps_diff_plus {d} (a b : ps d) k : tuple_derive (a+b) k == tuple_derive a k + tuple_derive b k.
  Proof.
    intros j.
    simpl.
    unfold tuple_derive.
    unfold ps_plus.
    ring.
  Qed.

  Lemma ps_pdiff_plus {d} (a b : ps d) i : ps_pdiff i (a+b)  == ps_pdiff i a + ps_pdiff i b.
  Proof.
     intros; unfold ps_pdiff;destruct (d-i)%nat;simpl; try apply ps_diff_plus.
     intros k.
     unfold zero_ps, ps_plus;ring.
  Qed.

  Lemma ps_diff_switch {d} (a: ps d) k j: tuple_derive (tuple_derive a j) k == tuple_derive (tuple_derive a k) j.
  Proof.
    intros i.
    unfold tuple_derive.
    simpl.
    rewrite <-!mulA.
    apply ring_eq_mult_eq.
    - rewrite !rising_factorialt_unfold.
      setoid_replace (k+i) with (i+k) by apply addC.
      ring_simplify.
      rewrite mulC.
      rewrite <-!mulA.
      rewrite invfact_factt.
      ring_simplify.
      rewrite !mulA.
      apply ring_eq_mult_eq; try reflexivity.
      rewrite mulC,mulA.
      setoid_replace (j+i) with (i+j) by apply addC.
      rewrite invfact_factt.
      ring_simplify.
      setoid_replace (i+j+k) with (i+k+j); try reflexivity.
      rewrite !(addC _ k), addA;reflexivity.
    - apply index_proper; try reflexivity.
      rewrite addC, (addC j), <-addA;reflexivity.
 Qed.

  #[global] Instance ps_diff_proper {d}: Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (tuple_derive (d := d)).
  Proof.
    intros a b eq k j eq'.
    intros i.
    unfold tuple_derive.
    apply ring_eq_mult_eq.
    rewrite eq';reflexivity.
    apply index_proper;auto.
    rewrite eq'.
    reflexivity.
  Defined.

  #[global] Instance ps_pdiff_proper {d} n : Proper (SetoidClass.equiv ==> SetoidClass.equiv ) (ps_pdiff (d := d) n).
  Proof.
     intros a b eq.
     unfold ps_pdiff;destruct (d-n)%nat;simpl; intros; try reflexivity.
     apply ps_diff_proper;auto;reflexivity.
  Defined.


  Opaque embNat.
  Lemma ps_ntimes_S {d} (a : ps d) n  : (fun k => #(S n) * a k) == (fun k => #n * a k) + a.
  Proof.
    intros k.
    simpl.
    setoid_rewrite ps_plus_index.
    rewrite !ntimes_embed.
    simpl.
    ring.
  Qed.

  Lemma ps_smul_mult {d} (a b : ps d) x  :  x [*] (a * b) == (x [*] a) * b.
  Proof.
    unfold ps_smul.
    induction d; intros k.
    simpl;ring.
    destruct (destruct_tuple_cons k) as [k0 [kt ->]].
    setoid_rewrite ps_mult_cons.
    rewrite !index_sum.
    rewrite sum_mult.
    apply sum_ext.
    intros.
    specialize (IHd (fun k1 => a (tuple_cons n k1)) (fun k1 => b (tuple_cons (k0-n)%nat k1)) kt).
    apply IHd.
  Qed.

  Lemma ps_smul_mult2 {d} (a b : ps d) x  :  x [*] (a * b) == a * (x [*] b).
  Proof.
    unfold ps_smul.
    induction d; intros k.
    simpl;ring.
    destruct (destruct_tuple_cons k) as [k0 [kt ->]].
    setoid_rewrite ps_mult_cons.
    rewrite !index_sum.
    rewrite sum_mult.
    apply sum_ext.
    intros.
    specialize (IHd (fun k1 => a (tuple_cons n k1)) (fun k1 => b (tuple_cons (k0-n)%nat k1)) kt).
    apply IHd.
  Qed.

  Lemma pdiff_shift {d} (a : ps (S d)) : ps_pdiff 0 a == coeff_shift1 (fun k => #(k\_0) * a k).
  Proof.
    apply partial_index_equiv.
    intros n.
    rewrite ps_pdiff_first.
    rewrite coeff_shift1_spec.
    intros k; unfold partial_index.
    rewrite tuple_nth_cons_hd.
    unfold ps_smul.
    ring.
  Qed.

  Lemma pdiff_partial_index_shift {d} (a : ps (S d)) n : partial_index (ps_pdiff 0 a) n == #(S n) [*] (partial_index a (S n)).
  Proof.
    rewrite ps_pdiff_first.
    intros k.
    unfold partial_index.
    unfold ps_smul.
    simpl.
    ring.
  Qed.

  Lemma ps_property_backwards {d} (a : nat^d -> A) k : a k == t![k] * (tuple_derive a k) 0.
  Proof.
    unfold tuple_derive.
    rewrite <-mulA.
    setoid_replace (0 +1 : nat^d) with (1 : nat^d) by (rewrite addC;apply add0).
    rewrite rising_factorialt1.
    rewrite invfact_factt.
    rewrite mulC,mul1.
    apply index_proper;try reflexivity.
    rewrite add0;reflexivity.
  Qed.

  Lemma deriv_next {d} (f : nat^(S d) -> A) hd tl : ps_pdiff 0 f (tuple_cons hd tl)  == # (hd+1) * f (tuple_cons (hd+1)%nat tl). 
  Proof.  
    replace (hd+1)%nat with (S hd) at 2 by lia.
    rewrite (ps_property_backwards f).
    rewrite <-mulA.
    rewrite inv_factt_S_reverse.
    assert (ps_pdiff 0 f = tuple_derive f (nth1 (S d) 0)) as -> by (simpl;auto).
    unfold tuple_derive.
    rewrite <-mulA.
    apply ring_eq_mult_eq.
    rewrite rising_factorialt_unfold.
    rewrite mulC.
    apply ring_eq_mult_eq; try reflexivity.
    rewrite rising_factorialt_unfold.
    rewrite inv_factt0, mul1.
    rewrite (addC 0), add0.
    apply fact_t_proper.
    simpl nth1.
    rewrite tuple_cons_plus.
    rewrite add0.
    apply tuple_cons_equiv_equiv; try reflexivity;simpl;lia.
    apply index_proper;try reflexivity.
    rewrite add0.
    simpl nth1; rewrite tuple_cons_plus.
    rewrite (addC 0), add0.
    apply tuple_cons_equiv_equiv; try reflexivity;simpl;lia.
  Qed.
    
  Lemma partial_index_mul_sum {d} (a b : ps (S d)) n : partial_index (a*b) n == sum (fun i => partial_index a i * partial_index b (n - i)) (S n).
  Proof.
    unfold partial_index.
    intros k.
    setoid_rewrite ps_mult_cons.
    reflexivity.
  Qed.

  Lemma smul_plus_compat {d} (a : ps d) x y : (x+y) [*] a == x[*]a + y[*]a.  
  Proof.
    unfold ps_smul.
    intros k.
    setoid_rewrite index_plus.
    ring.
  Qed.

  Lemma smul_plus_compat2 {d} (a b : ps d) x : x [*] (a +b) == x[*]a + x[*]b.  
  Proof.
    unfold ps_smul.
    intros k.
    setoid_rewrite index_plus.
    ring.
  Qed.

  Lemma smul_sum {d} (a : nat -> ps d) x n : sum (fun k => x [*] (a k)) n == x [*] (sum a n).
  Proof.
    unfold ps_smul.
    intros k.
    setoid_rewrite index_sum.
    rewrite sum_mult.
    reflexivity.
  Qed.

  #[global] Instance ps_smul_proper {d}: Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (ps_smul (d := d)).
  Proof.
    intros x y eq a b eq'.
    unfold ps_smul.
    intros k.
    rewrite eq.
    apply ring_eq_mult_eq;try reflexivity.
    apply eq'.
  Qed.

  
  Lemma ps_diff_product0 {d} (a b : ps d): ps_pdiff 0 (a*b) == b * ps_pdiff 0 a + a * ps_pdiff 0 b.
  Proof.
    destruct d.
    - unfold ps_pdiff;simpl; unfold ps_plus.
      intros.
      rewrite ps0;ring.
    - apply partial_index_equiv.
      intros.
      rewrite partial_index_plus.
      rewrite (mulC b).
      rewrite !partial_index_mul_sum.
      rewrite sum_S.
      replace (n-n)%nat with 0%nat by lia.
      rewrite sum_S_fun.
      replace (n-0)%nat with n%nat by lia.
      rewrite addC, addA,addC, <-addA.
      rewrite sum_plus.
      assert (forall i, (i < n)%nat -> partial_index a (S i) * partial_index (ps_pdiff 0 b) (n - S i ) + partial_index (ps_pdiff 0 a) i * partial_index b (n - i) == (# (S n)) [*] (partial_index a (S i) * partial_index b (n - i))).
      {
        intros.
        rewrite !pdiff_partial_index_shift.
        
        setoid_rewrite <-ps_smul_mult.
        rewrite <-ps_smul_mult2.
        replace (S (n- S i))%nat with (n-i)%nat by lia.
        rewrite <-smul_plus_compat.
        setoid_rewrite <-nat_plus_compat.
        replace (n-i + S i)%nat with (S n) by lia.
        reflexivity.
      }
      rewrite sum_ext; try apply H1.
      clear H1.

      rewrite !pdiff_partial_index_shift.
      rewrite partial_index_mul_sum.
      rewrite <-ps_smul_mult2.
      rewrite smul_sum.
      rewrite sum_S.
      rewrite sum_S_fun.
      rewrite addA,addC, !addA.
      rewrite smul_plus_compat2.
      apply ring_eq_plus_eq; try reflexivity.
      rewrite smul_plus_compat2.
      replace (S n - S n)%nat with 0%nat by lia.
      replace (S n - 0)%nat with (S n) by lia.
      apply ring_eq_plus_eq; try reflexivity.
      rewrite ps_smul_mult.
      reflexivity.
  Qed.
  Lemma ps_pdiff_sum {d} (a : nat -> ps d) n i : ps_pdiff i (sum a n) == sum (fun k => ps_pdiff i (a k)) n.
  Proof.
    induction n.
    unfold sum.
    intros k.
    simpl.
    unfold ps_pdiff, tuple_derive.
    destruct (d-i)%nat; try reflexivity.
    rewrite mul0;reflexivity.
    rewrite !sum_S.
    rewrite ps_pdiff_plus.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma ps_diff_product {d} (a b : ps d) i: ps_pdiff i (a*b) == b * ps_pdiff i a + a * ps_pdiff i b.
  Proof.
    generalize dependent d.
    induction i; intros; [apply ps_diff_product0 |].
    destruct d.
    simpl.
    intros.
    setoid_rewrite index_plus.
    unfold ps_pdiff, tuple_derive.
    simpl.
    rewrite ps0;ring.
    apply partial_index_equiv.
    intros.
    rewrite partial_index_plus.
    rewrite !ps_pdiff_next.
    rewrite !partial_index_mul_sum.
    rewrite ps_pdiff_sum.
    rewrite sum_ext; try (intros;apply IHi).
    rewrite <-sum_plus.
    apply ring_eq_plus_eq.
    - rewrite sum_backwards.
      apply sum_ext.
      intros.
      replace (n - (S n - S n0))%nat with n0 by lia.
      replace (S n - S n0)%nat with (n - n0)%nat by lia.
      rewrite ps_pdiff_next.
      reflexivity.
    - apply sum_ext.
      intros.
      rewrite ps_pdiff_next.
      reflexivity.
  Qed.

  #[global] Instance ps_diffRing {d} :  PartialDifferentialRing (A := ps d).
  Proof.
     exists (ps_pdiff (d := d)).
     - intros; apply ps_pdiff_plus.
     - intros;apply ps_diff_product.
     - intros;unfold ps_pdiff;destruct (d-d1)%nat;destruct (d-d2)%nat;simpl; try apply ps_diff_switch; unfold tuple_derive;intros k;simpl;try rewrite !ps0;ring.
     - apply ps_pdiff_proper. 
  Defined.

  Lemma deriv_rec_1 {d} (f : nat^d -> A) hd (tl : nat^0) : (derive_rec f (tuple_cons hd tl)) == nth_derivative 0 f hd.
  Proof.
    unfold derive_rec;simpl.
    destruct (destruct_tuple_cons (tuple_cons hd tl)) as [hd' [tl' P]].
    apply tuple_cons_ext in P.
    destruct P as [-> ->].
    reflexivity.
  Qed.

  Lemma order_nonzero {d} (v : nat^d) : order v <> 0 -> {i | v\_i <> 0}.
  Proof.
    intros.
    induction d.
    simpl in H1;lia.
    destruct (destruct_tuple_cons v) as [hd [tl ->]].
    destruct hd eqn:E.
    - rewrite order_cons in H1.
      destruct (IHd tl); try apply H1.
      exists (S x).
      rewrite tuple_nth_cons_tl;auto.
   -  exists 0.
      rewrite tuple_nth_cons_hd;auto.
  Qed.

  Definition tuple_pred {d} (v : nat^d) : nat^d.
  Proof.
    induction d.
    apply v.
    destruct (destruct_tuple_cons v) as [n [vt ->]].
    destruct n.
    apply (tuple_cons 0 (IHd vt)).
    apply (tuple_cons n vt).
  Defined.



  Lemma tuple_pred_cons0 {d} (v : nat^d) : tuple_pred (tuple_cons 0 v) == tuple_cons 0 (tuple_pred v).
  Proof.
    simpl tuple_pred.
    destruct (destruct_tuple_cons (tuple_cons 0 v)) as [z [v' P]] eqn:E.
    setoid_rewrite E.
    clear E.
    apply tuple_cons_ext in P.
    destruct P as [<- <-].
    reflexivity.
  Qed.

  Lemma tuple_pred_cons_S {d} (v : nat^d) i : tuple_pred (tuple_cons (S i) v) == tuple_cons i v.
  Proof.
    simpl tuple_pred.
    destruct (destruct_tuple_cons (tuple_cons (S i) v)) as [z [v' P]].
    apply tuple_cons_ext in P.
    destruct P as [<- <-].
    reflexivity.
  Qed.

  Lemma tuple_pred_spec {d} (v : nat^d) : order v <> 0 -> {i | i < d /\ v == tuple_pred v + nth1 d i}.
  Proof.
    intros.
    induction d.
    simpl in H1;lia.
    destruct (destruct_tuple_cons v) as [n [vt ->]].
    destruct n.
    - rewrite order_cons in H1.
      destruct (IHd vt); try apply H1.
      exists (S x).
      split;try lia.
      setoid_rewrite tuple_pred_cons0.
      simpl nth1.
      rewrite tuple_cons_plus.
      apply tuple_cons_equiv_equiv;  simpl;try lia.
      apply a.
   - exists 0.
     rewrite tuple_pred_cons_S.
      simpl nth1.
      rewrite tuple_cons_plus.
      rewrite add0.
      split;try (simpl;lia).
      apply tuple_cons_equiv_equiv;  try (simpl;lia);try reflexivity.
  Qed.

  Lemma tuple_pred_order {d} (v : nat^d) : order (tuple_pred v) = pred (order v).
  Proof.
    induction d.
    simpl;lia.
    destruct (destruct_tuple_cons v) as [n [vt ->]].
    destruct n.
    rewrite tuple_pred_cons0.
    rewrite !order_cons.
    rewrite IHd.
    simpl.
    lia.
    rewrite !tuple_pred_cons_S.
    rewrite !order_cons.
    lia.
Qed.
  Lemma order_zero_eq_zero {d} (k :nat^d) : order k = 0 -> k == 0.
  Proof.
    intros.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite vec0_nth.
    rewrite order_zero; try reflexivity;auto.
  Qed.

  Lemma deriv_zero {d e}  (a : ps d): Dx[(0 : nat^e)] a == a.
  Proof.
    enough (forall i, derive_rec_helper (d:=e) i a 0 == a ) by apply H1.
    induction e;intros.
    simpl.
    intros.
    simpl;reflexivity.
    simpl derive_rec_helper.
    destruct (destruct_tuple_cons (0 : nat^(S e))) as [z [zt P]].
    setoid_rewrite vec0_cons in P.
    apply tuple_cons_ext in P.
    destruct P as [<- <-].
    setoid_rewrite IHe.
    reflexivity.
  Qed.

  Lemma ps_derive_spec {d} (a : ps d) k: Dx[k] a == tuple_derive a k.
  Proof.
    enough (forall n, order k = n -> Dx[k] a == tuple_derive a k). apply (H1 (order k));reflexivity.
    intros n.
    generalize dependent k.
    generalize dependent a.
    induction n;intros.
    - apply order_zero_eq_zero in H1.
      rewrite H1.
      intros j'.
      unfold tuple_derive.
      rewrite rising_factorialt_unfold.
      rewrite add0.
      rewrite fact_invfactt.
      ring_simplify.
      apply index_proper; try rewrite addC,add0; try reflexivity.
      apply deriv_zero.
   - destruct (tuple_pred_spec k); try (simpl;lia).
     destruct a0.
     rewrite H3.
     rewrite <-deriv_rec_next_pdiff;auto.
     rewrite IHn;try rewrite tuple_pred_order;try lia.
     unfold pdiff.
     simpl tuple_derive.
     unfold ps_pdiff.
     destruct (d-x)%nat eqn:E; try lia.
     clear E.
     setoid_rewrite ps_diff_switch.
     unfold tuple_derive.
     intros j.
     simpl.
     rewrite <-mulA.
     apply ring_eq_mult_eq.
     rewrite !rising_factorialt_unfold.
     setoid_replace (t[ j + nth1 d x ]! * t![ j] * (t[ nth1 d x + j + tuple_pred k ]! * t![ nth1 d x + j])) with ((t[ nth1 d x + j + tuple_pred k ]!  * t![ j]) * (t[ j + nth1 d x ]! * t![ nth1 d x + j])) by ring.
     rewrite (addC j), fact_invfactt, mul1.
     apply ring_eq_mult_eq; try reflexivity.
     apply fact_t_proper.
     rewrite addC, (addC j), addA.
     reflexivity.
     apply index_proper; try reflexivity.
     rewrite addA;reflexivity.
 Qed.

  Lemma ps_derive : forall {d} (a : (nat^d -> A)) (k j : nat^d),  (Dx[k] a) j == t[j+1!k] * a (k+j).
  Proof.
    intros.
    rewrite index_proper; try apply ps_derive_spec; try reflexivity.
  Qed.

  Lemma cauchy_product {d} (a b : nat^(S d) -> A) n k : (a*b) (tuple_cons n k) == sum (fun i => (fun k0 => a (tuple_cons i k0)) * (fun k0 => b (tuple_cons (n-i)%nat k0))) (S n) k.
  Proof.
   rewrite ps_mult_cons.
   reflexivity.
  Qed.

  Definition ps_order_def d (P : (forall n, (forall (k : nat^d), (order  k) = n -> A))): ps d. 
  Proof.
    intros k.
    apply (P (order k) k).
    reflexivity.
  Defined.

  (* Definition ps_diff_def d (x0 : A) (f: (forall i, i <d -> A) -> A):  {a : ps d | foralli, D[i]  } *)
  (* Proof. *)
  (*  intros. *)
  (*  apply ps_order_def. *)
  (*  intros. *)
  (*  generalize dependent k. *)
  (*  induction n;intros. *)
  (*  apply x0. *)
  (*  destruct (tuple_pred_spec k); try (simpl;lia). *)
  (*  apply () *)

  Lemma deriv_next_backwards {d} (f : nat^(S d) -> A) hd tl : f (tuple_cons (S hd) tl) == (inv_Sn hd) * (D[0] f) (tuple_cons hd tl).
  Proof.  
    pose proof (inv_Sn_spec hd).
    rewrite <-mul1.
    rewrite <-H1.
    rewrite mulC.
    rewrite <-ntimes_embed.
    rewrite (mulC (# (S hd))).
    rewrite mulA.
    replace (S hd) with (hd + 1)%nat by lia.
    rewrite <-deriv_next.
    reflexivity.
  Qed.

  Lemma deriv_next_full {d} (f : nat^d -> A) k i : i < d -> D[i] f k  == # (k\_i+1) * f (k + nth1 d i).
  Proof.
    revert i.
    induction d;intros;try lia.
    destruct i.
    destruct (destruct_tuple_cons k) as [k0 [t ->]].
    setoid_rewrite deriv_next.
    rewrite tuple_nth_cons_hd.
    apply ring_eq_mult_eq; try reflexivity.
    apply index_proper; try reflexivity.
    setoid_rewrite tuple_cons_plus.
    rewrite add0.
    reflexivity.
    destruct (destruct_tuple_cons k) as [k0 [t ->]].
    pose proof (ps_pdiff_next i f k0 t).
    rewrite H2.
    setoid_rewrite IHd; try lia.
    rewrite tuple_nth_cons_tl.
    apply ring_eq_mult_eq; try reflexivity.
    simpl.
    unfold partial_index.
    apply index_proper; try reflexivity.
    rewrite tuple_cons_plus.
    replace (k0+0)%nat with k0 by lia.
    reflexivity.
  Qed.

  Lemma zero_tuple1 : (0 : nat^1) == t(0).
  Proof.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite vec0_nth.
    assert (i = 0)%nat as -> by lia.
    simpl.
    reflexivity.
  Qed.
  Lemma exchange_ps_factor (h h' g : nat^1 -> A) (k : nat) : (forall i, (i <= k)%nat -> (h t(i)) == (h' t(i))) -> (h * g) t(k) == (h' * g) t(k).
  Proof.
    revert h h' g.
    induction k;intros.
    - rewrite !ps_mul0.
      enough (h 0 == h' 0) as -> by reflexivity.
      assert (0 <= 0)%nat by lia.
      specialize (H1 _ H2).
      transitivity (h t(0)).
      apply index_proper;try reflexivity.
      rewrite H1.
      apply index_proper;try reflexivity.
    - rewrite !deriv_next_backwards.
      apply ring_eq_mult_eq; try reflexivity.
      rewrite index_proper; try apply pdiff_mult; try reflexivity.
      rewrite (index_proper (D[ 0] (h' * g)) _ (pdiff_mult _ _ _ ) t(k) t(k)); try reflexivity.
      rewrite !index_plus.
      apply ring_eq_plus_eq.
      + rewrite (index_proper (g *  (D[0] h)) _ (mulC _ _ ) t(k) t(k)); try reflexivity.
        rewrite (index_proper (g *  (D[0] h')) _ (mulC _ _ ) t(k) t(k)); try reflexivity.
        apply IHk.
        intros.
        setoid_rewrite deriv_next.
        apply (ring_eq_mult_eq); try reflexivity.
        apply H1; lia.
      + apply IHk.
        intros.
        apply H1;auto.
   Qed.


  Lemma deriv_eq_ps_equal {m} (a b : (nat^m -> A)) : (forall (k : nat^m), (Dx[k] a) == (Dx[k] b)) -> a == b.
  Proof.

    intros.
    intros i.
    rewrite ps_property_backwards.
    rewrite (ps_property_backwards b).
    apply ring_eq_mult_eq;try reflexivity.
    apply index_proper;try reflexivity.
    rewrite <-!ps_derive_spec.
    apply H1.
  Qed.

  Lemma deriv_eq_ps_equal1  (a b : (nat^1 -> A)) : (forall (k : nat), nth_derivative 0 a k == nth_derivative 0 b k) -> a == b.
  Proof.
    intros.
    apply deriv_eq_ps_equal.
    intros.
    destruct (destruct_tuple_cons k) as [k0 [N ->]].
    rewrite !deriv_rec_1.
    apply H1.
  Qed.

  Definition prefix_limit {d}  (an : forall n, ps d): (forall n k, (order k <= n)%nat -> an n k == an (S n) k) -> ps d.
  Proof.
    intros.
    apply ps_order_def.
    intros.
    apply (an n k).
  Defined.

  (* Definition initial_segment {d} n  (forall (k : nat^d), (order k <= n)%nat -> A) : ps d := fun k => if (order k <=? n) then (X _ ). *)
  (* Proof. *)
  (*   intros. *)
  (*   intros k. *)
  (*   destruct (le_lt_dec (order k) n). *)
  (*   apply (X _ l). *)
  (*   apply 0. *)
  (* Defined. *)

  Lemma prefix_limit_spec {d} (an : nat -> ps d) P :forall k, forall n, (order k <= n)%nat -> prefix_limit an P k == an n k.
  Proof.
    intros.
    induction n.
    - unfold prefix_limit, ps_order_def.
      assert (order k = 0)%nat as -> by lia.
      reflexivity.
   - assert ((order k <= n)%nat \/ (order k = S n)%nat) by lia.
     destruct H2;[rewrite <-P;auto|].
     unfold prefix_limit, ps_order_def.
     rewrite H2.
     reflexivity.
  Qed.


  (* Definition ps_composition_next n m (xn : ps (S m)) (bs : @tuple n (ps (S m))) (i : nat) v (k : nat^(S m))  : A. *)
  (* Proof. *)
  (*   apply ((inv_Sn i) * ((sum (fun j => D[v] bs\_j * (IHi (D[j] a))) n) (tuple_pred k))). *)
  (*   destruct (order k =? S i) eqn:E; [|apply 0]. *)
  (*   apply Nat.eqb_eq in E. *)
  (*   destruct (tuple_pred_spec k); try (simpl in *;lia). *)
  (*   apply ((inv_Sn i) * ((sum (fun j => D[x] bs\_j * xn ) n) (tuple_pred k))). *)
  (* Defined. *)

  Definition pred_index {d} (k : nat^d): nat.
  Proof.
    destruct (order k) eqn:E.
    apply 0.
    assert (order k <> 0) by (simpl in *;lia).
    apply (proj1_sig (tuple_pred_spec k H1)).
  Defined.

  Definition ps_composition_ith n m (a : ps n) (bs : @tuple n (ps (S m))) (i : nat) : (ps (S m)).
  Proof.
    revert a.
    induction i;intros.
    - intros k.
      apply (match (order k) with 0%nat => (a 0) | _ => 0 end).
    - intros k.
      destruct (order k <? (S i)) eqn:E;[apply (IHi a k) | ].
      destruct (order k =? S i) eqn:E'; [|apply 0].
      apply ((inv_Sn k\_(pred_index k)) * ((sum (fun j => D[pred_index k] bs\_j * (IHi (D[j] a))) n) (tuple_pred k))).
 Defined.


  Definition ps_comp_ith_converging n m a bs : forall i k, (order k <= i)%nat -> (ps_composition_ith n m a bs i k) = (ps_composition_ith n m a bs (S i) k).
  Proof.
    intros.
    Opaque order.
    simpl.
    Transparent order.
    enough (order k <? S i = true) as -> by auto.
    apply Nat.ltb_lt;lia.
 Qed.

  Definition ps_comp_ith_larger n m a bs : forall i k, (order k <= i)%nat -> (ps_composition_ith n m a bs i k) = (ps_composition_ith n m a bs (order k) k).
  Proof.
    intros.
    generalize dependent k.
    induction i;intros.
    assert (order k = 0)%nat by lia.
    rewrite H2.
    reflexivity.
    assert (order k <= i \/ order k = S i)%nat by lia.
    destruct H2.
    rewrite <-IHi; try lia.
    rewrite <-ps_comp_ith_converging; try lia;auto.
    rewrite H2.
    reflexivity.
 Qed.
  Definition ps_composition n m (a : ps n) (bs : @tuple n (ps (S m))) : (ps (S m)).
  Proof.
    apply (prefix_limit (ps_composition_ith n m a bs)).
    intros.
    rewrite ps_comp_ith_converging;auto;reflexivity.
  Defined.

  Definition ps_comp1 m : nat -> (ps m).
  Proof.
    intros n k.
    destruct (order k =? 1) eqn:E.
    - apply Nat.eqb_eq in E.
      destruct (k\_n =? 1).
      apply 1.
      apply 0.
   - apply 0.
  Defined.

  Lemma prefix_limit_simpl {d} (an : nat -> ps d) P :forall k, prefix_limit an P k == an (order k) k.
  Proof.
     intros.
     apply prefix_limit_spec;auto.
  Qed.

  Lemma ps_eq_order {d} (a b : ps d): (forall n, (forall k, (order k = n) -> a k == b k)) -> a == b.
  Proof.
    intros.
    intros k.
    apply (H1 (order k));auto.
  Qed.

  Lemma ps_composition_simpl n m a bs k : ps_composition n m a bs k == ps_composition_ith n m a bs (order k) k.
  Proof.
    unfold ps_composition.
    apply prefix_limit_simpl.
  Qed.

  Opaque order add tuple_pred sum mul.
  Lemma ps_composition_ith_next n m a bs i k : order k = (S i) -> ps_composition_ith n m a bs (S i) k == (inv_Sn k\_(pred_index k))  * (sum (fun j => D[pred_index k] bs\_j * (ps_composition_ith n m (D[j] a) bs i)) n (tuple_pred k)).
  Proof.
     intros.
     simpl.
     rewrite H1.
     simpl.
     rewrite Nat.ltb_irrefl.
     rewrite Nat.eqb_refl.
     reflexivity.
  Qed.
  

   Lemma partial_index_ps_comp1_first0 {d} : partial_index (ps_comp1 (S d) 0) 0 == 0.
   Proof.
     intros k.
     unfold partial_index.
     unfold ps_comp1.
     rewrite order_cons.
     replace (0 + order k)%nat with (order k) by lia.
     rewrite tuple_nth_cons_hd.
     destruct (order k =? 1) eqn:E; try reflexivity.
   Qed.

   Lemma partial_index_ps_comp1_first0' {d} k : k <> 1 ->  partial_index (ps_comp1 (S d) 0) k == 0.
   Proof.
     intros.
     destruct k.
     apply partial_index_ps_comp1_first0.
     intros j.
     unfold partial_index.
     unfold ps_comp1.
     rewrite order_cons.
     destruct (order j) eqn:E.
     simpl.
     replace (k+0)%nat with k by lia.
     destruct (k =? 0) eqn:E'; try reflexivity.
     apply Nat.eqb_eq in E'.
     simpl in H1.
     lia.
     simpl.
     replace (k + S n)%nat with (S (k+n)%nat) by lia.
     simpl.
     reflexivity.
   Qed.
   Lemma partial_index_ps_comp1_first1 {d} : partial_index (ps_comp1 (S d) 0) 1 == 1.
   Proof.
     intros k.
     unfold partial_index.
     unfold ps_comp1.
     rewrite order_cons.
     simpl.
     destruct (order k) eqn:E.
     rewrite tuple_nth_cons_hd.
     simpl.
     apply order_zero_eq_zero in E.
     apply is_zero_tuple_spec in E.
     unfold one_ps.
     rewrite E.
     reflexivity.
     simpl.
     unfold one_ps.
     enough (is_zero_tuple k = false) as -> by reflexivity.
     destruct (is_zero_tuple k) eqn:E';auto.
     apply is_zero_tuple_spec in E'.
     rewrite E' in E.
     rewrite zero_order in E.
     lia.
   Qed.

   Lemma partial_index_ps_comp1_next {d} n : partial_index (ps_comp1 (S d) (S n)) 0 == ps_comp1 d n.
   Proof.
     intros k.
     unfold partial_index.
     unfold ps_comp1.
     rewrite order_cons.
     replace (0 + order k)%nat with (order k) by lia.
     rewrite tuple_nth_cons_tl.
     destruct (order k =? 1) eqn:E; try reflexivity.
   Qed.

   Lemma partial_index_ps_comp1_next0 {d} n i : partial_index (ps_comp1 (S d) (S n)) (S i) == 0.
   Proof.
     intros k.
     unfold partial_index.
     unfold ps_comp1.
     rewrite order_cons.
     rewrite tuple_nth_cons_tl.
     simpl.
     destruct (order k) eqn:E.
     - destruct i;simpl;try reflexivity.
       destruct (tuple_nth n k 0 =? 1)%nat eqn:E';simpl; try reflexivity.
       apply Nat.eqb_eq in E'.
       apply order_zero_eq_zero in E.
       assert (tuple_nth n k 0 = 0).
       rewrite E.
       apply vec0_nth.
       simpl in H1.
       lia.
    - replace (i + S n0)%nat with (S (i+n0)) by lia.
      simpl.
      reflexivity.
   Qed.

   Lemma partial_index1_0 {d} : partial_index (d:=d) 1 0 == 1. 
   Proof.
     intros k.
     unfold partial_index.
     simpl.
     unfold one_ps.
     rewrite is_zero_tuple_next.
     reflexivity.
   Qed.
   Lemma partial_index1_S {d} n : partial_index (d:=d) 1 (S n) == 0. 
   Proof.
     intros k.
     unfold partial_index.
     simpl.
     unfold one_ps.
     destruct (is_zero_tuple (tuple_cons (S n) k)) eqn:E; try reflexivity.
     apply is_zero_tuple_spec in E.
     rewrite vec0_cons in E.
     apply tuple_cons_equiv in E.
     destruct E.
     simpl in H1.
     lia.
   Qed.

  Lemma fold_partial_index {d} (a : ps (S d)) k0 kt: a (tuple_cons k0 kt) == partial_index a k0 kt. 
  Proof.
    unfold partial_index;reflexivity.
  Qed.

  Lemma comp1_diff1 : forall d i : nat, i < d -> D[ i] (ps_comp1 d i) == 1.
  Proof.
    intros.
    destruct d; try lia.
    intros k.
    setoid_rewrite deriv_next_full;auto;try lia.
    revert dependent d.
    induction i;intros;destruct (destruct_tuple_cons k) as [k0 [kt ->]].
    - rewrite tuple_nth_cons_hd.
      destruct k0.
      simpl.
      rewrite ntimes_embed;simpl.
      ring_simplify.
      rewrite index_proper; try (apply tuple_cons_plus;try rewrite add0); try reflexivity.
      rewrite !fold_partial_index.
      rewrite index_proper; try rewrite add0; try reflexivity.
      replace (0+1)%nat with 1%nat by lia.
      rewrite partial_index1_0.
      rewrite partial_index_ps_comp1_first1; reflexivity.
      rewrite !fold_partial_index.
      rewrite (partial_index1_S k0 kt).
      rewrite index_proper; try (apply tuple_cons_plus;try rewrite add0); try reflexivity.
      rewrite fold_partial_index.
      setoid_rewrite (partial_index_ps_comp1_first0' (S k0 +1)%nat _ (kt+0)); try (simpl;lia).
      simpl.
      rewrite !ps0.
      ring.
   - rewrite tuple_nth_cons_tl.
     simpl nth1.
     rewrite index_proper; try (apply tuple_cons_plus); try reflexivity.
      rewrite !fold_partial_index.
      replace (k0+0)%nat with k0 by lia.
      destruct k0.
      rewrite (partial_index1_0 kt).
      rewrite (partial_index_ps_comp1_next _ (kt + nth1 d i)).
      destruct d; try lia.
      apply IHi; try lia.
      rewrite (partial_index1_S _ kt).
      rewrite (partial_index_ps_comp1_next0 _ _ (kt + nth1 d i)).
      simpl.
      rewrite !ps0.
      ring.
   Qed.

  Lemma out_of_range_diff {d} (a : ps d) i : (d <= i)%nat -> D[i] a == 0.
  Proof.
    simpl.
    intros.
    unfold ps_pdiff.
    destruct (d-i)%nat eqn:E; try lia.
    reflexivity.
  Qed.

  Lemma ps_comp1_wrong_order d i k : order k <> 1 -> ps_comp1 d i k == 0.
  Proof.
    intros.
    unfold ps_comp1.
    destruct (order k =? 1) eqn: E; try reflexivity.
    rewrite Nat.eqb_eq in E.
    simpl in *;lia.
  Qed.

  Lemma order1_nth1 d k : order k = 1 -> {i | i < d /\ k == nth1 d i}.
  Proof.
    intros.
    assert (order k <> 0) by (simpl in *;lia).
    destruct (tuple_pred_spec _ H2).
    exists x.
    destruct a.
    split;auto.
    rewrite H4.
    rewrite addC.
    enough (tuple_pred k == 0) as -> by (rewrite add0; reflexivity).
    apply order_zero_eq_zero.
    rewrite tuple_pred_order.
    rewrite H1.
    simpl;auto.
  Qed.

  Lemma order_nth1 {d} i : i <d -> order (nth1 d i) = 1.
  Proof.
    revert i.
    induction d;intros;try lia.
    intros.
    destruct i.
    simpl.
    rewrite order_cons.
    rewrite zero_order.
    lia.
    simpl.
    rewrite order_cons.
    rewrite IHd; simpl;try lia.
  Qed.

  Transparent order add tuple_pred  sum mul.
  Lemma exchange_ps_factor_order {d} (h h' g g' : nat^d -> A) (k : nat^d) : (forall i, (order i <= order k)%nat -> (h i) == (h' i)) -> (forall i, (order i <= order k)%nat -> (g i) == (g' i)) ->  (h * g) k == (h' * g') k.
  Proof.
    induction d.
    -  intros;simpl.
       rewrite H1,H2;auto.
       reflexivity.
    - intros.
      destruct (destruct_tuple_cons k) as [k0 [kt ->]].
      rewrite (mult_ps_cons_ps h g k0 kt).
      rewrite (mult_ps_cons_ps h' g' k0 kt).
      rewrite !index_sum.
      apply sum_ext.
      intros.
      apply IHd.
      + intros.
        apply H1.
        rewrite !order_cons.
        lia.
     + intros.
       apply H2.
        rewrite !order_cons.
        lia.
   Qed.

  Lemma order_plus {d} (k j : nat^d) : order (k+j) = order k + order j.
  Proof.
    induction d.
    simpl;reflexivity.
    destruct (destruct_tuple_cons k) as [k0 [kt ->]].
    destruct (destruct_tuple_cons j) as [j0 [jt ->]].
    rewrite tuple_cons_plus.
    rewrite !order_cons.
    rewrite IHd.
    simpl.
    lia.
  Qed.

  Opaque order add tuple_pred  sum mul.

  Definition ps_comp_ith_overflow n m a bs : forall i k, (i < order k)%nat -> (ps_composition_ith n m a bs i k) = 0.
  Proof.
    intros.
    induction i.
    simpl.
    destruct (order k); try lia;auto.
    simpl.
    assert (order k <? S i = false) as ->.
    apply Nat.ltb_ge;lia.
    assert (order k =? S i = false) as ->;auto.
    apply Nat.eqb_neq;lia.
  Qed.

   #[global] Instance  ps_composition_ith_proper : forall m n : nat, Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (ps_composition_ith m n).

   Proof.
     intros.
     intros a b eq z1 z2 eq' j j' eq''.
     simpl in eq''.
     rewrite <-eq''.
     clear eq'' j'.
     apply ps_eq_order.
     intros.
     assert (order k <= j \/ j <  order k)%nat by lia.
     destruct H2; [| rewrite !ps_comp_ith_overflow;auto;reflexivity].
     rewrite !(ps_comp_ith_larger _ _ _ _ j);auto.
      assert (order k <= n0)%nat by lia.
      clear H1 H2 j .
      generalize dependent a.
      generalize dependent b.
      generalize dependent k.
      induction n0;intros. 
      - assert (order k = 0)%nat by lia.
        rewrite H1;simpl; rewrite H1.
        apply eq.
      - assert (order k <= n0 \/ order k = S n0)%nat by lia.
       destruct H1;[apply IHn0;auto|].
       rewrite H1.
        rewrite !ps_composition_ith_next;auto.
        apply ring_eq_mult_eq; try reflexivity.
        setoid_rewrite index_sum.
        apply sum_ext.
        intros.
        apply exchange_ps_factor_order.
        + intros.
          apply index_proper; try rewrite eq'; reflexivity.
        + intros.
          rewrite tuple_pred_order in H4.
          rewrite H1 in H4.
          simpl in H4.
          rewrite !(ps_comp_ith_larger _ _ _ _ n0);auto.
          apply IHn0;auto.
          rewrite eq.
          reflexivity.
  Defined.

   #[global] Instance  ps_composition_proper : forall m n : nat, Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (ps_composition m n).
   Proof.
     intros.
     intros a b eq z1 z2 eq'.
     apply ps_eq_order.
     intros i k Hi.
     rewrite !ps_composition_simpl.
     apply ps_composition_ith_proper;auto.
     reflexivity.
  Defined.

  Lemma ps_composition_plus : forall (m n : nat) (x y : ps m) (z : ps (S n) ^ m), ps_composition m n (x + y) z == ps_composition m n x z + ps_composition m n y z.
  Proof.
     intros.
     apply ps_eq_order.
     intros.
     rewrite ps_plus_index.
     rewrite !ps_composition_simpl.
      assert (order k <= n0)%nat by lia.
      clear H1.
     generalize dependent k.
     revert x y.

     induction n0;intros.
     assert (order k = 0)%nat by lia.
     rewrite H1;simpl;rewrite H1; rewrite ps_plus_index;reflexivity.
     assert (order k <= n0 \/ order k = S n0)%nat by lia.
     destruct H1;[apply IHn0;auto|].
     rewrite H1.
     rewrite !ps_composition_ith_next;auto.
     rewrite <-distrL.
     apply ring_eq_mult_eq; try reflexivity.
     setoid_rewrite index_sum.
     rewrite sum_plus.
     apply sum_ext.
     intros.
     rewrite (exchange_ps_factor_order (D[pred_index k] (z\_n1)) (D[pred_index k] (z\_n1)) (ps_composition_ith m n D[ n1] (x + y) z n0) ((ps_composition_ith m n D[ n1] x z n0) + (ps_composition_ith m n D[n1] y z n0)) (tuple_pred k)).
     - rewrite <-index_plus.
       apply index_proper; try rewrite distrL; reflexivity.
     - intros;reflexivity.
     - intros.
       setoid_replace ( ps_composition_ith m n D[ n1] (x + y) z n0 i ) with ( ps_composition_ith m n (D[ n1] x + D[n1] y) z n0 i ) by (apply index_proper; try setoid_rewrite ps_pdiff_plus; try reflexivity).
       rewrite tuple_pred_order in H4.
       rewrite H1 in H4.
       simpl in H4.
       specialize (IHn0 (D[n1] x) (D[n1] y) i H4).
       setoid_rewrite index_plus.
       rewrite !(ps_comp_ith_larger _ _ _ _ n0);auto.
  Qed.

  Lemma ps_composition_simpl2 j n m a bs k  : (order k <= j)%nat ->  ps_composition n m a bs k == ps_composition_ith n m a bs j k.
  Proof.
    intros.
    rewrite ps_composition_simpl.
    rewrite (ps_comp_ith_larger _ _ _ _ j);auto.
    reflexivity.
  Qed.

   Transparent add.
   Lemma ps_composition_chain : forall (m n d : nat) (x : ps m) (y : ps (S n) ^ m), D[ d] (ps_composition m n x y) == sum (fun i : nat => D[ d] y \_ i * ps_composition m n D[ i] x y) m.
   Proof.
     intros.
     assert (S n <= d \/ d < S n)%nat by lia.
     destruct H1.
     {
       simpl.
       intros.
       unfold ps_pdiff.
       destruct (S n -d)%nat eqn:E; try lia.
       symmetry.
       apply index_proper; try apply sum_zero;try reflexivity.
       intros.
       rewrite mulC.
       rewrite mul0.
       reflexivity.
     }
     apply ps_eq_order.
     intros.
     setoid_rewrite deriv_next_full;auto.
     setoid_rewrite index_sum.
     intros.
     rewrite !ps_composition_simpl.
     rewrite order_plus.
     rewrite order_nth1;auto.
     replace (add (order k) 1)%nat with (S (order k)) by (simpl;lia).
     rewrite ps_composition_ith_next.
     (* setoid_rewrite exchange_ps_factor_order; [| apply (ps_composition_simpl2 (order k)) | apply (ps_composition_simpl2 (order k)) ]. *)
     (* assert (order k <= n0)%nat by lia. *)
     (* clear H1. *)
     (* generalize dependent k. *)
     (* revert x y. *)
     (* induction n0;intros. *)
     (* assert (order k = 0)%nat by lia. *)
     (* rewrite H1. *)
     (* admit. *)
     (* assert (order k <= n0 \/ order k = S n0)%nat by lia. *)
     (* destruct H1;[apply IHn0;auto|]. *)
   Admitted.

  Lemma ps_composition_mult :   forall (m n : nat) (x y : ps m) (z : ps (S n) ^ m),  ps_composition m n (x * y) z == ps_composition m n x z * ps_composition m n y z.
  Proof.
     intros.
     apply ps_eq_order.
     intros.
     rewrite !ps_composition_simpl.
     setoid_rewrite exchange_ps_factor_order; [| apply (ps_composition_simpl2 (order k)) | apply (ps_composition_simpl2 (order k)) ].
     assert (order k <= n0)%nat by lia.
     clear H1.
     generalize dependent k.
     revert x y.
     induction n0;intros.
     assert (order k = 0)%nat by lia.
     rewrite H1.
     admit.
     assert (order k <= n0 \/ order k = S n0)%nat by lia.
     destruct H1;[apply IHn0;auto|].
     
     (* rewrite !ps_composition_ith_next;auto. *)
     (* rewrite <-H1. *)
  Admitted.
  Transparent order add tuple_pred  sum mul.
  Lemma  comp1_diff0 : forall d i j : nat, i <> j -> D[ i] (ps_comp1 d j) == 0.
  Proof.
    intros.
    assert (i < d \/ d <= i)%nat by lia.
    destruct H2; [|apply out_of_range_diff;auto].
    destruct d; try lia.
    intros k.
    setoid_rewrite deriv_next_full;auto;try lia.
    enough (ps_comp1 (S d) j (k + nth1 (S d) i)  == 0) as -> by (simpl;rewrite ps0;ring).
    assert (order k = 0 \/ order k <> 0) by lia.
    destruct H3; [ | (apply ps_comp1_wrong_order;rewrite order_plus, order_nth1;simpl in *; lia)].
    apply order_zero_eq_zero in H3.
    rewrite index_proper; try (rewrite H3,addC,add0); try reflexivity.
    unfold ps_comp1.
    rewrite order_nth1;auto.
    rewrite nth1_spec0;auto.
    simpl.
    reflexivity.
  Qed.
  Opaque order.

  Lemma comp1_spec : forall (m n i : nat) (x : ps (S n) ^ m), ps_composition m n (ps_comp1 m i) x == x \_ i.
  Proof.
  Admitted.



  #[global] Instance ps_diffAlgebra  :  CompositionalDiffAlgebra (A := ps).
  Proof.
     exists ps_composition ps_comp1.
     apply comp1_spec.
     apply ps_composition_plus.
     apply ps_composition_mult.
     apply ps_composition_chain.
     apply ps_composition_proper.
     apply comp1_diff1.
     apply comp1_diff0.
  Defined.

  Definition sum_order {d} (a : nat^d -> A) (n : nat) : A.
  Proof.
    revert n.
    induction d;intros.
    destruct n.
    apply (abs (a t())).
    apply 0.
    apply (sum (fun i => (IHd (partial_index a i) (n-i)%nat)) (S n)).
  Defined.

  Lemma sum_order_next {d} (a : nat^(S d) -> A) (n : nat) : sum_order a n = (sum (fun i => (sum_order (partial_index a i) (n-i)%nat)) (S n)).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma sum_nonneg  f n: (forall i, i < n -> 0 <= f i) -> 0 <= sum f n.
  Proof.
    intros.
    apply (le_trans _ (sum (fun i => 0) n)).
    rewrite sum_zero; try apply le_refl;intros;reflexivity.
    apply sum_le.
    intros;apply H1;auto.
  Qed.

   Lemma sum_order_nonneg  {d} (a : nat^d -> A) n : 0 <= sum_order a n.
   Proof.
     revert n.
     induction d;intros.
     simpl.
     destruct n; try apply le_refl.
     apply abs_nonneg.
     simpl.
     apply sum_nonneg.
     intros.
     apply IHd.
   Qed.

   Lemma sum_order0  {d}  (a :  nat^d -> A):  sum_order  a 0 == abs (a 0).
   Proof.
     induction d.
     simpl;reflexivity.
     simpl.
     rewrite sum_1.
     rewrite IHd.
     setoid_rewrite vec0_cons.
     reflexivity.
   Qed.

   Lemma sum_order1d  (a :  nat^1 -> A)  k :  sum_order (d:=1) a k == abs (a t(k)).
   Proof.
     simpl sum_order.
     rewrite sum_S.
     replace (k-k)%nat with 0%nat by lia.
     rewrite sum_zero.
     rewrite addC,add0; reflexivity.
     intros.
     destruct (k-i)%nat eqn:E; try lia.
     reflexivity.
  Qed.

   #[global] Instance sum_order_proper  d : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (sum_order (d := d)).
   Proof.
     intros a b eq n n' eq'.
     simpl in eq'.
     rewrite <-eq'.
     clear eq' n'.
     revert n.
     induction d;intros.
     simpl.
     destruct n; try reflexivity.
     apply abs_proper.
     apply eq.
     simpl.
     apply sum_ext.
     intros.
     apply IHd.
     rewrite eq.
     reflexivity.
  Defined.

  Lemma sum_order_plus {d} (a b : nat^d -> A) n :  sum_order (a+b) n <= sum_order a n + sum_order b n.
  Proof.
    revert n.
    induction d;intros.
    destruct n.
    simpl.
    setoid_rewrite index_plus.
    apply abs_triangle.
    simpl.
    rewrite add0.
    apply le_refl.
    simpl.
    rewrite sum_plus.
    apply sum_le.
    intros.
    setoid_rewrite partial_index_plus.
    apply IHd.
  Qed. 

  Lemma sum_order_zero_ps {d} n (z : ps d) : z == 0 -> sum_order z n == 0. 
  Proof.
    intros.
    revert n.
    induction d;intros;rewrite H1.
    simpl.
    destruct n;simpl; try rewrite ps0,abs_zero; try reflexivity.
    simpl.
    apply sum_zero.
    intros.
    apply IHd.
    apply partial_index0.
  Qed.

  Lemma sum_order_sum  {d} (a : nat -> nat^d -> A) m n :  sum_order (sum a m) n <= sum (fun i => (sum_order (a i) n)) m.
  Proof.
    induction m.
    unfold sum;simpl.
    rewrite sum_order_zero_ps; try apply le_refl; reflexivity.
    rewrite !sum_S.
    apply (le_trans _ _ _ (sum_order_plus _ _ _)).
    apply le_plus_compat.
    apply IHm.
  Qed.



   Lemma sum_order1_S {d} i: sum_order (d:=d) 1 (S i) == 0.
   Proof.
     induction d.
     simpl.
     reflexivity.
     rewrite sum_order_next.
     apply sum_zero.
     intros.
     destruct i0.
     rewrite partial_index1_0.
     replace (S i - 0)%nat with (S i) by lia.
     apply IHd.
     rewrite partial_index1_S.
     rewrite sum_order_zero_ps; reflexivity.
   Qed.

   Lemma sum_order_comp1 {d} i k : i < d -> ( sum_order (d:=d) (ps_comp1 d i) 1 == 1) /\ ((k <> 1)%nat -> sum_order (d:=d) (ps_comp1  d i) k == 0).
   Proof.
     intros.
     generalize dependent i.
     revert k.
     induction d; try lia.
     intros.
     split;intros.
     - rewrite sum_order_next.
       rewrite sum_S.
       rewrite sum_1.
       replace (1-0)%nat with 1%nat by lia.
       replace (1-1)%nat with 0%nat by lia.
       destruct i.
       + rewrite partial_index_ps_comp1_first0.
         rewrite partial_index_ps_comp1_first1.
         rewrite sum_order_zero_ps; try reflexivity.
         rewrite sum_order0.
         simpl.
         ring_simplify.
         enough (one_ps d 0 == 1).
         rewrite H2;rewrite abs_pos;try reflexivity; apply le_0_1.
         unfold one_ps.
         assert (is_zero_tuple 0 = true) as ->; try reflexivity.
         apply is_zero_tuple_spec;reflexivity.
       + rewrite !partial_index_ps_comp1_next.
         rewrite !partial_index_ps_comp1_next0.
         assert (i < d) by lia.
         specialize (IHd i _ H2).
         destruct IHd.
         rewrite H3.
         rewrite sum_order_zero_ps; try reflexivity.
         ring.
    - rewrite sum_order_next.
       apply sum_zero.
       intros.
       destruct i0 eqn:I;(replace (k-0)%nat with k by lia);destruct i.
       rewrite partial_index_ps_comp1_first0; rewrite sum_order_zero_ps; try reflexivity.
       rewrite partial_index_ps_comp1_next;apply IHd;auto;lia.
       destruct n.
       rewrite partial_index_ps_comp1_first1.
       destruct (k-1)%nat eqn:K; try lia.
       rewrite sum_order1_S; reflexivity.
       rewrite partial_index_ps_comp1_first0'; simpl;try lia; try rewrite sum_order_zero_ps; reflexivity.
       rewrite partial_index_ps_comp1_next0, sum_order_zero_ps; try reflexivity.
   Qed.



   Lemma sum_order_mult {d} (a b : nat^d -> A) n : sum_order (a * b) n <= sum (fun j => sum_order a j * sum_order b (n-j)) (S n).
   Proof.
     revert n.
     induction d;intros.
     - destruct n.
       rewrite sum_1.
       replace (0-0)%nat with 0%nat by lia.
       simpl.
       rewrite abs_mult.
       apply le_refl.
       rewrite sum_zero;try apply le_refl.
       intros.
       destruct i;simpl;ring.
     - rewrite sum_order_next.
  Admitted.

   Lemma smul_partial_index {d} (a :  nat^(S d) -> A) x n :partial_index (x [*] a) n == x [*] (partial_index a n).
   Proof.
      unfold partial_index; unfold ps_smul.
      reflexivity.
   Qed.

   Lemma sum_order_smult {d} (a :  nat^d -> A) n x : sum_order (x [*] a) n == abs x * sum_order a n.
   Proof.
     revert n.
     induction d.
     - intros.
       simpl.
       destruct n.
       unfold ps_smul.
       rewrite abs_mult;reflexivity.
       ring.
    -  intros.
       simpl.
       rewrite sum_mult.
       apply sum_ext.
       intros.
       setoid_rewrite smul_partial_index.
       apply IHd.
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
    destruct H2.
    simpl.
    rewrite embNat_S.
    rewrite addC.
    setoid_replace (#n) with (0 + #n) by ring.
    apply le_le_plus_le.
    apply le_0_1.
    apply IHm;auto.
    rewrite H2.
    apply le_refl.
  Qed.

   Lemma sum_order_diff_le {d} (a :  nat^d -> A) i n : i < d -> sum_order (D[i] a) n <= #(n+1)%nat * sum_order a (n+1)%nat.
   Proof.
     intros.
     rewrite ntimes_embed.
     revert n a .
     generalize dependent i.
     induction d; intros; try lia.
     destruct i;intros.
     - rewrite sum_order_next.
       assert (sum (fun i => sum_order (partial_index D[0] a i) (n-i)) (S n) == sum (fun i => sum_order ( #( S i) [*] (partial_index a (S i))) (n-i)) (S n)) as ->.
       {
         apply sum_ext.
         intros.
         setoid_rewrite pdiff_partial_index_shift.
         reflexivity.
       }
       rewrite sum_order_next.
       rewrite sum_mult.
       rewrite (sum_S_fun _ (n+1)%nat).
       rewrite <-add0 at 1.
       rewrite addC.
       apply le_le_plus_le.
       apply mul_pos_pos;[apply le_0_n | apply sum_order_nonneg].
       replace (n+1)%nat with (S n) by lia.
       apply sum_le;intros.
       replace (S n - S i)%nat with (n - i)%nat by lia.
       rewrite sum_order_smult.
       rewrite abs_pos; try apply le_0_n.
       rewrite ntimes_embed.
       rewrite !(mulC (ntimes _ _)).
       apply mul_le_compat_pos; try apply sum_order_nonneg.
       rewrite <-!ntimes_embed.
       apply ntimes_monotone;lia.
       rewrite ntimes_embed.
       apply ntimes_nonneg;apply le_0_1.
    - rewrite sum_order_next.
       assert (sum (fun j => sum_order (partial_index D[S i] a j) (n-j)) (S n) == sum (fun j => sum_order (D[i] (partial_index  a j)) (n-j)) (S n)) as ->.
       {
         apply sum_ext;intros.
         setoid_rewrite ps_pdiff_next.
         reflexivity.
       }
       rewrite sum_order_next.
       rewrite sum_mult.
       rewrite (sum_S _ (n+1)%nat).
       rewrite addC.
       rewrite <-add0 at 1.
       rewrite addC.
       apply le_le_plus_le.
       apply mul_pos_pos;[apply le_0_n | apply sum_order_nonneg].
       replace (n+1)%nat with (S n) by lia.
       apply sum_le;intros.
       assert (i < d) by lia.
       apply (le_trans _ _ _ (IHd _ H3 _ _)).
       replace (n -i0 + 1)%nat with (S n - i0)%nat by lia.
       rewrite !(mulC (ntimes _ _)).
       apply mul_le_compat_pos; try apply sum_order_nonneg.
       rewrite <-!ntimes_embed.
       apply ntimes_monotone;lia.
   Qed.

  (*  Lemma sum_order1 {d} i k : i < d -> ((k == 1)%nat -> sum_order (d:=d) (comp1  i) k == 1) /\ ((k <> 1)%nat -> sum_order (d:=d) (comp1  i) k == 0). *)
  (*  Proof. *)
  (*   intros. *)
  (* Admitted. *)

    Lemma comp1_0 {d} i : (ps_comp1 d  i) 0 == 0.
    Proof.
      induction d.
      simpl.
      reflexivity.
      unfold ps_comp1.
      rewrite zero_order.
      simpl.
      reflexivity.
   Qed.

  Transparent order add tuple_pred sum mul.
  Lemma comp1_1d  k : ((k == 1%nat) -> (ps_comp1  1 0) t(k) == 1) /\ ((k <> 1%nat) -> (ps_comp1 1  0) t(k) == 0).
  Proof.
    split.
    - intros ->.
      reflexivity.
    - intros.
      unfold ps_comp1.
      simpl.
      replace (k+0)%nat with k by lia.
      destruct (k =? 1) eqn:E;try reflexivity.
      apply Nat.eqb_eq in E.
      lia.
   Qed.

  Lemma ps_comp0  {d e} (a : (nat^d -> A)) (bs : (nat^(S e) -> A)^d): (a \o1 bs) 0 == (a 0). 
  Admitted.
 (* Context `{CompositionalDiffAlgebra (A := ps) (H := _) (H0 := _) (H1 := _) (H2 := _)}. *)

  (* coefficient norm is currently formalized abstractly *)
  (* Class CoeffSum := { *)
  (*     (* sum_order {d} (a : nat^d -> A ) (n : nat) : A; *) *)
  (*     (* sum_order_proper d : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (sum_order (d := d)); *) *)
  (*     (* sum_order_mult {d} (a b : nat^d -> A) n : sum_order (a * b) n == sum (fun j => sum_order a j * sum_order b (n-j)) (S n); *) *)
  (*     (* sum_order_nonneg {d} (a : nat^d -> A) n : 0 <= sum_order a n; *) *)
  (*     (* sum_order_sum {d} (a : nat -> nat^d -> A) m n :  sum_order (sum a m) n == sum (fun i => (sum_order (a i) n)) m; *) *)
  (*     (* sum_order_diff_le {d} (a :  nat^d -> A) i n : i < d -> sum_order (D[i] a) n <= #(n+1)%nat * sum_order a (n+1)%nat; *) *)
  (*     sum_order1 {d} i k : i < d -> ((k == 1)%nat -> sum_order (d:=d) (comp1  i) k == 1) /\ ((k <> 1)%nat -> sum_order (d:=d) (comp1  i) k == 0); *)
  (*     (* sum_order1d  (a :  nat^1 -> A)  k :  sum_order (d:=1) a k == norm (a t(k)); *) *)
  (*     (* sum_order0  {d} (a :  nat^d -> A):  sum_order  a 0 == norm (a 0); *) *)
  (*   }. *)

  
  Lemma ntimes_index {d} (a : nat^d -> A) k n : (ntimes n a k) == ntimes n (a k).
  Proof.
    induction n.
    simpl.
    rewrite ps0;reflexivity.
    simpl.
    setoid_rewrite index_plus.
    rewrite IHn.
    reflexivity.
 Qed.
End AbstractPowerSeries.


