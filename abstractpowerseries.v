Require Import List.
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

  Definition idx {d} (a : nat^d -> A) n := a n.

  Lemma idx_index {d} a n : a n = idx (d:=d) a n.
  Proof. reflexivity. Qed.

  #[global] Instance idx_proper : forall {d}, Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (idx (d:=d)).
  Proof.
    intros.
    apply index_proper.
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

  Definition pred_index {d} (k : nat^d): nat.
  Proof.
    intros.
    induction d.
    apply 0.
    destruct (destruct_tuple_cons k) as [n [vt ->]].
    destruct n.
    -  apply (S (IHd vt)).
   - apply 0.
  Defined.

  Lemma tuple_pred_spec' {d} (v : nat^d) : order v <> 0 -> (pred_index v) < d /\ v == tuple_pred v + nth1 d (pred_index v).
  Proof.
    intros.
    induction d;[simpl in H1; lia|].
    simpl pred_index.
    destruct (destruct_tuple_cons v) as [n [vt ->]].
    destruct n.
    - split.
      enough (pred_index vt < d) by lia.
      apply IHd.
      rewrite order_cons in H1;lia.
      setoid_rewrite tuple_pred_cons0.
      simpl nth1.
      rewrite tuple_cons_plus.
      apply tuple_cons_equiv_equiv;  simpl;try lia;try reflexivity.
      apply IHd.
      rewrite order_cons in H1;lia.
   - split;try lia.
     rewrite tuple_pred_cons_S.
      simpl nth1.
      rewrite tuple_cons_plus.
      rewrite add0.
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

  Lemma deriv_next_backward_full {d} (f : nat^d -> A) k i : i < d -> f (k + nth1 d i) == (inv_Sn k\_i) *  D[i] f k.
  Proof.
    intros.
    setoid_replace (f (k + nth1 d i)) with ((# (S (k\_i)) * (inv_Sn k\_i)) * f (k + nth1 d i)) by (rewrite ntimes_embed, inv_Sn_spec;ring).
    rewrite (mulC #(_)), mulA.
    replace (S k\_i) with (k\_i + 1)%nat by lia.
    rewrite <-deriv_next_full;auto.
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



  #[global] Instance tuple_pred_proper {d} : Proper (SetoidClass.equiv ==> SetoidClass.equiv) (tuple_pred (d:=d)).
  Proof.
    intros a b Heq.
    induction d.
    simpl;auto.
    simpl tuple_pred.
    destruct (destruct_tuple_cons a) as [a0 [a1 ->]].
    destruct (destruct_tuple_cons b) as [b0 [b1 ->]].
    apply tuple_cons_equiv in Heq.
    destruct Heq.
    rewrite H1.
    destruct b0;apply tuple_cons_equiv_equiv;auto; reflexivity.
  Defined.

  #[global] Instance pred_index_proper {d} : Proper (SetoidClass.equiv ==> SetoidClass.equiv) (pred_index (d:=d)).
  Proof.
    intros a b Heq.
    simpl.
    induction d;simpl;auto.
    destruct (destruct_tuple_cons a) as [a0 [a1 ->]].
    destruct (destruct_tuple_cons b) as [b0 [b1 ->]].
    apply tuple_cons_equiv in Heq.
    destruct Heq.
    rewrite H1.
    destruct b0;auto.
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
      apply ((inv_Sn (pred k\_(pred_index k))) * ((sum (fun j => D[pred_index k] bs\_j * (IHi (D[j] a))) n) (tuple_pred k))).
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
  Lemma ps_composition_ith_next n m a bs i k : order k = (S i) -> ps_composition_ith n m a bs (S i) k == (inv_Sn (pred k\_(pred_index k)))  * (sum (fun j => D[pred_index k] bs\_j * (ps_composition_ith n m (D[j] a) bs i)) n (tuple_pred k)).
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
    generalize dependent d.
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


   Lemma ps_composition_spec : forall (m n : nat) (x : ps m) (y : ps (S n) ^ m) k, order k > 0 -> (ps_composition m n x y) k == inv_Sn (pred k\_(pred_index k)) * (D[pred_index k] (ps_composition m n x y)) (tuple_pred k).
   Proof.
     intros.
     rewrite !ps_composition_simpl.
     assert (order k<> 0)%nat by lia.
     pose proof (tuple_pred_spec' k ) as P.
     destruct (P H2)  as [P1 P2].
     rewrite ps_composition_ith_proper; try rewrite P2; try reflexivity.
     rewrite order_plus.
     rewrite order_nth1;auto.
     replace (add (order (tuple_pred k)) 1)%nat with (S (order (tuple_pred k))) by (simpl;lia).
     rewrite ps_composition_ith_next; [|rewrite tuple_pred_order;simpl;lia].
     apply ring_eq_mult_eq; try reflexivity.
     setoid_rewrite deriv_next_full;auto.
     rewrite !ps_composition_simpl.
     rewrite order_plus.
     rewrite order_nth1;auto.
     replace (add (order (tuple_pred k)) 1)%nat with (S (order (tuple_pred k))) by (simpl;lia).
     setoid_rewrite index_sum.
     rewrite ps_composition_ith_next.
     rewrite <-mulA.
     setoid_replace (  # ((tuple_pred k) \_ (pred_index k) + 1) * inv_Sn (Init.Nat.pred (tuple_pred k + nth1 (S n) (pred_index k)) \_ (pred_index (tuple_pred k + nth1 (S n) (pred_index k))))) with 1.
     rewrite mulC,mul1.
     setoid_rewrite index_sum.
     apply sum_ext.

     intros.
     apply index_proper;rewrite <-P2;reflexivity.

     replace ((pred_index (tuple_pred k + nth1 (S n) (pred_index k)))) with (pred_index k) by (rewrite <-P2;auto).
     rewrite vec_plus_spec;auto.
     rewrite nth1_spec1;auto.
     setoid_replace ((tuple_pred k) \_ (pred_index k) + 1) with (S (pred (add (tuple_pred k)\_(pred_index k) 1))) by (simpl;lia).
     rewrite ntimes_embed.
     rewrite inv_Sn_spec;reflexivity.
     rewrite order_plus, order_nth1;auto;simpl;lia.
   Qed.

   
   Lemma pred_index_pred {d} (k : nat^d) : order k <> 0 -> (tuple_pred k)\_(pred_index k) = pred (k\_(pred_index k)).
   Proof.
     intros.
     destruct (tuple_pred_spec' _ H1).
     pose proof (tuple_nth_proper (n:=d) (pred_index k) _ _  H3 0).
     rewrite H4; try reflexivity.
     rewrite vec_plus_spec;auto.
     rewrite nth1_spec1;auto.
     simpl;lia.
   Qed.

   Lemma ps_deriv_switch : forall (n : nat) (x : ps n) k d, d < n ->  (D[d] x) k  == # (k \_ d + 1) * (inv_Sn (pred ((k+nth1 n d))\_(pred_index (k+nth1 n d))) *   D[pred_index (k + nth1 n d)] x (tuple_pred (k+nth1 n d))).
     intros.
     setoid_rewrite deriv_next_full;auto.
     destruct (tuple_pred_spec' (k + nth1 n d)).
     rewrite order_plus, order_nth1;simpl;lia.
     setoid_rewrite (index_proper (d:=n) x x _ (tuple_pred _ + _) ); try rewrite <-H3; try reflexivity.
     apply ring_eq_mult_eq; try reflexivity.
     rewrite <-mulA, (mulC (inv_Sn _)).
     rewrite ntimes_embed.
     rewrite Nat.add_1_r.
     rewrite pred_index_pred.
     rewrite inv_Sn_spec.
     ring.
     rewrite order_plus, order_nth1;simpl;lia.
     apply tuple_pred_spec'.
     rewrite order_plus, order_nth1;simpl;lia.
   Qed.

   (* Lemma pred_plus_unit {d} (k : nat^d) i : i < d -> tuple_pred (k + nth1 d i) == tuple_pred k \/ tuple_pred (k + nth1 d i) == tuple_pred k + nth1 d i. *)
   (* Proof. *)
   (*   intros. *)
   (*   Search tuple_pred. *)
   Lemma ps_composition_next {n m} (a : ps n) (bs : ps (S m)^n) k : order k > 0 -> ps_composition n m a bs k == inv_Sn (Init.Nat.pred k \_ (pred_index k)) * sum (fun j : nat => D[ pred_index k] bs \_ j * ps_composition n m D[ j] a bs) n (tuple_pred k).
   Proof.
     intros.
     rewrite !ps_composition_simpl.
     destruct (order k) eqn:E;try lia.
     rewrite ps_composition_ith_next;auto.
     apply ring_eq_mult_eq; try reflexivity.
     setoid_rewrite index_sum.
     apply sum_ext;intros.
     pose proof (exchange_ps_factor_order (d:=(S m)) (D[ pred_index k] bs \_ n1) (D[ pred_index k] bs \_ n1)  (ps_composition_ith n m D[ n1] a bs n0)).
     rewrite H3; try (intros;reflexivity).
     intros.

     rewrite ps_composition_simpl.
     rewrite ps_comp_ith_larger;try reflexivity.
     enough (order (tuple_pred k) < order k)%nat by lia.
     rewrite tuple_pred_order.
     lia.
   Qed.

   Lemma nth1_pred_index d n: n < d -> pred_index (nth1 d n) = n.
   Proof.
     intros.
     destruct (tuple_pred_spec' (nth1 d n)).
     rewrite order_nth1;simpl;try lia.
     assert (tuple_pred (nth1 d n) == 0).
     {
       apply order_zero_eq_zero.
       rewrite tuple_pred_order.
       rewrite order_nth1;simpl;lia.
    }
    rewrite H4 in H3.
     rewrite addC, add0 in H3.
     assert (pred_index (nth1 d n) = n \/ (pred_index (nth1 d n) <> n))%nat by lia.
     destruct H5;auto.
     assert ((nth1 d n)\_(pred_index (nth1 d n)) = 1).
     {
       rewrite tuple_nth_proper; try apply H3;try reflexivity.
       rewrite nth1_spec1;auto.
     }
     contradict H6.
     rewrite nth1_spec0;auto.
   Qed.

   Lemma multiindex_plus_cancel {d} (x y z : nat ^d ) : x + z == y + z -> x == y.
   Proof.
    induction d.
    setoid_rewrite zero_tuple_zero;reflexivity.
    intros.
    destruct (destruct_tuple_cons x) as [x0 [xt ->]].
    destruct (destruct_tuple_cons y) as [y0 [yt ->]].
    destruct (destruct_tuple_cons z) as [z0 [zt ->]].
    rewrite !tuple_cons_plus in H1.
    apply tuple_cons_equiv in H1.
    destruct H1; simpl in H1.
    apply tuple_cons_equiv_equiv; try (simpl;lia).
    apply (IHd _ _ zt);auto.
   Qed.

   Lemma pred_index_backwards_same {d} (k : nat^d) n: n <d ->   pred_index (k+nth1 d n) = n -> tuple_pred (k + nth1 d n) == k.
   Proof.
     intros.
     destruct (tuple_pred_spec' (k+nth1 d n)) ;[rewrite order_plus, order_nth1;simpl;try lia;auto|].
     rewrite H2 in H4.
     apply multiindex_plus_cancel in H4;auto.
     rewrite H4 at 2.
     reflexivity.
   Qed.
   Lemma pred_index_spec1 {d} (k : nat^d): forall n, n < pred_index k -> k\_n = 0.
   Proof.
     induction d.
     simpl;intros;lia.
     simpl.
     destruct (destruct_tuple_cons k) as [k0 [kt ->]].
     intros.
     destruct k0; try lia.
     destruct n.
     rewrite tuple_nth_cons_hd;reflexivity.
     rewrite tuple_nth_cons_tl.
     apply IHd.
     lia.
   Qed.

   Lemma pred_index_spec2 {d} (k : nat^d): forall n, k\_n <> 0 -> (pred_index k <= n)%nat.
   Proof.
     induction d.
     simpl;intros;lia.
     simpl.
     destruct (destruct_tuple_cons k) as [k0 [kt ->]].
     intros.
     destruct k0; try lia.
     destruct n.
     rewrite tuple_nth_cons_hd in H1;lia.
     enough(pred_index kt <= n)%nat by lia.
     apply IHd.
     rewrite (tuple_nth_cons_tl) in H1;auto.
   Qed.

   Lemma pred_index_first {d} (k : nat^d) n:  k\_n <> 0 /\ (forall m, m < n -> k\_m = 0) -> (pred_index k = n)%nat.
   Proof.
     intros [H1 H2].
     enough (pred_index k <= n /\ n <= pred_index k)%nat by lia.
     split.
     apply pred_index_spec2;auto.
     generalize dependent k.
     generalize dependent n.
     induction d.
     intros.
     contradict H1.
     rewrite zero_tuple_zero.
     destruct n;auto.
     intros.
     simpl.
     destruct (destruct_tuple_cons k) as [k0 [kt ->]].
     destruct n;try lia.
     destruct k0.
     rewrite tuple_nth_cons_tl in H1.
     apply le_n_S.
     apply IHd;auto.
     intros.
     specialize (H2 (S m)).
     rewrite tuple_nth_cons_tl in H2.
     apply H2;lia.

     assert (0 < S n) by lia.
     specialize (H2 0 H3).
     rewrite tuple_nth_cons_hd in H2.
     simpl in H2.
     lia.
   Qed.

   Lemma pred_index_first' {d} (k : nat^d) :  order k > 0 ->  k\_(pred_index k) <> 0 /\ (forall m, m < (pred_index k) -> k\_m = 0).
   Proof.
     intros.
     split.
     destruct (tuple_pred_spec' k); try (simpl;lia).
     rewrite tuple_nth_proper; try apply H3; try reflexivity.
     rewrite vec_plus_spec;auto.
     rewrite nth1_spec1;auto;simpl;lia.
     intros.
     assert (k\_m = 0 \/ k\_m <> 0)%nat by lia.
     destruct H3;auto.
     enough (pred_index k <= m)%nat by lia.
     apply pred_index_spec2;auto.
   Qed.

   Lemma pred_index_diff {d} (k : nat^d) n: n <d -> 0 < order k ->   pred_index (k+nth1 d n) <> n -> pred_index (k+nth1 d n) = pred_index k.
   Proof.
     intros.

     destruct (tuple_pred_spec' (k+nth1 d n)) ;[rewrite order_plus, order_nth1;simpl;try lia;auto|].
     destruct (tuple_pred_spec' k) ;[simpl;try lia;auto|].
     assert (pred_index (k+nth1 d n) < n).
     {
       enough (Nat.le (pred_index (k+nth1 d n)) n) by lia.
       apply pred_index_spec2.
       rewrite vec_plus_spec;auto.
       rewrite nth1_spec1;auto;simpl;lia.
     }

     assert (pred_index k < n) as Hpn.
     {
        enough (k\_(pred_index (k + nth1 d n)) <> 0).
        apply pred_index_spec2 in H9.
        lia.
        destruct (pred_index_first' (k + nth1 d n)).
        rewrite order_plus, order_nth1;auto;simpl;try lia.
        intros Hk.
        contradict H9.
        rewrite vec_plus_spec;auto.
        rewrite Hk.
        rewrite nth1_spec0;simpl;try lia.
     }
       
     pose proof (pred_index_first' k H2).
     simpl in H9.
     destruct H9.
     apply pred_index_first.
     split.
     rewrite vec_plus_spec;auto;simpl;try lia.
     intros.
     rewrite vec_plus_spec;auto;try lia.
     rewrite H10;auto.
     rewrite nth1_spec0;auto;try lia.
   Qed.
   Lemma pred_index_backwards_different {d} (k : nat^d) n: n <d -> 0 < order k ->   pred_index (k+nth1 d n) <> n -> tuple_pred (k + nth1 d n) == tuple_pred k + nth1 d n.
   Proof.
     intros.
     destruct (tuple_pred_spec' (k+nth1 d n)) ;[rewrite order_plus, order_nth1;simpl;try lia;auto|].
     destruct (tuple_pred_spec' k) ;[simpl;try lia;auto|].
     assert (tuple_pred (k+nth1 d n) + nth1 d (pred_index (k + nth1 d n)) == (tuple_pred k + nth1 d n) + nth1 d (pred_index k)).
     {
       rewrite addA, (addC (nth1 d n)), <-addA.
       rewrite <-H7.
       rewrite <-H5.
       reflexivity.
     }
     enough (pred_index (k+nth1 d n) = pred_index k).
     rewrite H9 in H8.
     apply multiindex_plus_cancel in H8.
     apply H8.
     apply pred_index_diff;auto.
  Qed.
   Transparent sum.
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
     generalize dependent x.
     generalize dependent k.
     enough (forall k, (order k <= n0)%nat  ->forall x : ps m, D[ d] (ps_composition m n x y) k == sum (fun i : nat => D[ d] y \_ i * ps_composition m n D[ i] x y) m k ).
     intros;apply H2;lia.
     generalize dependent d.
     induction n0;intros.
     - rewrite index_proper; try apply order_zero_eq_zero;auto; try reflexivity;try (simpl;lia).
       setoid_rewrite deriv_next_full;auto.
       rewrite vec0_nth.
       rewrite ntimes_embed.
       simpl ntimes.
       ring_simplify.
       setoid_replace  (ps_composition m n x y (0 + nth1 (S n) d))  with   (ps_composition m n x y (nth1 (S n) d)) by (apply index_proper;try (rewrite addC, add0);reflexivity).
       rewrite ps_composition_next; [|rewrite order_nth1;auto].
       rewrite !nth1_pred_index;auto.
       rewrite !nth1_spec1;auto.
       simpl pred.
       rewrite inv_Sn0.
       ring_simplify.
       apply index_proper;[reflexivity|].
       rewrite order_zero_eq_zero, (order_zero_eq_zero k); try reflexivity;auto;try (simpl;lia).
       rewrite tuple_pred_order, order_nth1;simpl;auto.
    - setoid_rewrite deriv_next_full;auto.
      rewrite ps_composition_next; [|rewrite order_plus, order_nth1; simpl;lia].
      assert (pred_index (k + (nth1 (S n) d)) = d \/ pred_index (k + nth1 (S n) d) <> d) by lia. 
      destruct H3.
      + rewrite !H3.
        rewrite !vec_plus_spec;auto.
        rewrite !nth1_spec1;auto.
        rewrite ntimes_embed.
        setoid_replace (k\_d + 1) with (S (pred (add k\_d 1))) at 1 by (simpl;lia).
        rewrite <-mulA.
        rewrite inv_Sn_spec.
        ring_simplify.
        apply index_proper;try reflexivity.
        destruct (tuple_pred_spec' (k + nth1 (S n) d));try (rewrite order_plus, order_nth1;simpl;lia).
        apply pred_index_backwards_same;auto.
      + destruct m.
        {
          unfold sum;simpl.
          rewrite !ps0.
          ring.
        }
        assert (order k <> 0) as Hod.
        {
          intros Hk.
          apply order_zero_eq_zero in Hk.
          contradict H3.
          rewrite Hk.
          rewrite addC, add0.
          rewrite nth1_pred_index;auto.
        }
        simpl in Hod.
        rewrite idx_index.
        rewrite pred_index_backwards_different;auto;try lia;try reflexivity.

        assert ((k\_d ) = (tuple_pred k)\_d) as ->.
        {
          destruct (tuple_pred_spec' (k + nth1 (S n) d)).
          rewrite order_plus, order_nth1;simpl;lia.
          rewrite pred_index_backwards_different in H5;auto;simpl;try lia.
          enough ((k + nth1 (S n) d)\_d = (tuple_pred k + nth1 (S n) d + nth1 (S n) (pred_index (k+nth1 (S n) d)))\_d).
          rewrite !vec_plus_spec, nth1_spec1,nth1_spec0 in H6;auto;simpl in H6;simpl;lia.
          rewrite H5 at 1.
          reflexivity.
        }
        rewrite <-mulA, (mulC (# _)), mulA.
        rewrite <-deriv_next_full;auto.
        rewrite index_proper; try apply pdiff_sum; try reflexivity.
        destruct (tuple_pred_spec' k); try (simpl;lia).
        setoid_rewrite (index_proper _ _ _ k); try apply H5; try reflexivity.
        rewrite deriv_next_backward_full;auto.
        apply ring_eq_mult_eq.
        {
          rewrite tuple_nth_proper; try apply pred_index_backwards_different; try reflexivity.
          rewrite pred_index_diff;auto; try lia.
          enough (pred (k + nth1 (S n) d)\_(pred_index k) = (tuple_pred k)\_(pred_index k)) as -> by reflexivity.
          rewrite pred_index_pred; try (simpl;lia).
          f_equal.
          rewrite vec_plus_spec;auto.
          rewrite nth1_spec0;auto.
          rewrite pred_index_diff in H3;auto;lia.
        }
        pose proof (index_proper (  D[ pred_index k] (sum (fun i : nat => D[ d] y \_ i * ps_composition (S m) n D[ i] x y) (S m))) _ (pdiff_sum _ _ _) (tuple_pred k) (tuple_pred k)).
        rewrite H6; try reflexivity.
        clear H6.

        rewrite idx_index,sum_ext; try (intros;apply pdiff_mult).
        rewrite (idx_index (sum _ _) (tuple_pred k)).
        rewrite (sum_ext (fun j => (D[_] _))); try (intros;apply pdiff_mult).
        rewrite <-!sum_plus.
        rewrite <-!idx_index.
        rewrite !index_plus.
        apply ring_eq_plus_eq.
        {
          apply index_proper; try reflexivity.
          apply sum_ext; intros.
          rewrite pred_index_diff;auto; try lia.
          rewrite pdiff_comm.
          reflexivity.
        }
        rewrite idx_index.
        rewrite pred_index_diff; auto; try lia.
        rewrite index_sum.
        rewrite <-idx_index, index_sum.

        rewrite sum_ext; [|intros;apply exchange_ps_factor_order; [reflexivity | intros;apply IHn0;auto; rewrite tuple_pred_order in H7;lia]].
        rewrite <-(index_sum (fun n1 : nat =>
     (D[ pred_index k] y \_ n1 *
      (fun i : nat ^ S n =>
       sum (fun i0 : nat => D[ d] y \_ i0 * ps_composition (S m) n D[ i0] (D[ n1] x) y) (S m) i)))
 (tuple_pred k) (S m)).
        rewrite index_proper; [|apply sum_ext;intros;apply sum_mult| reflexivity].
        rewrite index_proper; [|apply sum_triple_reorder_sym;intros;rewrite pdiff_comm;reflexivity|reflexivity].
        symmetry.
        rewrite sum_ext; [|intros;apply exchange_ps_factor_order; [reflexivity | intros;apply IHn0;auto; rewrite tuple_pred_order in H7;lia]].
        rewrite index_sum.
        apply sum_ext.
        intros.
        apply index_proper; try reflexivity.
        rewrite sum_mult.
        reflexivity.
    Qed.


  Transparent mul.
  Lemma ps_mul_index0 {m} (x y : ps m): (x * y) 0 == x 0 * y 0. 
  Proof.
    induction m.
    simpl.
    reflexivity.
    rewrite vec0_cons.
    setoid_rewrite cauchy_product.
    rewrite index_sum.
    rewrite sum_1.
    rewrite IHm.
    reflexivity.
  Qed.
  Opaque mul.

  Lemma ps_composition_mult :   forall (m n : nat) (x y : ps m) (z : ps (S n) ^ m),  ps_composition m n (x * y) z == ps_composition m n x z * ps_composition m n y z.
  Proof.
     intros.
     apply ps_eq_order.
     intros.
     assert (order k <= n0)%nat by lia.
     clear H1.
     generalize dependent k.
     revert x y.
     induction n0;intros.
     - assert (order k = 0)%nat by lia.
       assert (k == 0) by (apply order_zero_eq_zero;auto).
       rewrite !ps_composition_simpl.
       setoid_rewrite exchange_ps_factor_order; [| apply (ps_composition_simpl2 (order k)) | apply (ps_composition_simpl2 (order k)) ].
       rewrite !H1.
       simpl.
       rewrite !H1.
       unfold ps_mult.
       rewrite (idx_index (_ * _) k).
       rewrite H3.
       rewrite <-idx_index.
       setoid_rewrite ps_mul_index0.
       rewrite zero_order;reflexivity.
     - assert (order k <= n0 \/ order k = S n0)%nat by lia.
       destruct H1;[apply IHn0;auto|].
       rewrite ps_composition_spec; try lia.
       destruct (tuple_pred_spec' k); try (simpl;lia).
       symmetry.
       rewrite idx_index.
       rewrite H4 at 1.
       rewrite <-idx_index.
       rewrite deriv_next_backward_full; try lia.
       rewrite pred_index_pred; try (simpl;lia).
       apply ring_eq_mult_eq; try reflexivity.
       rewrite idx_index, pdiff_mult, <-idx_index.
       symmetry.
       rewrite idx_index,ps_composition_chain, <-idx_index.
       setoid_rewrite index_sum; rewrite index_plus.
       rewrite sum_ext.
       2:{
         intros.
         apply exchange_ps_factor_order.
         reflexivity.
         intros.
         apply ps_composition_proper.
         apply pdiff_mult.
         apply 
         reflexivity.
       }
       rewrite sum_ext.
       2:{
         intros.
         apply exchange_ps_factor_order.
         reflexivity.
         intros.
         apply ps_composition_plus.
       }
       rewrite <-(index_sum (fun _ => (D[ _] _ * _))).
       rewrite index_proper.
       3: reflexivity.
       2:{
         apply sum_ext.
         intros.
         apply distrL.
       }
       rewrite index_proper.
       3: reflexivity.
       2: rewrite <-sum_plus;reflexivity.
       rewrite index_plus.
       rewrite !index_sum.
       apply ring_eq_plus_eq.
       +rewrite sum_ext.
        2:{
         intros.
         apply exchange_ps_factor_order.
         reflexivity.
         intros.
         apply IHn0.
         rewrite tuple_pred_order in H6;lia.
       }
       symmetry.
       rewrite idx_index.
       setoid_rewrite ps_composition_chain.
       rewrite sum_mult.
       rewrite <-idx_index.
       rewrite index_sum.
       apply sum_ext.
       intros.
       apply index_proper; try reflexivity.
       rewrite <-!mulA, (mulC _ (D[pred_index k] _)).
       apply ring_eq_mult_eq;try reflexivity.
       +rewrite sum_ext.
        2:{
         intros.
         apply exchange_ps_factor_order.
         reflexivity.
         intros.
         apply IHn0.
         rewrite tuple_pred_order in H6;lia.
       }
       symmetry.
       rewrite idx_index.
       setoid_rewrite ps_composition_chain.
       rewrite sum_mult.
       rewrite <-idx_index.
       rewrite index_sum.
       apply sum_ext.
       intros.
       apply index_proper; try reflexivity.
       rewrite <-!mulA, (mulC _ (D[pred_index k] _)).
       apply ring_eq_mult_eq;try reflexivity.
    Qed.

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


  Lemma ps_pdiff_zero d (i : nat) :  D[i] (0 : ps d) == 0.
  Proof.
    assert (d <= i \/ i < d)%nat by lia.
    destruct H1.
    rewrite out_of_range_diff;auto;reflexivity.
    intros k.
    setoid_rewrite deriv_next_full;auto.
    rewrite ps0.
    simpl; rewrite ps0.
    ring.
  Qed.

  Lemma is_zero_tuple_spec': forall {d : nat} (t : nat ^ d), is_zero_tuple t = false <-> order t > 0.
  Proof.
    intros.
    split.
    intros.
    enough (not (order t = 0)) by (simpl in H2;lia).
    intros Hz.
    contradict H1.
    apply Bool.not_false_iff_true.
    apply is_zero_tuple_spec.
    apply order_zero_eq_zero;auto.
    intros.
    apply Bool.not_true_is_false.
    intros Hz.
    apply is_zero_tuple_spec in Hz.
    enough (order t = 0) by (simpl in H2;lia).
    rewrite Hz.
    apply zero_order.
  Qed.
  Lemma ps_pdiff_one d (i : nat) :  D[i] (1 : ps d) == 0.
  Proof.
    assert (d <= i \/ i < d)%nat by lia.
    destruct H1.
    rewrite out_of_range_diff;auto;reflexivity.
    intros k.
    setoid_rewrite deriv_next_full;auto.
    rewrite ps0.
    simpl.
    unfold one_ps.
    enough (is_zero_tuple (k + nth1 d i) = false) as -> by ring.
    apply is_zero_tuple_spec'.
    rewrite order_plus, order_nth1;auto;simpl;lia.
  Qed.
  Lemma ps_composition_0 m n (x : ps (S n)^m): ps_composition m n 0 x == 0.
  Proof.
    intros.
    apply ps_eq_order.
    intros.
    assert (order k <= n0)%nat by lia.
    clear H1.
    generalize dependent k.
    generalize dependent x.
    induction n0;intros.
    - assert (order k = 0)%nat by lia.
       assert (k == 0) by (apply order_zero_eq_zero;auto).
       rewrite !ps_composition_simpl.
       rewrite H1.
       simpl; rewrite H1;reflexivity.
   - assert (order k <= n0 \/ order k = S n0)%nat by lia.
     destruct H1;[apply IHn0;auto|].
     rewrite ps_composition_next; try lia.
     setoid_rewrite index_sum.
     rewrite sum_zero.
     simpl;rewrite ps0;ring.
     intros.
     setoid_rewrite exchange_ps_factor_order.
     2 : reflexivity.
     2 : {
       intros.
       rewrite idx_index.
       setoid_rewrite ps_pdiff_zero.
       rewrite <-idx_index.
       rewrite tuple_pred_order in H4.
       apply IHn0;auto;lia.
     }
     rewrite idx_index.
     rewrite mul0.
     rewrite <-idx_index.
     rewrite ps0.
     reflexivity.
   Qed.

  Lemma ps_composition_1 m n (x : ps (S n)^m): ps_composition m n 1 x == 1.
  Proof.
    intros.
    apply ps_eq_order.
    intros.
    assert (order k <= n0)%nat by lia.
    clear H1.
    generalize dependent k.
    generalize dependent x.
    induction n0;intros.
    - assert (order k = 0)%nat by lia.
       assert (k == 0) by (apply order_zero_eq_zero;auto).
       rewrite !ps_composition_simpl.
       rewrite H1.
       simpl; rewrite H1.
       unfold one_ps.
       assert (is_zero_tuple 0 = true) as -> by (apply is_zero_tuple_spec;reflexivity).
       assert (is_zero_tuple k = true) as -> by (apply is_zero_tuple_spec;auto).
       reflexivity.
   - assert (order k <= n0 \/ order k = S n0)%nat by lia.
     destruct H1;[apply IHn0;auto|].
     assert (1 k == 0) as ->.
     {
       simpl.
       unfold one_ps.
       enough (is_zero_tuple k = false) as -> by reflexivity.
       apply is_zero_tuple_spec';lia.
     }
     rewrite ps_composition_next; try lia.
     setoid_rewrite index_sum.
     rewrite sum_zero.
     ring.
     intros.
     rewrite idx_index.
     rewrite ps_pdiff_one.
     rewrite ps_composition_0.
     rewrite mul0.
     rewrite <-idx_index.
     rewrite ps0.
     reflexivity.
   Qed.

  Lemma comp1_spec' : forall (m n i : nat) (x : ps (S n) ^ m), i < m -> (forall j, (x\_j 0 == 0)) -> ps_composition m n (ps_comp1 m i) x == x \_ i.
  Proof.
    intros.
    apply ps_eq_order.
    intros.
    assert (order k <= n0)%nat by lia.
    clear H3.
    generalize dependent k.
    induction n0;intros k H3.
    - assert (order k = 0)%nat by lia.
      assert (k == 0) by (apply order_zero_eq_zero;auto).
     rewrite !ps_composition_simpl.
     rewrite H4.
     simpl ps_composition_ith.
     rewrite H4.
     unfold ps_comp1.
     rewrite zero_order.
     rewrite idx_index, H5, <-idx_index.
     rewrite H2.
     simpl;reflexivity.
   - assert (order k <= n0 \/ order k = S n0)%nat by lia.
     destruct H4;[apply IHn0;auto|].
     rewrite ps_composition_next; try lia.
     destruct (tuple_pred_spec' k); try (simpl;lia).
     symmetry.
     rewrite idx_index.
     rewrite H6 at 1.
     rewrite <-idx_index.
     rewrite deriv_next_backward_full; try lia.
     rewrite pred_index_pred; try (simpl;lia).
     apply ring_eq_mult_eq; try reflexivity.

     setoid_rewrite index_sum.
     rewrite (sum_single _ i m);auto.
     + symmetry.
       rewrite idx_index.
       setoid_rewrite comp1_diff1;auto.
       rewrite ps_composition_1.
       rewrite mul1.
       rewrite <-idx_index.
       reflexivity.
     + intros.
       rewrite idx_index.
       setoid_rewrite comp1_diff0;auto.
       rewrite ps_composition_0.
       rewrite mul0.
       rewrite <-idx_index, ps0;reflexivity.
  Qed.

  Lemma ps_comp_0 {m n}  (x : ps m) (y : (ps (S n) ^ m)) : ps_composition m n x y 0 == x 0.
  Proof.
    rewrite ps_composition_simpl.
    rewrite zero_order.
    simpl.
    setoid_rewrite zero_order.
    reflexivity.
  Qed.

  Lemma order_pos_pred_index_lt {d} (k : nat^d) : order k > 0 -> pred_index k < d. 
  Proof.
    intros.
    apply tuple_pred_spec';simpl;lia.
  Qed.

  Lemma ps_composition_exchange {m n}  (x : ps m) (y : (ps (S n) ^ m)) (z : (ps (S n)^m)) k  : (forall j, (order j <= order k)%nat -> (forall i, i < m -> y\_i j == z\_i j)) ->  ps_composition m n x y k == ps_composition m n x z k.
  Proof.
    rewrite !ps_composition_simpl.
    intros.
    enough (forall K, ((order K <= order k)%nat -> ps_composition_ith m n x y (order K) K == ps_composition_ith m n x z (order K) K )) by (apply H2;auto).
    intros.
    remember (order k) as k0.
    clear Heqk0.
    clear k.
    revert H1.
    revert x.
    generalize dependent K.
    induction k0.
    intros;assert (order K = 0) by (simpl in * ;lia);rewrite H3;simpl;rewrite H3;reflexivity.
    intros.
    assert (order K <= k0 \/ order K = S k0 )%nat by lia.
    destruct H3.
    apply IHk0;auto.
    rewrite H3.
    clear H2.
    rewrite !ps_composition_ith_next;auto.
    apply ring_eq_mult_eq; [reflexivity|].
    setoid_rewrite index_sum.
    apply sum_ext.
    intros.
    apply exchange_ps_factor_order.
    - intros.
      rewrite tuple_pred_order in H4.
      setoid_rewrite deriv_next_full; try (apply order_pos_pred_index_lt;lia).
      apply ring_eq_mult_eq; [reflexivity|].
      apply H1;auto.
      rewrite !order_plus, order_nth1;[simpl;lia|].
      apply order_pos_pred_index_lt;simpl;lia.
   -  intros.
      rewrite tuple_pred_order in H4.
      setoid_rewrite ps_comp_ith_larger; try lia.
      apply IHk0; try lia.
      intros.
      apply H1;auto.
  Qed.
  #[global] Instance ps_diffAlgebra  :  CompositionalDiffAlgebra (A := ps).
  Proof.
     exists ps_composition ps_comp1.
     (* apply comp1_spec. *)
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


   Lemma double_sum_le f g n : (forall i j,  f i j <= g i j) ->  sum (fun i => (sum (fun j => f i j) (S i))) n <= sum (fun i => (sum (fun j => g i j) (S i))) n .
   Proof.
   intros.
   apply sum_le.
   intros.
   apply sum_le.
   intros.
   apply H1;auto.
  Qed.

   Lemma sum_0 f : sum f 0 == 0.
   Proof.
     unfold sum;simpl;reflexivity.
   Qed.
   Lemma sum_mult_to_double_sum f g n1 n2 : (sum f n1) * (sum g n2) == sum (fun i => (sum (fun j => f i * g j) n2)) n1.
   Proof.
     induction n1.
     rewrite !sum_0;ring.
     rewrite !sum_S.
     ring_simplify.
     rewrite IHn1.
     rewrite sum_mult.
     reflexivity.
   Qed.
   Lemma double_sum_exchange f n1 n2 : sum (fun i => (sum (fun j => f i j) n2)) n1 == sum (fun j => (sum (fun i => f i j) n1)) n2.
   Proof.
     generalize dependent n2.
     induction n1.
     - intros.
       symmetry.
       rewrite sum_ext.
       2 :{
         intros.
         apply sum_zero.
         intros.
         lia.
       }
       rewrite sum_zero;try reflexivity.
    - intros.
      rewrite sum_S.
      symmetry.
      rewrite sum_ext.
      2: intros;apply sum_S.
      rewrite <-sum_plus.
      rewrite IHn1.
      reflexivity.
   Qed.

   Lemma nested_sum_backwards f n : sum (fun i => (sum (fun j => f i j) (S (n-i)%nat))) (S n) == sum (fun i => (sum (fun j => f (n-i)%nat j) (S i))) (S n).
   Proof.
    rewrite sum_backwards.
    simpl.
    apply sum_ext.
    intros.
    replace (S (n-(n-n0)))%nat with (S n0) by lia.
    reflexivity.
  Qed.

   Lemma inner_sum1 f m: sum (fun j => (sum (f j)  1)) m == sum (fun i => (f i 0)) m.
   Proof.
     apply sum_ext.
     intros.
     apply sum_1.
  Qed.

   Lemma triple_sum_inner_S f n3 n2 n1 : sum (fun i => (sum (fun j => (sum (fun k => f i j k) (S (n1  i j)))) (n2 i))) n3 == sum (fun i => (sum (fun j => (sum (fun k => f i j k) (n1 i j))) (n2 i))) n3 +   sum (fun n : nat => sum (fun n0 : nat => f n n0 (n1 n n0)) (n2 n)) n3 .
   Proof.
   rewrite sum_ext.
   2:{
       intros.
       apply sum_ext.
       intros.
       apply sum_S.
   }
   assert (forall n, sum (fun n0 : nat => sum (f n n0) (n1 n n0) + f n n0 (n1 n n0)) (n2 n) == sum (fun n0 : nat => sum (f n n0) (n1 n n0)) (n2 n) + sum (fun n0  => f n n0 (n1 n n0)) (n2 n)).
   {
     intros.
     rewrite sum_plus.
     reflexivity.
   }

   rewrite sum_ext.
   2:{
       intros.
       apply H1.
   } 
   rewrite <-sum_plus.
   reflexivity.
 Qed.
  Lemma double_sum_reparam f m : sum (fun n : nat => sum (fun n0 : nat => f n n0) n) m == sum (fun n : nat => sum (fun n0 : nat => f (m - n + n0)%nat n0) n) m.
  Proof.
    induction m.
    rewrite !sum_0.
    reflexivity.
    rewrite sum_S.
    rewrite IHm.
    rewrite sum_S_fun.
    rewrite sum_0.
    ring_simplify.
    symmetry.
    rewrite sum_ext.
    2:{
      intros.
      apply sum_S.
    }
    simpl.
    rewrite sum_plus.
    apply sum_ext.
    intros.
    replace (m - n + n)%nat with m by lia.
    ring.
  Qed.
  Lemma triple_sum_reparam f n :  sum (fun i => sum (fun j => sum (fun k => f i j k) (S (n-i))) (S i)) (S n) == sum (fun i => sum (fun j => sum (fun k => f (k+j) j (i-j)%nat) (S (n-i))) (S i)) (S n).
  Proof.
    intros.
    induction n.
    simpl.
    rewrite !sum_1.
    replace (0+0)%nat with 0%nat by lia.
    replace (0-0)%nat with 0%nat by lia.
    reflexivity.
    remember (S n) as m.
    rewrite !sum_S.
    simpl.
    replace (m-m)%nat with 0%nat by lia.
    replace (0+m)%nat with m by lia.
    rewrite !sum_0.
    rewrite <-!addA.
    apply ring_eq_plus_eq;try reflexivity.
    rewrite !add0.
    rewrite !inner_sum1.
    simpl.
    rewrite !triple_sum_inner_S.
    simpl.
    rewrite !addA.
    apply ring_eq_plus_eq.
    assert (  sum (fun i =>  sum (fun j : nat => sum (fun k : nat => f i j k) (m - i)) (S i)) m == sum (fun i => sum (fun j : nat => sum (fun k : nat => f i j k) (S( n - i))) (S i)) m).
    {
      apply sum_ext.
      rewrite Heqm.
      intros.
      replace (S (n -n0)) with (S n - n0)%nat by lia.
      reflexivity.
    }
    rewrite H1.
    rewrite IHn.
    apply sum_ext.
    intros.
    rewrite Heqm.
    replace (S (n -n0)) with (S n - n0)%nat by lia.
    reflexivity.
    rewrite sum_ext.
    2:intros;apply sum_S.
    simpl.
    rewrite <-!sum_plus.
    rewrite addC, <-!addA.
    apply ring_eq_plus_eq; try reflexivity.
    symmetry.
    rewrite sum_ext.
    2:intros;apply sum_S.
    simpl.
    rewrite <-!sum_plus.
    rewrite addC.
    apply ring_eq_plus_eq.
    apply sum_ext.
    intros.
    replace (n0 - n0)%nat with 0%nat by lia.
    replace (m - n0 +n0)%nat with m by lia.
    reflexivity.
    symmetry.
    rewrite double_sum_reparam.
    apply sum_ext.
    intros.
    apply sum_ext.
    intros.
    replace  (m - (m - n0 + n1))%nat with (n0 - n1)%nat by lia.
    reflexivity.
 Qed.
 Lemma le_eq x y : (x == y) -> (x <= y).
 Proof.
   intros ->.
   apply le_refl.
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
       assert (sum (fun i => sum_order (partial_index (a*b) i) (n-i)) (S n) == sum (fun i =>(sum_order (sum (fun j => partial_index a j * partial_index b (i-j)) (S i)) (n-i))) (S n)) as ->.
       {
         apply sum_ext.
         intros.
         rewrite partial_index_mul_sum.
         reflexivity.
       }
       assert (forall i, i < (S n) -> sum_order (sum (fun j => partial_index a j * partial_index b (i - j)) (S i)) (n-i) <= sum (fun j => sum_order (partial_index a j * partial_index b (i - j)) (n-i)) (S i)).
       {
         intros.
         apply sum_order_sum.
       }
       apply (le_trans _ _ _ (sum_le _ _ _ H1)).
       assert ( (forall i j : nat,  sum_order (partial_index a j * partial_index b (i-j)) (n-i)  <= sum (fun k : nat => sum_order (partial_index a j) k  * sum_order (partial_index b (i - j)) (n-i-k)) (S (n-i)))).
       {
         intros.
         apply IHd.
       }

       apply (le_trans _ _ _ (double_sum_le _ _ _ H2)).
       rewrite (sum_ext (fun j => sum_order _ _ * _)).
       2:{
         intros.
         rewrite !sum_order_next.
         apply sum_mult_to_double_sum.
       }
       simpl.
       rewrite triple_sum_reparam.
       simpl.
       apply le_eq.
       apply sum_ext.
       intros.
       apply sum_ext.
       intros.
       apply sum_ext.
       intros.
       replace (n2+n1 - n1)%nat with n2 by lia.
       replace (n - (n2 + n1) - (n0 - n1)) %nat with (n - n0 - n2)%nat by lia.
       reflexivity.
    Qed.

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

  Opaque order.
  Lemma ps_comp0  {d e} (a : (nat^d -> A)) (bs : (nat^(S e) -> A)^d): (a \o1 bs) 0 == (a 0). 
  Proof.
    intros.
    simpl.
    rewrite ps_composition_simpl.
    setoid_rewrite zero_order.
    simpl.
    setoid_rewrite zero_order.
    reflexivity.
  Qed.
  Transparent order.
  
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


