From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Require Import algebra.
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

  Definition nth1 (d i : nat) : nat^d.
  Proof.
    revert i.
    induction d;intros.
    apply 0.
    destruct i.
    apply (tuple_cons 1 0).
    apply (tuple_cons 0 (IHd i)).
  Defined.

  Lemma nth1_spec1 d i : i < d -> (nth1 d i)\_i == 1.
  Proof.
    intros.
    generalize dependent i.
    induction d;intros;try lia.
    destruct i.
    simpl.
    rewrite tuple_nth_cons_hd;reflexivity.
    simpl.
    rewrite tuple_nth_cons_tl.
    apply IHd;lia.
  Qed.

  Lemma nth1_spec0 d i j: i <> j -> (nth1 d i)\_j == 0.
  Proof.
    intros.
    generalize dependent i.
    generalize dependent j.
    induction d;intros;try lia.
    destruct i.
    simpl.
    destruct j;reflexivity.
    simpl.
    destruct j;reflexivity.
    simpl.
    destruct i.
    destruct j;try lia.
    rewrite tuple_nth_cons_tl.
    enough ((0 : nat^d )\_j == 0) by (simpl;auto).
    apply vec0_nth.
    destruct j.
    rewrite tuple_nth_cons_hd;auto.
    rewrite tuple_nth_cons_tl.
    apply IHd;lia.
  Qed.

  Definition is_zero_tuple {d}  (t : nat^d) : bool.
  Proof.
    induction d.
    apply true.
    destruct (destruct_tuple_cons t) as [h [tl P]].
    destruct h.
    apply (IHd tl).
    apply false.
 Defined.

  Lemma is_zero_tuple_spec {d} (t : nat ^d ) : is_zero_tuple t = true <-> t == 0.
  Proof.
    split; intros.
    - induction d; [apply zero_tuple_zero|].
      simpl in H.
      destruct (destruct_tuple_cons t) as [h [tl ->]].
      destruct h;try discriminate H.
      rewrite vec0_cons.
      apply tuple_cons_equiv_equiv; try reflexivity.
      apply IHd;auto.
  - induction d;auto.
      simpl.
      destruct (destruct_tuple_cons t) as [h [tl ->]].
      rewrite vec0_cons in H.
      apply tuple_cons_equiv in H.
      simpl in H.
      destruct H as [-> H].
      apply IHd;auto.
  Qed.
Section AbstractPowerSeries.
  Context `{SemiRing}.
  Definition ps d := nat^d -> A.

  Add Ring ARing: (ComSemiRingTheory (A := A)). 
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

  Context `{invSn : Sn_invertible (A := A) (H := _) (R_rawRing := _) (H0 := _)}.
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


  Lemma ps_ntimes_S {d} (a : ps d) n  : (fun k => #(S n) * a k) == (fun k => #n * a k) + a.
  Proof.
    intros k.
    simpl.
    setoid_rewrite ps_plus_index.
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

  Lemma ps_derive_spec {d} (a : ps d) k: Dx[k] a == tuple_derive a k.
  Proof.
    destruct d.
    simpl.

    intros k0.
    unfold derive_rec, tuple_derive.
    simpl.
    ring_simplify.
    apply index_proper; try reflexivity.
    rewrite !zero_tuple_zero.
    reflexivity.
    destruct (destruct_tuple_cons k) as [k0 [kt ->]].
    unfold tuple_derive.
    Search derive_rec.
    apply partial_index_equiv.
    intros n.
 Admitted.

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
  
  #[global] Instance ps_diffAlgebra  :  CompositionalDiffAlgebra (A := ps).
  Proof.
  Admitted.
 (* Context `{CompositionalDiffAlgebra (A := ps) (H := _) (H0 := _) (H1 := _) (H2 := _)}. *)

  (* coefficient norm is currently formalized abstractly *)
  Class CoeffSum `{ArchimedeanField (A:=A) (H:=_) (R_rawRing := _) (R_semiRing := _) (invSn := _)}:= {
      sum_order {d} (a : nat^d -> A ) (n : nat) : A;
      sum_order_proper d : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (@sum_order d);
      sum_order_mult {d} (a b : nat^d -> A) n : sum_order (a * b) n == sum (fun j => sum_order a j * sum_order b (n-j)) (S n);
      sum_order_nonneg {d} (a : nat^d -> A) n : 0 <= sum_order a n;
      sum_order_sum {d} (a : nat -> nat^d -> A) m n :  sum_order (sum a m) n == sum (fun i => (sum_order (a i) n)) m;
      sum_order_diff_le {d} (a :  nat^d -> A) i n : i < d -> sum_order (D[i] a) n <= #(n+1)%nat * sum_order a (n+1)%nat;
      sum_order1 {d} i k : i < d -> ((k == 1)%nat -> sum_order (d:=d) (comp1  i) k == 1) /\ ((k <> 1)%nat -> sum_order (d:=d) (comp1  i) k == 0);
      sum_order1d  (a :  nat^1 -> A)  k :  sum_order (d:=1) a k == norm (a t(k));
      sum_order0  {d} (a :  nat^d -> A):  sum_order  a 0 == norm (a 0);
    }.

  Class AbstractPowerSeries := {
  ps_comp0 : forall {d e} (a : (nat^d -> A)) (bs : (nat^(S e) -> A)^d), (a \o1 bs) 0 ==  (a 0);
  comp1_0 {d} i : (comp1 (m:=d)  i) 0 == 0;
  comp1_1d  k : ((k == 1%nat) -> (comp1 (m:=1)  0) t(k) == 1) /\ ((k <> 1%nat) -> (comp1 (m:=1)  0) t(k) == 0);
  }.
  
End AbstractPowerSeries.


Section AbstractPowerSeriesProperties.
  Context `{AbstractPowerSeries}.

  Definition index {d} (a : nat^d -> A) n := a n.

  Instance index_prop {d}: Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (@index d). 
  Proof.
    apply index_proper.
  Defined.



  Add Ring ARing: (ComSemiRingTheory (A := A)). 

  (*  Lemma nth_deriv_independent {d} (f : nat^d -> A) i n : nth_derivative (S i) D[0] f n  == D[0] (nth_derivative (S i) f n). *)
  (*  Proof. *)
  (*    induction n. *)
  (*    simpl. *)
  (*    intros;reflexivity. *)
  (*    simpl. *)
  (*    intros. *)
  (*    apply index_proper; try reflexivity. *)
  (*    rewrite IHn. *)
  (*    rewrite pdiff_comm. *)
  (*    reflexivity. *)
  (*  Qed. *)
  
  (*  Lemma deriv_next_helper {d e} (f : nat^d -> A) i (k : nat^e) : derive_rec_helper (S i) D[0] f k == D[0] (derive_rec_helper (S i) f k). *)
  (*  Proof. *)
  (*    revert f i. *)
  (*    induction e;intros. *)
  (*    simpl. *)
  (*    intros;reflexivity. *)
  (*    simpl. *)
  (*    destruct (destruct_tuple_cons k) as [hd [tl P]]. *)
  (*    intros. *)
  (*    specialize (IHe tl f (S i)). *)
  (*    apply index_proper; try reflexivity. *)
  (*    rewrite nth_derivative_proper; try apply IHe. *)
  (*    apply nth_deriv_independent. *)
  (* Qed. *)

  (* Lemma deriv_rec_next {d e} (f : nat^d -> A) hd (tl : nat^e) : (derive_rec (D[0]f) (tuple_cons hd tl)) == (derive_rec f (tuple_cons (S hd) tl)). *)
  (* Proof. *)
  (*   Opaque SetoidClass.equiv. *)
  (*   unfold derive_rec;simpl. *)
  (*   destruct (destruct_tuple_cons (tuple_cons hd tl)) as [hd' [tl' P]]. *)
  (*   destruct (destruct_tuple_cons (tuple_cons (S hd) tl)) as [hd'' [tl'' P']]. *)
  (*   apply tuple_cons_ext in P. *)
  (*   apply tuple_cons_ext in P'. *)
  (*   destruct P as [<- <-]. *)
  (*   destruct P' as [<- <-]. *)
  (*   rewrite nth_derivative_proper; try apply deriv_next_helper. *)
  (*   rewrite nth_derivative_S. *)
  (*   reflexivity. *)
  (*   Transparent SetoidClass.equiv. *)
  (* Qed. *)
      
  Lemma deriv_next_backwards {d} (f : nat^(S d) -> A) hd tl : f (tuple_cons (S hd) tl) == (inv_Sn hd) * (D[0] f) (tuple_cons hd tl).
  Proof.  
    pose proof (inv_Sn_spec hd).
    rewrite <-mul1.
    rewrite <-H2.
    rewrite mulC.
    rewrite (mulC (# (S hd))).
    rewrite mulA.
    replace (S hd) with (hd + 1)%nat by lia.
    rewrite <-deriv_next.
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
      specialize (H2 _ H3).
      transitivity (h t(0)).
      apply index_proper;try reflexivity.
      rewrite H2.
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
        rewrite !deriv_next.
        apply (ring_eq_mult_eq); try reflexivity.
        apply H2; lia.
      + apply IHk.
        intros.
        apply H2;auto.
   Qed.


  Lemma deriv_eq_ps_equal {m} (a b : (nat^m -> A)) : (forall (k : nat^m), (Dx[k] a) == (Dx[k] b)) -> a == b.
  Proof.
    intros.
    intros i.
    rewrite ps_property_backwards.
    rewrite (ps_property_backwards b).
    apply ring_eq_mult_eq;try reflexivity.
    apply H2.
  Qed.
  Lemma deriv_eq_ps_equal1  (a b : (nat^1 -> A)) : (forall (k : nat), nth_derivative 0 a k == nth_derivative 0 b k) -> a == b.
  Proof.
    intros.
    apply deriv_eq_ps_equal.
    intros.
    destruct (destruct_tuple_cons k) as [k0 [N ->]].
    rewrite !deriv_rec_1.
    apply H2.
  Qed.

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

End AbstractPowerSeriesProperties.
