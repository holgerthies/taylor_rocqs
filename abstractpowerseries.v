From Coq Require Import Psatz.
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

Section AbstractPowerSeries.
  Context `{SemiRing}.
  Definition ps d := nat^d -> A.

  Context `{CompositionalDiffAlgebra (A := ps) (H := _)}.

  Context `{invSn : Sn_invertible (A := A) (H := _) (R_rawRing := _) (H0 := _)}.
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
      cauchy_product {d} (a b : nat^(S d) -> A) n k : (a*b) (tuple_cons n k) == sum (fun i => (fun k0 => a (tuple_cons i k0)) * (fun k0 => b (tuple_cons (n-i)%nat k0))) (S n) k
    }.

  Class AbstractPowerSeries := {
  ps_derive : forall {d} (a : (nat^d -> A)) (k j : nat^d),  (Dx[k] a) j == t[j+1!k] * a (k+j);
  ps0 : forall d  (k : nat^d), (0 : (nat^d -> A)) k == 0;
  ps_add0 : forall d (a b : (nat^d -> A)) , (a + b) 0 == a 0 + b 0;
  ps_mul0 : forall d (a b : (nat^d -> A)) , (a * b) 0 == a 0 * b 0;
  ps_comp0 : forall {d e} (a : (nat^d -> A)) (bs : (nat^(S e) -> A)^d), (a \o1 bs) 0 ==  (a 0);
  index_proper : forall {d}, Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun (a : nat^d -> A) n => a n);
  comp1_0 {d} i : (comp1 (m:=d)  i) 0 == 0;
  comp1_1d  k : ((k == 1%nat) -> (comp1 (m:=1)  0) t(k) == 1) /\ ((k <> 1%nat) -> (comp1 (m:=1)  0) t(k) == 0);

  }.
  
  (* todo: show cauchy product from other properties *)
End AbstractPowerSeries.


Section AbstractPowerSeriesProperties.
  Context `{AbstractPowerSeries}.

  Definition index {d} (a : nat^d -> A) n := a n.

  Instance index_prop {d}: Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (@index d). 
  Proof.
    apply index_proper.
  Defined.



  Add Ring ARing: (ComSemiRingTheory (A := A)). 
  Lemma ps_property_backwards {d} (a : nat^d -> A) k : a k == t![k] * (Dx[k] a) 0.
  Proof.
    rewrite ps_derive.
    rewrite <-mulA.
    setoid_replace (0 +1 : nat^d) with (1 : nat^d) by (rewrite addC;apply add0).
    rewrite rising_factorialt1.
    rewrite invfact_factt.
    rewrite mulC,mul1.
    apply index_proper;try reflexivity.
    rewrite add0;reflexivity.
  Qed.

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
      
  Lemma deriv_next {d} (f : nat^(S d) -> A) hd tl : (D[0] f) (tuple_cons hd tl) == # (hd+1) * f (tuple_cons (hd+1)%nat tl). 
  Proof.  
    replace (hd+1)%nat with (S hd) at 2 by lia.
    rewrite (ps_property_backwards f).
    rewrite <-mulA.
    rewrite inv_factt_S_reverse.
    replace (Dx[ tuple_cons (S hd) tl] f 0) with (index  (Dx[ tuple_cons (S hd) tl] f) 0) by auto.
    setoid_rewrite <-deriv_rec_next.
    unfold index.
    rewrite <-ps_property_backwards.
    reflexivity.
  Qed.
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

  Lemma deriv_next_backwards {d} (f : nat^(S d) -> A) hd tl : f (tuple_cons (S hd) tl) == (inv_Sn hd) * (D[0] f) (tuple_cons hd tl).
  Proof.  
    pose proof (inv_Sn_spec hd).
    rewrite <-mul1.
    rewrite <-H6.
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

  Lemma index_plus {m} (g1 g2 : nat^m -> A) (k : nat^m): (g1 + g2 ) k == g1 k + g2 k.
  Proof.
    rewrite ps_property_backwards.
    rewrite (ps_property_backwards g1).
    rewrite (ps_property_backwards g2).
    setoid_replace ( t![ k] * Dx[ k] g1 0 + t![ k] * Dx[ k] g2 0) with (t![ k] * (Dx[k] g1 0 + Dx[k] g2 0)) by ring.
    apply ring_eq_mult_eq; try reflexivity.
    rewrite <-ps_add0.
    apply index_proper; try reflexivity.
    apply derive_rec_plus.
  Qed.   

  Lemma exchange_ps_factor (h h' g : nat^1 -> A) (k : nat) : (forall i, (i <= k)%nat -> (h t(i)) == (h' t(i))) -> (h * g) t(k) == (h' * g) t(k).
  Proof.
    revert h h' g.
    induction k;intros.
    - rewrite !ps_mul0.
      enough (h 0 == h' 0) as -> by reflexivity.
      assert (0 <= 0)%nat by lia.
      specialize (H6 _ H7).
      transitivity (h t(0)).
      apply index_proper;try reflexivity.
      rewrite H6.
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
        apply H6; lia.
      + apply IHk.
        intros.
        apply H6;auto.
   Qed.
  Lemma deriv_rec_1 {d} (f : nat^d -> A) hd (tl : nat^0) : (derive_rec f (tuple_cons hd tl)) == nth_derivative 0 f hd.
  Proof.
    unfold derive_rec;simpl.
    destruct (destruct_tuple_cons (tuple_cons hd tl)) as [hd' [tl' P]].
    apply tuple_cons_ext in P.
    destruct P as [-> ->].
    reflexivity.
  Qed.

  Lemma index_sum {m} (g: (nat -> (nat^m -> A))) (k : nat^m) N: (sum g N) k == (sum (fun i => (g i k)) N).
  Proof.
    induction N.
    unfold sum;simpl.
    apply ps0.
    rewrite index_proper; try apply sum_S; try reflexivity.
    rewrite sum_S.
    rewrite index_plus.
    rewrite IHN;reflexivity.
  Qed.

  Lemma deriv_eq_ps_equal {m} (a b : (nat^m -> A)) : (forall (k : nat^m), (Dx[k] a) == (Dx[k] b)) -> a == b.
  Proof.
    intros.
    intros i.
    rewrite ps_property_backwards.
    rewrite (ps_property_backwards b).
    apply ring_eq_mult_eq;try reflexivity.
    apply H6.
  Qed.
  Lemma deriv_eq_ps_equal1  (a b : (nat^1 -> A)) : (forall (k : nat), nth_derivative 0 a k == nth_derivative 0 b k) -> a == b.
  Proof.
    intros.
    apply deriv_eq_ps_equal.
    intros.
    destruct (destruct_tuple_cons k) as [k0 [N ->]].
    rewrite !deriv_rec_1.
    apply H6.
  Qed.

  Lemma ntimes_index {d} (a : nat^d -> A) k n : (ntimes n a k) == ntimes n (a k).
  Proof.
    induction n.
    simpl.
    rewrite ps0;reflexivity.
    simpl.
    rewrite !index_plus.
    rewrite IHn.
    reflexivity.
 Qed.

End AbstractPowerSeriesProperties.
