Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import functions.
Require Import polynomial.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import Classical.
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

  Context `{invSn : Sn_invertible (A := A) (H := _) (R_rawRing := _)}.

  Class AbstractPowerSeries := {
  ps_derive : forall {d} (a : (nat^d -> A)) (k j : nat^d),  (Dx[k] a) j == t[j+1!k] * a (k+j);
  ps0 : forall d  (k : nat^d), (0 : (nat^d -> A)) k == 0;
  ps_add0 : forall d (a b : (nat^d -> A)) , (a + b) 0 == a 0 + b 0;
  ps_mul0 : forall d (a b : (nat^d -> A)) , (a * b) 0 == a 0 * b 0;
  ps_comp0 : forall {d e} (a : (nat^d -> A)) (bs : (nat^(S e) -> A)^d), (a \o1 bs) 0 ==  (a 0);
  index_proper : forall {d}, Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun (a : nat^d -> A) n => a n)
  }.
  
End AbstractPowerSeries.


Section AbstractPowerSeriesProperties.
  Context `{AbstractPowerSeries}.
  Context `{SemiRing (A := A) (H:=H) (R_rawRing := R_rawRing)}.

  Definition index {d} (a : nat^d -> A) n := a n.

  Instance index_prop {d}: Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (@index d). 
  Proof.
    apply index_proper.
  Defined.

  Notation "# n" := (ntimes n 1) (at level 2).


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

   Lemma nth_deriv_independent {d} (f : nat^d -> A) i n : nth_derivative (S i) D[0] f n  == D[0] (nth_derivative (S i) f n).
   Proof.
     induction n.
     simpl.
     intros;reflexivity.
     simpl.
     intros.
     apply index_proper; try reflexivity.
     rewrite IHn.
     rewrite pdiff_comm.
     reflexivity.
   Qed.
  
   Lemma deriv_next_helper {d e} (f : nat^d -> A) i (k : nat^e) : derive_rec_helper (S i) D[0] f k == D[0] (derive_rec_helper (S i) f k).
   Proof.
     revert f i.
     induction e;intros.
     simpl.
     intros;reflexivity.
     simpl.
     destruct (destruct_tuple_cons k) as [hd [tl P]].
     intros.
     specialize (IHe tl f (S i)).
     apply index_proper; try reflexivity.
     rewrite nth_derivative_proper; try apply IHe.
     apply nth_deriv_independent.
  Qed.

  Lemma deriv_rec_next {d e} (f : nat^d -> A) hd (tl : nat^e) : (derive_rec (D[0]f) (tuple_cons hd tl)) == (derive_rec f (tuple_cons (S hd) tl)).
  Proof.
    unfold derive_rec;simpl.
    intros k.
    destruct (destruct_tuple_cons (tuple_cons hd tl)) as [hd' [tl' P]].
    destruct (destruct_tuple_cons (tuple_cons (S hd) tl)) as [hd'' [tl'' P']].
    apply tuple_cons_ext in P.
    apply tuple_cons_ext in P'.
    destruct P as [<- <-].
    destruct P' as [<- <-].
    induction e;intros.
    - simpl.
      pose proof (nth_derivative_S 0 f hd).
      apply index_proper;try rewrite H6;try reflexivity.
   -  simpl.
      destruct (destruct_tuple_cons tl) as [hd' [tl' P']].
  Admitted.
      
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

  Lemma exchange_ps (h h' g : nat^1 -> A) (k : nat) : (forall i, (i <= k)%nat -> (h t(i)) == (h' t(i))) -> (h * g) t(k) == (h' * g) t(k).
  Admitted.

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
End AbstractPowerSeriesProperties.
