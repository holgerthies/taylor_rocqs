Require Import Setoid.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Classes.SetoidClass.
Require Import Psatz.
Require Import Classical.
Require Import List.
Require Import ZArith.
Import ListNotations.

 Definition tuple n A := {t : list A | length t = n}.
 Definition destruct_tuple {n} {A}  (t : @tuple (S n) A)  : {h : A & {t0 : @tuple n A | proj1_sig t = h :: (proj1_sig t0)}}.   
 Proof.
   destruct t.
   destruct x;[contradict e;simpl;lia|].
   exists a.
   assert (length x = n) by (simpl in e;lia).
   exists (exist _ x H).
   simpl;auto.
Defined.
  Definition tuple_cons {A} {n} (x :A ) (t : @tuple n A): @tuple (S n) A.  
  Proof.
   destruct t.
   exists (x :: x0).
   simpl.
   rewrite e.
   reflexivity.
  Defined.

Definition nil_tuple {A}: (@tuple 0 A).
Proof.
  exists [].
  simpl; reflexivity.
Defined.

Definition tuple_nth {m T} (n : nat) (t : @tuple m T) (d : T) : T.
Proof.
  destruct t.
  apply (nth n x d).
Defined.

 Definition tuple_equivalence {A n} {A_setoid : Setoid A} (x : @tuple n A) (y : @tuple n A) : Prop.
 Proof.
   destruct x, y.
   apply (eqlistA SetoidClass.equiv x x0).
 Defined.

 Instance tuple_setoid {A n} {A_setoid : Setoid A} : Setoid (@tuple n A).
 Proof.
 
   exists  tuple_equivalence.
   constructor.
   intros [x P];simpl;apply eqlistA_equiv;apply setoid_equiv.
   intros [x P] [y P'];simpl;apply eqlistA_equiv;apply setoid_equiv.
   intros [x P] [y P'] [z P''];simpl;apply eqlistA_equiv;apply setoid_equiv.
 Defined.


 Lemma tuple_nth_cons_hd {T m} (hd : T) (t : (@tuple m T)) d : (tuple_nth 0 (tuple_cons hd t) d) = hd.
 Proof.
   destruct t;simpl;auto.
 Defined.

 Lemma tuple_nth_cons_tl {T m} n (hd : T) (t : (@tuple m T)) d : (tuple_nth (S n) (tuple_cons hd t) d) = tuple_nth n t d.
 Proof.
   destruct t;simpl;auto.
 Defined.

 Lemma tuple_nth_nil {T} n (t : (@tuple 0 T)) d : (tuple_nth n t d) = d.
 Proof.
   destruct t.
   simpl.
   apply nth_overflow.
   lia.
 Defined.

 Lemma proj1_sig_tuple_cons {T n} x (y: @tuple n T) : proj1_sig (tuple_cons x y) = x :: (proj1_sig y).
 Proof.
   destruct y.
   simpl;auto.
 Qed.

 Lemma destruct_tuple_cons {T n} (y : @tuple (S n) T) : {hd & {tl | y = tuple_cons hd tl}}.
 Proof.
   destruct y.
   destruct x;simpl in e;try lia.
   exists t.
   assert (length x = n) by lia.
   exists (exist _ x H).
   apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
   reflexivity.
Defined.

Definition tuple_map {n A B} (f : A -> B) (x : @tuple n A) : @tuple n B.
Proof.
  induction n.
  apply nil_tuple.
  destruct (destruct_tuple_cons x) as [hd [tl P]].
  apply (tuple_cons (f hd) (IHn tl)).
 Defined.
  Definition seq_to_tuple  {T : Type} {def : T} (f : nat -> T) d : {t : @tuple d T | forall i, i < d -> tuple_nth i t def = (f i)}. 
  Proof.
    revert f.
    induction d;intros.
    exists nil_tuple;intros;lia.
    destruct (IHd (fun n => f (S n))).
    exists (tuple_cons (f 0%nat) x).
    intros.
    destruct i.
    rewrite tuple_nth_cons_hd;simpl;auto.
     rewrite tuple_nth_cons_tl.
     rewrite e;auto;lia.
   Defined.
  
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

 #[global] Instance tuple_cons_proper {n A} {A_setoid : Setoid A} : Proper (equiv ==> equiv ==> equiv) (@tuple_cons A n).
 Proof.
   intros a b eq1 c d eq2.
   unfold tuple_cons.
   simpl.
   destruct c, d.
   simpl.
   apply eqlistA_cons;auto.
 Defined.
 #[global] Instance tuple_nth_proper {n A} {A_setoid : Setoid A} : forall i, Proper (equiv ==> equiv ==> equiv) (@tuple_nth n A i).
 Proof.
   intros.
   intros a b eq1 c d eq2.
   simpl.
   destruct a, b.
   simpl.

   destruct (Nat.lt_ge_cases i n).
   apply eqlistA_nth_ext;try lia.
   apply eq1.
   rewrite !nth_overflow;auto;lia.
 Defined.
  Lemma tuple_cons_ext {n A}  (hd : A) (tl : @tuple n A) hd' tl': tuple_cons hd tl = tuple_cons hd' tl' -> hd = hd' /\ tl = tl'. 
  Proof.
    intros.
    destruct tl, tl'.
    apply eq_sig_fst in H.
    injection H;intros -> ->;split;auto.
    apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;auto.
  Qed.
  Lemma tuple_cons_equiv {n A} {A_setoid : Setoid A} (a0 b0 : A ) (a b : @tuple n A) : (tuple_cons a0 a == tuple_cons b0 b) -> (a0 == b0) /\ (a == b).
  Proof.
    intros.
    split.
    - replace a0 with (tuple_nth 0 (tuple_cons a0 a) a0) by apply tuple_nth_cons_hd.
      replace b0 with (tuple_nth 0 (tuple_cons b0 a) a0) by apply tuple_nth_cons_hd.
      rewrite H.
      rewrite !tuple_nth_cons_hd;reflexivity.
   - apply (tuple_nth_ext' _ _ a0 a0).
     intros.
     rewrite <-(tuple_nth_cons_tl _ a0).
     rewrite <-(tuple_nth_cons_tl _ b0 b).
     rewrite H.
     rewrite tuple_nth_cons_tl.
     reflexivity.
  Qed.

  Lemma tuple_cons_equiv_equiv {n A} {A_setoid : Setoid A} (a0 b0 : A ) (a b : @tuple n A) : (a0 == b0) -> (a == b) -> (tuple_cons a0 a == tuple_cons b0 b).
  Proof.
    intros.
    rewrite H, H0.
     reflexivity.
  Qed.
#[global] Instance tuple_map_proper {n A B} {A_setoid : Setoid A} {B_setoid : Setoid B}: forall f, Proper (equiv ==> equiv) f -> Proper (equiv ==> equiv) (@tuple_map n A B f).
Proof.
  intros f fp a b Heq.
  induction n.
  simpl;auto.
  simpl.
  destruct (destruct_tuple_cons a) as [hd [tl Pa]].
  destruct (destruct_tuple_cons b) as [hd' [tl' Pb]].
  enough (hd == hd' /\ tl == tl') as [-> P0] by (apply tuple_cons_proper;try apply IHn; try reflexivity;auto).
  apply tuple_cons_equiv.
  rewrite <-Pa, <-Pb;auto.
Defined.

Lemma tuple_map_nth {n A B}  (f : A -> B) (t : @tuple n A) i d d': i < n -> tuple_nth i (tuple_map f t) d = f (tuple_nth i t d').
Proof.
  revert i.
  induction n; intros; try lia.
  simpl.
  destruct (destruct_tuple_cons t) as [hd [tl ->]].
  destruct i.
  rewrite !tuple_nth_cons_hd;auto.
  rewrite !tuple_nth_cons_tl.
  apply IHn;lia.
Qed.

Notation "A ^ d" := (tuple d A).
Notation "t( x ; y ; .. ; z )" := (tuple_cons x (tuple_cons y .. (tuple_cons z nil_tuple) ..)).

Notation "t( x )" := (tuple_cons x nil_tuple).
Notation "t()" := nil_tuple.

