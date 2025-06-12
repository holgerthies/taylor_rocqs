(*
   This file defines algebraic structures such as semirings, rings,
   and fields and structures supporting differentiation
    and composition of functions, designed to model spaces of 
    differentiable functions or power series
*)
From Coq Require Import Psatz.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
From Coq Require Import Setoid.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Classes.SetoidClass.
From Coq Require Import Classical.
Require Import tuple.
Declare Scope algebra_scope.
Open Scope algebra_scope.
Declare Scope fun_scope.

Class RawRing  {A : Type} `{Setoid A}:= {
      zero : A;
      one : A;
      add : A -> A -> A;
      mul : A -> A -> A;

 }.

Class EmbedNat   `{R_rawRing : RawRing} := {
  embNat     : nat -> A ;
  embNat0     : embNat 0 == zero ;
  embNat_S     : forall n, embNat (S n) == add (embNat n) one ;
 }.

  Definition sum `{A_Rawring : RawRing } (f : nat -> A) n := (fold_right add zero (map f (seq 0 n))).

  Fixpoint npow `{A_Rawring : RawRing } (x : A) (n : nat) : A :=
    match n with
    | O => one 
    | S m => mul x (npow x m)
    end.
 Infix "+" := add : algebra_scope.
 Infix "*" := mul : algebra_scope.
 Notation "1" := one : algebra_scope.
 Notation "0" := zero : algebra_scope.

 Notation "x \_ i" := (tuple_nth i x 0) (at level 2).
 
Class SemiRing `{R_rawRing : RawRing}   := {

      add_proper :: Proper (equiv ==> equiv ==> equiv) add;
      mul_proper :: Proper (equiv ==> equiv ==> equiv) mul;
      addA : forall a b c, add (add a b) c == add a (add b c);
      addC : forall a b, add a b == add b a;
      add0 : forall a, add a zero == a; 
      mulA: forall a b c, mul (mul a b) c == mul a (mul b c);
      mulC : forall a b, mul a b == mul b a;
      mul0 : forall a, mul a zero == zero; 
      mul1 : forall a, mul a one == a; 
      distrL : forall a b c, mul a (add b c) == add (mul a b) (mul a c)
    }.

Lemma ComSemiRingTheory `{A_comSemiRing : SemiRing } : semi_ring_theory 0 1 add mul equiv.
  Proof.
    constructor.
    intro; rewrite addC; apply add0.
    exact addC.
    symmetry; apply addA.
    intro; rewrite mulC; apply mul1.
    intros;rewrite mulC;apply mul0.
    exact mulC.
    symmetry ; apply mulA.
    intros m n p.
    rewrite mulC.
    rewrite (mulC n p).
    rewrite (mulC m p).
    apply distrL.
Qed.

Class Ring `{R_semiRing : SemiRing} := {
    opp : A -> A;
    opp_proper :: Proper (equiv ==> equiv) opp;
    addI : forall a, add a (opp a) == zero;
}.

Definition minus  `{Ring} (x y : A)  := add x (opp y).

 #[global] Instance minus_proper `{Ring} : Proper (equiv ==> equiv ==> equiv) minus.
  Proof.
    intros a b P0 c d P1.
    unfold minus.
    rewrite P0,P1;reflexivity.
Defined.

Notation "- x" := (opp x) : algebra_scope.
Infix "-" := minus : algebra_scope.

(* Class Field `{A_Ring : Ring} := { *)
(*       inv : forall {x}, (not (x == zero)) -> A; *)
(*       mulI : forall x (p : (not (x == zero))), mul (inv p) x == one; *)
(*       distinct_0_1 : (not (zero == one)) *)
(*     }. *)

  Lemma sum_S_fun `{RawRing} (f : nat -> A) n : (sum f ( S n)) == f 0%nat + (sum (fun n => (f (S n))) n).
  Proof.
    unfold sum.
    simpl.
    enough (map f (seq 1 n) = map (fun n => f (S n)) (seq 0 n)) as -> by reflexivity.
    rewrite <- seq_shift.
    rewrite map_map;auto.
  Qed.

Section Sums.
  Context `{SemiRing}.
  Add Ring ARing : ComSemiRingTheory.

  Lemma distrR : forall a b c, mul (add b c) a == add (mul b a) (mul c a).
  Proof.
    intros;ring.
  Qed.

  Lemma sum_1 (f : nat -> A) : (sum f 1) == (f 0%nat). 
  Proof.
    unfold sum;simpl;auto.
    ring_simplify.
    reflexivity.
  Qed.
  Lemma sum_S (f : nat -> A) n : (sum f (S n)) == add (sum f n) (f n). 
  Proof.
    revert f.
    induction n;intros.
    unfold sum; simpl;ring.
    rewrite sum_S_fun.
    rewrite IHn.
    ring_simplify.
    rewrite <- sum_S_fun.
    ring.
  Qed.

   Lemma sum_ext f g d  : (forall n, (n < d)%nat -> (f n) == (g n)) -> sum f d == sum g d.
   Proof.
     intros.
     induction d;intros.
     unfold sum; simpl; reflexivity.
     rewrite !sum_S.
     rewrite IHd;[| intros; apply H1;  lia].
     rewrite H1;try lia;reflexivity.
   Qed.

  Lemma sum_backwards f n : sum f n == sum (fun j => f (n-(S j))%nat) n.
  Proof.
    induction n.
    unfold sum;simpl.
    reflexivity.
    rewrite sum_S.
    rewrite sum_S_fun.
    replace (S n - 1)%nat with n by lia.
    rewrite addC.
    apply add_proper; try reflexivity.
    rewrite IHn.
    apply sum_ext.
    intros.
    replace (S n - ((S (S n0))))%nat with (n - S n0)%nat by lia.
    reflexivity.
  Qed.

  Lemma sum_zero (f : nat -> A) d : (forall i, i < d  -> f i == 0) -> (sum f d) == 0. 
  Proof.
    intros.
    induction d.
    unfold sum;reflexivity.
    rewrite sum_S.
    rewrite IHd;auto.
    rewrite H1;auto.
    ring.
  Qed.

  Lemma sum_mult (f : nat -> A) (x : A) d : x * (sum f d) ==  (sum (fun n=> x * f n) d).
  Proof.
    induction d.
    unfold sum;simpl.
    ring.
    rewrite !sum_S.
    ring_simplify.
    rewrite IHd.
    ring.
  Qed.
  Lemma sum_plus (f : nat -> A) (g : nat -> A) d : (sum f d) + (sum g d) ==  (sum (fun n=> f n + g n) d).
  Proof.
    induction d.
    unfold sum;simpl.
    ring.
    rewrite !sum_S.
    rewrite addA.
    rewrite (addC (f d)).
    rewrite <-!addA.
    rewrite IHd.
    ring.
  Qed.
  Lemma sum_single (f : nat -> A) j d : (j < d) -> (forall i, i < d -> (not (i = j)) -> f i == 0) -> (sum f d) == f j. 
  Proof.
    intros.
    induction d; try lia.
    rewrite sum_S.
    assert (j < d \/ j = d)%nat by lia.
    destruct H3.
    rewrite IHd;auto.
    enough (f d == 0) as -> by ring.
    apply H2;lia.
    rewrite H3.
    rewrite sum_zero;[ring|].
    intros.
    apply H2;lia.
  Qed.
End Sums.

Class PartialDifferentialRing  `{R_semiRing : SemiRing}:= {
    pdiff : nat -> A -> A;
    pdiff_plus : forall  d r1 r2, pdiff d (add r1 r2) == add (pdiff d r1) (pdiff d r2);
    pdiff_mult : forall d r1 r2, pdiff  d (mul r1 r2) == add (mul r2 (pdiff d r1)) (mul r1  (pdiff d r2));
    pdiff_comm : forall d1 d2 r, pdiff d1 (pdiff d2 r) == pdiff d2 (pdiff d1 r);
    pdiff_proper :: forall n, Proper (equiv ==> equiv) (pdiff n);
}.

 Lemma pdiff_sum  `{PartialDifferentialRing }  (i : nat) (f : nat -> A) (d : nat) :  pdiff i (sum f (S d)) == sum (fun j => (pdiff i (f j))) (S d).
 Proof.
   induction d.
   unfold sum.
   simpl.
   rewrite !add0.
   reflexivity.
   rewrite !(sum_S _ (S d)).
   rewrite !pdiff_plus.
   rewrite IHd.
   reflexivity.
 Defined.

 Definition nth_derivative  `{PartialDifferentialRing }  (i : nat) (y : A) (n : nat) :  A.
 Proof.
   induction n.
   apply y.
   apply (pdiff i IHn).
 Defined.

 Lemma nth_derivative_S `{PartialDifferentialRing } i (f : A) n : (nth_derivative i f (S n)) == (nth_derivative i (pdiff i f) n).
 Proof.
   induction n.
   simpl;reflexivity.
   simpl.
   rewrite IHn;reflexivity.
 Qed.

  #[global] Instance nth_derivative_proper `{PartialDifferentialRing } i n : Proper (equiv ==> equiv) (fun f => nth_derivative i f n ).
  Proof.
    intros a b eq.
    induction n.
    simpl;rewrite eq;reflexivity.
    simpl.
    rewrite IHn.
    reflexivity.
  Defined.

 Lemma nth_derivative_plus `{PartialDifferentialRing } (f g : A) i n:  (nth_derivative i (f + g) n) == (nth_derivative i f n) + (nth_derivative i g n).
 Proof.
   intros.
   induction n.
   simpl;reflexivity.
   simpl.
   rewrite IHn.
   rewrite pdiff_plus.
   reflexivity.
 Qed.

 Lemma nth_derivative_twice `{PartialDifferentialRing } i (f : A) n1 n2 : (nth_derivative i (nth_derivative i f n1) n2) == (nth_derivative i f (n1+n2)).
 Proof.
   induction n2.
   replace (n1+0)%nat with n1 by lia.
   simpl;reflexivity.
   simpl.
   rewrite IHn2.
   replace (n1 + S n2)%nat with (S n1 + n2)%nat by lia.
   simpl.
   reflexivity.
 Qed.
 Lemma nth_derivative_S_prod1 `{PartialDifferentialRing } (f g : A) i n:  (nth_derivative i (f * g) (S n)) == (nth_derivative i (g * (pdiff i f) ) n) + (nth_derivative i (f* (pdiff i g) ) n).
 Proof.
   rewrite nth_derivative_S.  
   rewrite nth_derivative_proper; try apply (pdiff_mult).
   rewrite nth_derivative_plus.
   reflexivity.
 Qed.
 Definition derive_rec_helper  `{PartialDifferentialRing } {d} (i : nat) (y : A) (n : nat^d) : A.
 Proof.
   revert i.
   induction d;intros.
   apply y.
   destruct (destruct_tuple_cons n) as [hd [tl P]].
   apply (nth_derivative i (IHd tl (S i)) hd).
 Defined.

 Definition derive_rec_helper_next  `{PartialDifferentialRing } {d} (i : nat) (y : A) n0 (n : nat^d) : derive_rec_helper i y (tuple_cons n0 n) = nth_derivative i (derive_rec_helper (S i) y n) n0.
 Proof.
   simpl.
   destruct (destruct_tuple_cons (tuple_cons n0 n)) as [hd [tl p]].
   apply tuple_cons_ext in p.
   destruct p as [-> ->].
   reflexivity.
 Qed.
 Definition derive_rec `{PartialDifferentialRing } {d}  (y : A) (n : nat^d) := derive_rec_helper 0 y n.
  #[global] Instance derive_helper_proper `{PartialDifferentialRing } {d} (i : nat^d) j : Proper (equiv ==> equiv) (fun f => derive_rec_helper j f i ).
  Proof.
    intros a b eq.
    revert j.
    induction d;intros;simpl.
    rewrite eq;reflexivity.
    destruct (destruct_tuple_cons i) as [hd [tl P]].
    apply nth_derivative_proper.
    setoid_rewrite IHd.
    reflexivity.
  Defined.

  #[global] Instance derive_rec_proper `{PartialDifferentialRing } {d} (i : nat^d) : Proper (equiv ==> equiv) (fun f => derive_rec f i ).
  Proof.
    unfold derive_rec.
    apply derive_helper_proper.
  Defined.
 Lemma derive_rec_helper_plus  `{PartialDifferentialRing }  {m} (k : nat^m) a b i :  derive_rec_helper i (a+b) k == derive_rec_helper i a k + derive_rec_helper i b k.
 Proof.
   revert i.
   induction m;intros;simpl;try reflexivity.
    destruct (destruct_tuple_cons k) as [hd [tl P]].
    rewrite <-nth_derivative_plus.
    apply nth_derivative_proper.
    rewrite IHm.
    reflexivity.
  Qed.

 Lemma derive_rec_plus  `{PartialDifferentialRing }  {m} (k : nat^m) a b  :  derive_rec  (a+b) k == derive_rec  a k + derive_rec b k.
 Proof.  apply derive_rec_helper_plus.  Qed.

 Lemma derive_rec_sum  `{PartialDifferentialRing }  {m} (k : nat^m) (f : nat -> A) (d : nat) :  derive_rec (sum f (S d)) k == sum (fun j => (derive_rec (f j) k)) (S d).
 Proof.
   induction d.
   unfold sum.
   simpl.
   rewrite (add0 (derive_rec (f 0%nat) k)).
   apply derive_rec_proper.
   rewrite add0;reflexivity.
   rewrite !(derive_rec_proper _ _ _ (sum_S _ (S d))).
   rewrite (sum_S _ (S d)).
   rewrite derive_rec_plus.
   rewrite IHd.
   reflexivity.
 Defined.

   Lemma nth_deriv_independent `{PartialDifferentialRing }   f i j n : nth_derivative i (pdiff j f) n  == pdiff j (nth_derivative i f n).
   Proof.
     induction n.
     simpl.
     intros;reflexivity.
     simpl.
     intros.
     rewrite IHn.
     pose proof (pdiff_comm  i j (nth_derivative i f n)).
     apply H1.
   Qed.

   Lemma deriv_next_helper `{PartialDifferentialRing }  {m} f  i j (k : nat^m)  : derive_rec_helper i (pdiff j f) k == pdiff j (derive_rec_helper i f k).
   Proof.
     revert f i.
     induction m;intros.
     simpl.
     intros;reflexivity.
     simpl.
     destruct (destruct_tuple_cons k) as [hd [tl P]].
     specialize (IHm tl f (S i)).
     rewrite nth_derivative_proper; try apply IHm.
     rewrite nth_deriv_independent.
     reflexivity.
  Qed.

  Lemma deriv_rec_next `{PartialDifferentialRing }  {m} f  hd (tl : nat^m) : (derive_rec (pdiff 0 f) (tuple_cons hd tl)) == (derive_rec f (tuple_cons (S hd) tl)).
  Proof.
    Opaque SetoidClass.equiv.
    unfold derive_rec;simpl.
    destruct (destruct_tuple_cons (tuple_cons hd tl)) as [hd' [tl' P]].
    destruct (destruct_tuple_cons (tuple_cons (S hd) tl)) as [hd'' [tl'' P']].
    apply tuple_cons_ext in P.
    apply tuple_cons_ext in P'.
    destruct P as [<- <-].
    destruct P' as [<- <-].
    rewrite nth_derivative_proper; try apply deriv_next_helper.
    rewrite nth_derivative_S.
    reflexivity.
    Transparent SetoidClass.equiv.
  Qed.

Notation "D[ i ] f" := (pdiff i f) (at level 4) : algebra_scope.
Notation "Dx[ x ] f" := (derive_rec f x) (at level 4) : algebra_scope.
(* Notation "D[ i ]n f" := (nth_derivative i f n) (at level 4) : algebra_scope. *)


(* Class TotalOrder {A} `{Setoid A}:= { *)
(*       le : A -> A -> Prop; *)
(*       le_proper :: Proper (equiv ==> equiv ==> equiv) le; *)
(*       le_refl : forall x, le x x; *)
(*       le_anti_sym : forall x y, le x y -> le y x -> x == y; *)
(*       le_trans : forall x y z, le x y -> le y z -> le x z; *)
(*       le_total : forall x y, le x y \/ le y x *)
(*  }. *)

(*    Infix "<=" := le. *)

(*   Class TotallyOrderedField `{R_Field :Field} `{R_TotalOrder : TotalOrder (A := A) (H:=H)} := { *)
(*       le_plus_compat : forall x y z, le x y -> le (add x z) (add y z); *)
(*       mul_pos_pos : forall x y, le zero x -> le zero y -> le zero (mul x y) *)
(*     }. *)

(* Section Norm. *)
(*   Context `{A: Type} `{B : Type}. *)
(*   Context `{semiRingA : SemiRing A}. *)
(*   Context `{TotallyOrderedFieldB : TotallyOrderedField B}. *)
(*   Class NormedSemiRing := { *)
(*     norm : A -> B ; *)
(*     norm_proper :: Proper (SetoidClass.equiv ==> SetoidClass.equiv) norm; *)
(*     norm_nonneg : forall x, 0 <= norm x; *)
(*     norm_zero : forall x,  norm x == 0 <-> x == 0; *)
(*     norm_triangle : forall x y, norm (x+y) <= norm x + norm y; *)
(*     norm_mult : forall x y, norm (x*y) <= norm x * norm y; *)
(*   }. *)


(* End Norm. *)

(* Notation "|| x ||" := (norm x) (at level 2). *)


Section RingTheory.
  Context `{A_Ring : Ring }.
  Add Ring ARing : ComSemiRingTheory.
 Fixpoint ntimes (n : nat) x := 
   match n with
    | 0 => 0
    | (S n') => x + ntimes n' x
   end. 
 Lemma ntimes_zero n : ntimes n 0 == 0.
 Proof.
   induction n;simpl;auto;try ring.
   rewrite IHn; ring.
 Qed.
  Lemma ntimes_plus n x y : ntimes n (x+y) == ntimes n x + ntimes n y.
  Proof.
    induction n;simpl;[ring|].
    rewrite IHn;ring.
  Qed.

  Lemma ntimes_mult n x y : ntimes n (x*y) == x * ntimes n y.
  Proof.
    induction n;simpl;[ring|].
    rewrite IHn;ring.
  Qed.

 Lemma ntimes_twice : forall (n :nat) x, (ntimes (2*n) x) == (1+1) * (ntimes n x). 
 Proof.
   intros.
   induction n.
   simpl.
   ring.
   replace (2 * S n)%nat with (S ( S (2 * n))) by lia.
   simpl.
   rewrite IHn.
   ring.
 Qed.

  #[global] Instance ntimes_proper n : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (ntimes n)).
  Proof.
    intros a b H0.
    induction n.
    simpl;ring.
    simpl.
    rewrite IHn, H0.
    ring.
  Defined.

  #[global] Instance npow_proper n : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (fun x => npow x n)).
  Proof.
    intros a b H0.
    induction n.
    simpl;ring.
    simpl.
    rewrite IHn, H0.
    ring.
  Defined.
 Lemma npow_plus x n m: npow x (n+m) == npow x n * npow x m. 
 Proof.
   induction m.
   replace (n+0)%nat with n by lia.
   simpl.
   ring.
   replace (n + S m)%nat with (S (n+m)) by lia.
   simpl npow.
   rewrite IHm.
   ring.
 Qed.

   Lemma npow0 k : npow 0 (S k) == 0.
   Proof.
     induction k.
     simpl.
     ring.
     simpl.
     ring.
  Qed.
  Lemma ComRingTheory  : ring_theory 0 1 add mul minus opp  equiv.
  Proof.

    constructor; intros;unfold minus; try ring;auto.
    apply addI.
  Qed.

  Lemma ring_eq_plus_eq : forall x y x' y', x == x' -> y == y' -> x + y == x' + y'.
  Proof.
    intros x y _ _ <- <-;ring.
  Qed.
  Lemma ring_eq_mult_eq : forall x y x' y', x == x' -> y == y' -> x * y == x' * y'. 
  Proof. intros x y _ _ <- <-;ring. Qed.

  Lemma one_unique x : (forall y, x *y == y) -> x == 1.
  Proof.
    intros.
    rewrite <-(H0 1).
    assert (x * x == x * 1) as <- by (rewrite H0;ring).
    rewrite H0.
    reflexivity.
  Qed.

  Lemma npow_mult x  y n : npow (x*y) n == npow x n * npow y n.
  Proof.
    induction n.
    simpl.
    ring.
    simpl.
    rewrite IHn.
    ring.
  Qed.


 Lemma ntimes_spec `{@EmbedNat A _ _} n x:  ntimes n x == embNat n * x.
 Proof.
   induction n.
   simpl.
   rewrite embNat0;ring.
   simpl.
   rewrite embNat_S.
   rewrite IHn.
   ring.
 Qed.
End RingTheory.

Section VectorRawRing.
  Context `{RawRing}.
  #[global] Instance  VectorRawRing m  :  RawRing (A := A^m).  
  Proof.
  induction m;[constructor;intros; apply nil_tuple|].
  destruct IHm; constructor.
  - apply (tuple_cons 0 zero0).
  - apply (tuple_cons 1 one0).
  - intros.
    destruct (destruct_tuple_cons X) as [hd0 [tl0 _]].
    destruct (destruct_tuple_cons X0) as [hd1 [tl1 _]].
    apply (tuple_cons (hd0+hd1) (add1 tl0 tl1)).
  - intros.
    destruct (destruct_tuple_cons X) as [hd0 [tl0 _]].
    destruct (destruct_tuple_cons X0) as [hd1 [tl1 _]].
    apply (tuple_cons (hd0*hd1) (mul2 tl0 tl1)).
  Defined.

  Lemma vec0_cons {m} : (0 : A^(S m)) = (tuple_cons 0 (0 : A^m)).
  Proof.
  simpl.
  unfold zero.
  destruct VectorRawRing.
  reflexivity.
  Qed.

  Lemma vec1_cons {m} : (1 : A^(S m)) = (tuple_cons 1 (1 : A^m)).
  Proof.
  simpl.
  unfold one.
  destruct VectorRawRing.
  reflexivity.
  Qed.

  Lemma vec0_nth {m} : forall i,  tuple_nth i (0 : A^m) 0 = 0.
  Proof.
  induction m.
  intros.
  simpl.
  destruct i;reflexivity.
  intros.
  rewrite vec0_cons.
  destruct i.
  rewrite tuple_nth_cons_hd.
  reflexivity.
  rewrite tuple_nth_cons_tl.
  apply IHm.
  Qed.

  Lemma vec1_nth {m} : forall i,  (i < m) -> tuple_nth i (1 : A^m) 0 = 1.
  Proof.
  induction m; try lia.
  intros.
  rewrite vec1_cons.
  destruct i.
  rewrite tuple_nth_cons_hd.
  reflexivity.
  rewrite tuple_nth_cons_tl.
  apply IHm;lia.
  Qed.

  Lemma vec_plus_spec {m}  (x y : A^m) : forall i, i < m -> tuple_nth i (x+y) 0 == tuple_nth i x 0 + tuple_nth i y 0.
Proof.
  induction m;try lia.
  intros.
  unfold add at 1.
  simpl.
  destruct VectorRawRing.
  destruct (destruct_tuple_cons x) as [hd [tl0 ->]].
  destruct (destruct_tuple_cons y) as [hd1 [tl1 ->]].
  destruct i.
  rewrite !tuple_nth_cons_hd;reflexivity.
  rewrite !tuple_nth_cons_tl.
  rewrite IHm;try lia.
  reflexivity.
  Qed.

  Lemma vec_mult_spec {m}  (x y : A^m) : forall i, i < m -> tuple_nth i (x*y) 0 == tuple_nth i x 0 * tuple_nth i y 0.
Proof.
  induction m;try lia.
  intros.
  unfold mul at 1.
  simpl.
  destruct VectorRawRing.
  destruct (destruct_tuple_cons x) as [hd [tl0 ->]].
  destruct (destruct_tuple_cons y) as [hd1 [tl1 ->]].
  destruct i.
  rewrite !tuple_nth_cons_hd;reflexivity.
  rewrite !tuple_nth_cons_tl.
  rewrite IHm;try lia.
  reflexivity.
  Qed.

  Definition scalar_mult {m} (x : A) (y : A^m) := tuple_map (mul x) y. 

  Lemma scalar_mult_spec {m} x y : forall i, i<m -> tuple_nth i (@scalar_mult m x y) 0 == x * (tuple_nth i y 0).
  Proof.
    intros.
    unfold scalar_mult.
    rewrite (tuple_map_nth _ _ _ _ 0);auto.
    reflexivity.
  Qed.

End VectorRawRing. 

Section VectorSemiRing.
  Context `{SemiRing}.
  #[global] Instance VectorSemiRing {m} :  SemiRing (A := A^m).  
  Proof.
  constructor;intros;try reflexivity; try apply (tuple_nth_ext' _ _ 0 0);intros.
  - intros a b Heq c d Heq'.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite !vec_plus_spec;auto.
    rewrite Heq, Heq';reflexivity.
  - intros a b Heq c d Heq'.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite !vec_mult_spec;auto.
    rewrite Heq, Heq';reflexivity.
  - rewrite !vec_plus_spec;auto.
    rewrite addA;reflexivity.
  - rewrite !vec_plus_spec;auto.
    rewrite addC;reflexivity.
  - rewrite !vec_plus_spec;auto.
    rewrite vec0_nth.
    rewrite add0;reflexivity.
  - rewrite !vec_mult_spec;auto.
    rewrite mulA;reflexivity.
  - rewrite !vec_mult_spec;auto.
    rewrite mulC;reflexivity.
  - rewrite !vec_mult_spec;auto.
    rewrite vec0_nth.
    rewrite mul0;reflexivity.
  - rewrite !vec_mult_spec;auto.
    rewrite vec1_nth;auto.
    rewrite mul1;reflexivity.
  - rewrite !vec_mult_spec, !vec_plus_spec, !vec_mult_spec;auto.
    rewrite distrL;reflexivity.
  Defined.

  #[global] Instance scalar_mult_proper {m } : Proper (equiv ==> equiv ==> equiv) (scalar_mult (m := m)).
  Proof.
    intros a b Heq c d Heq'.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite !scalar_mult_spec;auto.
    rewrite Heq.
     unfold SetoidClass.equiv in Heq'.
     simpl in Heq'.
     destruct c, d.
     simpl in *.
     rewrite (eqlistA_nth_ext _ _ 0 0) in Heq';auto.
    destruct Heq'.
    rewrite H3;try lia.
    reflexivity.
 Defined.
  Lemma tuple_nth_sum {m} (f: nat -> A^m) d i : i < m -> tuple_nth i (sum f d) 0 == sum (fun x => (tuple_nth i (f x) 0)) d.
Proof.
  intros.
  induction d.
  unfold sum;simpl;rewrite vec0_nth;reflexivity.
  rewrite !sum_S.
  rewrite vec_plus_spec;auto.
  rewrite IHd.
  reflexivity.
  Qed.
End VectorSemiRing.

Notation "x ** y" := (scalar_mult x y) (at level 2).

Section VectorRing.
  Context `{Ring}.
  
  Lemma ntimes_nth {d} (x: A^d) n i: i<d -> ntimes n (tuple_nth i x 0) == tuple_nth i (ntimes n x) 0.
  Proof.
    intros.
    induction n.
    simpl;rewrite vec0_nth;reflexivity.
    simpl.
    rewrite vec_plus_spec;auto.
    rewrite IHn.
    reflexivity.
  Qed.
  #[global] Instance  VectorRing {m}:  Ring (A := A^m).  
  Proof.
   exists  (tuple_map opp).
   apply tuple_map_proper.
   apply H0.
   intros.
   apply (tuple_nth_ext' _ _ 0 0).
   intros.
   rewrite vec_plus_spec;auto.
   rewrite (tuple_map_nth _ _ _ _ 0);auto.
   rewrite addI.
   rewrite vec0_nth.
   reflexivity.
  Defined.
End VectorRing.

Section VectorDiffRing.
  Context `{PartialDifferentialRing}.
  
 Definition pdiff_tuple {m} (i : nat) (y : A^m)  :  A^m := tuple_map (pdiff i) y.

 Lemma pdiff_tuple_nth {m}  (x : A^m) n : forall i, i < m -> tuple_nth i (pdiff_tuple n x) 0 == pdiff n (tuple_nth i x 0).
 Proof.
   intros.
   unfold pdiff_tuple.
   rewrite (tuple_map_nth _ _ _ _ 0);auto.
   reflexivity.
 Defined.

  #[global] Instance  VectorPDiffRing {m} :  PartialDifferentialRing (A := A^m).  
  Proof.
    exists pdiff_tuple;intros; try (apply (tuple_nth_ext' _ _ 0 0);intros;rewrite !pdiff_tuple_nth;auto).
    - rewrite !vec_plus_spec;auto.
      rewrite pdiff_plus, !pdiff_tuple_nth;auto.
      reflexivity.
    - rewrite !vec_mult_spec, !vec_plus_spec, !vec_mult_spec;auto.
      rewrite pdiff_mult, !pdiff_tuple_nth;auto.
      reflexivity.
    - rewrite pdiff_comm.
      reflexivity.
   - apply tuple_map_proper;apply H0.
  Defined.

End VectorDiffRing.

   Lemma tuple_nth_nth_derivative_S `{PartialDifferentialRing } {d} n m (t : A^d) i : (n < d)%nat -> tuple_nth n (nth_derivative i t (S m)) 0 == pdiff i (tuple_nth n (nth_derivative i t m) 0).
   Proof.
     intros.
     simpl.
     rewrite pdiff_tuple_nth;auto.
     reflexivity.
   Defined.

Section Composition.
  Context `{SemiRing}.
End Composition.

Section PartialDiffAlgebra.

Context {A : nat -> Type} `{forall (n : nat), (Setoid (A n)) }  `{forall (n : nat), (RawRing (A:=(A n))) } `{forall (n : nat), (SemiRing (A:=(A n))) }  `{forall (n : nat), (PartialDifferentialRing (A:=(A n))) }.

Class CompositionalDiffAlgebra := {
    composition : forall {m n}, A m -> (A (S n))^m ->  (A (S n));
    comp1 {m} (n : nat) : A m;
    composition_id {m n} i (x : (A (S n))^m) : composition (comp1 i) x == tuple_nth i x 0;
    composition_plus_comp : forall {m n} x y (z :(A (S n))^m) , composition (x+y) z == (composition x z) + (composition y z);
    composition_mult_comp : forall {m n} x y (z :(A (S n))^m) , composition (x*y) z == (composition x z) * (composition y z);
    pdiff_chain : forall {m n d} (x : A m) (y : (A (S n))^m), D[d] (composition x y) == (sum (fun i => (pdiff d (tuple_nth i y zero)) * composition (pdiff i x) y) m);
    composition_proper {m n}:: Proper (equiv ==> equiv ==> equiv) (@composition m n);
    diff_id_same {d} i : i<d ->  D[i] (comp1 (m:=d) i) == 1;
    diff_id_distinct {d} i j : (i <> j)%nat -> D[i] (comp1 (m:=d) j) == 0
  }.



End PartialDiffAlgebra.


Infix "\o1" := composition (at level 2).

Section PartialDiffAlgebraTheory.

Context `{CompositionalDiffAlgebra} .
Lemma composition_sum_comp {m n} (f : nat -> A m) (g : (A (S n))^m) i : (sum f (S i)) \o1 g == (sum (fun i => (f i) \o1 g) (S i)). 
Proof.
  induction i.
  unfold sum; simpl.
  unfold sum;simpl;rewrite !add0;reflexivity.
  rewrite !(sum_S _ (S i)).
  rewrite composition_plus_comp.
  rewrite IHi.
  reflexivity.
Qed.
  Definition multi_composition {n m r} (ps : (A n)^r) (qs : (A (S m))^n) : (A (S m))^r.
Proof.
  induction r.
  apply nil_tuple.
  destruct (destruct_tuple ps) as [hd [tl P]].
  apply (tuple_cons (hd \o1 qs) (IHr tl)).
Defined.


 Lemma tuple_nth_multicomposition {n m r} i d (ps : (A n)^r) (qs : (A (S m))^n) : (i < r)%nat -> tuple_nth i (multi_composition ps qs) d = (tuple_nth i ps 0) \o1 qs.
 Proof.
   revert i.
  induction r;intros; try lia.
  simpl.
  destruct (destruct_tuple ps) as [hd [tl P]].
  destruct ps.
  destruct i.
  rewrite tuple_nth_cons_hd.
  simpl in *.
  rewrite P;auto.
  rewrite tuple_nth_cons_tl.
  rewrite IHr; try lia.
  simpl in *.
  rewrite P.
  destruct tl; simpl;auto.
 Qed.


Lemma multi_composition_sum_comp {m n r} (f : nat -> (A n)^r) (g : (A (S m))^n) i : multi_composition (sum f (S i)) g == (sum (fun i => (multi_composition (f i)  g)) (S i)). 
Proof.
  apply (tuple_nth_ext' _ _ 0 0).
  intros.
  rewrite tuple_nth_multicomposition;auto.
  rewrite !tuple_nth_sum;auto.
  rewrite composition_sum_comp.
  apply sum_ext.
  intros.
  rewrite tuple_nth_multicomposition;auto.
  reflexivity.
Qed.
 Lemma multicomposition_chain_rule {n m r} (f : (A n)^r) (g : (A (S m))^n) i : D[i] (multi_composition f g) == (sum (fun k => (D[i] (tuple_nth k g zero)) ** (multi_composition (D[k] f) g)) n).
 Proof.
   intros.
   apply (tuple_nth_ext' _ _ 0 0).
   intros.
   simpl.
   rewrite pdiff_tuple_nth;auto.
   rewrite tuple_nth_multicomposition;auto.
   rewrite pdiff_chain.
   rewrite tuple_nth_sum;auto.
   apply sum_ext; intros.
   rewrite scalar_mult_spec;auto.
   rewrite tuple_nth_multicomposition;auto.
   rewrite pdiff_tuple_nth;auto.
   reflexivity.
 Qed.

  Definition id (d : nat) : (A d)^d := proj1_sig (seq_to_tuple (comp1 (m:=d)) d (def:=0)).

  Lemma id_nth {d} i: i < d -> tuple_nth i (id d) 0 = comp1 i.  
  Proof.
    intros.
    unfold id.
    destruct (seq_to_tuple (comp1 (m:=d)) d (def := 0)).
    simpl.
    rewrite e;auto;reflexivity.
  Qed.

  Lemma id_spec {d} (f : (A 1)^d) : (multi_composition (id d) f) == f.
  Proof.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite tuple_nth_multicomposition;auto.
    rewrite id_nth;auto.
    rewrite composition_id.
    reflexivity.
  Qed.

End PartialDiffAlgebraTheory.


Infix "\o" := multi_composition (at level 2).
  Class Sn_invertible `{SemiRing} := {
      inv_Sn  (n : nat) : A; 
      inv_Sn_spec : forall n, (ntimes (S n) 1) * inv_Sn n == 1
  }.
