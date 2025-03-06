Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import Setoid.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Classes.SetoidClass.
Require Import Classical.
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

Class Field `{A_Ring : Ring} := {
      inv : forall {x}, (not (x == zero)) -> A;
      mulI : forall x (p : (not (x == zero))), mul (inv p) x == one;
      distinct_0_1 : (not (zero == one))
    }.


Class PartialDifferentialRing  `{R_semiRing : SemiRing}:= {
    pdiff : nat -> A -> A;
    pdiff_plus : forall  d r1 r2, pdiff d (add r1 r2) == add (pdiff d r1) (pdiff d r2);
    pdiff_mult : forall d r1 r2, pdiff  d (mul r1 r2) == add (mul r2 (pdiff d r1)) (mul r1  (pdiff d r2));
    pdiff_comm : forall d1 d2 r, pdiff d1 (pdiff d2 r) == pdiff d2 (pdiff d1 r);
    pdiff_proper :: forall n, Proper (equiv ==> equiv) (pdiff n);
}.

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
Notation "D[ i ] f" := (pdiff i f) (at level 4) : algebra_scope.
(* Notation "D[ i ]n f" := (nth_derivative i f n) (at level 4) : algebra_scope. *)


Class TotalOrder {A} `{Setoid A}:= {
      le : A -> A -> Prop;
      le_proper :: Proper (equiv ==> equiv ==> equiv) le;
      le_refl : forall x, le x x;
      le_anti_sym : forall x y, le x y -> le y x -> x == y;
      le_trans : forall x y z, le x y -> le y z -> le x z;
      le_total : forall x y, le x y \/ le y x
 }.

   Infix "<=" := le.

  Class TotallyOrderedField `{R_Field :Field} `{R_TotalOrder : TotalOrder (A := A) (H:=H)} := {
      le_plus_compat : forall x y z, le x y -> le (add x z) (add y z);
      mul_pos_pos : forall x y, le zero x -> le zero y -> le zero (mul x y)
    }.

Section Norm.
  Context `{A: Type} `{B : Type}.
  Context `{semiRingA : SemiRing A}.
  Context `{TotallyOrderedFieldB : TotallyOrderedField B}.
  Class NormedSemiRing := {
    norm : A -> B ;
    norm_proper :: Proper (SetoidClass.equiv ==> SetoidClass.equiv) norm;
    norm_nonneg : forall x, 0 <= norm x;
    norm_zero : forall x,  norm x == 0 <-> x == 0;
    norm_triangle : forall x y, norm (x+y) <= norm x + norm y;
    norm_mult : forall x y, norm (x*y) <= norm x * norm y;
  }.


End Norm.

Notation "|| x ||" := (norm x) (at level 2).

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

  Lemma sum_S_fun (f : nat -> A) n : (sum f ( S n)) == f 0%nat + (sum (fun n => (f (S n))) n).
  Proof.
    unfold sum.
    simpl.
    ring_simplify.
    enough (map f (seq 1 n) = map (fun n => f (S n)) (seq 0 n)) as -> by reflexivity.
    rewrite <- seq_shift.
    rewrite map_map;auto.
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
     rewrite IHd;[| intros; apply H0;  lia].
     rewrite H0;try lia;reflexivity.
   Qed.
End RingTheory.


Section OrderTheory.
Context {A : Type} `{TotallyOrderedField A}.
Add Ring TRing: ComRingTheory.

Lemma le_le_plus_le a b c d: a <= c -> b <= d -> a + b <= c + d.
Proof.
  intros.
  apply (le_trans _ _ _ (le_plus_compat _ _ _ H1)).
  rewrite !(addC c).
  apply le_plus_compat;auto.
Qed.
Lemma le_iff_le0 (x y : A) : (x <= y) <-> (0 <= (y - x)).
Proof.
  split;intros.
  setoid_replace 0 with (x-x) by ring.
  apply le_plus_compat;auto.
  setoid_replace x with (0 + x ) by ring.
  setoid_replace y with ((y-x)+x) by ring.
  apply le_plus_compat;auto.
Qed.

Lemma mul_le_compat_pos {r r1 r2} : 0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros.
  apply le_iff_le0.
  setoid_replace (r*r2 - r*r1) with (r * (r2 - r1)) by ring.
  apply mul_pos_pos;auto.
  rewrite <-le_iff_le0;auto.
Qed.

Lemma mul_le_le_compat_pos {r1 r2 x y} : 0 <= r1 -> (0 <= x) -> r1 <= r2 -> x <= y -> r1 * x <= r2 * y.
Proof.
  intros.
  apply (le_trans _ _ _ (mul_le_compat_pos H1 H4 )).
  rewrite !(mulC _ y).
  apply mul_le_compat_pos;auto.
  apply (le_trans _ _ _ H2);auto.
Qed.
Lemma le_0_1 : 0 <= 1.
Proof.
  destruct (le_total 0 1);auto.
  setoid_replace 1 with (opp 1 * opp 1) by ring.
  setoid_replace 0 with ((opp 1) * 0) by ring.
  enough (0 <= (opp 1))by (apply mul_le_compat_pos;auto).
  setoid_replace (opp 1) with (0 + (opp 1)) by ring.
  setoid_replace 0 with (1 + (opp 1)) at 1 by ring.
  apply le_plus_compat;auto.
Qed.

Lemma le_0_n n : 0 <= (ntimes n 1).
Proof.
  induction n.
  simpl;apply R_TotalOrder.
  simpl.
  setoid_replace 0 with (0 + 0) by ring.
  apply le_le_plus_le; [|apply IHn].
  apply le_0_1.
Qed.

 Lemma lt_0_2 : 0 <= (1+1).
 Proof.
   setoid_replace (1+1) with (ntimes 2 1).
   apply le_0_n.
   simpl.
   ring.
 Qed.
Lemma char0 : forall n, not ((ntimes (S n) 1) == 0).
Proof.
  intros.
  induction n;simpl;intros Hn.
  apply distinct_0_1;rewrite <-Hn; ring.
  contradict IHn.
  enough (ntimes (S n) 1 <= 0)by (apply le_anti_sym;auto;apply le_0_n).
  rewrite <- Hn.
  setoid_replace (ntimes (S n) 1) with (0 + ntimes (S n) 1) at 1 by ring.
  apply le_plus_compat.
  apply le_0_1.
Defined.
End OrderTheory.

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


Section Composition.
  Context `{SemiRing}.
End Composition.

Section PartialDiffAlgebra.

Context {A : nat -> Type} `{forall (n : nat), (Setoid (A n)) }  `{forall (n : nat), (RawRing (A:=(A n))) } `{forall (n : nat), (SemiRing (A:=(A n))) }  `{forall (n : nat), (PartialDifferentialRing (A:=(A n))) }.

Class CompositionalDiffAlgebra := {
    composition : forall {m n}, A m -> (A (S n))^m ->  (A (S n));
    comp1 {m} (n : nat) : A m;
    composition_proper {m n}:: Proper (equiv ==> equiv ==> equiv) (@composition m n);
    composition_id {m n} i (x : @tuple m (A (S n))) : composition (comp1 i) x == tuple_nth i x 0;
    composition_plus_comp : forall {m n} x y (z :@tuple m (A (S n))) , composition (x+y) z == (composition x z) + (composition y z);
    composition_mult_comp : forall {m n} x y (z :@tuple m (A (S n))) , composition (x*y) z == (composition x z) * (composition y z);
    pdiff_chain : forall {m n d} (x : A m) (y : @tuple m (A (S n))), pdiff d (composition x y) == (sum (fun i => (pdiff d (tuple_nth i y zero)) * composition (pdiff i x) y) m)
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
End PartialDiffAlgebraTheory.


Infix "\o" := multi_composition (at level 2).

