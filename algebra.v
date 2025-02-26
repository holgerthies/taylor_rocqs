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
    norm_mult : forall x y, norm (x*y) = norm x * norm y;
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


  #[global] Instance ntimes_proper n : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (ntimes n)).
  Proof.
    intros a b H0.
    induction n.
    simpl;ring.
    simpl.
    rewrite IHn, H0.
    ring.
  Defined.
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

Section Evaluation.
  Context {A: nat -> Type} `{forall (n : nat), (Setoid (A n)) }.
  Class HasEvaluation := {
      in_domain {n} (f : A n) (x : @tuple n (A 0)):  Prop;
      eval {n} (f : A n) x (P : in_domain f x) :  (A 0);
      in_domain_proper {n} :: Proper (equiv ==> equiv ==> equiv) (@in_domain n);
      eval_proper {n} : forall f1 f2 x1 x2 P1 P2, f1 == f2 -> x1 == x2 -> @eval n f1 x1 P1 == @eval n f2 x2 P2;
    }.

End Evaluation.
Section CInfinity.

  Context `{CompositionalDiffAlgebra} `{HasEvaluation (A := A) (H := H)}. 
  Definition in_domaint  {m n :nat} (f : @tuple m (A n)) (x : @tuple n (A 0)) := forall i, (i < m) -> in_domain (tuple_nth i f 0) x.

  Lemma in_domaint_cons {m n :nat} (hd : A n) (tl : @tuple m (A n)) (x : @tuple n (A 0)) : in_domaint (tuple_cons hd tl) x <-> (in_domain hd x) /\ (in_domaint tl x).
  Proof.
    split.
    - intros.
      rewrite <-(tuple_nth_cons_hd hd tl 0).
      split.
      apply H5;lia.

      unfold in_domaint.
      intros.
      rewrite <-(tuple_nth_cons_tl i hd tl 0).
      apply H5;lia.
   - intros [].
     unfold in_domaint;intros.
     destruct i.
     rewrite tuple_nth_cons_hd;auto.
     rewrite tuple_nth_cons_tl;auto.
     apply H6;lia.
  Qed.

  Lemma in_domaint_cons_impl {m n :nat} (hd : A n) (tl : @tuple m (A n)) f (x : @tuple n (A 0)) : f = tuple_cons hd tl -> in_domaint f x -> (in_domain hd x) /\ (in_domaint tl x).
  Proof. intros Hf; rewrite Hf; apply in_domaint_cons. Qed.

  Definition evalt {m n : nat} (f : @tuple m (A n)) (x : @tuple n (A 0)) (P : in_domaint f x) : (@tuple m (A 0)).
  Proof.
    induction m.
    apply nil_tuple.
    destruct (destruct_tuple_cons f) as [hd [tl P']].
    apply (tuple_cons (eval _ _ (proj1 (in_domaint_cons_impl _ _ _ _ P' P))) (IHm _ (proj2 (in_domaint_cons_impl _ _ _ _ P' P)))).
  Defined.

  Local Notation "[ f ] ( x ; p )" := (evalt f x p) (at level 10).
  Local Notation "x \in_dom f" := (in_domaint f x) (at level 10).
  Local Notation "A [ n ; m ]" := (@tuple n (A m)) (at level 10).

  Lemma evalt_dom_proof_irrelev m n (f : @tuple m (A n)) x P1 P2 : [f](x;P1) == [f](x;P2).
  Proof.
    replace P1 with P2;try reflexivity.
    apply proof_irrelevance.
  Qed.

   Lemma evalt_spec {m n} {f : @tuple m (A n)} {x : @tuple n (A 0)} (P : in_domaint f x)  i (lt : i < m): tuple_nth i (evalt _ _ P) 0 == eval _ _ (P i lt).  
  Proof.
    generalize dependent i.
    induction m;intros;try lia.
    simpl.
    destruct (destruct_tuple_cons f) as [hd [tl P']].
    simpl.
    destruct i.
    - rewrite !tuple_nth_cons_hd.
      apply eval_proper;try reflexivity.
      rewrite P'.
      rewrite tuple_nth_cons_hd;reflexivity.
    - rewrite !tuple_nth_cons_tl.
      assert (i < m) by lia.
      rewrite (IHm _ _ _ H5).
      apply eval_proper; try reflexivity.
      rewrite P'.
      rewrite tuple_nth_cons_tl;reflexivity.
    Qed.
  (* Context `{normK : (NormedSemiRing (A 0) (A 0) (H := (H 0)) (H0 := (H 0)) (R_rawRing := (H0 0%nat)) (R_rawRing0 := (H0 0%nat)) (R_TotalOrder := R_TotalOrder))} *)
  Class AbstractFunction := {
      const {m} (c : A 0): A m;
      const_dom {m} : forall c x, in_domain (const (m := m) c) x;
      const_eval {m} : forall c x, eval (const (m := m) c) x (const_dom (m:=m) c x ) == c;
      dom_id {m} (n : nat): forall x, in_domain (comp1 (m :=m) n) x; 
      eval_id {m} n : forall x H, (n < m) -> (eval (comp1 (m := m) n) x H) == tuple_nth n x 0;
      dom_plus {n} (f g : A n) x : in_domain f x -> in_domain g x -> in_domain (f+g) x;
      dom_mult {n} (f g : A n) x : in_domain f x -> in_domain g x -> in_domain (f*g) x;
      dom_diff {n} (f : A n) x i : in_domain f x -> in_domain (D[i] f) x;
      dom_composition {r m n} (f : A[r;n]) (g : A[n;(S m)]) x P gx : [g](x;P) == gx -> (gx \in_dom f) -> (x \in_dom (f \o g));
      eval_composition_compat {r m n : nat} (f : A[r;n]) (g : A[n;(S m)]) x (Px : (x \in_dom g)) (Py : ([g](x;Px) \in_dom f)) (Pz : x \in_dom (f \o g)) : [f \o g](x;Pz)  == [f]([g](x;Px);Py)
    }.

End CInfinity.
  Notation "x \in_dom f" := (in_domaint f x) (at level 5) : fun_scope.
  Notation " f @ ( x ; p )" := (evalt f x p) (at level 5):fun_scope.  
Section AbstractFunctionTheory.

  Context `{AbstractFunction}.
  Local Open Scope fun_scope.
  Lemma dom_sum {n} (fs : nat -> A n) x d : (forall i, (i <= d)%nat -> in_domain (fs i) x) -> in_domain (sum fs (S d)) x. 
  Proof.
    intros.
    induction d.
    - unfold sum;simpl.
      rewrite add0.
      apply H6;lia.
   - rewrite sum_S.
     apply dom_plus;auto.
  Qed.

   #[global] Instance in_domt_proper {n m} :Proper (equiv ==> equiv ==> equiv) (in_domaint (n :=n) (m := m)).
    Proof.
    intros a b eq0 c d eq1.
    unfold in_domaint.
    split;intros.
    rewrite <-eq0 ,<-eq1;apply H6;auto.
    rewrite eq0 ,eq1;apply H6;auto.
   Defined.
    Lemma meval_proper {n m} : forall (f1 : (A n)^m)  f2 x1 x2 P1 P2, f1 == f2 -> x1 == x2 -> (f1 @ (x1;P1)) == f2 @ (x2;P2).  
    Proof.
      intros.
      apply (tuple_nth_ext' _ _ 0 0).
      intros.
      rewrite !(evalt_spec _ _ H8).
      apply eval_proper;auto.
      rewrite H6;reflexivity.
   Qed.

    Definition scalar_multf {n} (x : A 0) (f : A n) := const x * f.
    Definition scalar_addf {n} (x : A 0) (f : A n) := const x + f.

End AbstractFunctionTheory.

Infix "[*]" := scalar_multf (at level 2).
Infix "[+]" := scalar_addf (at level 2).


(* Section Interval. *)
(*   Context `{K : Type}. *)
(*   Context `{ofieldK : TotallyOrderedField K}. *)
(*   Context `{normK : (NormedSemiRing K K (H := H) (H0 := H) (R_rawRing := R_rawRing) (R_rawRing0 := R_rawRing) (R_TotalOrder := R_TotalOrder))}. *)

(*   Add Ring TRing: ComRingTheory. *)
(*   Definition cinterval := (K * K)%type. *)
(*   Definition in_cinterval x i := (normK.(norm) (x-(fst i))) <= snd i. *)
(*   Definition in_cintervalt {n} (x : @tuple n K) (i : @tuple n cinterval) : Prop. *)
(*   Proof. *)
(*     induction n. *)
(*     apply True. *)
(*     destruct (destruct_tuple x) as [x0 [xt P1]]. *)
(*     destruct (destruct_tuple i) as [i0 [it P2]]. *)
(*     apply ((in_cinterval x0 i0) /\ (IHn xt it)). *)
(*   Defined. *)
(* End Interval. *)
  (* Class differentialRing `{R_semiRing : comSemiRing} := *)
  (*   { *)
  (*   derivation : A -> A; *)
  (*   derivation_plus : forall r1 r2, derivation (add r1 r2) == add (derivation r1) (derivation r2); *)
  (*   derivation_mult : forall r1 r2, derivation (mul r1 r2) == add (mul r2 (derivation r1)) (mul r1  (derivation r2)); *)
  (*   derivation_proper :> Proper (equiv ==> equiv) derivation; *)
  (*   }. *)

(* Section DifferentialAlgebra. *)
(*   Context {K V : Type} . *)
  
(*   Class differentialAlgebra `{K_field : Field (A := K)} `{R_differentialRing : (differentialRing (A := V))} := { *)
(*       smult : K -> V -> V; *)
(*       smult1 : forall v, smult one v == v; *)
(*       smult_proper :> Proper (equiv ==> equiv ==> equiv) smult; *)
(*       smult_plus_distr : forall a u v, smult a (u+v) == smult a u + smult a v; *)
(*       splus_mult_dist : forall a b v, smult (a+b) v == smult a v + smult b v; *)
(*       smult_mult_compat : forall a b v, smult a (smult b v) == smult (a*b) v *)
(*     }.  *)

(* End DifferentialAlgebra. *)

(* Local Infix "[*]" := smult (at level 2, left associativity). *)

(* Section DifferentialAlgebraTheory. *)
(*   Context {K V : Type}  `{DA : differentialAlgebra (K:=K) (V := V)}. *)
(*   Add Ring RRing: (ComSemiRingTheory (A:=V)). *)
(*   Add Ring RRing: (ComRingTheory (A:=K)). *)
(*   Lemma smult_zero  a : a [*] 0 == 0. *)
(*   Proof. *)
(*     enough (0 [*] 0 == 0). *)
(*     rewrite <-H1. *)
(*     rewrite smult_mult_compat. *)
(*     setoid_replace (a*0) with (0 : K) by ring;auto. *)
(*     reflexivity. *)
(*     pose proof (smult1 0). *)
(*     rewrite <- H1 at 2. *)
(*     setoid_replace (1 : K) with (0+1 : K) by ring. *)
(*     rewrite splus_mult_dist. *)
(*     rewrite smult1. *)
(*     rewrite add0;reflexivity. *)
(*   Qed. *)

(* End DifferentialAlgebraTheory. *)
