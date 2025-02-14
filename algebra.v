Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import Setoid.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Classes.SetoidClass.
 Definition tuple n {A} := {t : list A | length t = n}.
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
Section AlgebraicStructures.
  Context {A : Type} `{Setoid A}.
  Class RawRing := {
      zero : A;
      one : A;
      add : A -> A -> A;
      mul : A -> A -> A;

    }.

  Definition sum `{A_Rawring : RawRing } (f : nat -> A) n := (fold_right add zero (map f (seq 0 n))).
  Class comSemiRing `{R_rawRing : RawRing}   := {

      add_proper :> Proper (equiv ==> equiv ==> equiv) add;
      mul_proper :> Proper (equiv ==> equiv ==> equiv) mul;
      zero_proper :> equiv zero zero;
      one_proper :> equiv one one;
      addA : forall a b c, add (add a b) c == add a (add b c);
      addC : forall a b, add a b == add b a;
      add0 : forall a, add a zero == a; 
      mulA: forall a b c, mul (mul a b) c == mul a (mul b c);
      mulC : forall a b, mul a b == mul b a;
      mul0 : forall a, mul a zero == zero; 
      mul1 : forall a, mul a one == a; 
      distrL : forall a b c, mul a (add b c) == add (mul a b) (mul a c)
    }.

  Class comRing `{R_semiRing : comSemiRing} := {
      opp : A -> A;
      opp_proper :> Proper (equiv ==> equiv) opp;
      addI : forall a, add a (opp a) == zero;
  }.

  Class Field `{R_Ring : comRing} := {
      inv : forall {x}, (not (x == zero)) -> A;
      mulI : forall x (p : (not (x == zero))), mul (inv p) x == one;
      distinct_0_1 : (not (zero == one))
    }.

  Class differentialRing `{R_semiRing : comSemiRing} :=
    {
    derivation : A -> A;
    derivation_plus : forall r1 r2, derivation (add r1 r2) == add (derivation r1) (derivation r2);
    derivation_mult : forall r1 r2, derivation (mul r1 r2) == add (mul r2 (derivation r1)) (mul r1  (derivation r2));
    derivation_proper :> Proper (equiv ==> equiv) derivation;
    }.

Class PartialDifferentialRing  `{R_semiRing : comSemiRing}:= {
    pdiff : nat -> A -> A;
    pdiff_plus : forall  d r1 r2, pdiff d (add r1 r2) == add (pdiff d r1) (pdiff d r2);
    pdiff_mult : forall d r1 r2, pdiff  d (mul r1 r2) == add (mul r2 (pdiff d r1)) (mul r1  (pdiff d r2));
    pdiff_comm : forall d1 d2 r, pdiff d1 (pdiff d2 r) == pdiff d2 (pdiff d1 r);
    pdiff_proper :> forall n, Proper (equiv ==> equiv) (pdiff n);
  }.

  Class TotalOrder := {
      le : A -> A -> Prop;
      le_proper :> Proper (equiv ==> equiv ==> equiv) le;
      le_refl : forall x, le x x;
      le_anti_sym : forall x y, le x y -> le y x -> x == y;
      le_trans : forall x y z, le x y -> le y z -> le x z;
      le_total : forall x y, le x y \/ le y x
    }.
    
  Class TotallyOrderedField `{R_Field : Field} `{R_TotalOrder : TotalOrder} := {
      le_plus_compat : forall x y z, le x y -> le (add x z) (add y z);
      mul_pos_pos : forall x y, le zero x -> le zero y -> le zero (mul x y)
    }.

  Definition minus  `{R_comRing : comRing} (x y : A)  := add x (opp y).
  #[global] Instance minus_proper `{R_comRing : comRing} : Proper (equiv ==> equiv ==> equiv) minus.
  Proof.
    intros a b P0 c d P1.
    unfold minus.
    rewrite P0,P1;reflexivity.
  Defined.
End AlgebraicStructures. 

Infix "+" := add.
Infix "*" := mul.
Notation "- x" := (opp  x). 
Infix "-" := minus.
Infix "<=" := le.
Notation "0" := zero.
Notation "1" := one.
Notation "p ^'" := (derivation p) (at level 2, left associativity).
Section Norm.
  Context `{A: Type} `{B : Type}.
  Context `{semiRingA : comSemiRing A}.
  Context `{TotallyOrderedFieldB : TotallyOrderedField B}.
  Class NormedSemiRing := {
    norm : A -> B ;
    norm_proper :> Proper (SetoidClass.equiv ==> SetoidClass.equiv) norm;
    norm_nonneg : forall x, 0 <= norm x;
    norm_zero : forall x,  norm x == 0 <-> x == 0;
    norm_triangle : forall x y, norm (x+y) <= norm x + norm y;
    norm_mult : forall x y, norm (x*y) = norm x * norm y;
  }.


End Norm.
Section DifferentialAlgebra.
  Context {K V : Type} .
  
  Class differentialAlgebra `{K_field : Field (A := K)} `{R_differentialRing : (differentialRing (A := V))} := {
      smult : K -> V -> V;
      smult1 : forall v, smult one v == v;
      smult_proper :> Proper (equiv ==> equiv ==> equiv) smult;
      smult_plus_distr : forall a u v, smult a (u+v) == smult a u + smult a v;
      splus_mult_dist : forall a b v, smult (a+b) v == smult a v + smult b v;
      smult_mult_compat : forall a b v, smult a (smult b v) == smult (a*b) v
    }. 

End DifferentialAlgebra.

Infix "[*]" := smult (at level 2, left associativity).


  Lemma ComSemiRingTheory `{A_comSemiRing : comSemiRing } : semi_ring_theory 0 1 add mul equiv.
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
  Context `{A_Ring : comRing }.
  Add Ring ARing : ComSemiRingTheory.

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

Section DifferentialAlgebraTheory.
  Context {K V : Type}  `{DA : differentialAlgebra (K:=K) (V := V)}.
  Add Ring RRing: (ComSemiRingTheory (A:=V)).
  Add Ring RRing: (ComRingTheory (A:=K)).
  Lemma smult_zero  a : a [*] 0 == 0.
  Proof.
    enough (0 [*] 0 == 0).
    rewrite <-H1.
    rewrite smult_mult_compat.
    setoid_replace (a*0) with (0 : K) by ring;auto.
    reflexivity.
    pose proof (smult1 0).
    rewrite <- H1 at 2.
    setoid_replace (1 : K) with (0+1 : K) by ring.
    rewrite splus_mult_dist.
    rewrite smult1.
    rewrite add0;reflexivity.
  Qed.

End DifferentialAlgebraTheory.

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
Lemma le_iff_le0 x y: x <= y <-> 0 <= (y-x). 
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
End OrderTheory.

Section PartialDiffAlgebra.

Context {A : nat -> Type} `{forall (n : nat), (Setoid (A n)) }  `{forall (n : nat), (RawRing (A:=(A n))) } `{forall (n : nat), (comSemiRing (A:=(A n))) } `{forall (n : nat), (PartialDifferentialRing (A:=(A n))) }.

  
Class CompositionalDiffAlgebra := {
    composition : forall {m n}, A m -> @tuple m (A n) -> A n;
    composition_proper {m n}:> Proper (equiv ==> equiv ==> equiv) (@composition m n);
    comp1 {m} (n : nat) : A m;
    composition_id {m n} i (x : @tuple m (A n)) : composition (comp1 i) x == tuple_nth i x 0;
    composition_plus_comp : forall {m n} x y (z :@tuple m (A n)) , composition (x+y) z == (composition x z) + (composition y z);
    composition_mult_comp : forall {m n} x y (z :@tuple m (A n)) , composition (x*y) z == (composition x z) * (composition y z);
    pdiff_chain : forall {m n d} (x : A m) (y : @tuple m (A n)), pdiff d (composition x y) == (sum (fun i => (pdiff d (tuple_nth i y zero)) * composition (pdiff i x) y) m)
  }.

End PartialDiffAlgebra.

Notation "D[ i ] f" := (pdiff i f) (at level 50, left associativity).

Infix "\o" := composition (at level 2).

Section PartialDiffAlgebraTheory.

Context `{CompositionalDiffAlgebra} .
Lemma composition_sum_comp {m n} (f : nat -> A m) (g : @tuple m (A n)) i : (sum f (S i)) \o g == (sum (fun i => (f i) \o g) (S i)). 
Proof.
  induction i.
  unfold sum; simpl.
  unfold sum;simpl;rewrite !add0;reflexivity.
  rewrite !(sum_S _ (S i)).
  rewrite composition_plus_comp.
  rewrite IHi.
  reflexivity.
Qed.
End PartialDiffAlgebraTheory.
