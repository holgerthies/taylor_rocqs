Require Import Coq.QArith.QArith.
From Coq Require Import Psatz.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
From Coq Require Import Setoid.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Classes.SetoidClass.
From Coq Require Import Classical.
Require Import tuple algebra.
Declare Scope algebra_scope.
Open Scope algebra_scope.
Declare Scope fun_scope.


Class PartialOrder {A} `{Setoid A}:= {
      le : A -> A -> Prop;
      le_proper :: Proper (equiv ==> equiv ==> equiv) le;
      le_refl : forall x, le x x;
      le_anti_sym : forall x y, le x y -> le y x -> x == y;
      le_trans : forall x y z, le x y -> le y z -> le x z;
 }.

 Infix "<=" := le.
  #[global] Instance Q_setoid : @Setoid Q.
  Proof.
    exists Qeq.
    apply Q_Setoid.
  Defined.

Class QEmbedding `{R_Ring :Ring} `{R_ordered : @PartialOrder A _} := {
  embedQ : Q -> A ;
  embedQ_proper :: (Proper (SetoidClass.equiv ==> SetoidClass.equiv) embedQ);
  Q0     : embedQ 0%Q == zero ;
  Q1     : embedQ 1%Q == one ;
  Qplus  : forall x y, embedQ (x + y)%Q == add (embedQ x) (embedQ y) ;
  Qmult  : forall x y, embedQ(x * y)%Q == mul (embedQ x) (embedQ y) ;
  Qneg   : forall x, embedQ (- x)%Q == opp (embedQ x) ;
  Qinj   : forall x y, embedQ x == embedQ y -> (x == y)%Q;
  Qle : forall x y, (x <= y)%Q -> embedQ x <= embedQ y 
}.

Class HasAbs `{R_Ring :Ring} `{R_ordered : @PartialOrder A _} := {
    abs : A -> A;
    abs_proper :: (Proper (SetoidClass.equiv ==> SetoidClass.equiv) abs);
    abs_pos : forall x, 0 <= x -> abs x == x;
    abs_neg : forall x, x <= 0 -> abs x == -x;
    abs_mult a b: abs (a * b) == abs a * abs b;
    abs_triangle : forall x y, abs (x+y) <= abs x + abs y;
    abs_nonneg a: 0 <= abs a; 
    abs_zero : forall x,  abs x == 0 <-> x == 0;

 }.

Class ArchimedeanField `{emb : QEmbedding} `{hasAbs : @HasAbs A _ _ _ _ _ }     := {
       distinct_0_1 : not (0 == 1);
       le_plus_compat : forall x y z, le x y -> le (add x z) (add y z);
       mul_pos_pos : forall x y, le zero x -> le zero y -> le zero (mul x y); 
      upper : forall (x : A), {n : nat | x <= ntimes n 1}
     }.


Section OrderTheory.
Context  `{ArchimedeanField }.
Add Ring TRing: ComRingTheory.

#[global] Instance ArchimedeanFieldNatEmb : EmbedNat (A := A).
Proof.
  exists (fun n => (embedQ (inject_Z (Z.of_nat n)))).
  simpl;exact Q0.
  intros.
  rewrite Nat2Z.inj_succ.
  unfold Z.succ;rewrite inject_Z_plus.
  rewrite Qplus, Q1;ring.
Defined.

#[global] Instance ArchimedeanInvSn : Sn_invertible (A := A).
Proof.
  exists (fun n => (embedQ (1 # (Pos.of_succ_nat n)))).
  intros.
  rewrite ntimes_spec.
  simpl;ring_simplify.
  rewrite <-Qmult, <-Q1.
  unfold inject_Z.
  apply embedQ_proper.
  rewrite <-Qmult_frac_r.
  simpl.
  replace (Z.pos (Pos.of_succ_nat n)) with (1 * Z.pos (Pos.of_succ_nat n))%Z by lia.
  rewrite Qreduce_den_inject_Z_r.
  unfold inject_Z;reflexivity.
Defined.
Lemma embedQ_inv : forall x, (not (x == 0)%Q) -> embedQ (/ x)%Q * embedQ x == 1. 
Proof.
  intros.
  rewrite <-Qmult.
  rewrite Qmult_comm.
  rewrite Qmult_inv_r;auto.
  apply Q1.
Qed.
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
   rewrite <-Q0, <-Q1.
   apply Qle;auto.
   lra.
Qed.

Lemma embNatQ : forall n, embNat n == embedQ (inject_Z (Z.of_nat n)).
Proof.
  intros;reflexivity.
Qed.

Lemma le_0_n n : 0 <= (ntimes n 1).
Proof.
  rewrite ntimes_spec.
  rewrite mul1.
  rewrite embNatQ.
  rewrite <-Q0.
  apply Qle.
  replace 0%Q with (inject_Z 0%Z) by reflexivity.
  rewrite <-Zle_Qle.
  lia.
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


 Lemma npow_pos : forall x n, (0 <= x) -> 0 <= npow x n.
 Proof.
   intros.
   induction n.
   simpl;apply le_0_1.
   simpl.
   apply mul_pos_pos;auto.
 Qed.

 Lemma sum_le (f g : nat -> A) d : (forall i, (i < d)%nat -> (f i) <= (g i)) -> sum f d <= sum g d.
 Proof.
   intros.
   induction d.
   unfold sum;simpl.
   apply le_refl.
   rewrite !sum_S.
   apply le_le_plus_le;auto.
Qed.

  Lemma inv_Sn_pos n : 0 <= inv_Sn n.
  Proof.
    simpl.
    rewrite <-Q0.
    apply Qle.
    unfold QArith_base.Qle.
    simpl.
    lia.
 Qed.
End OrderTheory.


Infix "\o" := multi_composition (at level 2).
Section ArchimedeanFieldProperties.
  Context `{ArchimedeanField}.
  Add Ring ARing: (ComRingTheory (A := A)). 

  Lemma  opp_pos  x y : opp y <= opp x -> x <= y.
  Proof.
    intros.
    setoid_replace x with (-y + (x + y)) by ring.
    setoid_replace y with (-x + (x + y) ) at 3 by ring.
    apply (le_plus_compat);apply H1.
  Qed.

  (* Lemma abs_mult a b: abs (a * b) == abs a * abs b. *)
  (* Proof. *)
  (*   destruct (le_total a 0); destruct (le_total b 0). *)
  (*   rewrite (norm_abs_neg _ H1). *)
  (*   rewrite (norm_abs_neg _ H2). *)
  (*   ring_simplify. *)
  (*   rewrite norm_abs; try reflexivity. *)
  (*   setoid_replace (a * b) with (-a * - b) by ring. *)
  (*   apply mul_pos_pos;apply opp_pos;ring_simplify;auto. *)
  (*   rewrite (norm_abs_neg _ H1). *)
  (*   rewrite (norm_abs _ H2). *)
  (*   rewrite norm_abs_neg; try ring. *)
  (*   apply opp_pos. *)
  (*   ring_simplify. *)
  (*   apply mul_pos_pos;auto. *)
  (*   apply opp_pos. *)
  (*   ring_simplify;auto. *)
  (*   rewrite (norm_abs_neg _ H2). *)
  (*   rewrite (norm_abs _ H1). *)
  (*   rewrite norm_abs_neg; try ring. *)
  (*   apply opp_pos. *)
  (*   setoid_replace (-0) with 0 by ring. *)
  (*   setoid_replace (-(a*b)) with (a * (-b)) by ring. *)
  (*   apply mul_pos_pos;auto. *)
  (*   apply opp_pos. *)
  (*   ring_simplify;auto. *)
  (*   rewrite !norm_abs; auto; try reflexivity. *)
  (*   apply mul_pos_pos;auto. *)
  (* Qed. *)

End ArchimedeanFieldProperties.
