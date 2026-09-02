(**
   * Sound approximation relations between two ring structures

   The solver of [pivp.v] is generic in the arithmetic ([RawRing] /
   [RawFieldOps]).  To compare a run of the algorithm in one arithmetic with a
   run in another (concretely: interval arithmetic against exact real
   arithmetic) we use a relation between the two carriers that is compatible
   with the ring operations ([RingRel] below) and lift it to polynomials
   ([mrel]) and tuples ([trel]), showing that all the operations the algorithm
   performs preserve it.

   The lifting to polynomials is itself such a relation ([mrel_RingRel]), which
   is what makes polynomial composition (used by [shift_mpoly]) work: it is the
   evaluation of a polynomial whose coefficients are polynomials.
*)
Require Import algebra archimedean polynomial tuple pivp.
From Coq Require Import Psatz List Setoid Arith PeanoNat Compare_dec.
Require Import Coq.Classes.SetoidClass.
Import ListNotations.

Class RingRel {A B : Type} {SA : Setoid A} {RA : @RawRing A SA} {SB : Setoid B} {RB : @RawRing B SB} := {
    rrel : A -> B -> Prop;
    rrel_zero : rrel 0 0;
    rrel_one : rrel 1 1;
    rrel_add : forall a b a' b', rrel a a' -> rrel b b' -> rrel (a + b) (a' + b');
    rrel_mul : forall a b a' b', rrel a a' -> rrel b b' -> rrel (a * b) (a' * b');
  }.

Section PolyRel.
  Context {A B : Type} {SA : Setoid A} {RA : @RawRing A SA} {SB : Setoid B} {RB : @RawRing B SB}.
  Context {RR : @RingRel A B SA RA SB RB}.

  (** * Enclosures for (multivariate) polynomials and tuples *)

  Fixpoint mrel (d : nat) : @mpoly A d -> @mpoly B d -> Prop :=
    match d with
    | O => fun a b => rrel a b
    | S d' => fun p q => Forall2 (mrel d') p q
    end.

  Definition trel {d} (X : A^d) (x : B^d) := forall i, (i < d)%nat -> rrel (tuple_nth i X 0) (tuple_nth i x 0).

  Definition ptrel {e d} (P : (@mpoly A d)^e) (p : (@mpoly B d)^e) :=
    forall i, (i < e)%nat -> mrel d (tuple_nth i P 0) (tuple_nth i p 0).


  (** ** Basic properties of polynomial enclosures *)

  Lemma mrel_zero d : mrel d 0 0.
  Proof. induction d;simpl;[apply rrel_zero|constructor]. Qed.

  Lemma mrel_one d : mrel d 1 1.
  Proof. induction d;simpl;[apply rrel_one|constructor;[apply IHd|constructor]]. Qed.

  Lemma mrel_length d P p : mrel (S d) P p -> length P = length p.
  Proof. simpl; apply Forall2_length. Qed.

  Lemma mrel_nth d P p : mrel (S d) P p -> forall i, mrel d (nth i P 0) (nth i p 0).
  Proof.
    simpl; intros H.
    induction H;intros i;destruct i;simpl;auto using mrel_zero.
  Qed.

  Lemma mrel_hd d P p : mrel (S d) P p -> mrel d (hd 0 P) (hd 0 p).
  Proof. simpl; intros H; destruct H;simpl;auto using mrel_zero. Qed.

  (** ** Ring operations on polynomials *)

  Lemma mrel_add : forall d P p Q q, mrel d P p -> mrel d Q q -> mrel d (P + Q) (p + q).
  Proof.
    induction d;[intros P p Q q H1 H2;exact (rrel_add P Q p q H1 H2)|].
    intros P p Q q H1 H2.
    simpl in H1,H2 |- *.
    revert Q q H2.
    induction H1;intros Q q H2;[exact H2|].
    destruct H2 as [|Q0 q0 Q' q'];simpl;constructor;auto.
  Qed.

  Lemma mrel_convolution_rec d
    (Hmul : forall X x Y y, mrel d X x -> mrel d Y y -> mrel d (X * Y) (x * y))
    P p Q q : mrel (S d) P p -> mrel (S d) Q q ->
    forall n i, mrel d (convolution_coeff_rec P Q n i) (convolution_coeff_rec p q n i).
  Proof.
    intros H1 H2 n i.
    induction i;simpl.
    - apply mrel_add;[apply Hmul;apply mrel_nth;auto|apply mrel_zero].
    - apply mrel_add;[apply Hmul;apply mrel_nth;auto|apply IHi].
  Qed.

  Lemma mrel_convolution d
    (Hmul : forall X x Y y, mrel d X x -> mrel d Y y -> mrel d (X * Y) (x * y))
    P p Q q : mrel (S d) P p -> mrel (S d) Q q ->
    forall n, mrel d (convolution_coeff P Q n) (convolution_coeff p q n).
  Proof.
    intros;unfold convolution_coeff;apply mrel_convolution_rec;auto.
  Qed.

  Lemma mrel_mult_coefficients_rec d
    (Hmul : forall X x Y y, mrel d X x -> mrel d Y y -> mrel d (X * Y) (x * y))
    P p Q q : mrel (S d) P p -> mrel (S d) Q q ->
    forall n, mrel (S d) (mult_coefficients_rec P Q n) (mult_coefficients_rec p q n).
  Proof.
    intros H1 H2 n.
    induction n;simpl;[constructor|].
    rewrite <-(mrel_length _ _ _ H1), <-(mrel_length _ _ _ H2).
    constructor;[apply mrel_convolution|];auto.
  Qed.

  Lemma mrel_mul : forall d P p Q q, mrel d P p -> mrel d Q q -> mrel d (P * Q) (p * q).
  Proof.
    induction d;[intros P p Q q H1 H2;exact (rrel_mul P Q p q H1 H2)|].
    intros P p Q q H1 H2.
    assert (mrel (S d) (mult_coefficients P Q) (mult_coefficients p q)) as Hmc.
    {
      unfold mult_coefficients.
      rewrite <-(mrel_length _ _ _ H1), <-(mrel_length _ _ _ H2).
      apply mrel_mult_coefficients_rec;auto.
    }
    simpl in H1,H2|-*.
    destruct H1 as [|P0 p0 P' p' HP0 HP'];[constructor|].
    destruct H2 as [|Q0 q0 Q' q'];[constructor|].
    apply Hmc.
  Qed.


  (** ** Evaluation *)

  Lemma mrel_eval_poly d P p X x : mrel (S d) P p -> mrel d X x -> mrel d (eval_poly P X) (eval_poly p x).
  Proof.
    simpl;intros H HX.
    induction H;simpl;[apply mrel_zero|].
    apply mrel_add;auto.
    apply mrel_mul;auto.
  Qed.

  Lemma mrel_const d X x : rrel X x -> mrel d (const_to_mpoly d X) (const_to_mpoly d x).
  Proof.
    intros;induction d;simpl;[exact H|constructor;[auto|constructor]].
  Qed.

  Lemma mrel_eval_mpoly d P p X x : mrel (S d) P p -> rrel X x -> mrel d (P.{X}) (p.{x}).
  Proof.
    intros;unfold eval_mpoly;apply mrel_eval_poly;auto using mrel_const.
  Qed.

  (** ** Tuples *)

  Lemma trel_cons_inv {d} (X : A) (x : B) (T : A^d) (t : B^d) :
    trel (tuple_cons X T) (tuple_cons x t) -> rrel X x /\ trel T t.
  Proof.
    intros H;split.
    - specialize (H 0%nat (Nat.lt_0_succ _));rewrite !tuple_nth_cons_hd in H;auto.
    - intros i Hi;specialize (H (S i) (proj1 (Nat.succ_lt_mono _ _) Hi));rewrite !tuple_nth_cons_tl in H;auto.
  Qed.

  Lemma rrel_eval_tuple d P p (T : A^d) (t : B^d) : mrel d P p -> trel T t -> rrel (eval_tuple P T) (eval_tuple p t).
  Proof.
    revert P p T t.
    induction d;intros P p T t H HT;[exact H|].
    destruct (destruct_tuple_cons T) as [Xh [T' ->]].
    destruct (destruct_tuple_cons t) as [xh [t' ->]].
    rewrite !eval_tuple_cons_simpl.
    destruct (trel_cons_inv _ _ _ _ HT) as [Hh Ht].
    apply IHd;auto.
    apply mrel_eval_mpoly;auto.
  Qed.

  (** ** Derivatives, projections and sums *)

  Lemma mrel_derive_helper d P p N n : mrel (S d) P p -> mrel d N n -> mrel (S d) (derive_fast_helper P N) (derive_fast_helper p n).
  Proof.
    simpl;intros H;revert N n.
    induction H as [|X x P' p' Hx HP IH];intros N n HN;simpl;[constructor|].
    constructor;[apply mrel_mul;auto|apply IH;apply mrel_add;auto using mrel_one].
  Qed.

  Lemma mrel_derive d P p : mrel (S d) P p -> mrel (S d) (derive_poly P) (derive_poly p).
  Proof.
    intros H;unfold derive_poly, derive_fast.
    apply mrel_derive_helper;[|apply mrel_one].
    destruct H;simpl;[constructor|auto].
  Qed.

  Lemma mrel_pdiff : forall j d P p, mrel d P p -> mrel d (poly_pdiff j P) (poly_pdiff j p).
  Proof.
    induction j;intros d P p H.
    - destruct d;simpl;[apply rrel_zero|apply mrel_derive;auto].
    - destruct d;simpl;[apply rrel_zero|].
      simpl in H.
      induction H;simpl;constructor;auto.
  Qed.

  Lemma mrel_poly_comp1 d i : mrel d (poly_comp1 i) (poly_comp1 i).
  Proof.
    revert d;induction i;intros d;destruct d;simpl.
    - apply rrel_zero.
    - constructor;[apply mrel_zero|constructor;[apply mrel_one|constructor]].
    - apply rrel_zero.
    - constructor;[apply IHi|constructor].
  Qed.

  Lemma mrel_fold d F f : (forall i, mrel d (F i) (f i)) -> forall n k, mrel d (fold_right add 0 (map F (seq k n))) (fold_right add 0 (map f (seq k n))).
  Proof.
    intros H n;induction n;intros k;simpl;[apply mrel_zero|apply mrel_add;auto].
  Qed.

  Lemma mrel_sum d F f n : (forall i, mrel d (F i) (f i)) -> mrel d (sum F n) (sum f n).
  Proof. intros;unfold sum;apply mrel_fold;auto. Qed.


  (** ** Out-of-range components *)

  Lemma tuple_nth_over {T} {e} (t : tuple e T) i (df : T) : (e <= i)%nat -> tuple_nth i t df = df.
  Proof.
    intros;destruct t;simpl;apply nth_overflow;lia.
  Qed.

  Lemma trel_nth {e} (X : A^e) (x : B^e) : trel X x -> forall i, rrel (tuple_nth i X 0) (tuple_nth i x 0).
  Proof.
    intros H i.
    destruct (Compare_dec.le_lt_dec e i);[|apply H;auto].
    rewrite !tuple_nth_over;auto using rrel_zero.
  Qed.

  Lemma ptrel_nth {e d} (P : (@mpoly A d)^e) (p : (@mpoly B d)^e) : ptrel P p -> forall i, mrel d (tuple_nth i P 0) (tuple_nth i p 0).
  Proof.
    intros H i.
    destruct (Compare_dec.le_lt_dec e i);[|apply H;auto].
    rewrite !tuple_nth_over;auto using mrel_zero.
  Qed.

End PolyRel.

(** the lifting to polynomials is again a compatible relation, which is what
    makes polynomial composition work *)
#[global] Instance mrel_RingRel {A B : Type} {SA : Setoid A} {RA : @RawRing A SA}
  {SB : Setoid B} {RB : @RawRing B SB} (RR : @RingRel A B SA RA SB RB) (d : nat) :
  @RingRel (@mpoly A d) (@mpoly B d) (mpoly_setoid d) (mpoly_rawRing d) (mpoly_setoid d) (mpoly_rawRing d) :=
  {| rrel := mrel d;
     rrel_zero := mrel_zero d;
     rrel_one := mrel_one d;
     rrel_add := fun a b a' b' H1 H2 => mrel_add d a a' b b' H1 H2;
     rrel_mul := fun a b a' b' H1 H2 => mrel_mul d a a' b b' H1 H2 |}.

Section Composition.
  Context {A B : Type} {SA : Setoid A} {RA : @RawRing A SA} {SB : Setoid B} {RB : @RawRing B SB}.
  Context {RR : @RingRel A B SA RA SB RB}.

  Lemma mrel_to_mmpoly : forall n m (P : @mpoly A n) (p : @mpoly B n),
      mrel n P p -> @mrel _ _ _ _ _ _ (mrel_RingRel RR m) n (to_mmpoly m P) (to_mmpoly m p).
  Proof.
    induction n;intros m P p H.
    - apply (mrel_const m);exact H.
    - simpl in H.
      induction H;simpl;constructor;auto.
  Qed.

  Lemma mrel_composition : forall n m (P : @mpoly A n) p (QS : (@mpoly A m)^n) qs,
      mrel n P p -> ptrel QS qs -> mrel m (mpoly_composition P QS) (mpoly_composition p qs).
  Proof.
    intros n m P p QS qs H HQ.
    unfold mpoly_composition.
    apply (@rrel_eval_tuple _ _ _ _ _ _ (mrel_RingRel RR m) n).
    - apply mrel_to_mmpoly;auto.
    - exact HQ.
  Qed.

  Lemma ptrel_map_comp {d e} (P : (@mpoly A e)^d) p (S : (@mpoly A e)^e) s :
    ptrel P p -> ptrel S s ->
    ptrel (tuple_map (fun q => mpoly_composition q S) P) (tuple_map (fun q => mpoly_composition q s) p).
  Proof.
    intros HP HS i Hi.
    rewrite (tuple_map_nth _ P i 0 0), (tuple_map_nth _ p i 0 0);auto.
    apply mrel_composition;auto.
  Qed.

  Lemma ptrel_shift {d e} (P : (@mpoly A (S d))^e) (p : (@mpoly B (S d))^e) (Y : A^(S d)) (y : B^(S d)) :
    ptrel P p -> trel Y y -> ptrel (shift_mpoly P Y) (shift_mpoly p y).
  Proof.
    intros HP HY.
    unfold shift_mpoly.
    repeat match goal with
    | |- context[@seq_to_tuple ?T ?def ?f ?n] => destruct (@seq_to_tuple T def f n) as [? ?]
    end.
    apply ptrel_map_comp;auto.
    intros i Hi.
    rewrite e0, e1;auto.
    apply mrel_add;[apply mrel_poly_comp1|apply mrel_const;apply HY;auto].
  Qed.

End Composition.
