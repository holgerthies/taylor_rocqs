Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import polynomial.
Require Import intervalpoly.
Require Import symbolic.

Definition tuple_map {n A B} (f : A -> B) (x : @tuple n A) : @tuple n B.
Proof.
  induction n.
  apply nil_tuple.
  destruct (destruct_tuple x) as [hd [tl P]].
  apply (tuple_cons (f hd) (IHn tl)).
 Defined.


Section PIVP.

  Context (T: Type) (d : nat).
  Context `{comSemiRing (A:=T)}.

  Definition mpolys_composition {n m r} (ps : (@tuple r (@mpoly T n))) (qs : @tuple n (@mpoly T m)) : (@tuple r (@mpoly T m)).
Proof.
  induction r.
  apply nil_tuple.
  destruct (destruct_tuple ps) as [hd [tl P]].
  apply (tuple_cons (hd \o qs) (IHr tl)).
  Defined.

  Record PIVP  := {
    p : (@tuple d (@mpoly T d));
    t0 : T;
    y0 : (@tuple d T)
  }.


Definition is_PIVP_solution_series (ivp : PIVP) (y : @tuple d (@mpoly T 1)) := tuple_map derive_poly y = mpolys_composition (p ivp) y.


End PIVP.
