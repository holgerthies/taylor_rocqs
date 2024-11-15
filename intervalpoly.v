Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import symbolic.
Require Import polynomial.

Section Interval.
  Context {K : Type}.
  Context `{ofieldK : TotallyOrderedField K}.
  Context `{normK : (NormedSemiRing K K (H := H) (H0 := H) (R_semiRing := R_semiRing) (semiRingA := R_semiRing) (R_TotalOrder := R_TotalOrder))}.

  Add Ring TRing: ComRingTheory.
  Definition cinterval := (K * K)%type.
  Definition in_cinterval x i := (normK.(norm) (x-(fst i))) <= snd i.
  Definition in_cintervalt {n} (x : @tuple n K) (i : @tuple n cinterval) : Prop.
  Proof.
    induction n.
    apply True.
    destruct (destruct_tuple x) as [x0 [xt P1]].
    destruct (destruct_tuple i) as [i0 [it P2]].
    apply ((in_cinterval x0 i0) /\ (IHn xt it)).
  Defined.

  Definition add_cinterval (a b : cinterval) := ((fst a + fst b), (snd a + snd b)).
  Definition mul_cinterval (a b : cinterval) := ((fst a * fst b), (normK.(norm) (fst a))*(snd b) + (normK.(norm) (fst b))*(snd a) + (snd a)*(snd b)).

  Lemma add_cinterval_spec a b x y : in_cinterval x a -> in_cinterval y b -> in_cinterval (x+y) (add_cinterval a b). 
  Proof.
    intros.
    unfold add_cinterval, in_cinterval.
    simpl.
    setoid_replace (x + y - (fst a + fst b)) with ((x - fst a) + (y - fst b)) by ring.
    apply(le_trans _ _ _ (norm_triangle _ _)).
    apply le_le_plus_le;auto.
  Qed.

  Lemma mul_cinterval_spec a b x y : in_cinterval x a -> in_cinterval y b -> in_cinterval (x*y) (mul_cinterval a b). 
  Proof.
    intros.
    unfold mul_cinterval, in_cinterval;simpl.
    setoid_replace (x*y - fst a * fst b) with (fst a * (y - fst b) +  fst b * (x - fst a) + (x- fst a)*(y - fst b)) by ring.
    apply(le_trans _ _ _ (norm_triangle _ _)).
    apply le_le_plus_le.
    - apply(le_trans _ _ _ (norm_triangle _ _)).
      apply le_le_plus_le;apply (le_trans _ _ _ (norm_mult _ _)).
      apply mul_le_compat_pos;try apply norm_nonneg;apply H1.
      apply mul_le_compat_pos;try apply norm_nonneg;apply H0.
    - apply (le_trans _ _ _ (norm_mult _ _)).
      apply mul_le_le_compat_pos; try apply norm_nonneg;auto.
    Qed.

End Interval.
Section IntervalPoly.
  Context `{K : Type}.
  Context `{ofieldK : TotallyOrderedField K}.
  Context `{normK : (NormedSemiRing K K (H := H) (H0 := H) (R_semiRing := R_semiRing) (semiRingA := R_semiRing) (R_TotalOrder := R_TotalOrder))}.
  Definition symInterval := (Symbolic (@cinterval K)).

  Definition eval_symInterval (i : symInterval) : (@cinterval K).
  Proof.
    induction i.
    apply (0,0).
    apply (1,0).
    apply a.
    apply (add_cinterval IHi1 IHi2).
    apply (mul_cinterval IHi1 IHi2).
 Defined.
  Definition toIntervalPoly {n} (p : @mpoly K n) : (@mpoly (Symbolic (@cinterval K)) n).
  Proof.
    induction n.
    apply (Sconst (@cinterval K) (p,0)).
    induction p.
    apply [].
    apply ((IHn a) :: IHp).
  Defined.

  Definition tupleToSymbolic {A n} (t : @tuple n A) : (@tuple n (Symbolic A)).
  Proof.
    induction n.
    apply nil_tuple.
    destruct (destruct_tuple t) as [h [tl T]].
    apply (tuple_cons (Sconst A h) (IHn tl)).
  Defined.

  Definition evalInterval {n} (p : @mpoly K n) (i : @tuple n (@cinterval K)) := eval_symInterval (toIntervalPoly p).[tupleToSymbolic i].

  Lemma evalInterval_spec {n} (p : @mpoly K n) (i : @tuple n (@cinterval K)) (x : @tuple n K) : in_cintervalt x i -> in_cinterval p.[x] (evalInterval p i) .
  Proof.
    intros.
    induction n.
    - simpl.
     unfold in_cinterval,evalInterval;simpl.
     unfold minus;rewrite addI.
     setoid_replace (norm 0) with 0 by apply norm_zero;try apply le_refl;reflexivity.
    - simpl.
      
     unfold evalInterval.
     simpl.
      destruct (destruct_tuple i) as [i0 [it P]].
     destruct (destruct_tuple x) as [x0 [xt Px]].
     rewrite destruct_tuple_cons.
  Admitted.
End IntervalPoly.

