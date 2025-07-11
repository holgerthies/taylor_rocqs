From Coq Require Import QArith.
Require Import Qreals.
Require Import combinatorics.
Require Import algebra.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
From Coq Require Import Reals Psatz.
From Interval Require Import Tactic Plot.
Require Import Interval.Interval.Float.        
Require Import Interval.Float.Specific_ops.    
Require Import Interval.Float.Specific_bigint. 
Require Import polynomial.
Require Import pivp examples.
Require Import tuple.
Require Import odebounds.
Require Import realanalytic.
Require Import abstractpowerseries.
Require Import Interval.Real.Xreal.
Require Import Coq.Reals.Rdefinitions.
Require Import coqrationals.

Require Import Coq.Reals.Raxioms.
Require Import String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import interval interval_string.
From Coq Require Import List.


Module Type IIVP_PARAMS.
  Parameter prec : positive.
  Parameter order : nat.
  Parameter max_steps : nat.
  Parameter step_factor : F.
End IIVP_PARAMS.

Module IIVP (params : IIVP_PARAMS).

Module p  <: PRECISION_POS.  Definition precision := params.prec.  End p.
Module FI := FloatInterval p.

Definition interval_trajectory {d} (p : (@mpoly I (S d)) ^(S d)) (y0 : I^(S d)) (t0 : F) (t_end : F)  : list (I^(S (S d))).
Proof.
   pose (Fis := pivp_F p params.order).
   pose (step_factor := singleton params.step_factor).
   revert y0 t0.
   induction params.max_steps;intros.
   apply ((tuple_cons (singleton t0) y0) :: nil).
   destruct (FI.F'.le (t_end - t0) SFBI2.zero).
   - apply ((tuple_cons (singleton t0) y0) :: nil).
   - pose (y_err := approx_pivp_step' p y0 Fis step_factor params.order).
     destruct (y_err) as [[t1 y1] err].
     pose (y1' := FI.add_errort (FI.upper err) y1).
     pose (t_next := (t0+(FI.lower t1))).
     apply ((tuple_cons (singleton t0) y0) :: IHn y1' t_next).
 Defined.

Definition itrajectory {d} (p : (PolyExpr) ^(S d)) (y0 : Q^(S d)) (t0 : F) (t_end : F)  := interval_trajectory (vecp (A:=I) (S d) p) (tuple_map archimedean.inject_Q y0) t0 t_end.

End IIVP.


