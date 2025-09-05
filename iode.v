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

(*helper used for benchmarks only *)
Definition interval_steps {d} (p : (@mpoly I (S d)) ^(S d)) (y0 : I^(S d)) (t0 : F) (order :nat) (factor : F) (steps :nat)  :  I^(S (S d)).
Proof.
   pose (Fis := pivp_F p order).
   pose (step_factor := singleton factor).
   revert y0 t0.
   induction steps;intros.
   apply (tuple_cons (singleton t0) y0).
   pose (y_err := approx_pivp_step' p y0 Fis step_factor order).
   destruct (y_err) as [[t1 y1] err].
   pose (y1' := FI.add_errort (FI.upper err) y1).
   pose (t_next := (t0+(FI.lower t1))).
   apply  (IHsteps y1' t_next).
Defined.
Definition interval_step {d} (p : (@mpoly I (S d)) ^(S d)) (y0 : I^(S d)) (t0 : I) (order :nat) (factor : F)  :  I * I^((S d)).
Proof.
   pose (Fis := pivp_F p order).
   pose (step_factor := singleton factor).
   pose (y_err := approx_pivp_step' p y0 Fis step_factor order).
   destruct (y_err) as [[t1 y1] err].
   pose (y1' := FI.add_errort (FI.upper err) y1).
   apply  (t0+t1, y1').
Defined.

(* interval trajectory tactic *)

Tactic Notation "itraj"
  uconstr(p) uconstr(y0) uconstr(t0) constr(steps) :=

  let order := eval vm_compute in params.order in
  let step_factor := eval vm_compute in params.step_factor in
  let Fis   := eval vm_compute in (pivp_F p order) in
  let stepf := eval vm_compute in (singleton step_factor) in
  let n := eval cbv in steps in

  idtac "------------------------------------------------------------";
  idtac "order     :" order;
  idtac "step_fact :" step_factor;

  (* Main loop *)
  let rec loop steps y t :=
    lazymatch steps with
    | O =>
        idtac "done."
    | S ?steps' =>
        idtac "------------------------------------------------------------";
        let ys := eval vm_compute in (intervalt_to_cr_string y) in 
        let ts := eval vm_compute in (interval_to_cr_string t) in 
        idtac "t      =" ts;
        idtac "y(t)   =" ys;

          let ty :=
            eval vm_compute in
              (interval_step p y t order step_factor)
          in
          lazymatch ty with
          | (?t1, ?y1) =>
              loop steps' y1 t1
          end
    end in
  loop n y0 t0.
End IIVP.


