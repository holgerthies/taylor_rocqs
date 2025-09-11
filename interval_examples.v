(*
Interval version of the ODE solver.
Uses coq-interval for operations on floating point intervals.
 *)
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

Require Import Coq.Numbers.DecimalString.
Require Import interval interval_string iode.
From Coq Require Import List.

From Coq Require Import Strings.String .
Open Scope string_scope.

(* only floating point precision prec is used for the benchmarks *)
Module IIVP_setup  <: IIVP_PARAMS.
  Definition prec := 100%positive. (* interval precision *)
  Definition order := 5%nat. (* taylor expansion order *)
  Definition max_steps := 1%nat. (* max number of iterations *)
  Definition step_factor := (Q2Fa 0.5) (* factor of max step size for each step *).
End IIVP_setup.

 Module IIVP1 := IIVP IIVP_setup.
(** Example Functions **)
Definition exp_example :=  exp_ivp (A:=I).
Definition sin_cos_example := sin_cos_ivp (A:=I).
Definition tan_example := tan_ivp (A := I).
Definition vdp_example := (vdp_ivp (A:=I) (FI.div (FI.F.PtoP 1) 1 (Z2I 2))).
Definition atan_example := (arctan_ivp (A:=I)).
Definition lorenz_example := (lorenz_ivp (A:=I) (Z2I 10) (Z2I 28) (IIVP1.FI.Q2I (Qmake 8 3))).

Tactic Notation "bench_interval_single" constr(lbl) uconstr(f) constr(order) constr(factor) constr(steps):=
  let prec  := eval cbv in IIVP_setup.prec in
   let fact := eval cbv in (Q2Fa factor) in
  idtac "------------------------------------------------------------";
  idtac "System    :" lbl;
  idtac "Precision:" prec;
  idtac "Order:" order;
  idtac "Size:" factor;
  idtac "Steps:" steps;
  time let r := eval vm_compute in (IIVP1.interval_steps f.(pf) f.(py0) 0 order fact steps) in let rl := eval vm_compute in (intervalt_to_cr_string r) in idtac "Result: " rl;
  idtac "------------------------------------------------------------".

Ltac bench_interval name f orders steps factors :=
  let ods := eval cbv in orders in
  let stps := eval cbv in steps in
  let facts := eval cbv in factors in
  lazymatch ods with
  | nil => idtac
  | ?o :: ?resto =>
      lazymatch stps with
      | nil => idtac
      | ?s :: ?rests =>
          lazymatch factors with
          | nil => idtac
          | ?fc :: ?restf =>
          bench_interval_single name f o fc s;
          bench_interval name f (o::nil) (s :: nil) restf;
          bench_interval name f (o :: nil) rests facts;
            bench_interval name f resto stps facts
         end
      end
  end.
Goal True.
  idtac "1) Single step of the interval method".
  bench_interval "exp" exp_example (( 10 :: 50 :: 100 :: 200:: nil)%nat)  (1  :: nil)%nat (0.5 ::  nil)%Q.
  bench_interval "tan" tan_example (( 10 :: 50 :: 100 :: 200:: nil)%nat)  (1  :: nil)%nat (0.5 ::  nil)%Q.
  bench_interval "sin/cos" sin_cos_example (( 10 :: 50 :: 100 :: 200:: nil)%nat)  (1  :: nil)%nat (0.5 ::  nil)%Q.
  bench_interval "vdp" vdp_example (( 10 :: 50 :: 100 ::  nil)%nat)  (1  :: nil)%nat (0.5 ::  nil)%Q.
  bench_interval "lorenz" lorenz_example (( 10 :: 50 :: 100 ::  nil)%nat)  (1  :: nil)%nat (0.5 ::  nil)%Q.
  exact Logic.I.
  idtac "------------------------------------".
Qed.
Goal True.
  idtac "1) Multiple steps and step sizes".
  bench_interval "exp" exp_example ((5 :: 10 :: 15 :: 30 :: 50 :: nil)%nat)  (1 :: 10 :: 100 :: 1000 :: nil)%nat (0.5 :: 0.25 :: 0.125 :: nil).
  bench_interval "sin/cos" sin_cos_example ((5 :: 10 :: 15 :: 30 ::  nil)%nat)  (1 :: 10 :: 100 :: 1000 :: nil)%nat (0.5 :: 0.25 :: 0.125:: nil).
  bench_interval "tan" tan_example ((5 :: 10 :: 15 :: 30 ::  nil)%nat)  (1 :: 10 :: 100 :: 1000 :: nil)%nat (0.5 :: 0.25 :: 0.125:: nil).
  bench_interval "vdp" vdp_example ((5 :: 10 :: 15 :: 30 :: nil)%nat)  (1 :: 10 :: 100 :: 1000 :: nil)%nat (0.5 :: 0.25 :: 0.125:: nil).
  bench_interval "lorenz" vdp_example ((5 :: 10 :: 15 ::  nil)%nat)  (1 :: 10 :: 100 :: 1000 :: nil)%nat (0.5 :: 0.25 :: 0.125:: nil).
  exact Logic.I.
  idtac "------------------------------------".
Qed.
