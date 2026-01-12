(** Demo for the IVP solver using Cauchy Reals and Intervals *)

(* PIVPs with rational coefficients can be defined abstractly *)

Require Import algebra ode polynomial functions.
From Coq Require Import Psatz. 
Require Import List tuple.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import combinatorics.
Require Import archimedean realanalytic pivp coqrationals.
Import ListNotations.
From Coq Require Import QArith.
Open Scope poly_scope.

(* working example *)
Section IVP_def.
Local Notation x := (PVar 0).
Local Notation y := (PVar 1).
Definition p1 := 25*y - x * (x^2 + y^2).
Definition p2 := -25*x - y * (x^2 + y^2).
Definition spiral_f := t(p1;p2).
Definition spiral_y0 := t(0.2;1).
End IVP_def.

(** Part 1: Solutions over Cauchy Reals **)
Require Import Coq.Reals.Abstract.ConstructiveReals.
From Coq.Reals Require Import ConstructiveCauchyReals.
From Coq.Reals.Cauchy Require Import ConstructiveRcomplete.
Require Import coqreals.

Definition RQ := CRcarrier CRealConstructive.

(*helper function for printing *)
 Definition  seq_tuple {d} (p : (RQ * tuple d RQ))  (z : Z): Q * list Q.
 Proof.
   destruct p.
   destruct t.
   apply ((seq r z) , (map (fun x => (seq x z)) x)).
 Defined.

(* convert to PIVP over Cauchy reals *)

(* exact solution at t=r/2 *)

Definition spiral_exact := (pivp_max_step (A:=RQ) spiral_f spiral_y0). 
Eval vm_compute in (seq_tuple (spiral_exact) (3)).


(** Part 2: Solutions using coq interval **)

Require Import interval interval_string iode.
Require Import Coq.Strings.String.
SetPythonPath "/Users/holgerthies/miniconda3/bin/python3".
Open Scope string_scope.
Close Scope Q_scope.
Module IIVP_params  <: IIVP_PARAMS.
  Definition prec := 30%positive. (* interval precision *)
  Definition order := 10%nat. (* taylor expansion order *)
  Definition max_steps := 1000%nat. (* max number of iterations *)
  Definition step_factor := (Q2Fa 0.25) (* factor of max step size for each step *).
End IIVP_params.  

Module IIVP  := IIVP IIVP_params.
Import IIVP.
Goal True.
  trajectory spiral_f spiral_y0 5.
  plot_trajectory spiral_f spiral_y0 1000.
  exact Logic.I.
Qed.
