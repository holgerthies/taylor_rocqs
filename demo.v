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

Definition tan_ivp_abstr : APIVP := {|
     ivp_rhs := t(1+vx^2);
     ivp_y0 := t(0)
 |}.

(* y' = 1/(1+y^2) reformulated as PIVP *)
Definition atan_ivp_abstr : APIVP := {|
  ivp_rhs := t(PConst 1; vz;  -2 * vx * vz^2 );
  ivp_y0 := t(0;0;1)                                  
 |}.

Definition tan_ivp_rq := convert_pivp (A:=RQ) tan_ivp_abstr.
(* Definition atan_ivp_rq := convert_pivp (A:=RQ) atan_ivp_abstr. *)

(* same IVP but without overhead for conversion *)
Close Scope Q_scope.
(* direct definitions for faster computation *)
Definition tan_ivp_rq' : PIVP (A:=RQ) := {|
     pf := t([1;0;1]);
     py0 := t(0)
|}.
Definition neg2 : RQ := inject_Z (-2).
Definition atan_ivp_rq' : PIVP (A:=RQ) := {|
     pf := t([[1]];[[[0;1]]];[0;[[0;0;neg2]]]);
     py0 := t(0;0;1)
  |}.


(* Definition tan_exact := (pivp_solution_max tan_ivp_rq.(pf) tan_ivp_rq.(py0)). *)
(* faster versions *)
Definition tan_exact := (pivp_solution_max tan_ivp_rq'.(pf) tan_ivp_rq'.(py0)).
Definition atan_exact := (pivp_solution_max atan_ivp_rq'.(pf) atan_ivp_rq'.(py0)).

Eval vm_compute in (seq_tuple (tan_exact) (-5)).
Eval vm_compute in (seq_tuple (atan_exact) (-2)).

(** Part 2: Solutions using coq interval **)

Require Import interval interval_string iode.

Require Import Coq.Strings.String.
Open Scope string_scope.
Module IIVP_params  <: IIVP_PARAMS.
  Definition prec := 30%positive. (* interval precision *)
  Definition order := 10%nat. (* taylor expansion order *)
  Definition max_steps := 1000%nat. (* max number of iterations *)
  Definition step_factor := (Q2Fa 0.25) (* factor of max step size for each step *).
End IIVP_params.  

Module IIVP  := IIVP IIVP_params.
Import IIVP.

Definition tan_ivp_i : PIVP (A:=I) := {|
     pf := t([1;0;1]);
     py0 := t(0)
|}.
Definition atan_ivp_i : PIVP (A:=I) := {|
     pf := t([[1]];[[[0;1]]];[0;[[0;0;Z2I (-2)]]]);
     py0 := t(0;0;1)
  |}.

SetPythonPath "/Users/holgerthies/miniconda3/bin/python3".
Goal True.
  plot_start.
  plot_traj tan_ivp_i.(pf) tan_ivp_i.(py0) 0 10.
  itraj tan_ivp_i.(pf) tan_ivp_i.(py0) 0 10.
  (* itraj atan_ivp_i.(pf) atan_ivp_i.(py0) 0 5. *)
  exact Logic.I.
Qed.
