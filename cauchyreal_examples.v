Require Import polynomial.
Require Import Coq.Reals.Abstract.ConstructiveReals.
Require Import coqreals.
Require Import examples.
Require Import tuple.
Require Import List.
Require Import Coq.Classes.SetoidClass.
From Coq.Reals Require Import ConstructiveCauchyReals.
From Coq.Reals.Cauchy Require Import ConstructiveRcomplete.
Require Import QArith.
Require Import Qpower.
Require Import Qabs.
Require Import Qround.
Require Import odebounds.
Require Import realanalytic.
Require Import abstractpowerseries.
Require Import ConstructiveCauchyAbs.
Open Scope algebra_scope.
Open Scope fun_scope.
Open Scope Q_scope.
Definition q (x : Z) (y : positive) := ({| Qnum := x; Qden := y |}).
Definition RQ := CRcarrier CRealConstructive.
Context `{AbstractPowerSeries (A := RQ) (H := (R_setoid )) (R_rawRing := R_rawRing) (H0 := _) (invSn := invSn) }.
Context `{cs_exists : CoeffSum (A := RQ) (H:= _ ) (R_rawRing := _) (H0 := _) (H1 := _) (H2 := _) (H3 := _) (H4 := _ ) (invSn := _) (A_Ring := _) (R_TotalOrder := _) (normK := _) (R_Field := _) (R_Field0 := _) (H5 := _) }.
 
 Definition  seq_tuple {d} (p : (RQ * tuple d RQ))  (z : Z): Q * list Q.
 Proof.
   destruct p.
   destruct t.
   apply ((seq r z) , (map (fun x => (seq x z)) x)).
 Defined.
 Definition  seq_trajectory {d} (p : list (RQ * tuple d RQ))  (z : Z) :=  map (fun p => seq_tuple p z) p.


(** exponential function (1d) **)

Definition exp_example := exp_ivp (A := RQ).

Definition exp_analytic  := analytic_poly exp_example.(pf) exp_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 20 approximation *)
Definition exp_taylor := taylor_poly exp_analytic 0 20.

(*evaluate at 1/2 *)
Definition exp_approx := (eval_poly exp_taylor (inject_Q (1#2 ))).
Compute (seq (exp_approx) (-10)).

(* now with guaranteed error bound  at max time *)
Definition exp_exact := (ivp_solution_max exp_analytic).

(* prints the time and the value as pair *)
Compute (seq_tuple (exp_exact) (-15)).

(** sine/cosine  (2d) **)

Definition sin_cos_example := sin_cos_ivp (A := RQ).

Definition sin_cos_analytic  := analytic_poly sin_cos_example.(pf) sin_cos_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 10 approximation *)
Definition sin_taylor := taylor_poly sin_cos_analytic 0 10.
Definition cos_taylor := taylor_poly sin_cos_analytic 1 10.

(*evaluate at 1/2 *)
Definition sin_approx := (eval_poly sin_taylor (inject_Q (1#2 ))).
Definition cos_approx := (eval_poly cos_taylor (inject_Q (1#2 ))).
Compute (seq (sin_approx) (-10)).
Compute (seq (cos_approx) (-10)).

(* now with guaranteed error bound  at max time *)
Definition sin_cos_exact := (ivp_solution_max sin_cos_analytic).

(* prints the time and the value as pair *)
Compute (seq_tuple (sin_cos_exact) (-5)).

(** tan function (1d) **)

Definition tan_example := tan_ivp (A := RQ).

Definition tan_analytic  := analytic_poly tan_example.(pf) tan_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 5 approximation *)
Definition tan_taylor := taylor_poly tan_analytic 0 5.

(*evaluate at 1/2 *)
Definition tan_approx := (eval_poly tan_taylor (inject_Q (1#2 ))).
Compute (seq (tan_approx) (-10)).

(* now with guaranteed error bound  at max time *)
Definition tan_exact := (ivp_solution_max tan_analytic).

(* prints the time and the value as pair *)

Compute (seq_tuple (tan_exact) (-1)).


(** van der pol oscillator (2d) **)

Definition vdp_example := vdp_ivp (A := RQ) (inject_Q (1#2)).

Definition vdp_analytic  := analytic_poly vdp_example.(pf) vdp_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 5 approximation *)
Definition vdp_taylor1 := taylor_poly vdp_analytic 0 5.
Definition vdp_taylor2 := taylor_poly vdp_analytic 1 5.

(*evaluate at 1/2 *)
Definition vdp1_approx := (eval_poly vdp_taylor1 (inject_Q (1#2 ))).
Definition vdp2_approx := (eval_poly vdp_taylor1 (inject_Q (1#2 ))).
Compute (seq (vdp1_approx) (-10)).
Compute (seq (vdp2_approx) (-10)).

(* now with guaranteed error bound  at max time *)
Definition vdp_exact := (ivp_solution_max vdp_analytic).

(* prints the time and the value as pair *)
(* This takes a while and thus commented out *)

 (* Compute (seq_tuple (vdp_exact) 0). *)

(** Lorenz system (3d) **)

Definition lorenz_example := lorenz_ivp (A := RQ) (inject_Q (10)) (inject_Q 28) (inject_Q (8#3)).

Definition lorenz_analytic  := analytic_poly lorenz_example.(pf) lorenz_example.(py0).

(* compute finite Taylor polynomial *)

(* order 5 approximation *)
Definition lorenz_taylor1 := taylor_poly lorenz_analytic 0 5.
Definition lorenz_taylor2 := taylor_poly lorenz_analytic 1 5.
Definition lorenz_taylor3 := taylor_poly lorenz_analytic 2 5.

(*evaluate at 1/2 *)
Definition l1_approx := (eval_poly lorenz_taylor1 (inject_Q (1#4 ))).
Definition l2_approx := (eval_poly lorenz_taylor2 (inject_Q (1#4 ))).
Definition l3_approx := (eval_poly lorenz_taylor3 (inject_Q (1#4 ))).
Compute (seq (l1_approx) (-10)).
Compute (seq (l2_approx) (-10)).
Compute (seq (l3_approx) (-10)).


Definition lorenz_exact := (ivp_solution_max lorenz_analytic).

(* prints the time and the value as pair *)
(* This takes a while and thus commented out *)

  (* Compute (seq_tuple (lorenz_exact) 0).   *)
