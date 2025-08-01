Require Import polynomial.
Require Import Coq.Reals.Abstract.ConstructiveReals.
Require Import coqreals.
Require Import examples.
Require Import tuple.
From Coq Require Import List.
From Coq Require Import Classes.SetoidClass.
From Coq.Reals Require Import ConstructiveCauchyReals.
From Coq.Reals.Cauchy Require Import ConstructiveRcomplete.
From Coq Require Import QArith.
From Coq Require Import Qpower.
From Coq Require Import Qabs.
From Coq Require Import Qround.
Require Import odebounds.
Require Import realanalytic pivp.
Require Import abstractpowerseries.
From Coq Require Import ConstructiveCauchyAbs.
Open Scope algebra_scope.
Open Scope fun_scope.
Open Scope Q_scope.
Definition q (x : Z) (y : positive) := ({| Qnum := x; Qden := y |}).
Definition RQ := CRcarrier CRealConstructive.
Section Examples.
 
 Definition  seq_tuple {d} (p : (RQ * tuple d RQ))  (z : Z): Q * list Q.
 Proof.
   destruct p.
   destruct t.
   apply ((seq r z) , (map (fun x => (seq x z)) x)).
 Defined.
 Definition  seq_trajectory {d} (p : list (RQ * tuple d RQ))  (z : Z) :=  map (fun p => seq_tuple p z) p.


(** exponential function (1d) **)

Definition exp_example := convert_pivp (A:=RQ) exp_ivp.


(* First compute finite Taylor polynomial *)

(* order 20 approximation *)
Definition exp_approx' := approx_pivp exp_example (inject_Q 0.5) 20.

(*evaluate at 1/2 *)
Time Eval vm_compute in (seq_tuple (inject_Q (1#2) ,exp_approx') (-10)).
(* now with guaranteed error bound  at max time *)
Definition exp_exact := (pivp_trajectory exp_example.(pf) (inject_Q 0) (exp_example.(py0)) 1).

(* prints the time and the value as pair *)
Eval vm_compute in (seq_trajectory (exp_exact) (-5)).



(* Definition exp_approx'' := approx_pivp (Build_PIVP 1 (exp_example.(pf)) (snd exp_exact)) (inject_Q 0.5) 1. *)

(* Time Eval vm_compute in . *)


(** sine/cosine  (2d) **)

Definition sin_cos_example := convert_pivp (A:=RQ) sin_cos_ivp.

Definition sin_cos_analytic  := analytic_poly sin_cos_example.(pf) sin_cos_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 10 approximation *)
Definition sin_taylor := taylor_poly sin_cos_analytic 0 10.
Definition cos_taylor := taylor_poly sin_cos_analytic 1 10.
Definition sin_cos_approx := approx_pivp sin_cos_example (inject_Q 0.5) 10.
(*evaluate at 1/2 *)
Definition sin_approx := (eval_poly sin_taylor (inject_Q (1#2 ))).
Definition cos_approx := (eval_poly cos_taylor (inject_Q (1#2 ))).
Time Eval vm_compute in (seq (sin_approx) (-10)).
Time Eval vm_compute in (seq (cos_approx) (-10)).
Time Eval vm_compute in (seq_tuple (inject_Q (1#2) ,sin_cos_approx)).
(* Time Eval vm_compute in (seq (approx_nb_error (inject_nat := algebra.embedNat) sin_cos_example (inject_Q (1#34)) 10) (-10)). *)
(* now with guaranteed error bound  at max time *)
Definition sin_cos_exact := (ivp_solution_max sin_cos_analytic).

(* prints the time and the value as pair *)

(*trajectory *)

Definition sin_cos_trajectory := (pivp_trajectory sin_cos_example.(pf) (inject_Q 0) sin_cos_example.(py0) 1).

Eval vm_compute in (seq_trajectory (sin_cos_trajectory) (-3)).
(** tan function (1d) **)

Definition tan_example := convert_pivp tan_ivp (A := RQ).

Definition tan_analytic  := analytic_poly tan_example.(pf) tan_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 5 approximation *)
Definition tan_taylor := taylor_poly tan_analytic 0 5.

(*evaluate at 1/2 *)
Definition tan_approx := (eval_poly tan_taylor (inject_Q (1#2 ))).
Time Eval vm_compute in (seq (tan_approx) (-10)).

(* now with guaranteed error bound  at max time *)
Definition tan_exact := (ivp_solution_max tan_analytic).

(* prints the time and the value as pair *)

Time Eval vm_compute in (seq_tuple (tan_exact) (-1)).


(** van der pol oscillator (2d) **)

Definition vdp_example := convert_pivp (A := RQ) (vdp_ivp 0.5).

Definition vdp_analytic  := analytic_poly vdp_example.(pf) vdp_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 5 approximation *)
Definition vdp_taylor1 := taylor_poly vdp_analytic 0 5.
Definition vdp_taylor2 := taylor_poly vdp_analytic 1 5.

(*evaluate at 1/2 *)
Definition vdp1_approx := (eval_poly vdp_taylor1 (inject_Q (1#2 ))).
Definition vdp2_approx := (eval_poly vdp_taylor1 (inject_Q (1#2 ))).
Time Eval vm_compute in (seq (vdp1_approx) (-10)).
Time Eval vm_compute in  (seq (vdp2_approx) (-10)).

(* now with guaranteed error bound  at max time *)
Definition vdp_exact := (ivp_solution_max vdp_analytic).

(* prints the time and the value as pair *)
(* This takes a while and thus commented out *)

 (* Compute (seq_tuple (vdp_exact) 0). *)

(** Lorenz system (3d) **)

Definition lorenz_example := convert_pivp (A:=RQ) (lorenz_ivp 10 28 (8#3)).

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
Time Eval vm_compute in (seq (l1_approx) (-10)).
Time Eval vm_compute in (seq (l2_approx) (-10)).
Time Eval vm_compute in (seq (l3_approx) (-10)).


Definition lorenz_exact := (ivp_solution_max lorenz_analytic).
(* prints the time and the value as pair *)

(* Compute (seq_tuple (lorenz_exact) 0).   *)

End Examples.




