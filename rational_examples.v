Require Import polynomial.
Require Import coqrationals.
Require Import examples.
Require Import tuple.
From Coq Require Import List.
From Coq Require Import Classes.SetoidClass.
From Coq Require Import QArith.
From Coq Require Import Qpower.
From Coq Require Import Qabs.
From Coq Require Import Qround.
Require Import odebounds.
Require Import realanalytic.
Require Import abstractpowerseries.
Open Scope algebra_scope.
Open Scope fun_scope.
Open Scope Q_scope.
Definition rough_approx (q : Q) (factor : Z) : Q :=
  let '(Qmake a b) := q in
  Qmake (Z.shiftr a factor)%Z (Pos.shiftr b  (ZtoN factor))%positive.

Definition q (x : Z) (y : positive) := ({| Qnum := x; Qden := y |}).
 

 Definition  seq_tuple {d} (p : (Q * tuple d Q))  : Q * list Q.
 Proof.
   destruct p.
   destruct t.
   apply (q0,x).
 Defined.

 (* Definition  seq_trajectory {d} (p : list (RQ * tuple d RQ))  (z : Z) :=  map (fun p => seq_tuple p z) p. *)


(** exponential function (1d) **)

Definition exp_example := exp_ivp (A := Q).

Definition exp_analytic  := analytic_poly exp_example.(pf) exp_example.(py0).

(* First compute finite Taylor polynomial *)

(* order 20 approximation *)
Definition exp_taylor := taylor_poly exp_analytic 0 20.
(*evaluate at 1/2 *)
Definition exp_approx1 := (eval_poly exp_taylor ((1#2 ))).
Eval vm_compute in (taylor_error exp_analytic 2 10).
Definition exp_approx1' := (rough_approx exp_approx1 520).
Compute exp_approx1'.
 Definition exp_cont1  := analytic_poly exp_example.(pf) t(exp_approx1').

Definition exp_taylor2 := taylor_poly exp_cont1 0 20.
Definition exp_approx2 := (eval_poly exp_taylor2 ((1#2 ))).
Definition exp_approx2' := (rough_approx exp_approx2 1200).
Compute exp_approx2'.
