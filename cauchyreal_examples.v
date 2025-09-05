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
From Coq Require Import Strings.String .
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

Open Scope string_scope.

Definition  max_time {d} f :=  ivp_r_max (d:=d) (analytic_poly (A := RQ) f.(pf) f.(py0)).

Definition approx_example {d} f t order precision := (seq_tuple (t , approx_pivp (d:=d) f t order) precision).

Tactic Notation "bench_order_single" uconstr(name) uconstr(f) uconstr(t) constr(order) constr(prec) :=
  let lbl   := eval cbv in name in
  let nm := fresh "res" in
  idtac "------------------------------------------------------------"; 
  idtac "System    :" lbl;
  idtac "Order    :" order;
  idtac "Precision:" prec;
  time (let r := eval vm_compute in (approx_example f t order prec) in pose (nm := r));
  let  show := eval cbv in nm in idtac "Result:" show;
  idtac "------------------------------------------------------------";
  clear nm.

Ltac bench_orders_rec name f t prec orders :=
  let os := eval cbv in orders in
  lazymatch os with
  | nil => idtac
  | ?o :: ?rest =>
      bench_order_single name f t o prec;
      bench_orders_rec name f t prec rest
  end.

Ltac bench_orders name f prec orders :=
  let t := constr: (max_time f) in
  bench_orders_rec name f t prec orders.

Tactic Notation "bench_exact_single" uconstr(name) uconstr(f) constr(prec) :=
  let lbl   := eval cbv in name in
  let nm := fresh "res" in
  idtac "------------------------------------------------------------";
  idtac "System    :" lbl;
  idtac "Precision:" prec;
  time (let r := eval vm_compute in (seq_tuple (pivp_solution_max f.(pf) f.(py0)) prec) in pose (nm := r));
  let  show := eval cbv in nm in idtac "Result:" show;
  idtac "------------------------------------------------------------";
  clear nm.

Ltac bench_exact name f precs :=
  let ps := eval cbv in precs in
  lazymatch ps with
  | nil => idtac
  | ?o :: ?rest =>
      bench_exact_single name f o;
      bench_exact name f rest
  end.

(** Example Functions **)
Definition exp_example := exp_ivp (A:=RQ).
Definition sin_cos_example := sin_cos_ivp (A:=RQ).
Definition tan_example := tan_ivp (A := RQ).
Definition vdp_example :=  (vdp_ivp (A := RQ) (inject_Q 0.5)).
Definition atan_example := arctan_ivp (A:=RQ).
Definition lorenz_example := (lorenz_ivp (A:=RQ) (inject_Q 10) (inject_Q 28) (inject_Q (8#3))).

(* Eval vm_compute in (seq_trajectory (pivp_trajectory exp_example.(pf) (inject_Q 0) exp_example.(py0) 2) 1%Z). *)
Goal True.
  idtac "1) Finite Taylor approximations of fixed order for the local solution";   idtac "Here, precision is the guaranteed  precision for the arithmetic operations in the form 2^z.";  
  idtac "The approximation error from the Taylor approximation is not taken into account.".
  bench_orders "exp" exp_example (-100 : Z) ((5 :: 10 :: 50 :: 70 :: nil) % nat).
  bench_orders "tan" tan_example (-100 : Z) ((5 :: 10 :: nil) % nat).
  bench_orders "sin/cos" sin_cos_example (-100 : Z) ((5 :: 10 :: 50 :: 10 :: nil) % nat).
  bench_orders "vdp" vdp_example (-100 : Z) ((5 :: 6  :: 7:: nil) % nat);
  bench_orders "lorenz" lorenz_example (-100 : Z) ((5 :: 6  :: nil) % nat); 
  bench_orders "atan" atan_example (-100 : Z) ((5 :: 6  :: nil) % nat); 
  exact I.
Qed.

Definition test_precs := ( -5 :: -10 ::  -50 :: -100 :: nil)%Z.
Goal True.
  idtac "2) Exact Computation of the local solution";
  idtac "The error of the approximation is guaranteed to be less than 2^precision".
  bench_exact "exp" exp_example test_precs.
  bench_exact "tan" tan_example (-5 :: -10 :: nil)%Z.
  bench_exact "sin/cos" sin_cos_example test_precs.
  bench_exact "vdp" vdp_example ((-5 ::  nil) % Z).
  bench_exact "atan" atan_example ((-5 :: -6:: nil) % Z).
  bench_exact "lorenz" lorenz_example ((-5 :: -6 ::  nil) % Z).
  exact I.
Qed.

End Examples.




