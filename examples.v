(*
We abstractly formalize some polynomial example ODEs so that they can be
instantiated over an arbitrary type
 *)
Require Import algebra ode polynomial functions.
From Coq Require Import Psatz. 
Require Import tuple.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import combinatorics.
Require Import archimedean realanalytic pivp.

From Coq Require Import QArith.
Close Scope Q_scope.

From Coq Require Import List.
Import ListNotations.
Open Scope poly_scope.
Open Scope list_scope.
Section IVP_Examples.
   Context `{ArchimedeanField }.
   Definition exp_ivp : PIVP := {|
                                 pf := t([0;1] );
                                 py0 := t(1)
                               |}.


   Definition tan_ivp : PIVP := {|
       pf := t([1;0;1]);
       py0 := t(0)
     |}.

  (* two-dimensional examples *)

  (* y1' = y2; y2' = -y1; y0 = (0,1) *)
   Definition sin_cos_ivp : PIVP := {|
       pf := t([[0;1]]; [0;[opp 1]]);
       py0 := t(0;1)
     |}.
    (* y1' = y2; y2' = mu * (1 - y1^2)y_2 - y_1; y0 = (0,0.1) *)

   Definition vdp_ivp (mu : A): PIVP := {|
       pf := t([[0;1]]; [[0;mu]; [opp 1]; [0; opp mu]]);
       py0 := t(0;inv_approx (inject_nat 10))
     |}.

  (* (* three-dimensional examples *) *)
  (*       y1' = y2^2;  y2' = - y2^2 * y3; y2^3 ); *)
   Definition arctan_ivp : PIVP := {|
       pf := t([[0;0;1]];[[0;0;[0;opp 1]]];[[0;0;0;1]]);
       py0 := t(0;1;0)
     |}.


  (* (* y1' = a(y2 - y1); y2' = y1*(b-y3)-y2; y3' = y1*y2 - c*y3; y0 = (1;1;1) *) *)

   Definition lorenz_ivp (a b c : A) : PIVP := {|
                                                pf := t(
                                                          (* y2*a + y1*(-a) *)
                                                          [[0;[a]];[[opp a]]];
                                                          (* y2*-1 + y1*(b) *)
                                                          [[0;[opp 1]];[[b;opp 1]]];
                                                          [[[0;opp c]]; [0;[1]]]);
       py0 := t(1;1;1)
     |}.

End IVP_Examples.

(* Section IVP_Examples. *)
(*    Context `{ArchimedeanField }. *)

(*    Definition exp_ivp : APIVP := {| *)
(*                                  ivp_rhs := t(vx); *)
(*                                  ivp_y0 := t(1) *)
(*                                |}. *)


(*    Definition tan_ivp : APIVP := {| *)
(*        ivp_rhs := t(1+vx^2); *)
(*        ivp_y0 := t(0) *)
(*      |}. *)

(*   (* two-dimensional examples *) *)

(*   (* y1' = y2; y2' = -y1; y0 = (0,1) *) *)
(*    Definition sin_cos_ivp : APIVP := {| *)
(*        ivp_rhs := t(vy; -vx); *)
(*        ivp_y0 := t(0;1) *)
(*      |}. *)

(*     (* y1' = y2; y2' = mu * (1 - y1^2)y_2 - y_1; y0 = (0,0.1) *) *)
(*    Definition vdp_ivp (mu : Q): APIVP := {| *)
(*        ivp_rhs := t(vy; mu * (1 - vx^2)*vy - vx); *)
(*        ivp_y0 := t(0;0.1) *)
(*      |}. *)


(*   (* three-dimensional examples *) *)
(*    Definition arctan_ivp : APIVP := {| *)
(*        ivp_rhs := t(vy^2; - vy^2 * vz; vy^3 ); *)
(*        ivp_y0 := t(0;1;0) *)
(*      |}. *)

(*   (* y1' = a(y2 - y1); y2' = y1*(b-y3)-y2; y3' = y1*y2 - c*y3; y0 = (1;1;1) *) *)

(*    Definition lorenz_ivp a b c : APIVP := {| *)
(*        ivp_rhs := t(a * (vy - vx); vx * (b-vz)-vy; vx*vy - c*vz); *)
(*        ivp_y0 := t(1;1;1) *)
(*      |}. *)

(* End IVP_Examples. *)
