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
Open Scope poly_scope.
Section IVP_Examples.
   Context `{ArchimedeanField }.

   Definition exp_ivp : APIVP := {|
                                 ivp_rhs := t(vx);
                                 ivp_y0 := t(1)
                               |}.


   Definition tan_ivp : APIVP := {|
       ivp_rhs := t(1+vx^2);
       ivp_y0 := t(0)
     |}.

  (* two-dimensional examples *)

  (* y1' = y2; y2' = -y1; y0 = (0,1) *)
   Definition sin_cos_ivp : APIVP := {|
       ivp_rhs := t(vy; -vx);
       ivp_y0 := t(0;1)
     |}.

    (* y1' = y2; y2' = mu * (1 - y1^2)y_2 - y_1; y0 = (0,0.1) *)
   Definition vdp_ivp (mu : Q): APIVP := {|
       ivp_rhs := t(vy; mu * (1 - vx^2)*vy - vx);
       ivp_y0 := t(0;0.1)
     |}.


  (* three-dimensional examples *)
   Definition arctan_ivp : APIVP := {|
       ivp_rhs := t(vy^2; - vy^2 * vz; vy^3 );
       ivp_y0 := t(0;1;0)
     |}.

  (* y1' = a(y2 - y1); y2' = y1*(b-y3)-y2; y3' = y1*y2 - c*y3; y0 = (1;1;1) *)

   Definition lorenz_ivp a b c : APIVP := {|
       ivp_rhs := t(a * (vy - vx); vx * (b-vz)-vy; vx*vy - c*vz);
       ivp_y0 := t(1;1;1)
     |}.

End IVP_Examples.
