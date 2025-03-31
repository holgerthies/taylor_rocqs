(*
We abstractly formalize some polynomial example ODEs so that they can be
instantiated over an arbitrary type
 *)
Require Import algebra ode polynomial functions.
From Stdlib Require Import Psatz. 
Require Import tuple.
From Stdlib Require Import Setoid.
Require Import Stdlib.Classes.SetoidClass.
Require Import combinatorics.
Require Import realanalytic.
Section IVP_Examples.
  Open Scope fun_scope.
   Context `{Ring }. 
 (*  Context `{TotallyOrderedField (A := (A 0)) (H := H 0) (R_rawRing := (H0 0)) (R_semiRing := (H1 0)) }. *)
 (* Context `{normK : (NormedSemiRing (A 0) (A 0) (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }. *)
 (*  Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat))}. *)

 (*  Context `{total : forall n (x : (A 0)^n) (f : A n) , x \in_dom f}. *)
  (* Record Analytic {d} := { *)
  (*     y0 : (A 0)^d; *)
  (*     f : (A d)^d; *)
  (*     logM : nat; *)
  (*     r : (A 0); *)
  (*     (* Mgt0 : not (M == 0) /\ (0 <= M); *) *)
  (*     (* rgt0 : not (r == 0) /\ (0 <= r); *) *)
  (*     in_dom : y0 \in_dom f; *)
  (*     (* deriv_bound : forall k, (Dx[k] f) @ (y0 ; (dom_D in_dom))\_0 <= t[k]! * M * npow r (order k) *) *)
  (*   }. *)

  (* Definition ylogM {d} (f : @Analytic d) := d*f.(logM).  *)
  (* Definition y_radius {d} (f : @Analytic d)  := #2 * (ntimes d (npow #2 f.(logM))) * f.(r). *)
  (* Definition AIVP_nth_approx {d} (F : @Analytic d) n := ivp_taylor_poly F.(f) F.(y0) F.(in_dom) (n + 1 + d * F.(logM)). *)

  (* one-dimensional examples *)

  Notation "\x_ i" := (comp1 i) (at level 2).

  (* y' = y; y0 = 1 *)
  Definition exp_ivp : (PIVP (A := A) (d:=1)).
  Proof.
    unshelve eapply Build_PIVP.
    apply t(\x_0).
    apply t(1).
  Defined.

  (* y' = 1 + y^2; y0 = 0 *)
  Definition tan_ivp : (PIVP (A := A) (d:=1)).
  Proof.
    unshelve eapply Build_PIVP.
    apply t(1 [+] \x_0*\x_0 ).
    apply t(0).
  Defined.


  (* two-dimensional examples *)

  (* y1' = y2; y2' = -y1; y0 = (0,1) *)
  Definition sin_cos_ivp : (PIVP (A := A) (d:=2)).
  Proof.
    unshelve eapply Build_PIVP.
    apply t(\x_1;(opp 1) [*] \x_0). 
    apply t(0;1).
  Defined.

    (* y1' = y2; y2' = mu * (1 - y1^2)y_2 - y_1; y0 = (0,1) *)
  Definition vdp_ivp (mu : @mpoly A 0) : (PIVP (A := A) (d:=2)).
  Proof.
    unshelve eapply Build_PIVP.
    apply t(\x_1; mu [*] ((1 [+] ((opp 1) [*] \x_0 *\x_0)) * \x_1 + (opp 1) [*] \x_0)).
    apply t(0;1).
  Defined.

  (* three-dimensional examples *)
  (* y1' = a(y2 - y1); y2' = y1*(b-y3)-y2; y3' = y1*y2 - c*y3; y0 = (1;1;1) *)
  Definition lorenz_ivp (a b c  : @mpoly A 0) : (PIVP (A:=A) (d:=3)).
  Proof.
    unshelve eapply Build_PIVP.
    apply t(a [*] (\x_1 + ((opp 1) [*] \x_0)); \x_0 * (b [+] (opp 1) [*] \x_2) + (opp 1) [*] \x_1; \x_0 * \x_1 + (opp 1) [*] (c [*] \x_2)).
    apply t(1;1;1).
  Defined.
End IVP_Examples.
