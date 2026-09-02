Require Import demo_prelude.
SetPythonPath "/Users/holgerthies/miniconda3/bin/python3".

Section IVP_def.
Local Notation x := (PVar 0).
Local Notation y := (PVar 1).
Definition p1 := 25*y - x * (x^2 + y^2).
Definition p2 := -25*x - y * (x^2 + y^2).
Definition spiral_f := t(p1;p2).
Definition spiral_y0 := t(0.2;1).
End IVP_def.

Section IVP_def2.
Local Notation x := (PVar 0).
Definition p1' := x^2+1.
Definition f' := t(p1').
Definition y0' := t(0).
End IVP_def2.

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
  trajectory spiral_f spiral_y0 10.
  plot_trajectory spiral_f spiral_y0 300.
  exact Logic.I.
Qed.

Goal True.
  plot_trajectory f' y0' 2000.
  exact Logic.I.
Qed.

