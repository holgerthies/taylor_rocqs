(*
Interval version of the ODE solver.
Uses coq-interval for operations on floating point intervals.
 *)
Require Import tuple.
Require Import List.
Require Import interval.
Require Import String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Open Scope string_scope.

Definition ZtoStr (z : Z) := NilZero.string_of_int (Z.to_int z).
Definition PostoStr z := NilZero.string_of_int (Pos.to_int z).

Definition decimal_to_string (num : positive) (denum : positive) : string.
Proof.
   destruct (Z.div_eucl (Z.pos num) (Z.pos denum)) as [d r].
   remember (r + (Z.pos denum))%Z as rn.
   apply ((ZtoStr d) ++ "." ++ (substring 1 (length (ZtoStr rn)) (ZtoStr rn))).
 Defined.

Definition output_bound_to_string (b : Interval.output_bound) : string.
Proof.
  destruct b.
  - apply (ZtoStr z).
  - destruct q.
    destruct Qnum.
    apply ("0" : string).
    apply (decimal_to_string p Qden).
    apply ("-" ++ (decimal_to_string p Qden)).
  - apply (append (ZtoStr z) (append "/"  (ZtoStr z0))).
Defined.
Definition interval_to_string (i : I) : string.
Proof.
  destruct (print_interval i) as [l r].
  destruct l as [l |];[|apply ("None" : string)].
  destruct r as [r | ]; [|apply ("None" : string)].
  remember ((output_bound_to_string l)) as ls.
  remember ((output_bound_to_string r)) as rs.
  apply  ("⟦" ++ ls ++ "," ++ rs ++ "⟧" ).
Defined.

Definition interval_to_cr_string (i : I) : string.
Proof.
  remember (FI.midpoint i) as m.
  remember (FI.F.sub_UP (FI.F.PtoP 20) (FI.upper i) (FI.lower i)) as R.
  destruct (print_interval (singleton m)) as [l _].
  destruct (print_interval (singleton R)) as [r _].
  destruct l as [l |];[|apply ("None" : string)].
  destruct r as [r |];[|apply ("None" : string)].
  remember ((output_bound_to_string l)) as center.
  remember ((output_bound_to_string r)) as radius.
  apply  (center ++ "±" ++ radius).
Defined.
Definition intervalt_to_string {d} (i : I^d) : list string.
Proof.
  destruct i.
  apply (map interval_to_string x).
Defined.

Definition intervalt_to_cr_string {d} (i : I^d) : list string.
Proof.
  destruct i.
  apply (map interval_to_cr_string x).
Defined.

Definition output_intervals {d} (i : list (I^d)) : string.
Proof.
  induction i.
  apply "".
  apply ((fold_right (fun x y => (x++" "++y)) "" (intervalt_to_string a))++";"++ IHi).
Defined.
Close Scope string_scope.

  
