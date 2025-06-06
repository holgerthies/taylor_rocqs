(*
Interval version of the ODE solver.
Uses coq-interval for operations on floating point intervals.
 *)

From Coq Require Import QArith.
Require Import Qreals.
Require Import combinatorics.
Require Import algebra.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
From Coq Require Import Reals Psatz.
From Interval Require Import Tactic Plot.
Require Import Interval.Interval.Float.        
Require Import Interval.Float.Specific_ops.    
Require Import Interval.Float.Specific_bigint. 
Require Import polynomial.
Require Import examples.
Require Import tuple.
From Coq Require Import List.
Require Import odebounds.
Require Import realanalytic.
Require Import abstractpowerseries.
Require Import Interval.Real.Xreal.
Require Import Coq.Reals.Rdefinitions.
Require Import coqrationals.

Require Import Coq.Reals.Raxioms.
Require Import String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Module SFBI2 := SpecificFloat BigIntRadix2.    
Module FI   := FloatInterval SFBI2.         
Definition I := FI.type.
Definition F := SFBI2.type.

Definition prec := (FI.F.PtoP 100).
Definition print_interval := FI.output true.


Definition singleton (f : F) := (FI.bnd f f).
Definition ZtoStr z := NilZero.string_of_int (Z.to_int z).
Definition PostoStr z := NilZero.string_of_int (Pos.to_int z).

Open Scope string_scope.
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
  remember (FI.F.sub_UP prec (FI.upper i) (FI.lower i)) as R.
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
Close Scope string_scope.
  
#[global] Instance I_setoid: Setoid I.
Proof.
  exists (fun x y => x = y).
  split;auto.
  intros a b c -> eq';auto.
Defined.

#[global] Instance F_setoid: Setoid F.
Proof.
  exists (fun x y => x = y).
  split;auto.
  intros a b c -> eq';auto.
Defined.


#[global] Instance I_rawRing: (@RawRing FI.type _).
Proof.
   constructor.
   apply (FI.bnd (SFBI2.fromZ 0) (SFBI2.fromZ 0)).
   apply (FI.bnd (SFBI2.fromZ 1) (SFBI2.fromZ 1)).
   intros x y.
   apply (FI.add prec x y).
   intros x y.
   apply (FI.mul prec x y).
Defined.

#[global] Instance F_rawRing: (@RawRing F _).
Proof.
   constructor.
   apply  (SFBI2.fromZ 0).
   apply  (SFBI2.fromZ 1).
   intros x y.
   apply (FI.F.add_DN prec x y).
   intros x y.
   apply (FI.F.mul_DN prec x y).
Defined.
Definition to_Rpoly {d} (p : @mpoly F d) : @mpoly R d.
Proof.
  induction d.
  apply (SFBI2.toR p).
  induction p.
  apply nil.
  apply (cons (IHd a) IHp).
Defined.

Definition Z2I (z : Z) := FI.bnd (SFBI2.fromZ z) (SFBI2.fromZ z).

Lemma Z2I_spec z : Interval.contains (FI.convert (Z2I z)) (Xreal (IZR z)).
Proof.
  unfold Interval.contains;simpl;rewrite SFBI2.fromZ_correct';lra.
Qed.
Definition Q2F (q : Q) := (FI.F.div_UP prec (SFBI2.fromZ (Qnum q)) (SFBI2.fromZ (Z.pos (Qden q)))).
Definition Q2I (q : Q) := (FI.div prec (Z2I (Qnum q)) (Z2I (Z.pos (Qden q)))).

Lemma Q2I_spec q : Interval.contains (FI.convert (Q2I q)) (Xreal (Q2R q)).
Proof.
  enough ((Xreal (Q2R q)) = ((Xreal (IZR (Qnum q))) / (Xreal (IZR (Z.pos (Qden q)))))%XR) as ->.
  apply FI.div_correct;apply Z2I_spec.
  unfold Q2R.
  simpl.
  unfold Xdiv'.
  rewrite is_zero_false;auto.
Qed.

Definition Q2Ipoly {d} (p : @mpoly Q d) : @mpoly I d.
Proof.
  induction d.
  apply (Q2I p).
  induction p.
  apply nil.
  apply (cons (IHd a) IHp).
Defined.

Definition Q2Ipolyt {m d} (p :tuple m (@mpoly Q d)) : (tuple m (@mpoly I d)) := (tuple_map Q2Ipoly p).
Lemma Xreal_add a b :  Xreal (a + b) = (Xreal a + Xreal b)%XR.
Proof. reflexivity. Qed.

Lemma Xreal_mul a b :  Xreal (a * b) = (Xreal a * Xreal b)%XR.
Proof. reflexivity. Qed.

Lemma Q2Ipoly_spec1 (p : @mpoly Q 1) xi x : Interval.contains (FI.convert xi) (Xreal (Q2R x)) -> Interval.contains (FI.convert (eval_poly (Q2Ipoly p) (Q2I x))) (Xreal (Q2R (eval_poly p x))).
Proof.
  intros.
  induction p.
  simpl;lra.
  simpl eval_poly.
  rewrite Q2R_plus.
  rewrite Xreal_add.
  apply FI.add_correct; [apply Q2I_spec|].
  rewrite Q2R_mult.
  rewrite Xreal_mul.
  apply FI.mul_correct; [apply Q2I_spec|].
  apply IHp.
Qed.

Definition Q2err (q : Q) := (FI.add prec (FI.bnd FI.F.zero (FI.upper (Q2I q))) (FI.bnd (FI.lower (Q2I (-q))) FI.F.zero)).

Definition F2err (f : F) := (FI.add prec (FI.bnd FI.F.zero f) (FI.bnd (FI.F.sub_DN prec 0 f) FI.F.zero)).

Definition add_errorq (err : Q) (i : I) : I := FI.add prec i (Q2err err).
Definition add_error (err : F) (i : I) : I := FI.add prec i (F2err err).

(* #[global] Instance Xreal_semiRing: (SemiRing (A := ExtendedR)). *)
(* Proof. *)
(*   constructor. *)
(*   intros a b -> c d ->;simpl;auto. *)
(*   intros a b -> c d ->;simpl;auto. *)
(*   intros;simpl. *)
(*   unfold Xadd. *)
(*   Search Xreal ExtendedR.  *)
(*   apply Xadd_assoc. *)
(* Search FI.add. *)

(* #[global] Instance AR_semiRing: (algebra.SemiRing (A := FI.type)). *)
(* Proof. *)
(* Admitted. *)

Definition inv_fact (n :nat) : I.
Proof.
   induction n.
   apply 1.
   apply (IHn * (FI.inv prec (FI.bnd (SFBI2.fromZ (Z.of_nat (S n))) (SFBI2.fromZ (Z.of_nat (S n)))))).
Defined.

Definition Fi_to_taylor {d} (l : list (@mpoly I (S d))) (y0 : (tuple (S d) I)) : @poly I.
Proof.
  induction l.
  apply nil.

  apply ( IHl ++ (cons (inv_fact (Datatypes.length IHl) * (eval_tuple a y0)) nil)).
Defined.


   (* Fixpoint Fi {d} (f : (tuple (S d) (@mpoly I (S d)))) (n i : nat) : @mpoly I (S d) :=  *)
   (*   match n with *)
   (*   | 0%nat => (poly_comp1 i) *)
   (*   | (S n') => (sum (fun j => (tuple_nth j f 0) * (poly_pdiff j (Fi f n' i))) d) *)
   (*   end. *)

Definition Fi {d} (f : (tuple (S d) (@mpoly I (S d)))) (n i : nat) : list (@mpoly I (S d)).
  Proof.
    induction n.
    apply (cons (cons 0 (cons 1 nil)) nil).
    apply (cons (sum (fun j =>  (tuple_nth j f 0) * (poly_pdiff j (hd 0 IHn))) (S d))  IHn).
Defined.

 Definition taylor_poly {d} (f : (tuple (S d) (@mpoly I (S d)))) (y0 : I^(S d)) (order : nat) (i :nat) := Fi_to_taylor (Fi f order i) y0.
 (* transform a rational polynomial IVP to an interval IVP *)
 Definition ode_isolution_partial {d} (f : (tuple (S d) (@mpoly I (S d)))) (y0 : I^(S d)) (t: I) (order : nat)  : I^(S d).
 Proof.
     apply (seq_to_tuple (def := 0) (fun j => eval_poly (taylor_poly f y0 order j) t) (S d)).
  Defined.

   Definition poly_abs {d} (p : (@mpoly I d)) : @mpoly I d.
   Proof.
     induction d.
     apply (FI.abs p).
     induction p.
     apply nil.
     apply (cons (IHd a) IHp).
   Defined.
Definition pos_tuple_max {d} (f : F^d) : F.
Proof.
  induction d.
  apply (FI.F.fromZ 0).
  destruct (destruct_tuple_cons f) as [f0 [ft P]].
  apply (FI.F.max f0 (IHd ft)).
Defined.

Section QIVP.
   Context {d: nat} (p : (mpoly (A:=Q) (S d))^(S d)).

   Definition pi := Q2Ipolyt p.
   Definition abs_pi := tuple_map poly_abs pi.

   Definition poly_Mi (y0 : I^(S d)) i := FI.upper (FI.abs (eval_tuple (abs_pi\_i) (tuple_map (add_error (FI.F.fromZ 1)) y0))).

   Definition poly_M (y0 : I^(S d)) := (pos_tuple_max (proj1_sig (seq_to_tuple (def := 0) (poly_Mi y0) (S d)))).
   Definition isolution_r (y0  : I^(S d)) := (FI.F.div_DN prec 1 ((FI.F.fromZ (Z.of_nat (S (S d)))) *  poly_M y0)).

  Definition itail_error  (y0 : I^(S d)) (fact : positive) (n : nat) : F.
  Proof.
     remember (SFBI2.div_UP prec 1 (SFBI2.fromZ (Zpos fact))) as x.
     remember (SFBI2.sub_UP prec 1 x) as y.
     apply  ((FI.Fpower_pos_UP prec x (Pos.of_nat (S n))) * y).
  Defined.


  Fixpoint ode_trajectory (t0 : I) (y0 : I^(S d)) (order : nat) (step_factor : positive) (steps : nat) :   list (I^(S (S d))) :=
    match steps with
    | 0%nat => cons (tuple_cons t0 y0) nil
    | (S n) => let r := (isolution_r y0) in let t := (FI.div prec (singleton r) (singleton (SFBI2.fromZ (Zpos step_factor))))  in let p := (ode_isolution_partial pi y0 t order) in ode_trajectory (t0+t) (tuple_map (add_error (itail_error p step_factor order)) p) order step_factor n
    end.
  Fixpoint ode_solution (t0 : I) (y0 : I^(S d)) (t_end : F) (order : nat) (step_factor : positive) (max_steps : nat) :  I^(S (S d)) :=
    if (FI.F'.le t_end SFBI2.zero) then (tuple_cons t0 y0) else
    match max_steps with
    | 0%nat => (tuple_cons t0 y0)
    | (S n) => let r := (isolution_r y0) in let t := (SFBI2.min t_end (FI.F.div_DN prec r (SFBI2.fromZ (Zpos step_factor))))  in let p := (ode_isolution_partial pi y0 (singleton t) order) in ode_solution (t0+(singleton t)) (tuple_map (add_error (itail_error p step_factor order)) p) (FI.F.sub_UP prec t_end t) order step_factor n
    end.

  Fixpoint ode_trajectory' (t0 : I) (y0 : I^(S d)) (order : nat) (step_factor : positive) (steps : nat) :   list (I^(S (S d))) :=
    match steps with
    | 0%nat => cons (tuple_cons t0 y0) nil
    | (S n) => let r := (isolution_r y0) in let t := (FI.div prec (singleton r) (singleton (SFBI2.fromZ (Zpos step_factor))))  in let p := (ode_isolution_partial pi y0 t order) in ode_trajectory (t0+t) p order step_factor n
    end.
(*    Fixpoint ode_isolution (order : nat) (step_size : Q) (steps : nat) :  I^d := *)
(*    match steps with *)
(*    | 0 => tuple_map Q2I y0 *)
(*    | n+1 => *)
(*   Definition Qanalytic {d y0} := Analytic (A := mpoly (A:=Q)) (d := d) (y0 := y0) (in_dom := poly_tot y0). *)
(*    Definition iivp_taylor {d} (f : Qanalytic (d:=d) ) : R. *)
(* Definition interval_ivp *)

  
(*   Search (FI.type -> _). *)
(* Goal True. *)
(* Proof. *)
(* interval_intro (ln 2) with i_decimal. *)
(* ). *)
End QIVP.
Definition exp_example := exp_ivp (A := Q).
Definition exp_pf := Q2Ipolyt exp_example.(pf).
Definition exp_y0 := tuple_map Q2I exp_example.(py0).
Definition exp_taylor10 := (ode_isolution_partial exp_pf 1 1 10).
Definition r := singleton (isolution_r exp_ivp.(pf) 1).
Eval vm_compute in (interval_to_string r).
Eval vm_compute in (interval_to_cr_string r).
Definition q (x : Z) (y : positive) := ({| Qnum := x; Qden := y |}).
Definition t := (itail_error (d:=1)  1 2 10).
Definition a := (add_error t 1).
Eval vm_compute in (interval_to_cr_string a).
Definition t' := (ode_trajectory exp_ivp.(pf) 0 1 20 2 11).
Definition t'' := (ode_solution exp_ivp.(pf) 0 1 1 20 2 11).
Eval vm_compute in (map intervalt_to_cr_string t').
Eval vm_compute in (intervalt_to_cr_string t'').
Eval vm_compute in (map intervalt_to_string t').
                                                                    



Definition exp_analytic  := analytic_poly exp_example.(pf) exp_example.(py0).
Fixpoint interval_trajectory (n : nat) := match n with
                          | 0%nat => exp_y0\_0 
                          | (S n') => (add_error (eval_poly (Fi_to_taylor exp10 (tuple_cons (interval_trajectory n') nil_tuple)) 1 ) (taylor_error exp_analytic 1 10))
                                       end.


Eval vm_compute in (interval_to_string (add_error 1 (q 1 2))).

Eval vm_compute in (interval_to_string (interval_trajectory 1)).
(* Definition output_bound_normalize (b : Interval.output_bound) : Interval.output_bound. *)
(* Proof. *)
(*    destruct b. *)
(*    apply (Interval.BDecimal (q z 1)). *)
(*    apply (Interval.BDecimal q). *)
(*    apply (Interval.BDecimal (q z z0)). *)
(*   Print Interval.output_bound.  *)

Definition exp_approx0 : I :=  (eval_poly exp_taylor10 ((FI.bnd (SFBI2.fromZ (1)) (SFBI2.fromZ  (1))))).

Eval vm_compute in (interval_to_string exp_approx0).
Eval vm_compute in (taylor_error exp_analytic 1 10).


Eval vm_compute in (output_bound_to_string (Interval.BDecimal (q (-3) 10))).

Ltac print_interval' e :=
  let I_val := (eval vm_compute in e) in
  let lo := (eval vm_compute in (SFBI2.toR (FI.lower I_val))) in
  let hi := (eval vm_compute in (SFBI2.toR (FI.upper I_val))) in
  idtac "⟦" lo "," hi "⟧" .

  Goal True.
  Check FI.output.
  Print Interval.output_bound.
  Eval vm_compute in (print_interval exp_approx0).
  Search BinarySingleNaN.B2R.
 Eval vm_compute in  (BinarySingleNaN.B2R (FI.lower exp_approx0)).
 Check  BinarySingleNaN.B2R.
 Locate B2R.
 Search (SFBI2.type -> R).
 Print SFBI2.type.
 Search FI.F.type.

  interval_intro (SFBI2.toR (FI.lower (1 : I))).
Search Interval.output_bound.

Eval vm_compute in (print_interval test').
Goal True.
  let t := reify_R (R0 +
 (R1 + R1) * (R1 + (R1 + R1) * (R1 + R1)) * (R1 + (R1 + R1) * (R1 + (R1 + R1) * (R1 + R1)) * R0))%R in (interval_intro t).
Definition test' :=exp_ivp.(pf)\_0.
Definition test'' := Eval vm_compute in (hd 0 test').
Open Scope R_scope.
Definition a := 
Definition test0 := exp_approx0.
Time Eval vm_compute in test0.


Definition testc0 := (exp_continue0 1000).
Time Eval vm_compute in testc0.
