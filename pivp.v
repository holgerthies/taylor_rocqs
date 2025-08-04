From Coq Require Import Psatz.
From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Require Import algebra archimedean.
Require Import abstractpowerseries.
Require Import functions.
Require Import polynomial.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
From Coq Require Import Classical.
Require Import tuple.
Require Import combinatorics.
Require Import ode.
Require Import polynomial.
Require Import odebounds.
Require Import realanalytic.


Section PolyOde.

  Context `{RawFieldOps}. 
  

  Record PIVP  {d} := {
    pf : A{x^d}^d;
    py0 : A^d
  }.

  Definition inject_nat n := inject_Q (QArith_base.inject_Z (Z.of_nat n)).
  Definition inject_nat_inv (n : nat) :=inject_Q (QArith_base.Qmake 1 (Pos.of_nat n)).

  Fixpoint inv_fact (n : nat) :=
    match n with
    | 0 => 1
    | (S n') => inject_nat_inv n  * inv_fact n'
   end.

  Definition poly_to_ps {d} (p : A{x^d}) (k : nat^d) : A.
  Proof.
    induction d.
    apply p.
    destruct (destruct_tuple_cons k) as [hd [tl P]].
    apply (IHd (nth hd p 0) tl).
  Defined.

  Local Definition Fi {d} (f : (tuple (S d) (@mpoly A (S d)))) (n i : nat) : list (@mpoly A (S d)).
  Proof.
    induction n.
    apply (cons (poly_comp1 i) nil).
    apply (cons (sum (fun j =>  (tuple_nth j f 0) * (poly_pdiff j (hd 0 IHn))) (S d))  IHn).
Defined.

  Definition pivp_F {d} (f : (tuple (S d) (@mpoly A (S d)))) n := proj1_sig (seq_to_tuple (def:=0) (Fi (d:=d) f n) (S d)).

  Local Definition Fi_to_taylor {d} (l : list (@mpoly A (S d)))  : @poly A.
Proof.
  induction l.
  apply nil.
  apply ( IHl ++ (cons (inv_fact (Datatypes.length IHl) * (poly_to_ps a 0)) nil)).
  Defined.

  Local Definition Fi_to_taylor' {d} (l : list (@mpoly A (S d))) (y0 : A^(S d))  : @poly A.
Proof.
  induction l.
  apply nil.
  apply ( IHl ++ (cons (inv_fact (Datatypes.length IHl) * (eval_tuple a y0)) nil)).
  Defined.
  Local Definition poly_taylor {d} (p : @mpoly A (S d)^(S d))  n i := Fi_to_taylor (Fi p n i).

  Definition approx' {d} (p : @mpoly A (S d)^(S d))  (t : A)  ( n i : nat) : A :=  (eval_poly (poly_taylor p n i)  t) .

  Definition approx_pivp_raw {d} (p : PIVP (d:=(S d))) (t : A) (n : nat) : A^(S d) := let p' := shift_mpoly p.(pf) p.(py0)  in (proj1_sig (seq_to_tuple (def := 0) (fun i => approx' p'  t  n i) (S d)))+p.(py0).

  Definition poly_norm {d} (p : A{x^d}) : A.
  Proof.
    induction d.
    apply (abs p).
    induction p.
    apply 0.
    apply (IHp + (IHd a)).
  Defined.


   Definition poly_vec_bound {d} {e} (p : A{x^S d}^e)  : A.  
   Proof.
     induction e.
     apply 0.
     destruct (destruct_tuple_cons p) as [p0 [tl P]].
     apply (max (poly_norm p0)  (IHe tl)).
   Defined.

  Definition approx_nb_error {d} (p : PIVP (d := (S d))) (t_factor :A) (n : nat) : A.
  Proof.
    pose (p' := (shift_mpoly p.(pf) p.(py0))).
    pose (M := poly_vec_bound p').
    pose (M' := inject_nat ((S d)) * M).
    (* todo *)
    apply ( inject_nat 2 * npow (t_factor * M')  n).
  Qed.

  Definition min x y:= - (max (-x) (-y)).


  Definition poly_r {d} (p : @mpoly A d ^d ) (y0 : A^d):= 1.
  Definition poly_M {d} (p : @mpoly A (S d) ^ (S d)  ) (y0 : A^(S d)):= let p' := (shift_mpoly p y0) in max 1 (poly_vec_bound p').

  Definition approx_pivp_step {d} (p : PIVP (d:=(S d))) (t : A) (step_factor : A) (n : nat) : A * A^(S d) * A.
  Proof.
    pose (p' := (shift_mpoly p.(pf) p.(py0))). 
    pose (M0 := (poly_M p.(pf) p.(py0))).
    pose (r0 := (poly_r p.(pf) p.(py0))).

    pose (M := (analytic_solution_M M0 r0)).
    pose (r := inject_nat (2 * (S d)) * M0 * r0).
    pose (t1 := min t ((inv_approx r*step_factor))).
    pose (t_fact := (t1 * r)).
    pose (y1 := proj1_sig (seq_to_tuple (def := 0) (fun i => approx' p'  t1  n i) (S d))+p.(py0)).
    pose (err := M*inv_approx (1-t_fact) * npow (t_fact ) (S n)).
    apply (t1,y1,err).
  Defined.

  Definition approx_pivp_step' {d} (p : A{x^(S d)}^(S d)) (y0 : A^(S d)) (Fis : list (@mpoly A (S d))^(S d)) (step_factor : A) (n : nat) : A * A^(S d) * A.
  Proof.
    pose (M0 := (poly_M p y0)).
    pose (r0 := (poly_r p y0)).
    (* pose (M := (analytic_solution_M M0 r0)). *)
    pose (r := inject_nat (2 * (S d)) * M0 * r0).
    pose (t1 := (inv_approx r*step_factor)).
    pose (t_fact := step_factor).
    pose (y1 := proj1_sig (seq_to_tuple (def := 0) (fun i => eval_poly (Fi_to_taylor' Fis\_i y0)  t1) (S d))).
    pose (err := inject_nat 2 * npow (t_fact ) (S n)).
    apply (t1,y1,err).
  Defined.


  Definition update_y0 {d} (p : PIVP (d:=d)) (y0 : A^d) := Build_PIVP d p.(pf) y0.

  (* Definition approx_pivp_trajectory {d} (p : A{x^(S d)}^(S d)) (y0 : A^(S d)) (t0 : A) (step_factor : A) (n steps : nat) :  list (A * A^(S d)). *)
  (* Proof. *)
  (*    pose (Fis := pivp_F p n). *)
  (*    revert y0 t0. *)
  (*    induction steps;intros. *)
  (*    apply [(t0,y0)]. *)
  (*    pose (y_err := approx_pivp_step' p y0 Fis step_factor n). *)
  (*    destruct (y_err) as [[t1 y1] err]. *)
  (*    apply ((t0, y0) :: (IHsteps y1 (t0+t1))). *)
  (* Defined. *)
  Definition approx_pivp_trajectory {d} (p : A{x^(S d)}^(S d)) (y0 : A^(S d)) (t0 : A) (step_factor : A) (n steps : nat) :  list (A * A^(S d)).
  Proof.
     (* pose (Fis := pivp_F p n). *)
     revert y0 t0.
     induction steps;intros.

     apply [(t0,y0)].
      pose (pi := Build_PIVP (S d) p y0).
     pose (y_err := approx_pivp_step pi 1 step_factor n).
     destruct (y_err) as [[t1 y1] err].
     apply ((t0, y0) :: (IHsteps y1 (t0+t1))).
  Defined.

  Definition approx_pivp_step_size {d} (p : A{x^(S d)}^(S d)) (y0 : A^(S d))  (step_factor : A)  : A.
  Proof.
    pose (M0 := (poly_M p y0)).
    pose (r0 := (poly_r p y0)).
    pose (M := (analytic_solution_M M0 r0)).
    pose (r := inject_nat (2 * (S d)) * M0 * r0).
    pose (t1 := (inv_approx r*step_factor)).
    apply t1.
  Defined.

  Definition approx_pivp_step'' {d} (p : A{x^(S d)}^(S d)) (y0 : A^(S d)) (Fis : list (@mpoly A (S d))) (t1 : A) (i : nat) : A.
  Proof.
    pose (y1 := eval_poly (Fi_to_taylor' Fis y0)  t1).
    apply y1.
  Defined.

   Definition pivp_trajectory_fast {lim : (nat -> A) -> A} {d} (p : (@mpoly A (S d))^(S d)) (t0 : A) (y0 : A^(S d)) (steps : nat) :  list (A * (A^(S d))).
   Proof.
     pose (Fis := pivp_F p 200).
     revert t0 y0.
     induction steps;intros.
     apply [(t0,y0)].
     pose (pi := Build_PIVP (S d) p y0).
     pose (t1 := (approx_pivp_step_size p y0 (inject_Q (QArith_base.Qmake 1 2)))).
     pose (f := (fun i n => approx_pivp_step'' p y0 (firstn n Fis\_i) t1 i)).
     pose proof (seq_to_tuple (def:=0) (fun i => lim (f i)) (S d)).
     apply ((t0, y0) :: (IHsteps (t0 + t1) (proj1_sig X))).
   Defined.
End PolyOde.
Section AnalyticPoly.


  Context `{ArchimedeanField}.

  Definition approx_pivp { d} := approx_pivp_raw (d := d) .
  (* Local Fixpoint poly_taylor_acc {d} (p: @mpoly A (S d)^(S d)) (y0 : A) n i  acc  : @mpoly A 1:= *)
  (*   match n with *)
  (*     | 0 => y0 :: acc *)
  (*    | (S n') => poly_taylor_acc p y0 n' i (((Fi (A := ps (A:=A)) (tuple_map poly_to_ps p) n i) 0)  :: acc) *)
  (*   end. *)
   Add Ring KRing: (ComRingTheory (A :=A)).
  Lemma poly_tot {d} (y0 : A^(S d)) : forall (f : @mpoly A (S d)), @in_domain _ _ _ (mpoly_setoid (S d) (A := A)) _ _ _ _ _ f y0.
  Proof.
    intros.
    apply poly_total.
  Qed.


  Definition max_order {d} (p : A{x^d}) : nat.
  Proof.
    induction d.
    apply 0.
    induction p.
    apply 0.
    apply (Nat.max (S IHp) (IHd a)).
  Defined.


  Lemma max_order_cons {d} a (p : A{x^(S d)})  : max_order (a :: p : A{x^(S d)}) = Nat.max (S (max_order p)) (max_order a).
  Proof.
    simpl;reflexivity.
  Qed.


  Lemma poly_to_ps_cons {d} (p : A{x^(S d)}) hd tl : poly_to_ps p (tuple_cons hd tl) = poly_to_ps (nth hd p 0) tl.
  Proof.
   simpl.
   destruct (destruct_tuple_cons (tuple_cons hd tl)) as [hd' [tl' P]].
   apply tuple_cons_ext in P.
   destruct P as [-> ->].
   reflexivity.
 Qed.
  Lemma poly_to_ps0 {d} : poly_to_ps (0 : A{x^d}) == 0.
  Proof.
    induction d.
    simpl;reflexivity.
    intros k.
    destruct (destruct_tuple_cons k) as [hd [tl ->]].
    rewrite poly_to_ps_cons.
    simpl;destruct hd;rewrite (IHd tl);reflexivity.
  Qed.

   Lemma max_order0 {d} : max_order (0 : A{x^d}) = 0.
  Proof.
    destruct d.
    simpl;reflexivity.
    simpl.
    reflexivity.
  Qed.




  Lemma partial_index_to_ps {d} (p : A{x^(S d)}) i: partial_index (poly_to_ps p) i == poly_to_ps (nth i p 0).
  Proof.
    unfold partial_index.
    intros k.
    rewrite poly_to_ps_cons;reflexivity.
  Qed.
  Definition poly_norm' {d} := poly_norm (d:=d) .
  Lemma poly_norm_sum {d} (p : A{x^(S d)}) :  poly_norm'  p == (sum (fun i => (poly_norm' (nth i p 0))) (length p)).
  Proof.
    induction p.
    unfold sum;simpl;reflexivity.
    simpl length.
    replace (poly_norm' (a :: p : A{x^(S d)})) with (poly_norm' (p : A{x^(S d)}) + poly_norm' a) by (simpl;auto).
    rewrite IHp.
    rewrite sum_S_fun.
    rewrite addC;simpl nth.
    reflexivity.
  Qed.

  Lemma sum_fin_monotone (f : nat -> A) m :(forall i, 0 <= f i ) -> (forall i, i >= m  -> f i == 0) -> forall d,  (sum f d) <= (sum f m). 
  Proof.
    intros.
    assert (m <= d \/ d < m)%nat  as [Hd | Hd] by lia.
    rewrite (sum_fin _ m);auto;try apply le_refl.
    replace  m with (d + (m - d))%nat by lia.
    induction (m-d)%nat.
    replace (d+0)%nat with d by lia; apply le_refl.
    replace (d+(S n))%nat with (S (d + n)) by lia.
    rewrite sum_S.
    setoid_replace (sum f d) with (sum f d + 0) by ring.
    apply le_le_plus_le;auto.
  Qed.

  Lemma poly_norm_spec {d} (p : A{x^(d)}) n : sum_order (poly_to_ps p) n <= poly_norm' p.
  Proof.
    revert n.
    induction d;intros.
    destruct n; try apply le_refl; try apply abs_nonneg.
    rewrite sum_order_next.
    rewrite poly_norm_sum.
    apply (le_trans _ (sum (fun i => sum_order (partial_index (poly_to_ps p) i) (n-i)) (length p))).
    - apply sum_fin_monotone; [intros;apply sum_order_nonneg|].
      intros.
      apply sum_order_zero_ps.
      unfold partial_index.
      intros k.
      rewrite poly_to_ps_cons.
      enough (nth i p 0 = 0) as -> by apply poly_to_ps0.
      rewrite nth_overflow; try reflexivity;lia.
   - apply sum_le.
     intros.
     rewrite partial_index_to_ps.
     apply IHd.
  Qed.


  Definition poly_vec_bound' {d e} := poly_vec_bound (A:=A)  (d:=d) (e:=e).
  Lemma poly_vec_bound_cons {d e} p0 pt : poly_vec_bound (A:=A) (d:=d) (e:=(S e)) (tuple_cons p0 pt) == max (poly_norm p0) (poly_vec_bound pt).
  Proof.
    Opaque poly_norm.
    simpl.
    destruct (destruct_tuple_cons (tuple_cons p0 pt)) as [p0' [pt' P]] eqn:E.
    setoid_rewrite E.
    clear E.
    apply tuple_cons_ext in P.
    destruct P as [-> -> ].
    reflexivity.
  Qed.

   Lemma poly_vec_bound_spec {d} {e} (p : A{x^S d}^e) i n : i < S d -> sum_order  (poly_to_ps p\_i) n <= poly_vec_bound p.   
   Proof.
     intros.
     apply (le_trans _ _ _ (poly_norm_spec _ _)).
     
     unfold poly_norm'.
     generalize dependent i.
     induction e;intros.
     rewrite tuple_nth_nil;apply le_refl.
     destruct (destruct_tuple_cons p) as [p0 [pt ->]].
     rewrite poly_vec_bound_cons.
     destruct i.
     - rewrite tuple_nth_cons_hd.
       apply max_le_left.
    - rewrite tuple_nth_cons_tl.
      assert (i < S d) by lia.
      apply (le_trans _ _ _ (IHe _ _ H2)).
      apply max_le_right.
   Qed.

   Lemma poly_bound_spec {d} (p : A{x^S d}^S d) i : i < S d -> strong_bound (poly_to_ps p\_i) (to_ps (fun (n : nat) => max 1 (poly_vec_bound p)  * npow 1 n)).
   Proof.
     intros.
     unfold strong_bound.
     intros.
     rewrite to_ps_simpl.
     rewrite npow1; [|reflexivity].
     rewrite mul1.
     apply (le_trans _ (poly_vec_bound p)); [|apply max_le_right].
     apply (le_trans _ _ _ (poly_vec_bound_spec _ _ n H1));apply le_refl.
   Qed.




   Lemma fun_ps_poly_ps {d} (p : A{x^S d}) : poly_to_ps p == fun_ps p (y0 := 0) (in_dom := poly_tot 0).
   Proof.
     intros k.
  Admitted.
  Definition analytic_poly {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d))  : Analytic (A := @mpoly A) (d := d) (y0 := 0) (in_dom := poly_tot 0).
  Proof.
    pose (p' := shift_mpoly p y0).
    unshelve eapply Build_Analytic.
    apply p'.
    apply (poly_M p y0).
    apply (poly_r p y0).
    apply max_le_left.
    apply le_refl.
    intros.

    rewrite <-fun_ps_poly_ps.
    unfold a_bound_series.
    apply poly_bound_spec;auto.
  Defined.
    


   Definition approx {d} {y0 in_dom} (F : (Analytic (d:=d) (A := @mpoly A ) (y0 := y0) (in_dom := in_dom))) (t : A) i n :=  partial_sum (H := H) (R_rawRing := R_rawRing) (A := A)  (to_ps  (analytic_solution_ps  (A := mpoly) (H3 := mpoly_comp_diff_algebra) (F ) i)) t (n + 1).
   Lemma fast_cauchy_neighboring_approx {d} {y0 in_dom} (F : (Analytic (d:=d) (A := @mpoly A ) (y0 := y0) (in_dom := in_dom))) t i : abs t <=inv2 * (solution_rinv (d:=d)   F.(M) F.(r))-> i < S d -> fast_cauchy_neighboring (approx F t i).
   Proof.
     intros.
     apply (analytic_modulus (H3 := mpoly_comp_diff_algebra));auto.
   Qed.

   Definition ivp_r_max {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly))   := ((inv2 * solution_rinv (d:=d) (A := @mpoly A)  F.(M) F.(r))).

   (* Lemma neighboring_error   *)

   (* Definition pivp_approx_with_error {d} (p : @mpoly A d) (t : A) (n : nat) : {yt : A^t * A | dist  }. *)

   Context `{ConstrComplete (A := A) (H := _) (R_rawRing := _) (R_semiRing := _) (R_Ring := _) (R_ordered := _)  (emb := _) (hasAbs := _) (Ropp := _) (hasOps := _) (H0 := H0) }.
   Definition ivp_solution_i {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly))  (i : nat) t  :  abs t <= (ivp_r_max F)  -> A.
   Proof.
     intros.
     destruct (le_lt_dec i d); [|apply 0].
     assert (  fast_cauchy_neighboring  (approx  F t i)).
     {
       apply fast_cauchy_neighboring_approx;try lia.
       apply (le_trans _ _ _ H2).
       apply le_refl.
     }
     pose proof (has_limit (approx F t i)).
     destruct (X H3).
     apply x.
   Defined.

   Lemma solution_r_pos  {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly)) : 0 <= solution_rinv F.(M) F.(r) (d:=d).
   Proof.
   Admitted.
   Definition ivp_solution_i_max {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly))  (i : nat)  : A * A.
   Proof.
     assert (abs (ivp_r_max F) <= ivp_r_max F).
     {
       rewrite abs_pos;try apply le_refl.
       apply mul_pos_pos.
       apply inv2_pos.
       apply solution_r_pos.
     }
     apply ((ivp_r_max F), (ivp_solution_i F i (ivp_r_max F)) H2).
   Defined.

   Definition ivp_solution_max  {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly)) : (A * ( A^(S d))).
   Proof.
     destruct (seq_to_tuple ((fun i => snd (ivp_solution_i_max F i))) (S d) (def := 0)).
     apply ((ivp_r_max F) , x).
   Defined.

   Definition pivp_solution_ith {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) (t : A) i := ivp_solution_i (analytic_poly p y0) i t.

   Definition pivp_solution_ith_max {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) i := let s := ivp_solution_i_max (analytic_poly p y0) i in (fst s, snd s + y0\_i).

   Definition pivp_solution_max {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) :  (A * ( A^(S d))).
   Proof.
     destruct (seq_to_tuple ((fun i => snd (pivp_solution_ith_max p y0 i))) (S d) (def := 0)).
     apply ((ivp_r_max (analytic_poly p y0)) , x).
   Defined.

   Definition pivp_trajectory {d} (p : (@mpoly A (S d))^(S d)) (t0 : A) (y0 : A^(S d)) (steps : nat) :  list (A * (A^(S d))).
   Proof.
     revert t0 y0.
     induction steps;intros.
     apply [(t0,y0)].
     pose proof (pivp_solution_max p y0).
     apply ((t0, y0) :: (IHsteps (t0 + fst X) (snd X))).
   Defined.
   Definition pivp_solve {d} (p : (@mpoly A (S d))^(S d)) (t0 : A) (y0 : A^(S d)) (steps : nat) : (A * (A ^ (S d))).
   Proof.
     revert t0 y0.
     induction steps;intros.
     apply (t0,y0).
     pose proof (pivp_solution_max p y0).
     apply  (IHsteps (t0 + fst X) (snd X)).
  Defined.

End AnalyticPoly.

(* for conveniently defining polynomials *)
Declare Scope poly_scope.

Delimit Scope poly_scope with poly.
Inductive PolyExpr : Type :=
| PConst : QArith_base.Q -> PolyExpr
| PVar : nat -> PolyExpr          (* e.g., Var 0 = x, Var 1 = y *)
| PAdd : PolyExpr -> PolyExpr -> PolyExpr
| PSub : PolyExpr -> PolyExpr -> PolyExpr
| POpp :  PolyExpr -> PolyExpr
| PMul : PolyExpr -> PolyExpr -> PolyExpr
| PPow : PolyExpr -> nat -> PolyExpr.

Notation "x + y" := (PAdd x y) : poly_scope.
Notation "- x" := (POpp x) : poly_scope.
Notation "x - y" := (PSub x y) : poly_scope.
Notation "x * y" := (PMul x y) : poly_scope.
Notation "x ^ n" := (PPow x n) (at level 30, right associativity) : poly_scope.

Coercion PConst : QArith_base.Q >-> PolyExpr.

Notation "'vx'" := (PVar 0) (only parsing) : poly_scope.
Notation "'vy'" := (PVar 1) (only parsing) : poly_scope.
Notation "'vz'" := (PVar 2) (only parsing) : poly_scope.
Notation "'v1'" := (PVar 3) : poly_scope.
Notation "'v2'" := (PVar 4) : poly_scope.
Notation "'v3'" := (PVar 5) : poly_scope.
Notation "'v4'" := (PVar 6) : poly_scope.


Record APIVP {d}:= {
    ivp_rhs : PolyExpr^d;
    ivp_y0 : QArith_base.Q^d
  }.
Section MakeIVP.
Context `{RawFieldOps}.
Definition make_poly  d (p : PolyExpr)  : (@mpoly A d).
Proof.
  induction p.
  - apply (const_to_mpoly d (inject_Q q)).
  - apply (poly_comp1 n).
  - apply (IHp1 + IHp2).
  - apply (IHp1 + const_to_mpoly d (opp 1) * IHp2).
  - apply (const_to_mpoly d (opp 1) * IHp).
  - apply (IHp1 * IHp2).
  - apply (npow IHp n).
Defined.
Definition vecp  {e} d  (p : PolyExpr^e)  : (@mpoly A d)^e := tuple_map (make_poly d) p.

Definition convert_pivp {d} (ivp : APIVP (d :=d)) : PIVP (d:=d) := {|
pf := vecp d ivp.(ivp_rhs);
py0 := tuple_map inject_Q ivp.(ivp_y0);
 |}.

End MakeIVP.
