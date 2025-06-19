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


Section AnalyticPoly.
  Context `{ArchimedeanField}.
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
    apply (max (S IHp) (IHd a)).
  Defined.

  Definition poly_norm {d} (p : A{x^d}) : A.
  Proof.
    induction d.
    apply (abs p).
    induction p.
    apply 0.
    apply (IHp + (IHd a)).
  Defined.

  Lemma max_order_cons {d} a (p : A{x^(S d)})  : max_order (a :: p : A{x^(S d)}) = max (S (max_order p)) (max_order a).
  Proof.
    simpl;reflexivity.
  Qed.

  Definition poly_to_ps {d} (p : A{x^d}) (k : nat^d) : A.
  Proof.
    induction d.
    apply p.
    destruct (destruct_tuple_cons k) as [hd [tl P]].
    apply (IHd (nth hd p 0) tl).
  Defined.

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

  Lemma poly_norm_sum {d} (p : A{x^(S d)}) :  poly_norm p == (sum (fun i => (poly_norm (nth i p 0))) (length p)).
  Proof.
    induction p.
    unfold sum;simpl;reflexivity.
    simpl length.
    replace (poly_norm (a :: p : A{x^(S d)})) with (poly_norm (p : A{x^(S d)}) + poly_norm a) by (simpl;auto).
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

  Lemma poly_norm_spec {d} (p : A{x^(d)}) n : sum_order (poly_to_ps p) n <= poly_norm p.
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


   Definition poly_vec_bound {d} {e} (p : A{x^S d}^e)  : A.  
   Proof.
     induction e.
     apply 0.
     destruct (destruct_tuple_cons p) as [p0 [tl P]].
     apply ((poly_norm p0) +  (IHe tl)).
   Defined.

   Lemma poly_vec_bound_spec {d} {e} (p : A{x^S d}^e) i n : i < S d -> sum_order  (poly_to_ps p\_i) n <= poly_vec_bound p.   
   Admitted.

   Lemma poly_bound_spec {d} (p : A{x^S d}^S d) i : i < S d -> strong_bound (poly_to_ps p\_i) (to_ps (fun (n : nat) => #(proj1_sig (upper (poly_vec_bound p)))  * npow #1 n)).
   Proof.
     intros.
     unfold strong_bound.
     intros.
     rewrite to_ps_simpl.
     rewrite npow1; [|rewrite ntimes_embed;simpl;ring].
     rewrite mul1.
     destruct (upper (poly_vec_bound p)) as [x P].
     
     apply (le_trans _ _ _ (poly_vec_bound_spec _ _ n H1)).
     apply (le_trans _ _ _ P).
     rewrite ntimes_embed.
     simpl.
     apply le_refl.
   Qed.




   Lemma fun_ps_poly_ps {d} (p : A{x^S d}) : poly_to_ps p == fun_ps p (y0 := 0) (in_dom := poly_tot 0).
   Proof.
   Admitted.

  Definition analytic_poly {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d))  : Analytic (A := mpoly) (d := d) (y0 := 0) (in_dom := poly_tot 0).
  Proof.
    pose (p' := shift_mpoly p y0).
    unshelve eapply Build_Analytic.
    apply p'.
    apply (upper (poly_vec_bound p')).
    apply 1.
    intros.
    rewrite <-fun_ps_poly_ps.
    unfold a_bound_series.
    apply poly_bound_spec;auto.
  Defined.
    

   Definition approx {d} {y0 in_dom} (F : (Analytic (d:=d) (A := @mpoly A ) (y0 := y0) (in_dom := in_dom))) (t : A) i n :=  partial_sum (H := H) (R_rawRing := R_rawRing) (A := A)  (to_ps  (analytic_solution_ps  (A := mpoly) (H3 := mpoly_comp_diff_algebra) (F ) i)) t ((proj1_sig (analytic_solution_logM  F )) + n + 1).

   Lemma fast_cauchy_neighboring_approx {d} {y0 in_dom} (F : (Analytic (d:=d) (A := @mpoly A ) (y0 := y0) (in_dom := in_dom))) t i : abs t <=inv2 * inv_Sn (proj1_sig (analytic_solution_r   F))-> i < S d -> fast_cauchy_neighboring (approx F t i).
   Proof.
     intros.
     apply (analytic_modulus (H3 := mpoly_comp_diff_algebra));auto.
   Qed.

   Definition ivp_r_max {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly))   := ((inv2 * inv_Sn (proj1_sig (analytic_solution_r (A := @mpoly A)  F)))).

   Context `{ConstrComplete (A := A) (H := _) (R_rawRing := _) (R_semiRing := _) (R_Ring := _) (R_ordered := _)  (emb := _) (hasAbs := _) (H0 := H0) }.
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

   Definition ivp_solution_i_max {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly))  (i : nat)  : A * A.
   Proof.
     assert (abs (ivp_r_max F) <= ivp_r_max F).
     {
       rewrite abs_pos;try apply le_refl.
       apply mul_pos_pos.
       apply inv2_pos.
       apply inv_Sn_pos.
     }
     apply ((ivp_r_max F), (ivp_solution_i F i (ivp_r_max F)) H2).
   Defined.

   Definition ivp_solution_max  {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly)) : (A * ( A^(S d))).
   Proof.
     destruct (seq_to_tuple ((fun i => snd (ivp_solution_i_max F i))) (S d) (def := 0)).
     apply ((ivp_r_max F) , x).
   Defined.

   Definition pivp_solution_ith {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) (t : A) i := ivp_solution_i (analytic_poly p y0) i t.

   Definition pivp_solution_ith_max {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) i := ivp_solution_i_max (analytic_poly p y0) i.

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
Context `{ArchimedeanField}.
Definition make_poly  d (p : PolyExpr)  : (@mpoly A d).
Proof.
  induction p.
  - apply (const_to_mpoly d (embedQ q)).
  - apply (poly_comp1 n).
  - apply (IHp1 + IHp2).
  - apply (IHp1 + (opp 1) [*]IHp2).
  - apply ((opp 1) [*]IHp).
  - apply (IHp1 * IHp2).
  - apply (npow IHp n).
Defined.
Definition vecp  {e} d  (p : PolyExpr^e)  : (@mpoly A d)^e := tuple_map (make_poly d) p.

Record PIVP  {d} := {
    pf : A{x^d}^d;
    py0 : A^d
  }.

Definition convert_pivp {d} (ivp : APIVP (d :=d)) : PIVP (d:=d) := {|
pf := vecp d ivp.(ivp_rhs);
py0 := tuple_map embedQ ivp.(ivp_y0);
 |}.

End MakeIVP.
