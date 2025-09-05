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

  Definition approx' {d} (p : @mpoly A (S d)^(S d))  (t : A)  ( i n : nat) : A :=  (eval_poly (poly_taylor p n i)  t) .

  Definition approx_pivp_raw {d} (p : PIVP (d:=(S d))) (t : A) (n : nat) : A^(S d) := let p' := shift_mpoly p.(pf) p.(py0)  in (proj1_sig (seq_to_tuple (def := 0) (fun i => approx' p'  t  i n) (S d)))+p.(py0).

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



   Lemma poly_to_ps_eval {d} (q : A{x^d}) :  poly_to_ps q 0 == q.[0].
   Proof.
     induction d.
     simpl;reflexivity.
     rewrite vec0_cons.
     rewrite poly_to_ps_cons.
     rewrite IHd.
     rewrite vec0_cons.
     rewrite eval_tuple_cons_simpl.
     unfold eval_mpoly.
     rewrite const_to_mpoly_zero.
     destruct q.
     simpl.
     reflexivity.
     simpl.
     rewrite mulC, mul0,add0.
     reflexivity.
   Qed.
   #[global] Instance poly_to_ps_proper {d}: Proper (SetoidClass.equiv ==> SetoidClass.equiv )  (poly_to_ps (d:=d)).
   Proof.
     intros a b eq.
     induction d.
     simpl;auto.
     simpl.
     intros k.
     destruct (destruct_tuple_cons k) as [k0 [kt ->]].
     apply IHd.
     apply eq.
   Defined.
   Lemma tuple_cons_destruct {A0 d} k0 (k : A0^d) : destruct_tuple_cons (tuple_cons k0 k) = existT _ k0 (exist _ k eq_refl).
   Proof.

     destruct (destruct_tuple_cons (tuple_cons k0 k)) as [k0' [kt' P]].
     destruct (tuple_cons_ext _ _  _ _ P) as [-> ->].
     f_equal.
     apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
     reflexivity.
  Qed.

   Lemma deriv_rec_0 {d e} (k : nat^e) : Dx[k] (0 : A{x^d}) == 0.
   Proof.
     enough (forall i, derive_rec_helper i (0 : A{x^d}) k == (0 : A{x^d})).
     {
        unfold derive_rec.
        apply H1.
     }
     induction e;intros.
     simpl;reflexivity.
     destruct (destruct_tuple_cons k) as [k0 [kt ->]].
     rewrite derive_rec_helper_next.
     rewrite nth_derivative_proper.
     2: apply IHe.
     induction k0.
     simpl.
     reflexivity.
     rewrite nth_derivative_S.
     simpl.
     rewrite poly_pdiff0.
     apply IHk0.
   Qed.

   Lemma deriv_rec_ntimes {d} (p : A{x^d}) (k : nat^d) n : (Dx[k] (ntimes n p)) == ntimes n (Dx[k] p).
   Proof.
     induction n.
     simpl.
     apply deriv_rec_0.
     simpl ntimes.
     rewrite derive_rec_plus.
     rewrite IHn.
     reflexivity.
  Qed.
   
   Lemma ntimes_eval {d} (p : A{x^d}) n x : (ntimes n p).[x] == ntimes n (p.[x]).
   Proof.
     induction n.
     simpl.
     rewrite zero_poly_eval.
     reflexivity.
     simpl.
     rewrite mpoly_add_spec.
     rewrite IHn.
     reflexivity.
   Qed.

   Lemma nth_derivative_0 {d} (p : A{x^d}) i : nth_derivative i p 0 == p.
   Proof.
     simpl;reflexivity.
   Qed.

   Lemma poly_eval_0 {d} (p : A{x^S d}) : p.{0} == nth 0 p 0.
   Proof.
     destruct p.
     simpl.
     setoid_rewrite nil_eval;reflexivity.
     simpl.
     unfold eval_mpoly.
     simpl.
     rewrite const_to_mpoly_zero.
     rewrite mulC,mul0,add0.
     reflexivity.
   Qed.
   Lemma pdiff_nth0 {d} (p : A{x^S d}) i :   D[i] (nth 0 p 0) == nth 0 (D[S i] p) 0. 
   Proof.
     destruct p.
     simpl.
     setoid_rewrite poly_pdiff0.
     reflexivity.
     simpl.
     reflexivity.
   Qed.
   Lemma nth_derivative_nth0 {d} (p : A{x^S d}) i k :   nth_derivative i (nth 0 p 0) k == nth 0 (nth_derivative (S i) p k) 0. 
   Proof.
     induction k.
     simpl;reflexivity.
     rewrite nth_derivative_S.
     rewrite nth_deriv_independent.
     rewrite IHk.
     rewrite pdiff_nth0.
     apply nth_proper_list.
     rewrite nth_derivative_S.
     rewrite nth_deriv_independent.
     reflexivity.
   Qed.
   Lemma derive_rec_helper_nth0 {d e} (p : A{x^S d}) (k : nat^e) i :   (derive_rec_helper i (nth 0 p 0) k) == nth 0 (derive_rec_helper (S i) p k) 0. 
   Proof.
     revert i.
     induction e;intros.
     simpl;reflexivity.
     destruct (destruct_tuple_cons k) as [k0 [kt ->]].
     rewrite !derive_rec_helper_next.
     rewrite nth_derivative_proper.
     2: apply IHe.
     apply nth_derivative_nth0.
  Qed.    

   Lemma nth_derivative_poly_spec (p : A{x^1}) k : nth 0 (nth_derivative 0 p k) 0 == [k]! *  (nth k p 0).
   Proof.
     revert p.
     induction k;intros.
     simpl;ring.
     rewrite nth_proper_list.
     2: apply nth_derivative_S.
     rewrite IHk.
     simpl (D[_]_).
     rewrite derive_poly_nth.
     rewrite ntimes_spec, <-mulA.
     apply ring_eq_mult_eq;try reflexivity.
     simpl.
     rewrite mulC.
     reflexivity.
   Qed.
   Lemma fun_ps_poly_ps {d} (p : A{x^S d}) : poly_to_ps p == fun_ps p (y0 := 0) (in_dom := poly_tot 0).
   Proof.
      intros k.
      enough (poly_to_ps p k == t![k] * (Dx[k] p).[0]).
      {
        rewrite H1.
        unfold fun_ps.
        reflexivity.
      }

      induction d.
      simpl.
      destruct (destruct_tuple_cons k) as [k0 [kt ->]].
      unfold derive_rec.
      simpl.
      rewrite tuple_cons_destruct.
      rewrite poly_eval_0.
      rewrite nth_derivative_poly_spec.
      rewrite mul1, <-mulA,(mulC ![k0]), fact_invfact, mulC,mul1.
      reflexivity.
      destruct (destruct_tuple_cons k) as [k0 [kt ->]].
      rewrite poly_to_ps_cons.
      rewrite IHd.

      enough ((Dx[ tuple_cons k0 kt] p) .[0] == [k0]! * ((Dx[kt] ((nth k0 p 0) : A{x^(S d)}))).[0]).
      {
        rewrite H1.
        rewrite <-mulA.
        apply ring_eq_mult_eq;try reflexivity.
        rewrite inv_factt_cons.
        rewrite mulC,<-mulA.
        rewrite fact_invfact.
        ring.
      }
      generalize dependent p.
      induction k0;intros.
      - unfold derive_rec.
        rewrite derive_rec_helper_next.
        simpl factorial.
        ring_simplify.
        rewrite nth_derivative_0.
        rewrite vec0_cons.
        rewrite eval_tuple_cons_simpl.
        rewrite poly_eval_0.
        rewrite derive_rec_helper_nth0.
        reflexivity.
      - rewrite <-deriv_rec_next.
        rewrite IHk0.
        setoid_rewrite derive_poly_nth.
        rewrite deriv_rec_ntimes.
        rewrite ntimes_eval.
        rewrite ntimes_spec.
        rewrite <-mulA.
        apply ring_eq_mult_eq; try reflexivity.
        simpl;ring.
    Qed.
        (*         Search nth_derivative (_ :: _). *)
(*         simpl. *)
(*         ring. *)
(*         destruct p. *)
(*         simpl. *)
(*         ring. *)
(*         rewrite idx_index, (idx_index (poly_to_ps _)).  *)
(*         Search (Dx[_] _). *)
(*          rewrite ps_derive_spec. *)
(*          rewrite P. *)
(*          simpl. *)
(*          rewrite E. *)
(*         ring_simplify. *)

(*       induction n. *)
(*       - intros. *)
(*         apply order_zero_eq_zero in H1. *)
(*         rewrite H1 at 2. *)
(*         rewrite inv_factt0. *)
(*         rewrite idx_index, (idx_index (poly_to_ps _)).  *)
(*         rewrite H1. *)
(*         rewrite derive_rec_0. *)
(*         ring. *)
(*      - intros. *)
(*        destruct (tuple_pred_spec' k); try (simpl in *;lia). *)
(*         rewrite idx_index, (idx_index (poly_to_ps _)).  *)
(*         rewrite H3. *)
(*         rewrite <-!idx_index. *)
(*         rewrite deriv_next_backward_full. *)
(*       rewrite ps_property_backwards. *)
(*       apply ring_eq_mult_eq;try reflexivity. *)
      
(*       revert k. *)
(* - *)
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
     unfold solution_rinv.
     apply inv_approx_pos.
     unfold analytic_solution_r.
     rewrite mulA.
     setoid_replace 1 with (1 * (1 *1)) by ring.
     apply mul_le_le_compat_pos;[|rewrite mul1| |apply mul_le_le_compat_pos];try apply le_0_1.
     - setoid_replace 1 with (# 1) by (setoid_rewrite ntimes_embed;simpl;ring).
       apply ntimes_monotone;lia.
    - apply (M_pos (in_dom := poly_tot y0)).
    - apply (r_pos (in_dom := poly_tot y0)).
   Qed.
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


   Lemma eval_poly_sum (p : poly) (x : A): eval_poly p x == sum (fun i => (nth i p 0) * npow x i ) (length p). 
   Proof.
     induction p.
     simpl.
     reflexivity.
     unfold eval_poly2.
     simpl.
     rewrite sum_S_fun.
     rewrite IHp.
     apply ring_eq_plus_eq;try (simpl;ring).
     rewrite sum_mult.
     apply sum_ext.
     intros.
     simpl.
     ring.
   Qed.

   Lemma poly_taylor_length {d}  (p : (mpoly (S d) (A := A))^(S d))  i n : (length (poly_taylor p n i)) = n+1.
   Proof.
   unfold poly_taylor.
   induction n.
   simpl;lia.
   simpl.
   rewrite length_app.
   simpl.
   rewrite IHn.
   simpl;lia.
   Qed.
   Lemma Fi_to_taylor_length {d} (l : list (@mpoly A (S d))) : length (Fi_to_taylor l) == length l.
   Proof.
     induction l.
     simpl;reflexivity.
     simpl.
     rewrite length_app.
     rewrite IHl;simpl.
     lia.
   Qed.

   Lemma Fi_to_taylor_cons {d} (a : @mpoly A (S d)) (l : list (@mpoly A (S d))) : (Fi_to_taylor (a :: l)) = Fi_to_taylor l ++ [inv_fact (length l) * poly_to_ps a 0].
   Proof.
    rewrite <-Fi_to_taylor_length.
    simpl.
    reflexivity.
  Qed.

   Lemma Fi_to_taylor_nth {d} (l : list (@mpoly A (S d))) i : i< length l -> nth i (Fi_to_taylor l) 0 ==  inv_fact i * (poly_to_ps (nth i (rev l) 0) 0).
   Proof.
     intros.
     induction l.
     simpl in H2.
     lia.
     rewrite Fi_to_taylor_cons.
     simpl in H2.
     assert (i < length l \/ i = length l)%nat by (simpl;lia).
     destruct H3.
     -  rewrite app_nth1;[|rewrite Fi_to_taylor_length;auto].
        simpl rev.
        rewrite app_nth1; [|rewrite length_rev;auto].
        apply IHl;auto.
     -  rewrite H3.
        rewrite <-Fi_to_taylor_length, nth_middle, Fi_to_taylor_length.
        simpl rev.
        rewrite <-length_rev, nth_middle, length_rev;auto.
        reflexivity.
   Qed.

   Lemma Fi_length {d} (p : @mpoly A (S d) ^ (S d)) n i : length (Fi p n i) = S n.
   Proof.
     induction n.
     reflexivity.
     simpl.
     setoid_rewrite IHn.
     lia.
   Qed.

  Lemma Fi_to_taylor_Fi_nth {d} (p : @mpoly A (S d) ^ (S d)) n i n0 : n0< S n -> nth n0 (Fi_to_taylor (Fi p n i)) 0 ==  inv_fact n0 * (poly_to_ps (nth (n-n0)%nat (Fi p n i) 0) 0).
    Proof.
      intros.
      rewrite Fi_to_taylor_nth;[|rewrite Fi_length;auto].
      rewrite rev_nth; [|rewrite Fi_length;auto].
      rewrite Fi_length.
      replace (S n - S n0)%nat with (n - n0)%nat by lia.
      reflexivity.
   Qed.
   Local Lemma inv_fact_inv_factorial (n : nat) : inv_fact n == ![n].
   Proof.
    induction n.
    reflexivity.
    simpl.
    rewrite IHn.
    unfold inject_nat_inv.
    rewrite Pos.of_nat_succ.
    apply ring_eq_mult_eq;try reflexivity.
   Qed.


   Lemma Fi_nth {d} (p : @mpoly A (S d) ^ (S d)) n i n0 : n0 < S n -> nth (n - n0) (Fi p n i) 0 == ode.Fi p n0 i.
  Proof.
  generalize dependent n0.
   induction n.
   - intros.
     replace (n0)%nat with 0%nat by lia.
     simpl.
     reflexivity.
   - intros.
     assert (n0 < S n \/ n0 = S n)%nat by lia.
     simpl Fi.
     destruct H3.
     +  replace (S n - n0)%nat with (S (n - n0))%nat by lia.
        rewrite nth_S.
        apply IHn;auto.
     +  rewrite H3.
        replace (S n - S n)%nat with 0%nat by lia.
        simpl nth.
        simpl ode.Fi.
        apply sum_ext.
        intros.
        apply mult_poly_proper; try reflexivity.
        replace (hd [] (Fi p n i)) with (nth 0 (Fi p n i) 0) by (destruct (Fi p n i);reflexivity).
        apply (mpoly_pdiff_proper (S d) n1).
        replace 0%nat with (n-n)%nat by lia.
        apply IHn;lia.
  Qed.

   Lemma approx_approx' {d}  (p : (mpoly (S d) (A := A))^(S d)) y0  t i n : approx' (shift_mpoly p y0) t i n == approx (analytic_poly p y0) t i n.
   Proof.
     unfold approx', approx, partial_sum.
     rewrite eval_poly_sum.
     rewrite poly_taylor_length.
     apply sum_ext.
     intros.
     apply ring_eq_mult_eq; try reflexivity.
     unfold to_ps, poly_taylor, analytic_solution_ps.
     rewrite Fi_to_taylor_Fi_nth, inv_fact_inv_factorial;try lia.
     apply ring_eq_mult_eq; try reflexivity.
     rewrite poly_to_ps_eval.
     simpl eval0.
     replace (eval0 (ode.Fi (shift_mpoly p y0) n0 i)) with ((ode.Fi (shift_mpoly p y0) n0 i).[0]) by reflexivity.
     rewrite Fi_nth;[reflexivity|lia].
   Qed.    

   Definition pivp_solution_ith_max_analytic {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) i := let s := ivp_solution_i_max (analytic_poly p y0) i in (fst s, snd s + y0\_i).
   Definition pivp_r_max {d}  (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) := inv2 * (inv_approx (# (2*(S d)) * (poly_M (d:=d) p y0)  * (poly_r (d:=S d) p y0))).

   Lemma pivp_r_max_spec {d} p y0 : pivp_r_max (d:=d) p y0 == ivp_r_max (analytic_poly p y0).
   Proof.
   unfold pivp_r_max, ivp_r_max, solution_rinv, analytic_solution_r.
   apply ring_eq_mult_eq;try reflexivity.
  Qed.

   Lemma fast_cauchy_approx' {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d))   (i : nat) t : (i <= d)%nat -> abs t <= (pivp_r_max p y0)  -> fast_cauchy_neighboring (approx' (shift_mpoly p y0) t i).
   Proof.
     intros.
     intros m.
     rewrite !approx_approx'.
     apply fast_cauchy_neighboring_approx;try lia.
     apply (le_trans _ _ _ H3).
     apply le_refl.
   Qed.

   Definition pivp_solution_i {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d))   (i : nat) t  :  abs t <= (pivp_r_max p y0)  -> A.
   Proof.
     intros.
     destruct (le_lt_dec i d); [|apply 0].
     apply (proj1_sig (has_limit (approx' (shift_mpoly p y0) t i) (fast_cauchy_approx' p y0 i t l H2))).
   Defined.

   Lemma abs_le_pivpr {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) :  (abs (pivp_r_max p y0) <= pivp_r_max p y0).
     Proof.
       rewrite !pivp_r_max_spec.
       rewrite abs_pos;try apply le_refl.
       apply mul_pos_pos.
       apply inv2_pos.
       apply solution_r_pos.
    Qed.

   Definition pivp_solution_i_max {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d))  (i : nat)  : A := (pivp_solution_i p y0 i (pivp_r_max p y0) (abs_le_pivpr p y0))+y0\_i.

   Definition pivp_solution_max {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) :  (A * ( A^(S d))).
   Proof.
     destruct (seq_to_tuple ((fun i => pivp_solution_i_max p y0 i)) (S d) (def := 0)).
     apply ((pivp_r_max p y0) , x).
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
