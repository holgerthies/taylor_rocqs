(**
   * Correctness of the interval version of the PIVP solver

   The solver in [pivp.v] is generic in the arithmetic: it only uses the
   operations of a [RawFieldOps] structure.  [iode.v] instantiates it with
   floating point intervals ([interval.v]); that instantiation is what is
   actually executed by [itraj] / [plot_trajectory], and nothing was proved
   about it.

   A correctness result should say: *the boxes printed by the interval solver
   contain the solution of the initial value problem*.  This is what is proved
   here.  The development is in three layers:

   - [polyrel.v] : a relation between two arithmetics that is compatible with
     the ring operations, lifted to polynomials and tuples.  Every operation
     the algorithm performs preserves it.
   - [taylor_correct.v] : the algorithm executed in exact real arithmetic is
     correct - its symbolic derivatives are the derivatives of the solution and
     its Taylor step differs from the solution by the Lagrange remainder.
   - this file : the interval instantiation encloses the exact one, hence the
     printed boxes enclose the solution.

   Main results
   ------------
   - [taylor_step_sound] : the interval Taylor step encloses the Taylor step of
     the same algorithm executed in exact real arithmetic.
   - [cont_add_error] : widening by the reported error term is sound (no
     assumption on the error being finite: [Fnan] widens to all of [R]).
   - [step_admissible] : the step size the interval solver computes contains a
     time increment that is admissible for the exact algorithm.  (The interval
     [max] of [interval.v] is an upper bound rather than an enclosure, so the
     step size is *not* an enclosure of the exact step size; what holds - and
     what is proved here - is that the interval [poly_M] dominates the exact
     one.)
   - [interval_step_correct] : one step maps an enclosure of the solution at
     [t0] to an enclosure of the solution at [t0 + h].
   - [interval_trajectory_correct] : every box of a trajectory encloses the
     solution at some time enclosed by the box's time component ([encloses_at]).
     Apart from the input enclosures this needs *only* [taylor_step_accurate],
     i.e. a statement about the exact algorithm, and that the steps stay inside
     the interval on which the solution exists; nothing about intervals is
     assumed.
   - [interval_trajectory_correct_of_remainder] : the same theorem with the
     more concrete Lagrange-remainder hypothesis [remainder_bounded].
   - [pcont_Q2Ipoly], [tcont_inject_Q], [cont_singleton] discharge the input
     hypotheses for rational IVPs, so the theorems are not vacuous.

   Solutions are required to exist only on an open interval [(a,b)]
   ([is_pivp_solution_on]); polynomial systems can blow up in finite time, so a
   global requirement would make the statements vacuous exactly for the systems
   where enclosures matter most.  Consequently the iteration theorems also
   assume that a step which is admissible for the exact algorithm does not
   leave [(a,b)] - i.e. the solver is not asked to step past the end of the
   solution.

   What is still assumed
   ---------------------
   - [taylor_step_accurate] (from [taylor_correct.v]): the Taylor step of the
     *exact* algorithm approximates the solution within the error term the
     algorithm reports.  By [taylor_step_lagrange] this is equivalent to a
     bound on one derivative along the step ([remainder_bounded]); that bound
     is the analytic content of the method (it is where the majorant estimates
     of [odebounds.v] / [realanalytic.v] would be used) and is not proved here.
     It mentions no intervals: it is a property of the algorithm of [pivp.v]
     over the reals, needed for the exact solver just as much.
   - The old float-time trajectory code in [iode.v] accumulates times with
     [F.add_DN] and reports them as point intervals.  The theorem below avoids
     that bookkeeping issue altogether: [interval_trajectory] now carries time
     as an interval internally.
*)
Require Import interval iode pivp algebra archimedean polynomial tuple.
Require Import taylor_correct polyrel.
From Coq Require Import Reals QArith Qreals Psatz.
From Coq Require Import List.
From Interval Require Import Interval.Float.
Require Import Interval.Real.Xreal.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Import ListNotations.
Local Close Scope Q_scope.

(** The reals as a [RawFieldOps] structure, the generic Taylor step, the
    notion of solution of a polynomial IVP and the accuracy statement for the
    exact algorithm all come from [taylor_correct.v]. *)

Module IntervalSolverCorrect (params : IIVP_PARAMS).

  Module Solver := IIVP params.
  Close Scope Q_scope.
  Open Scope algebra_scope.

  (** * Enclosures *)

  (** [cont i x] : the interval [i] encloses the real number [x]. *)
  Definition cont (i : I) (x : R) : Prop := Interval.contains (FI.convert i) (Xreal x).

  Lemma cont_add i j x y : cont i x -> cont j y -> cont (i + j) (x + y).
  Proof. intros; apply (FI.add_correct _ _ _ (Xreal x) (Xreal y));auto. Qed.

  Lemma cont_mul i j x y : cont i x -> cont j y -> cont (i * j) (x * y).
  Proof. intros; apply (FI.mul_correct _ _ _ (Xreal x) (Xreal y));auto. Qed.

  Lemma cont_opp i x : cont i x -> cont (opp i) (opp x).
  Proof. intros; apply (FI.neg_correct _ (Xreal x));auto. Qed.

  Lemma cont_zero : cont 0 0.
  Proof. apply Solver.FI.Z2I_spec. Qed.

  Lemma cont_one : cont 1 1.
  Proof. apply (Solver.FI.Z2I_spec 1). Qed.

  Lemma cont_injectQ q : cont (inject_Q q) (inject_Q q).
  Proof. apply Solver.FI.Q2I_spec. Qed.

  (** * Enclosures for polynomials and tuples

      [cont] is compatible with the ring operations, so all of [polyrel.v]
      applies: [mrel d] is the enclosure relation on [d]-variate polynomials,
      [trel] on tuples and [ptrel] on tuples of polynomials. *)

  #[local] Instance cont_RingRel : @RingRel I R _ _ _ _ :=
    {| rrel := cont;
       rrel_zero := cont_zero;
       rrel_one := cont_one;
       rrel_add := fun a b a' b' H1 H2 => cont_add a b a' b' H1 H2;
       rrel_mul := fun a b a' b' H1 H2 => cont_mul a b a' b' H1 H2 |}.

  Notation pcont := (@mrel I R _ _ _ _ cont_RingRel).
  Notation tcont := (@trel I R _ _ _ _ cont_RingRel).
  Notation ptcont := (@ptrel I R _ _ _ _ cont_RingRel).

  (** ** The Taylor coefficients *)

  Lemma cont_inv_fact n : cont (inv_fact n) (inv_fact n).
  Proof.
    induction n;simpl;[apply cont_one|].
    apply cont_mul;[apply cont_injectQ|apply IHn].
  Qed.

  Lemma cont_inv_fact_eq n m : n = m -> cont (inv_fact n) (inv_fact m).
  Proof. intros ->;apply cont_inv_fact. Qed.

  Definition fcont {d} (F : tuple (S d) (list (@mpoly I (S d)))) (f : tuple (S d) (list (@mpoly R (S d)))) :=
    forall i, (i < S d)%nat -> pcont (S (S d)) (tuple_nth i F 0) (tuple_nth i f 0).

  Lemma pcont_Fi_to_taylor' d (L : list (@mpoly I (S d))) (l : list (@mpoly R (S d))) (Y0 : I^(S d)) (y0 : R^(S d)) :
    pcont (S (S d)) L l -> tcont Y0 y0 -> pcont 1 (pivp.Fi_to_taylor' L Y0) (pivp.Fi_to_taylor' l y0).
  Proof.
    intros H HY.
    simpl in H.
    induction H as [|L0 l0 L' l' HL0 HL IH].
    - constructor.
    - rewrite (Fi_to_taylor'_cons (A:=I) (d:=d) L0 L' Y0).
      rewrite (Fi_to_taylor'_cons (A:=R) (d:=d) l0 l' y0).
      rewrite (Fi_to_taylor'_length (A:=I) (d:=d) L' Y0), (Fi_to_taylor'_length (A:=R) (d:=d) l' y0).
      apply Forall2_app;[exact IH|].
      constructor;[|constructor].
      apply cont_mul;[apply cont_inv_fact_eq;apply (Forall2_length HL)|apply (rrel_eval_tuple (RR:=cont_RingRel));auto].
  Qed.

  Lemma pcont_Fi d (P : (@mpoly I (S d))^(S d)) (p : (@mpoly R (S d))^(S d)) :
    ptcont P p -> forall n i, pcont (S (S d)) (pivp.Fi P n i) (pivp.Fi p n i).
  Proof.
    intros HP n i.
    induction n.
    - rewrite (Fi_0 (A:=I) (d:=d) P i), (Fi_0 (A:=R) (d:=d) p i).
      constructor;[apply (mrel_poly_comp1 (S d))|constructor].
    - rewrite (Fi_S (A:=I) (d:=d) P n i), (Fi_S (A:=R) (d:=d) p n i).
      constructor;[|exact IHn].
      apply (mrel_sum (S d));intros j.
      apply (mrel_mul (S d));[apply ptrel_nth;auto|].
      apply mrel_pdiff.
      apply (mrel_hd (S d));exact IHn.
  Qed.

  Lemma fcont_pivp_F d (P : (@mpoly I (S d))^(S d)) (p : (@mpoly R (S d))^(S d)) n :
    ptcont P p -> fcont (pivp_F P n) (pivp_F p n).
  Proof.
    intros HP i Hi.
    unfold pivp_F.
    rewrite (proj2_sig (seq_to_tuple (pivp.Fi P n) (S d)) i Hi).
    rewrite (proj2_sig (seq_to_tuple (pivp.Fi p n) (S d)) i Hi).
    apply pcont_Fi;auto.
  Qed.

  (** ** Soundness of the Taylor step *)

  Lemma taylor_step_sound d (F : tuple (S d) (list (@mpoly I (S d)))) (f : tuple (S d) (list (@mpoly R (S d)))) (Y0 : I^(S d)) (y0 : R^(S d)) T t :
    fcont F f -> tcont Y0 y0 -> cont T t -> tcont (taylor_step F Y0 T) (taylor_step f y0 t).
  Proof.
    intros HF HY HT i Hi.
    unfold taylor_step.
    rewrite (proj2_sig (seq_to_tuple (fun i => eval_poly (pivp.Fi_to_taylor' (tuple_nth i F 0) Y0) T) (S d)) i Hi).
    rewrite (proj2_sig (seq_to_tuple (fun i => eval_poly (pivp.Fi_to_taylor' (tuple_nth i f 0) y0) t) (S d)) i Hi).
    apply (mrel_eval_poly 0);auto.
    apply pcont_Fi_to_taylor';auto.
  Qed.


  (** ** Widening an enclosure by the reported error bound

      The interval solver adds the (upper bound of the) error term to every
      component of the computed value.  We show that this widens an enclosure
      of [x] to an enclosure of every real within that bound of [x].  A float
      bound of [Fnan] denotes no information (+infinity) and then the widened
      interval is all of [R], so nothing has to be assumed about the error
      term being finite. *)

  (** the floats of this implementation are never -infinity, so the validity
      side conditions of the coq-interval bound constructors always hold *)
  Lemma valid_ub_all (e : F) : FI.F.valid_ub e = true.
  Proof. destruct e;vm_compute;reflexivity. Qed.

  Lemma valid_lb_all (e : F) : FI.F.valid_lb e = true.
  Proof. destruct e;vm_compute;reflexivity. Qed.

  (** [err_le e v] : [v] is below the error bound denoted by the float [e] *)
  Definition err_le (e : F) (v : R) : Prop :=
    match FI.F.toX e with Xnan => True | Xreal E => (v <= E)%R end.

  Lemma err_le_trans e v w : (v <= w)%R -> err_le e w -> err_le e v.
  Proof. unfold err_le;destruct (FI.F.toX e);auto;lra. Qed.

  Lemma err_le_pos e v : (0 <= v)%R -> err_le e v -> err_le e 0%R.
  Proof. intros;apply (err_le_trans _ _ v);auto. Qed.

  Lemma cont_bnd_zero_up (e : F) a :
    (0 <= a)%R -> err_le e a -> Interval.contains (FI.convert (FI.bnd FI.F.zero e)) (Xreal a).
  Proof.
    unfold err_le;intros Ha He.
    rewrite (FI.bnd_correct _ _ (valid_lb_all _) (valid_ub_all _)).
    rewrite FI.F.zero_correct.
    destruct (FI.F.toX e);simpl;(split;[lra|auto]).
  Qed.

  Lemma cont_bnd_down_zero (e : F) b :
    (b <= 0)%R -> err_le e (-b)%R -> Interval.contains (FI.convert (FI.bnd (FI.F.sub_DN Solver.FI.prec 0 e) FI.F.zero)) (Xreal b).
  Proof.
    unfold err_le;intros Hb He.
    destruct (FI.F.sub_DN_correct Solver.FI.prec 0 e (valid_lb_all _) (valid_ub_all _)) as [Hv Hle].
    rewrite (FI.bnd_correct _ _ Hv (valid_ub_all _)).
    rewrite FI.F.zero_correct.
    assert (FI.F.toX (0 : FI.F.type) = Xreal 0) as Hz by (exact (SFBI2.fromZ_correct' 0)).
    unfold Basic.le_lower, Basic.le_upper in Hle.
    rewrite Hz in Hle.
    destruct (FI.F.toX (FI.F.sub_DN Solver.FI.prec 0 e)) as [|r];simpl;[split;auto;lra|].
    destruct (FI.F.toX e) as [|E];simpl in Hle;[contradiction|].
    split;simpl;lra.
  Qed.

  Lemma cont_F2err (e : F) w : err_le e (Rabs w) -> cont (Solver.FI.F2err e) w.
  Proof.
    intros He.
    pose proof (Rabs_pos w) as Hp0.
    unfold Solver.FI.F2err, cont.
    destruct (Rle_dec 0 w) as [Hp|Hp].
    - replace (Xreal w) with (Xbind2 (fun x y => Xreal (x+y)) (Xreal w) (Xreal 0)) by (simpl;f_equal;lra).
      apply FI.add_correct.
      + apply cont_bnd_zero_up;auto.
        apply (err_le_trans _ _ (Rabs w));[rewrite Rabs_right;lra|auto].
      + apply cont_bnd_down_zero;[lra|].
        apply (err_le_trans _ _ (Rabs w));[lra|auto].
    - replace (Xreal w) with (Xbind2 (fun x y => Xreal (x+y)) (Xreal 0) (Xreal w)) by (simpl;f_equal;lra).
      apply FI.add_correct.
      + apply cont_bnd_zero_up;[lra|].
        apply (err_le_trans _ _ (Rabs w));[lra|auto].
      + apply cont_bnd_down_zero;[lra|].
        apply (err_le_trans _ _ (Rabs w));[rewrite Rabs_left;lra|auto].
  Qed.

  Lemma cont_add_error (e : F) i x z :
    cont i x -> err_le e (Rabs (z - x)) -> cont (Solver.FI.add_error e i) z.
  Proof.
    intros Hi Hz.
    unfold Solver.FI.add_error, cont.
    replace (Xreal z) with (Xbind2 (fun a b => Xreal (a+b)) (Xreal x) (Xreal (z - x))) by (simpl;f_equal;lra).
    apply FI.add_correct;auto.
    apply cont_F2err;auto.
  Qed.

  (** the upper bound of an enclosure of [x] is an error bound for [x] *)
  Lemma cont_upper (i : I) x : cont i x -> err_le (FI.upper i) x.
  Proof.
    intros Hi;unfold err_le.
    destruct (FI.F.toX (FI.upper i)) as [|U] eqn:Hu;auto.
    assert (Interval.not_empty (FI.convert i)) as Hne by (exists x;auto).
    rewrite (FI.upper_correct _ Hne) in Hu.
    unfold cont in Hi.
    destruct (FI.convert i);simpl in Hu;[discriminate|].
    destruct u;[discriminate|].
    injection Hu as ->.
    apply Hi.
  Qed.

  Lemma tcont_add_errort {e} (er : F) (Y : I^e) (y z : R^e) :
    tcont Y y ->
    (forall i, (i < e)%nat -> err_le er (Rabs (tuple_nth i z 0 - tuple_nth i y 0))) ->
    tcont (Solver.FI.add_errort er Y) z.
  Proof.
    intros HY Hz i Hi.
    unfold Solver.FI.add_errort.
    rewrite (tuple_map_nth (Solver.FI.add_error er) Y i 0 0);auto.
    apply (cont_add_error er _ (tuple_nth i y 0));[apply HY;auto|apply Hz;auto].
  Qed.

  (** ** The error term *)

  Lemma cont_inject_nat n : cont (inject_nat n) (inject_nat n).
  Proof. apply cont_injectQ. Qed.

  Lemma cont_npow X x k : cont X x -> cont (npow X k) (npow x k).
  Proof.
    intros;induction k;simpl;[apply cont_one|apply cont_mul;auto].
  Qed.

  (** * Soundness of one step of the interval solver *)

  Lemma interval_step_fst {d} P (Y0 : I^(S d)) T0 o f :
    fst (Solver.interval_step (d:=d) P Y0 T0 o f) = T0 + approx_pivp_step_size P Y0 (singleton f).
  Proof. reflexivity. Qed.

  Lemma interval_step_snd {d} P (Y0 : I^(S d)) T0 o f :
    snd (Solver.interval_step (d:=d) P Y0 T0 o f)
    = Solver.FI.add_errort (FI.upper (snd (approx_pivp_step' P Y0 (pivp_F P o) (singleton f) o)))
                           (taylor_step (pivp_F P o) Y0 (approx_pivp_step_size P Y0 (singleton f))).
  Proof. reflexivity. Qed.

  (** The interval solver's step: if [Y0] encloses the state [y t0] of a
      solution [y] at time [t0], if [T0] encloses [t0], and if [h] is a time
      increment that is
        - enclosed by the step size the interval solver computed, and
        - admissible for the exact algorithm at [y t0],
      then the box returned by [interval_step] encloses [(t0+h, y (t0+h))]. *)
  Theorem interval_step_correct {d}
    (PI : (@mpoly I (S d))^(S d)) (pR : (@mpoly R (S d))^(S d))
    (Y0 : I^(S d)) (T0 : I) (factor : F) (sf : R)
    (y : R -> R^(S d)) (a b t0 h : R) :
    ptcont PI pR ->
    is_pivp_solution_on a b pR y ->
    taylor_step_accurate a b pR params.order sf ->
    tcont Y0 (y t0) -> cont T0 t0 ->
    cont (singleton factor) sf ->
    cont (approx_pivp_step_size PI Y0 (singleton factor)) h ->
    (a < t0)%R -> (t0 + h < b)%R ->
    (0 <= h)%R -> (h <= approx_pivp_step_size pR (y t0) sf)%R ->
    cont (fst (Solver.interval_step PI Y0 T0 params.order factor)) (t0 + h)%R
    /\ tcont (snd (Solver.interval_step PI Y0 T0 params.order factor)) (y (t0 + h)%R).
  Proof.
    intros Hp Hsol Hacc HY HT Hsf Hh Ha Hb Hh0 Hadm.
    split.
    - rewrite interval_step_fst.
      apply cont_add;auto.
    - rewrite interval_step_snd.
      apply (tcont_add_errort _ _ (taylor_step (pivp_F pR params.order) (y t0) h)).
      + apply taylor_step_sound;auto.
        apply fcont_pivp_F;auto.
      + intros i Hi.
        apply (err_le_trans _ _ (snd (approx_pivp_step' pR (y t0) (pivp_F pR params.order) sf params.order)));
          [apply Hacc;auto|].
        apply cont_upper.
        rewrite !step_error_spec.
        apply cont_mul;[apply cont_inject_nat|apply cont_npow;auto].
  Qed.


  (** * The step size chosen by the interval solver is admissible

      The interval [max] of [interval.v] is not an enclosure but an upper bound
      (it returns the point [singleton (max (upper x) (upper y))]), so neither
      [poly_M] nor the step size computed from it is an enclosure of its exact
      counterpart.  What does hold is that the interval [poly_M] *dominates* the
      exact one, and that suffices: the computed step interval then contains a
      time increment which is admissible for the exact algorithm, which is all
      the correctness proof needs. *)

  Lemma cont_singleton (f : F) (v : R) : FI.F.toX f = Xreal v -> cont (singleton f) v.
  Proof.
    intros Hf.
    unfold cont, singleton.
    rewrite (FI.bnd_correct _ _ (valid_lb_all _) (valid_ub_all _)), Hf;simpl;lra.
  Qed.

  Lemma cont_singleton_nan (f : F) : FI.F.toX f = Xnan -> forall x, cont (singleton f) x.
  Proof.
    intros Hf x.
    unfold cont, singleton.
    rewrite (FI.bnd_correct _ _ (valid_lb_all _) (valid_ub_all _)), Hf;simpl;auto.
  Qed.

  Lemma max_I_spec (i j : I) : max i j = singleton (FI.F.max (FI.upper i) (FI.upper j)).
  Proof. reflexivity. Qed.

  (** [dom i x] : the interval [i] contains a point above [x] *)
  Definition dom (i : I) (x : R) := exists u, cont i u /\ (x <= u)%R.

  Lemma dom_cont i x : cont i x -> dom i x.
  Proof. intros;exists x;split;auto;lra. Qed.

  Lemma dom_add i j x y : dom i x -> dom j y -> dom (i + j) (x + y)%R.
  Proof.
    intros [u [Hu Hxu]] [v [Hv Hyv]];exists (u + v)%R;split;[apply cont_add;auto|lra].
  Qed.

  Lemma dom_abs i x : cont i x -> dom (abs i) (Rabs x).
  Proof.
    intros Hi;exists (Rabs x);split;[|lra].
    apply (FI.abs_correct _ (Xreal x));auto.
  Qed.

  Lemma dom_upper i x : dom i x -> err_le (FI.upper i) x.
  Proof.
    intros [u [Hu Hxu]];apply (err_le_trans _ _ u);auto.
    apply cont_upper;auto.
  Qed.

  Lemma dom_max i j x y : dom i x -> dom j y -> dom (max i j) (Rmax x y).
  Proof.
    intros Hi Hj.
    pose proof (dom_upper i x Hi) as Hui.
    pose proof (dom_upper j y Hj) as Huj.
    unfold err_le in Hui, Huj.
    destruct (FI.F'.max_valid_ub (FI.upper i) (FI.upper j) (valid_ub_all _) (valid_ub_all _)) as [_ Hmax].
    rewrite max_I_spec.
    destruct (FI.F.toX (FI.F.max (FI.upper i) (FI.upper j))) as [|M] eqn:HM.
    - exists (Rmax x y);split;[apply cont_singleton_nan;auto|lra].
    - exists M;split.
      + apply cont_singleton;auto.
      + destruct (FI.F.toX (FI.upper i)) as [|ui];[simpl in Hmax;discriminate|].
        destruct (FI.F.toX (FI.upper j)) as [|uj];[simpl in Hmax;discriminate|].
        simpl in Hmax;injection Hmax as ->.
        apply Rmax_lub;[apply (Rle_trans _ ui);[lra|apply Rmax_l]|apply (Rle_trans _ uj);[lra|apply Rmax_r]].
  Qed.

  Lemma dom_poly_norm {d} (P : @mpoly I d) (p : @mpoly R d) : pcont d P p -> dom (poly_norm P) (poly_norm p).
  Proof.
    revert P p;induction d;intros P p H.
    - rewrite (poly_norm_0 (A:=I)), (poly_norm_0 (A:=R)), R_absE;apply dom_abs;exact H.
    - simpl in H.
      induction H.
      + rewrite (poly_norm_nil (A:=I)), (poly_norm_nil (A:=R));apply dom_cont;apply cont_zero.
      + rewrite (poly_norm_cons (A:=I)), (poly_norm_cons (A:=R)).
        apply dom_add;auto.
  Qed.

  Lemma dom_poly_vec_bound {d e} (P : (@mpoly I (S d))^e) (p : (@mpoly R (S d))^e) :
    ptcont P p -> dom (poly_vec_bound P) (poly_vec_bound p).
  Proof.
    revert P p;induction e;intros P p H.
    - rewrite (poly_vec_bound_nil (A:=I)), (poly_vec_bound_nil (A:=R));apply dom_cont;apply cont_zero.
    - destruct (destruct_tuple_cons P) as [P0 [Pt ->]].
      destruct (destruct_tuple_cons p) as [p0 [pt ->]].
      rewrite (poly_vec_bound_cons (A:=I)), (poly_vec_bound_cons (A:=R)), R_maxE.
      apply dom_max.
      + apply dom_poly_norm.
        specialize (H 0%nat (Nat.lt_0_succ _));rewrite !tuple_nth_cons_hd in H;exact H.
      + apply IHe;intros i Hi.
        specialize (H (S i) (proj1 (Nat.succ_lt_mono _ _) Hi));rewrite !tuple_nth_cons_tl in H;exact H.
  Qed.

  Lemma dom_poly_M {d} (PI : (@mpoly I (S d))^(S d)) (pR : (@mpoly R (S d))^(S d)) (Y : I^(S d)) (y0 : R^(S d)) :
    ptcont PI pR -> tcont Y y0 -> dom (poly_M PI Y) (poly_M pR y0).
  Proof.
    intros HP HY.
    rewrite (poly_M_spec (A:=I)), (poly_M_spec (A:=R)), R_maxE, R_oneE.
    apply dom_max;[apply dom_cont;apply cont_one|].
    apply dom_poly_vec_bound.
    apply ptrel_shift;auto.
  Qed.

  Lemma cont_inv i x : (x <> 0)%R -> cont i x -> cont (inv_approx i) (/ x)%R.
  Proof.
    intros Hx Hi.
    pose proof (FI.inv_correct Solver.FI.prec i (Xreal x) Hi) as H.
    simpl in H;unfold Xinv' in H;rewrite is_zero_false in H;auto.
  Qed.

  Lemma poly_M_ge_1 {d} (pR : (@mpoly R (S d))^(S d)) (y0 : R^(S d)) : (1 <= poly_M pR y0)%R.
  Proof.
    rewrite (poly_M_spec (A:=R)), R_maxE, R_oneE;apply Rmax_l.
  Qed.

  Theorem step_admissible {d} (PI : (@mpoly I (S d))^(S d)) (pR : (@mpoly R (S d))^(S d))
    (Y : I^(S d)) (y0 : R^(S d)) (SF : I) (sf : R) :
    ptcont PI pR -> tcont Y y0 -> cont SF sf -> (0 <= sf)%R ->
    exists h, cont (approx_pivp_step_size PI Y SF) h
              /\ (0 <= h)%R
              /\ (h <= approx_pivp_step_size pR y0 sf)%R.
  Proof.
    intros HP HY HSF Hsf.
    destruct (dom_poly_M PI pR Y y0 HP HY) as [m [Hm Hmle]].
    pose proof (poly_M_ge_1 pR y0) as HM1.
    assert (2 <= INR (2 * S d))%R as Hc2.
    { rewrite mult_INR;simpl (INR 2);rewrite S_INR.
      pose proof (pos_INR d);lra. }
    exists ((/ (INR (2 * S d) * m * 1)) * sf)%R.
    assert (0 < INR (2 * S d) * poly_M pR y0 * 1)%R as Hpos by nra.
    assert (INR (2 * S d) * poly_M pR y0 * 1 <= INR (2 * S d) * m * 1)%R as Hle by nra.
    split;[|split].
    - rewrite (step_size_unfold (A:=I)).
      apply cont_mul;[|exact HSF].
      apply cont_inv;[nra|].
      apply cont_mul;[apply cont_mul;[|exact Hm]|apply cont_one].
      rewrite <-inject_natR;apply cont_inject_nat.
    - apply Rmult_le_pos;[|auto].
      apply Rlt_le, Rinv_0_lt_compat;nra.
    - rewrite (step_size_unfold (A:=R)).
      change (@mul R R_Setoid R_RawRing) with Rmult.
      change (@inv_approx R R_Setoid R_RawRing R_RawRingOpp R_RawFieldOps) with Rinv.
      change (@one R R_Setoid R_RawRing) with 1%R.
      rewrite inject_natR.
      apply Rmult_le_compat_r;auto.
      apply Rinv_le_contravar;nra.
  Qed.

  (** * Soundness of the iteration *)

  Definition next_state {d} (P : (@mpoly I (S d))^(S d)) (Y : I^(S d)) (factor : F) : I^(S d) :=
    Solver.FI.add_errort
      (FI.upper (snd (approx_pivp_step' P Y (pivp_F P params.order) (singleton factor) params.order)))
      (taylor_step (pivp_F P params.order) Y (approx_pivp_step_size P Y (singleton factor))).

  (** A box [b] of the trajectory (time component followed by the state
      components) is a correct enclosure if the solution passes through it at
      some time enclosed by its time component. *)
  Definition encloses_at {d} (y : R -> R^(S d)) (b : I^(S (S d))) : Prop :=
    exists tk, cont (tuple_nth 0 b 0) tk
               /\ forall i, (i < S d)%nat -> cont (tuple_nth (S i) b 0) (tuple_nth i (y tk) 0).

  (** * Instantiating the hypotheses for rational input

      A concrete IVP is given by polynomials with rational coefficients, which
      are converted to intervals by [Q2Ipoly] and to reals by [Q2Rpoly].  The
      lemmas below discharge the hypotheses [ptcont] and [tcont] for such
      input, so the theorems above are applicable (in particular they are not
      vacuous). *)

  Fixpoint Q2Rpoly {d} : @mpoly Q d -> @mpoly R d :=
    match d with
    | O => fun q => inject_Q q
    | S d' => fun p => map (Q2Rpoly (d:=d')) p
    end.

  Lemma pcont_Q2Ipoly : forall d (p : @mpoly Q d), pcont d (Solver.FI.Q2Ipoly p) (Q2Rpoly p).
  Proof.
    induction d;intros p;[apply cont_injectQ|].
    induction p;[constructor|constructor;[apply IHd|exact IHp]].
  Qed.

  Lemma ptcont_Q2Ipolyt {e d} (p : (@mpoly Q d)^e) :
    ptcont (Solver.FI.Q2Ipolyt p) (tuple_map Q2Rpoly p).
  Proof.
    intros i Hi.
    unfold Solver.FI.Q2Ipolyt.
    rewrite (tuple_map_nth Solver.FI.Q2Ipoly p i 0 0), (tuple_map_nth Q2Rpoly p i 0 0);auto.
    apply pcont_Q2Ipoly.
  Qed.

  Lemma tcont_inject_Q {e} (y0 : Q^e) :
    tcont (tuple_map (inject_Q (A:=I)) y0) (tuple_map (inject_Q (A:=R)) y0).
  Proof.
    intros i Hi.
    rewrite (tuple_map_nth (inject_Q (A:=I)) y0 i 0 0), (tuple_map_nth (inject_Q (A:=R)) y0 i 0 0);auto.
    apply cont_injectQ.
  Qed.

  (** The user-facing polynomial syntax used in the demos is also sound:
      interpreting a [PolyExpr] over intervals encloses the same expression
      interpreted over the reals. *)
  Lemma pcont_make_poly d (p : PolyExpr) :
    pcont d (make_poly (A:=I) d p) (make_poly (A:=R) d p).
  Proof.
    induction p;simpl.
    - apply mrel_const;apply cont_injectQ.
    - apply mrel_poly_comp1.
    - apply mrel_add;auto.
    - apply mrel_add;[auto|].
      apply mrel_mul;[apply mrel_const;change (cont (opp 1) (opp 1));apply cont_opp, cont_one|auto].
    - apply mrel_mul;[apply mrel_const;change (cont (opp 1) (opp 1));apply cont_opp, cont_one|auto].
    - apply mrel_mul;auto.
    - induction n;simpl;[apply mrel_one|apply mrel_mul;auto].
  Qed.

  Lemma ptcont_vecp {e d} (p : PolyExpr^e) :
    ptcont (vecp (A:=I) d p) (vecp (A:=R) d p).
  Proof.
    intros i Hi.
    unfold vecp.
    rewrite (tuple_map_nth (make_poly (A:=I) d) p i 0 (PConst 0));auto.
    rewrite (tuple_map_nth (make_poly (A:=R) d) p i 0 (PConst 0));auto.
    apply pcont_make_poly.
  Qed.



  (** * Correctness of interval-time trajectories

      [interval_trajectory] carries time as an interval and iterates
      [interval_step], so no additional hypothesis about floating-point time
      accumulation is needed. *)

  (** for every reachable state box the solver must produce a finite error
      bound and a step that is admissible for the exact system; no condition on
      the reported times is needed *)
  Definition steps_ok {d} (PI : (@mpoly I (S d))^(S d)) (pR : (@mpoly R (S d))^(S d))
             (y : R -> R^(S d)) (factor : F) (sf : R) : Prop :=
    forall (Y : I^(S d)) (t : R),
      tcont Y (y t) ->
      exists h : R,
          cont (approx_pivp_step_size PI Y (singleton factor)) h
          /\ (0 <= h)%R
          /\ (h <= approx_pivp_step_size pR (y t) sf)%R.

  (** [steps_ok] is not an assumption: it follows from [step_admissible] *)
  Lemma steps_ok_holds {d} (PI : (@mpoly I (S d))^(S d)) (pR : (@mpoly R (S d))^(S d))
        (y : R -> R^(S d)) (factor : F) (sf : R) :
    ptcont PI pR -> cont (singleton factor) sf -> (0 <= sf)%R -> steps_ok PI pR y factor sf.
  Proof.
    intros HP Hsf Hsf0 Y t HY.
    apply (step_admissible PI pR Y (y t) (singleton factor) sf);auto.
  Qed.

  (** * Correctness of the trajectory, with no assumption on the interval
        computation

      Every box of the trajectory encloses the solution at some time enclosed
      by the box's time component.  The only hypotheses are about the input
      ([PI] encloses [pR], [Y] encloses the initial state, [T] the initial
      time, [sf] the step factor) and the accuracy of the *exact* algorithm. *)
  Theorem interval_trajectory_steps_correct {d}
    (PI : (@mpoly I (S d))^(S d)) (pR : (@mpoly R (S d))^(S d)) (sf : R) (y : R -> R^(S d)) (a b : R) :
    ptcont PI pR ->
    is_pivp_solution_on a b pR y ->
    taylor_step_accurate a b pR params.order sf ->
    cont (singleton params.step_factor) sf -> (0 <= sf)%R ->
    (forall t h, (a < t < b)%R -> (0 <= h)%R -> (h <= approx_pivp_step_size pR (y t) sf)%R -> (a < t + h < b)%R) ->
    forall steps Y T Tend t, (a < t < b)%R -> tcont Y (y t) -> cont T t ->
      Forall (encloses_at y) (Solver.interval_trajectory_steps steps PI Y T Tend).
  Proof.
    intros Hp Hsol Hacc Hsf Hsf0 Hdom steps.
    pose proof (steps_ok_holds PI pR y params.step_factor sf Hp Hsf Hsf0) as Hok.
    revert steps.
    induction steps;intros Y T Tend t Ht HY HT.
    - cbn [Solver.interval_trajectory_steps].
      constructor;[|constructor].
      exists t;split;[rewrite tuple_nth_cons_hd;auto|intros i Hi;rewrite tuple_nth_cons_tl;apply HY;auto].
    - assert (encloses_at y (tuple_cons T Y)) as Hhd.
      { exists t;split;[rewrite tuple_nth_cons_hd;auto|intros i Hi;rewrite tuple_nth_cons_tl;apply HY;auto]. }
      cbn [Solver.interval_trajectory_steps].
      destruct (FI.F'.le (Tend - FI.lower T) SFBI2.zero);
        [constructor;[exact Hhd|constructor]|].
      constructor;[exact Hhd|].
      destruct (Hok Y t HY) as [h [Hh [Hh0 Hadm]]].
      pose proof (Hdom t h Ht Hh0 Hadm) as Ht2.
      destruct (Solver.interval_step PI Y T params.order params.step_factor) as [T' Y'] eqn:Hstep.
      destruct (interval_step_correct PI pR Y T params.step_factor sf y a b t h Hp Hsol Hacc HY HT Hsf Hh (proj1 Ht) (proj2 Ht2) Hh0 Hadm) as [Htime Hstate].
      rewrite Hstep in Htime,Hstate;simpl in Htime,Hstate.
      apply (IHsteps Y' T' Tend (t + h)%R);auto.
  Qed.

  Theorem interval_trajectory_correct {d}
    (PI : (@mpoly I (S d))^(S d)) (pR : (@mpoly R (S d))^(S d)) (sf : R) (y : R -> R^(S d)) (a b : R) :
    ptcont PI pR ->
    is_pivp_solution_on a b pR y ->
    taylor_step_accurate a b pR params.order sf ->
    cont (singleton params.step_factor) sf -> (0 <= sf)%R ->
    (forall t h, (a < t < b)%R -> (0 <= h)%R -> (h <= approx_pivp_step_size pR (y t) sf)%R -> (a < t + h < b)%R) ->
    forall Y T Tend t, (a < t < b)%R -> tcont Y (y t) -> cont (singleton T) t ->
      Forall (encloses_at y) (Solver.interval_trajectory PI Y T Tend).
  Proof.
    intros Hp Hsol Hacc Hsf Hsf0 Hdom Y T Tend t Ht HY HT.
    unfold Solver.interval_trajectory.
    exact (interval_trajectory_steps_correct PI pR sf y a b Hp Hsol Hacc Hsf Hsf0 Hdom
                                            params.max_steps Y (singleton T) Tend t Ht HY HT).
  Qed.

  Theorem interval_trajectory_correct_of_remainder {d}
    (PI : (@mpoly I (S d))^(S d)) (pR : (@mpoly R (S d))^(S d)) (sf : R) (y : R -> R^(S d)) (a b : R) :
    ptcont PI pR ->
    is_pivp_solution_on a b pR y ->
    remainder_bounded a b pR params.order sf ->
    cont (singleton params.step_factor) sf -> (0 <= sf)%R ->
    (forall t h, (a < t < b)%R -> (0 <= h)%R -> (h <= approx_pivp_step_size pR (y t) sf)%R -> (a < t + h < b)%R) ->
    forall Y T Tend t, (a < t < b)%R -> tcont Y (y t) -> cont (singleton T) t ->
      Forall (encloses_at y) (Solver.interval_trajectory PI Y T Tend).
  Proof.
    intros Hp Hsol Hrem Hsf Hsf0 Hdom Y T Tend t Ht HY HT.
    exact (interval_trajectory_correct PI pR sf y a b
             Hp Hsol (taylor_step_accurate_of_remainder a b pR params.order sf Hrem)
             Hsf Hsf0 Hdom Y T Tend t Ht HY HT).
  Qed.

  (** This is the same theorem in the form used by the demo tactics: the vector
      field is a tuple of [PolyExpr]s with rational constants, and the initial
      state is a rational tuple.  The coefficient and initial-state enclosure
      hypotheses are discharged by computation. *)
  Theorem itrajectory_correct {d}
    (P : PolyExpr^(S d)) (YQ : Q^(S d)) (sf : R) (y : R -> R^(S d)) (a b : R) :
    is_pivp_solution_on a b (vecp (A:=R) (S d) P) y ->
    taylor_step_accurate a b (vecp (A:=R) (S d) P) params.order sf ->
    cont (singleton params.step_factor) sf -> (0 <= sf)%R ->
    (forall t h, (a < t < b)%R -> (0 <= h)%R ->
                 (h <= approx_pivp_step_size (vecp (A:=R) (S d) P) (y t) sf)%R ->
                 (a < t + h < b)%R) ->
    forall T Tend t,
      (a < t < b)%R ->
      tuple_map (inject_Q (A:=R)) YQ = y t ->
      cont (singleton T) t ->
      Forall (encloses_at y) (Solver.itrajectory P YQ T Tend).
  Proof.
    intros Hsol Hacc Hsf Hsf0 Hdom T Tend t Ht Hinit HT.
    unfold Solver.itrajectory.
    assert (HY : tcont (tuple_map (inject_Q (A:=I)) YQ) (y t)).
    { rewrite <- Hinit;apply tcont_inject_Q. }
    exact (@interval_trajectory_correct d
             (vecp (A:=I) (S d) P)
             (vecp (A:=R) (S d) P)
             sf y a b
             (ptcont_vecp P) Hsol Hacc Hsf Hsf0 Hdom
             (tuple_map (inject_Q (A:=I)) YQ) T Tend t Ht HY HT).
  Qed.

  Theorem itrajectory_correct_of_remainder {d}
    (P : PolyExpr^(S d)) (YQ : Q^(S d)) (sf : R) (y : R -> R^(S d)) (a b : R) :
    is_pivp_solution_on a b (vecp (A:=R) (S d) P) y ->
    remainder_bounded a b (vecp (A:=R) (S d) P) params.order sf ->
    cont (singleton params.step_factor) sf -> (0 <= sf)%R ->
    (forall t h, (a < t < b)%R -> (0 <= h)%R ->
                 (h <= approx_pivp_step_size (vecp (A:=R) (S d) P) (y t) sf)%R ->
                 (a < t + h < b)%R) ->
    forall T Tend t,
      (a < t < b)%R ->
      tuple_map (inject_Q (A:=R)) YQ = y t ->
      cont (singleton T) t ->
      Forall (encloses_at y) (Solver.itrajectory P YQ T Tend).
  Proof.
    intros Hsol Hrem Hsf Hsf0 Hdom T Tend t Ht Hinit HT.
    exact (itrajectory_correct P YQ sf y a b Hsol
             (taylor_step_accurate_of_remainder a b (vecp (A:=R) (S d) P) params.order sf Hrem)
             Hsf Hsf0 Hdom T Tend t Ht Hinit HT).
  Qed.

  Theorem apivp_trajectory_correct {d}
    (ivp : APIVP (d:=S d)) (sf : R) (y : R -> R^(S d)) (a b : R) :
    is_pivp_solution_on a b (vecp (A:=R) (S d) ivp.(ivp_rhs)) y ->
    taylor_step_accurate a b (vecp (A:=R) (S d) ivp.(ivp_rhs)) params.order sf ->
    cont (singleton params.step_factor) sf -> (0 <= sf)%R ->
    (forall t h, (a < t < b)%R -> (0 <= h)%R ->
                 (h <= approx_pivp_step_size (vecp (A:=R) (S d) ivp.(ivp_rhs)) (y t) sf)%R ->
                 (a < t + h < b)%R) ->
    forall T Tend t,
      (a < t < b)%R ->
      tuple_map (inject_Q (A:=R)) ivp.(ivp_y0) = y t ->
      cont (singleton T) t ->
      Forall (encloses_at y) (Solver.itrajectory ivp.(ivp_rhs) ivp.(ivp_y0) T Tend).
  Proof.
    intros Hsol Hacc Hsf Hsf0 Hdom T Tend t Ht Hinit HT.
    exact (itrajectory_correct ivp.(ivp_rhs) ivp.(ivp_y0) sf y a b
             Hsol Hacc Hsf Hsf0 Hdom T Tend t Ht Hinit HT).
  Qed.

  Theorem apivp_trajectory_correct_of_remainder {d}
    (ivp : APIVP (d:=S d)) (sf : R) (y : R -> R^(S d)) (a b : R) :
    is_pivp_solution_on a b (vecp (A:=R) (S d) ivp.(ivp_rhs)) y ->
    remainder_bounded a b (vecp (A:=R) (S d) ivp.(ivp_rhs)) params.order sf ->
    cont (singleton params.step_factor) sf -> (0 <= sf)%R ->
    (forall t h, (a < t < b)%R -> (0 <= h)%R ->
                 (h <= approx_pivp_step_size (vecp (A:=R) (S d) ivp.(ivp_rhs)) (y t) sf)%R ->
                 (a < t + h < b)%R) ->
    forall T Tend t,
      (a < t < b)%R ->
      tuple_map (inject_Q (A:=R)) ivp.(ivp_y0) = y t ->
      cont (singleton T) t ->
      Forall (encloses_at y) (Solver.itrajectory ivp.(ivp_rhs) ivp.(ivp_y0) T Tend).
  Proof.
    intros Hsol Hrem Hsf Hsf0 Hdom T Tend t Ht Hinit HT.
    exact (itrajectory_correct_of_remainder ivp.(ivp_rhs) ivp.(ivp_y0) sf y a b
             Hsol Hrem Hsf Hsf0 Hdom T Tend t Ht Hinit HT).
  Qed.

End IntervalSolverCorrect.
