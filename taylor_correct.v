(**
   * Correctness of the Taylor step of the PIVP solver over the reals

   [pivp.v] computes, for a polynomial IVP  y' = p(y),  the symbolic
   derivatives [pivp_F p n] and evaluates the resulting Taylor polynomial
   ([approx_pivp_step']).  Nothing in the development connects this to an
   actual solution of the ODE.  This file establishes that connection over the
   classical reals, using only the ordinary notion of solution
   ([is_pivp_solution], stated with Coquelicot's [is_derive]):

   - [eval_tuple_is_derive] : the chain rule for evaluating a multivariate
     polynomial along a differentiable curve.
   - [Derive_n_pivp] : the k-th derivative of a solution [y] of  y' = p(y)  is
     [eval_tuple (Dpoly p k i) (y t)], where [Dpoly p k i = hd 0 (Fi p k i)] is
     exactly the polynomial the solver computes.  So the symbolic derivatives
     of the solver are the derivatives of the solution.
   - [taylor_step_sum] : the value the solver's Taylor step computes is the
     truncated Taylor series  sum_{k<=n} y^(k)(t0)/k! h^k  of the solution.
   - [taylor_step_lagrange] : *unconditionally*, the error of the step is the
     Lagrange remainder  h^(n+1)/(n+1)! * y^(n+1)(xi)  for some intermediate
     [xi].
   - [taylor_step_accurate_of_remainder] : consequently the accuracy statement
     used in [iode_correct.v] follows from a bound on that single derivative
     along the step ([remainder_bounded]).

   [remainder_bounded] is the one ingredient that is not proved: it is the
   analytic content of the method (the majorant estimates of [odebounds.v] and
   [realanalytic.v] bound exactly these derivatives, but they are formulated
   for formal power series in the abstract [ArchimedeanField] setting, not for
   classical solutions).  Everything else here is proved.

   The file also makes the classical reals a [RawFieldOps] / [SemiRing]
   structure, i.e. gives the exact-arithmetic instance of the generic solver
   which the interval version is compared against in [iode_correct.v].
*)
From Coq Require Import Reals.
From Coquelicot Require Import Hierarchy Derive.
Require Import algebra archimedean polynomial tuple pivp.
From Coq Require Import QArith Qreals Psatz List Setoid.
Require Import Coq.Classes.SetoidClass.
Import ListNotations.
Local Close Scope Q_scope.

(** * The classical reals as a [RawFieldOps] / [SemiRing] structure

    Instantiating the generic solver with this gives the algorithm as executed
    in exact real arithmetic. *)
Definition Rinv_approx (x : R) := Rinv x.
Definition Rupper (x : R) := 0%nat.

#[global] Instance R_Setoid : SetoidClass.Setoid R.
Proof.
  exists (fun x y => x = y).
  constructor;auto.
  intros a b c -> ->;auto.
Defined.

#[global] Instance R_RawRing : RawRing (A:=R).
Proof. constructor; [apply R0 | apply R1 | apply Rplus | apply Rmult]. Defined.

#[global] Instance R_RawRingOpp : RawRingWithOpp (A:=R).
Proof. constructor. apply Ropp. Defined.

#[global] Instance R_RawFieldOps : RawFieldOps (A:=R).
Proof. constructor; [apply Q2R | apply Rabs | apply Rmax | apply Rinv_approx | apply Rupper]. Defined.

#[global] Instance R_SemiRing : SemiRing (A:=R).
Proof.
  constructor;simpl;try (intros;ring).
  - intros a b -> c d ->;auto.
  - intros a b -> c d ->;auto.
Defined.

#[global] Instance R_Ring : Ring (A:=R).
Proof.
  constructor;simpl;[intros a b ->;auto|intros;ring].
Defined.

(** * The Taylor step of the generic algorithm

    [approx_pivp_step'] (the function the interval solver actually runs)
    computes, from the pre-computed symbolic derivatives [Fis], a step size
    [t1], the value [taylor_step Fis y0 t1] of the order-[n] Taylor
    approximation at [t1], and an error bound.  We isolate the Taylor
    evaluation, because the interval version and the exact version choose
    (slightly) different step sizes, so soundness has to be stated for an
    arbitrary time in the computed step interval. *)
Section TaylorStep.
  Context `{RawFieldOps}.

  Definition taylor_step {d} (Fis : tuple (S d) (list (@mpoly A (S d)))) (y0 : tuple (S d) A) (t : A) : tuple (S d) A :=
    proj1_sig (seq_to_tuple (def := 0) (fun i => eval_poly (pivp.Fi_to_taylor' (tuple_nth i Fis 0) y0) t) (S d)).

  Lemma Fi_0 {d} (f : tuple (S d) (@mpoly A (S d))) i : pivp.Fi f 0 i = [poly_comp1 i].
  Proof. reflexivity. Qed.

  Lemma Fi_S {d} (f : tuple (S d) (@mpoly A (S d))) n i :
    pivp.Fi f (S n) i = (sum (fun j => (tuple_nth j f 0) * (poly_pdiff j (hd 0 (pivp.Fi f n i)))) (S d)) :: pivp.Fi f n i.
  Proof. reflexivity. Qed.

  Lemma Fi_to_taylor'_nil {d} (y0 : tuple (S d) A) : pivp.Fi_to_taylor' [] y0 = [].
  Proof. reflexivity. Qed.

  Lemma Fi_to_taylor'_cons {d} (a : @mpoly A (S d)) l (y0 : tuple (S d) A) :
    pivp.Fi_to_taylor' (a :: l) y0 = pivp.Fi_to_taylor' l y0 ++ [inv_fact (length (pivp.Fi_to_taylor' l y0)) * eval_tuple a y0].
  Proof. reflexivity. Qed.

  Lemma Fi_to_taylor'_length {d} (l : list (@mpoly A (S d))) (y0 : tuple (S d) A) : length (pivp.Fi_to_taylor' l y0) = length l.
  Proof.
    induction l;[reflexivity|].
    rewrite Fi_to_taylor'_cons, length_app, IHl;simpl;lia.
  Qed.

  (** the three components of a step *)
  Lemma step_size_spec {d} p y0 Fis sf n :
    fst (fst (approx_pivp_step' (d:=d) p y0 Fis sf n)) = approx_pivp_step_size p y0 sf.
  Proof. reflexivity. Qed.

  Lemma step_value_spec {d} p y0 Fis sf n :
    snd (fst (approx_pivp_step' (d:=d) p y0 Fis sf n)) = taylor_step Fis y0 (approx_pivp_step_size p y0 sf).
  Proof. reflexivity. Qed.

  Lemma step_error_spec {d} p y0 Fis sf n :
    snd (approx_pivp_step' (d:=d) p y0 Fis sf n) = inject_nat 2 * npow sf (S n).
  Proof. reflexivity. Qed.

End TaylorStep.



(** operations of the algebraic structure on [R] are the real operations *)
Lemma R_addE (a b : R) : add a b = (a + b)%R. Proof. reflexivity. Qed.
Lemma R_mulE (a b : R) : mul a b = (a * b)%R. Proof. reflexivity. Qed.
Lemma R_zeroE : (zero : R) = 0%R. Proof. reflexivity. Qed.
Lemma R_oneE : (one : R) = 1%R. Proof. reflexivity. Qed.

(** * Sums over [R] *)

Lemma sumR_0 (f : nat -> R) : sum f 0 = 0%R.
Proof. reflexivity. Qed.

Lemma sumR_S (f : nat -> R) n : sum f (S n) = (sum f n + f n)%R.
Proof. rewrite (sum_S f n);reflexivity. Qed.

Lemma sumR_S_fun (f : nat -> R) n : sum f (S n) = (f 0%nat + sum (fun i => f (S i)) n)%R.
Proof. rewrite (sum_S_fun f n);reflexivity. Qed.

Lemma sumR_zero n : sum (fun _ => 0%R) n = 0%R.
Proof. induction n;[reflexivity|rewrite sumR_S, IHn;ring]. Qed.

Lemma sumR_plus (f g : nat -> R) n : sum (fun i => (f i + g i)%R) n = (sum f n + sum g n)%R.
Proof. induction n;[rewrite !sumR_0;ring|rewrite !sumR_S, IHn;ring]. Qed.

Lemma sumR_mult (c : R) (f : nat -> R) n : sum (fun i => (c * f i)%R) n = (c * sum f n)%R.
Proof. induction n;[rewrite !sumR_0;ring|rewrite !sumR_S, IHn;ring]. Qed.

Lemma sumR_ext (f g : nat -> R) n : (forall i, (i < n)%nat -> f i = g i) -> sum f n = sum g n.
Proof.
  induction n;intros H;[reflexivity|].
  rewrite !sumR_S.
  assert (sum f n = sum g n) as -> by (apply IHn;intros;apply H;lia).
  rewrite (H n);auto.
Qed.

(** * Tails of tuples *)

Definition ttail {A m} (t : @tuple (S m) A) : @tuple m A.
Proof.
  destruct t as [l e].
  exists (tl l).
  destruct l;simpl in *;lia.
Defined.

Lemma ttail_nth {A m} (t : @tuple (S m) A) j d : tuple_nth j (ttail t) d = tuple_nth (S j) t d.
Proof. destruct t as [l e];destruct l;simpl in *;[lia|auto]. Qed.

Lemma ttail_cons {A m} (h : A) (t : @tuple m A) : ttail (tuple_cons h t) = t.
Proof.
  destruct t as [l e];simpl.
  apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  reflexivity.
Qed.

Lemma tuple_cons_ttail {A m} (t : @tuple (S m) A) d : t = tuple_cons (tuple_nth 0 t d) (ttail t).
Proof.
  destruct t as [l e];destruct l as [|a l'];simpl in e;[lia|].
  apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  reflexivity.
Qed.

(** * Evaluation of polynomials over [R] *)

Lemma eqR {a b : R} : a == b -> a = b.
Proof. auto. Qed.

Lemma evalR_zero {m} (x : tuple m R) : @eval_tuple R _ _ m zero x = 0%R.
Proof. exact (zero_poly_eval x). Qed.

Lemma evalR_nil {m} (t : tuple (S m) R) : eval_tuple ([] : @mpoly R (S m)) t = 0%R.
Proof. exact (zero_poly_eval t). Qed.

Lemma one_const {m} : (one : @mpoly R m) = const_to_mpoly m 1%R.
Proof. induction m;[reflexivity|simpl;rewrite <-IHm;reflexivity]. Qed.

Lemma evalR_one {m} (x : tuple m R) : eval_tuple (one : @mpoly R m) x = 1%R.
Proof. rewrite one_const, const_to_mpoly_eval;reflexivity. Qed.

Lemma evalR_add {m} (p q : @mpoly R m) x : eval_tuple (add p q) x = (eval_tuple p x + eval_tuple q x)%R.
Proof. rewrite mpoly_add_spec;reflexivity. Qed.

Lemma evalR_mul {m} (p q : @mpoly R m) x : eval_tuple (mul p q) x = (eval_tuple p x * eval_tuple q x)%R.
Proof. rewrite mpoly_mul_spec;reflexivity. Qed.

Lemma evalR_fold {m} (f : nat -> @mpoly R m) x : forall n k,
    eval_tuple (fold_right add zero (map f (seq k n))) x = fold_right Rplus 0%R (map (fun i => eval_tuple (f i) x) (seq k n)).
Proof.
  induction n;intros k;simpl;[apply evalR_zero|].
  rewrite evalR_add, IHn;reflexivity.
Qed.

Lemma evalR_sum {m} (f : nat -> @mpoly R m) n x : eval_tuple (sum f n) x = sum (fun i => eval_tuple (f i) x) n.
Proof. unfold sum;apply evalR_fold. Qed.

Lemma evalR_cons {m} (p0 : @mpoly R m) (p : @mpoly R (S m)) hd (tl : tuple m R) :
  eval_tuple ((p0 :: p) : @mpoly R (S m)) (tuple_cons hd tl)
  = (eval_tuple p0 tl + hd * eval_tuple p (tuple_cons hd tl))%R.
Proof. rewrite eval_tuple_cons;reflexivity. Qed.

Lemma evalR_cons' {m} (p0 : @mpoly R m) (p : @mpoly R (S m)) (x : tuple (S m) R) :
  eval_tuple ((p0 :: p) : @mpoly R (S m)) x
  = (eval_tuple p0 (ttail x) + tuple_nth 0 x 0%R * eval_tuple p x)%R.
Proof.
  destruct (destruct_tuple_cons x) as [x0 [xs ->]].
  rewrite ttail_cons, tuple_nth_cons_hd.
  apply evalR_cons.
Qed.

(** * The formal derivative in the first variable *)

Lemma eval_derive_helper_S {m} (l : list (@mpoly R m)) x (xs : tuple m R) : forall (n : @mpoly R m),
  eval_tuple (derive_fast_helper l (add n one) : @mpoly R (S m)) (tuple_cons x xs)
  = (eval_tuple (derive_fast_helper l n : @mpoly R (S m)) (tuple_cons x xs)
     + eval_tuple (l : @mpoly R (S m)) (tuple_cons x xs))%R.
Proof.
  induction l as [|a l IH];intros n.
  - simpl derive_fast_helper;rewrite !evalR_nil;ring.
  - simpl derive_fast_helper.
    rewrite !evalR_cons, IH, !evalR_mul, !evalR_add, evalR_one.
    ring.
Qed.

Lemma eval_derive_poly_cons {m} (a : @mpoly R m) (p : list (@mpoly R m)) x (xs : tuple m R) :
  eval_tuple (derive_poly (a :: p) : @mpoly R (S m)) (tuple_cons x xs)
  = (eval_tuple (p : @mpoly R (S m)) (tuple_cons x xs)
     + x * eval_tuple (derive_poly p : @mpoly R (S m)) (tuple_cons x xs))%R.
Proof.
  unfold derive_poly, derive_fast.
  destruct p as [|p0 p'].
  - simpl derive_fast_helper;rewrite !evalR_nil;ring.
  - simpl tl;simpl derive_fast_helper.
    rewrite evalR_cons, eval_derive_helper_S, evalR_cons, !evalR_mul, evalR_one.
    ring.
Qed.

(** * The chain rule for polynomial evaluation along a curve *)

Lemma is_derive_plusR (f g : R -> R) (x df dg : R) :
  is_derive f x df -> is_derive g x dg -> is_derive (fun s => (f s + g s)%R) x (df + dg)%R.
Proof. intros;exact (is_derive_plus f g x df dg H H0). Qed.

Lemma poly_pdiff_cons {m} j (a : @mpoly R m) (p : list (@mpoly R m)) :
  poly_pdiff (S j) ((a :: p) : @mpoly R (S m)) = ((poly_pdiff j a) :: (poly_pdiff (S j) (p : @mpoly R (S m))))%list.
Proof. reflexivity. Qed.

Lemma poly_pdiff_0 {m} (p : @mpoly R (S m)) : poly_pdiff 0 p = derive_poly p.
Proof. reflexivity. Qed.

Lemma poly_pdiff_nil {m} j : poly_pdiff j ([] : @mpoly R (S m)) = ([] : @mpoly R (S m)).
Proof. destruct j;reflexivity. Qed.

Lemma arith_chain (A B v0 S1 S2 x0 : R) :
  ((A + x0*B)*v0 + (S1 + x0*S2))%R = (S1 + (v0*A + x0*(B*v0 + S2)))%R.
Proof. ring. Qed.

(** the algebraic identity underlying the chain rule step *)
Lemma pdiff_sum_cons {m} (a : @mpoly R m) (p : list (@mpoly R m)) (x0 : R) (xs : tuple m R) (v : nat -> R) :
  sum (fun j => (eval_tuple (poly_pdiff j ((a::p) : @mpoly R (S m))) (tuple_cons x0 xs) * v j)%R) (S m)
  = (sum (fun j => (eval_tuple (poly_pdiff j a) xs * v (S j))%R) m
     + (v 0%nat * eval_tuple (p : @mpoly R (S m)) (tuple_cons x0 xs)
        + x0 * sum (fun j => (eval_tuple (poly_pdiff j (p : @mpoly R (S m))) (tuple_cons x0 xs) * v j)%R) (S m)))%R.
Proof.
  rewrite (sumR_S_fun (fun j => (eval_tuple (poly_pdiff j ((a::p) : @mpoly R (S m))) (tuple_cons x0 xs) * v j)%R)).
  rewrite (sumR_S_fun (fun j => (eval_tuple (poly_pdiff j (p : @mpoly R (S m))) (tuple_cons x0 xs) * v j)%R)).
  rewrite !(poly_pdiff_0 (m:=m)), eval_derive_poly_cons.
  rewrite (sumR_ext (fun j => (eval_tuple (poly_pdiff (S j) ((a::p) : @mpoly R (S m))) (tuple_cons x0 xs) * v (S j))%R)
                    (fun j => ((eval_tuple (poly_pdiff j a) xs * v (S j))
                               + x0 * (eval_tuple (poly_pdiff (S j) (p : @mpoly R (S m))) (tuple_cons x0 xs) * v (S j)))%R));
    [|intros j Hj;rewrite poly_pdiff_cons, evalR_cons;ring].
  rewrite sumR_plus, sumR_mult.
  apply arith_chain.
Qed.

Lemma pdiff_sum_cons' {m} (a : @mpoly R m) (p : list (@mpoly R m)) (x : tuple (S m) R) (v : nat -> R) :
  sum (fun j => (eval_tuple (poly_pdiff j ((a::p) : @mpoly R (S m))) x * v j)%R) (S m)
  = (sum (fun j => (eval_tuple (poly_pdiff j a) (ttail x) * v (S j))%R) m
     + (v 0%nat * eval_tuple (p : @mpoly R (S m)) x
        + tuple_nth 0 x 0%R * sum (fun j => (eval_tuple (poly_pdiff j (p : @mpoly R (S m))) x * v j)%R) (S m)))%R.
Proof.
  destruct (destruct_tuple_cons x) as [x0 [xs ->]].
  rewrite ttail_cons, tuple_nth_cons_hd.
  apply pdiff_sum_cons.
Qed.

(** The chain rule: differentiating a polynomial along a differentiable curve.
    [poly_pdiff j q] is the partial derivative of [q] in the j-th variable. *)
Lemma eval_tuple_is_derive : forall (m : nat) (q : @mpoly R m) (z : R -> tuple m R) (v : nat -> R) (t : R),
  (forall j, (j < m)%nat -> is_derive (fun s => tuple_nth j (z s) 0%R) t (v j)) ->
  is_derive (fun s => eval_tuple q (z s)) t (sum (fun j => (eval_tuple (poly_pdiff j q) (z t) * v j)%R) m).
Proof.
  induction m as [|m IHm];intros q z v t Hz.
  - rewrite sumR_0.
    apply (is_derive_ext (fun _ => q));[reflexivity|exact (is_derive_const q t)].
  - assert (is_derive (fun s => tuple_nth 0 (z s) 0%R) t (v 0%nat)) as Hz0 by (apply Hz;lia).
    assert (forall j, (j < m)%nat -> is_derive (fun s => tuple_nth j (ttail (z s)) 0%R) t (v (S j))) as Hzs.
    { intros j Hj.
      apply (is_derive_ext (fun s => tuple_nth (S j) (z s) 0%R));
        [intros;rewrite ttail_nth;reflexivity|apply Hz;lia]. }
    induction q as [|a p IHp].
    + rewrite (sumR_ext _ (fun _ => 0%R));[rewrite sumR_zero| ].
      * apply (is_derive_ext (fun _ => 0%R));[intros;rewrite evalR_nil;reflexivity|exact (is_derive_const 0%R t)].
      * intros j Hj;rewrite poly_pdiff_nil, evalR_nil;ring.
    + apply (is_derive_ext (fun s => (eval_tuple a (ttail (z s)) + (tuple_nth 0 (z s) 0%R) * eval_tuple (p : @mpoly R (S m)) (z s))%R)).
      * intros s;symmetry;apply evalR_cons'.
      * rewrite pdiff_sum_cons'.
        apply is_derive_plusR.
        -- apply (IHm a (fun s => ttail (z s)) (fun j => v (S j)) t Hzs).
        -- apply (is_derive_mult (fun s => tuple_nth 0 (z s) 0%R) (fun s => eval_tuple (p : @mpoly R (S m)) (z s)) t (v 0%nat) _ Hz0 IHp).
Qed.

(** * Solutions of polynomial initial value problems

    [y] is a solution of  y' = p(y)  on the open interval [(a,b)] in the
    ordinary sense of real analysis.  Restricting to an interval is essential:
    polynomial systems need not have global solutions (y' = y^2 blows up in
    finite time), so requiring a solution on all of [R] would make the
    statements below vacuous for exactly the systems where enclosures matter
    most. *)
Definition is_pivp_solution_on (a b : R) {d} (p : tuple (S d) (@mpoly R (S d))) (y : R -> tuple (S d) R) : Prop :=
  forall t i, (a < t < b)%R -> (i < S d)%nat ->
    is_derive (fun s => tuple_nth i (y s) 0%R) t (eval_tuple (tuple_nth i p 0) (y t)).

(** [Dpoly p k i] is the polynomial the solver computes for the k-th
    derivative of the i-th component ([hd 0 (Fi p k i)]). *)
Definition Dpoly {d} (p : tuple (S d) (@mpoly R (S d))) (k i : nat) : @mpoly R (S d) :=
  hd 0 (pivp.Fi p k i).

Lemma Dpoly_0 {d} (p : tuple (S d) (@mpoly R (S d))) i : Dpoly p 0 i = poly_comp1 i.
Proof. reflexivity. Qed.

Lemma Dpoly_S {d} (p : tuple (S d) (@mpoly R (S d))) k i :
  Dpoly p (S k) i = sum (fun j => mul (tuple_nth j p 0) (poly_pdiff j (Dpoly p k i))) (S d).
Proof. reflexivity. Qed.

Section Solution.
  Context {d : nat}.
  Variable p : tuple (S d) (@mpoly R (S d)).
  Variable y : R -> tuple (S d) R.
  Variable a b : R.
  Hypothesis Hsol : is_pivp_solution_on a b p y.

  (** differentiating [Dpoly p k i] along the solution gives [Dpoly p (S k) i] *)
  Lemma pivp_deriv k i t : (a < t < b)%R ->
    is_derive (fun s => eval_tuple (Dpoly p k i) (y s)) t (eval_tuple (Dpoly p (S k) i) (y t)).
  Proof.
    intros Ht.
    pose proof (eval_tuple_is_derive (S d) (Dpoly p k i) y
                  (fun j => eval_tuple (tuple_nth j p zero) (y t)) t) as H.
    rewrite Dpoly_S, evalR_sum.
    rewrite (sumR_ext _ (fun j => Rmult (eval_tuple (poly_pdiff j (Dpoly p k i)) (y t)) (eval_tuple (tuple_nth j p zero) (y t))));
      [|intros j Hj;rewrite evalR_mul;ring].
    apply H.
    intros j Hj;apply Hsol;auto.
  Qed.

  Lemma Derive_n_pivp k i : (i < S d)%nat ->
    forall t, (a < t < b)%R -> Derive_n (fun s => tuple_nth i (y s) 0%R) k t = eval_tuple (Dpoly p k i) (y t).
  Proof.
    intros Hi;induction k;intros t Ht.
    - rewrite Dpoly_0, poly_comp1_eval;reflexivity.
    - simpl Derive_n.
      rewrite (Derive_ext_loc (Derive_n (fun s => tuple_nth i (y s) 0%R) k)
                              (fun s => eval_tuple (Dpoly p k i) (y s))).
      + apply is_derive_unique, pivp_deriv;auto.
      + apply (locally_interval _ _ (Rbar.Finite a) (Rbar.Finite b));try apply Ht.
        intros s Ha Hb;apply IHk;split;auto.
  Qed.

  Lemma ex_derive_n_pivp k i : (i < S d)%nat ->
    forall t, (a < t < b)%R -> ex_derive_n (fun s => tuple_nth i (y s) 0%R) k t.
  Proof.
    intros Hi t Ht.
    destruct k;[exact I|].
    exists (eval_tuple (Dpoly p (S k) i) (y t)).
    apply (is_derive_ext_loc (fun s => eval_tuple (Dpoly p k i) (y s))).
    - apply (locally_interval _ _ (Rbar.Finite a) (Rbar.Finite b));try apply Ht.
      intros s Ha Hb;symmetry;apply Derive_n_pivp;auto.
    - apply pivp_deriv;auto.
  Qed.

End Solution.

(** * The value computed by the solver is the truncated Taylor series *)

Lemma npowR (x : R) k : npow x k = (x ^ k)%R.
Proof. induction k;[reflexivity|simpl;rewrite IHk;reflexivity]. Qed.

Lemma evalR_poly_sum (q : list R) (x : R) :
  eval_poly q x = sum (fun k => (nth k q 0%R * x ^ k)%R) (length q).
Proof.
  induction q as [|a q IH];[reflexivity|].
  simpl length;rewrite sumR_S_fun.
  simpl eval_poly.
  rewrite IH.
  rewrite <-sumR_mult.
  f_equal;[simpl;ring|].
  apply sumR_ext;intros i Hi;simpl;ring.
Qed.

Lemma Fi_length_R {d} (p : tuple (S d) (@mpoly R (S d))) n i : length (pivp.Fi p n i) = S n.
Proof.
  induction n;[reflexivity|].
  rewrite Fi_S;cbn [length];rewrite IHn;reflexivity.
Qed.

Lemma Fi_nth_Dpoly {d} (p : tuple (S d) (@mpoly R (S d))) n i :
  forall k, (k <= n)%nat -> nth (n - k) (pivp.Fi p n i) zero = Dpoly p k i.
Proof.
  induction n;intros k Hk.
  - assert (k = 0)%nat as -> by lia.
    rewrite Fi_0;reflexivity.
  - rewrite Fi_S.
    destruct (Nat.eq_dec k (S n)) as [->|Hne].
    + rewrite Nat.sub_diag;cbn [nth].
      unfold Dpoly;rewrite Fi_S;reflexivity.
    + assert (S n - k = S (n - k))%nat as -> by lia.
      cbn [nth].
      apply IHn;lia.
Qed.

Lemma Fi_to_taylor'_nth {d} (L : list (@mpoly R (S d))) (y0 : tuple (S d) R) : forall k,
    nth k (pivp.Fi_to_taylor' L y0) 0%R
    = (inv_fact k * eval_tuple (nth k (rev L) zero) y0)%R.
Proof.
  induction L as [|a L IH];intros k.
  - rewrite Fi_to_taylor'_nil.
    rewrite !nth_overflow by (cbn;lia).
    rewrite (evalR_zero y0);ring.
  - rewrite Fi_to_taylor'_cons, Fi_to_taylor'_length.
    destruct (Compare_dec.lt_dec k (length L)) as [Hlt|Hge].
    + rewrite app_nth1 by (rewrite Fi_to_taylor'_length;auto).
      rewrite IH.
      cbn [rev].
      rewrite app_nth1 by (rewrite length_rev;auto).
      reflexivity.
    + rewrite app_nth2 by (rewrite Fi_to_taylor'_length;lia).
      rewrite Fi_to_taylor'_length.
      cbn [rev].
      rewrite app_nth2 by (rewrite length_rev;lia).
      rewrite length_rev.
      destruct (k - length L)%nat as [|u] eqn:Hu.
      * assert (k = length L)%nat as -> by lia.
        cbn [nth];rewrite R_mulE;reflexivity.
      * rewrite !nth_overflow by (cbn;lia).
        rewrite (evalR_zero y0);ring.
Qed.

(** [length] of the same list can appear with different (convertible) type
    arguments, which blocks [rewrite]; this normalises all of them. *)
Ltac norm_Fi_length :=
  repeat match goal with
  | |- context[@length ?A (pivp.Fi ?p ?n ?i)] =>
      let H := fresh "HFl" in
      assert (@length A (pivp.Fi p n i) = S n) as H by (exact (Fi_length_R p n i));
      rewrite H;clear H
  end.

Lemma Fi_rev_nth {d} (p : tuple (S d) (@mpoly R (S d))) n i :
  forall k, (k <= n)%nat -> nth k (rev (pivp.Fi p n i)) zero = Dpoly p k i.
Proof.
  intros k Hk.
  rewrite rev_nth by (norm_Fi_length;lia).
  norm_Fi_length.
  assert (S n - S k = n - k)%nat as -> by lia.
  apply Fi_nth_Dpoly;lia.
Qed.

Lemma taylor_step_sum {d} (p : tuple (S d) (@mpoly R (S d))) (n : nat) (y0 : tuple (S d) R) (h : R) i :
  (i < S d)%nat ->
  tuple_nth i (taylor_step (pivp_F p n) y0 h) 0%R
  = sum (fun k => (inv_fact k * eval_tuple (Dpoly p k i) y0 * h ^ k)%R) (S n).
Proof.
  intros Hi.
  unfold taylor_step.
  rewrite (proj2_sig (seq_to_tuple (fun i => eval_poly (pivp.Fi_to_taylor' (tuple_nth i (pivp_F p n) zero) y0) h) (S d)) i Hi).
  unfold pivp_F.
  rewrite (proj2_sig (seq_to_tuple (pivp.Fi p n) (S d)) i Hi).
  rewrite evalR_poly_sum, Fi_to_taylor'_length.
  norm_Fi_length.
  apply sumR_ext;intros k Hk.
  rewrite Fi_to_taylor'_nth, Fi_rev_nth by lia.
  reflexivity.
Qed.

(** * Taylor's theorem with Lagrange remainder *)

Lemma injectQ_inv_S n :
  @inject_Q R _ _ _ R_RawFieldOps (QArith_base.Qmake 1 (Pos.of_nat (S n))) = (/ INR (S n))%R.
Proof.
  change (@inject_Q R _ _ _ R_RawFieldOps) with Q2R.
  unfold Q2R;cbn [QArith_base.Qnum QArith_base.Qden].
  rewrite <-Pos.of_nat_succ, Zpos_P_of_succ_nat, <-Nat2Z.inj_succ, <-INR_IZR_INZ.
  lra.
Qed.

Lemma inv_fact_S n :
  @inv_fact R _ _ _ R_RawFieldOps (S n)
  = (@inject_nat_inv R _ _ _ R_RawFieldOps (S n) * @inv_fact R _ _ _ R_RawFieldOps n)%R.
Proof. reflexivity. Qed.

Lemma inv_fact_R n : inv_fact n = (/ INR (fact n))%R.
Proof.
  induction n.
  - simpl;lra.
  - rewrite inv_fact_S, IHn.
    unfold inject_nat_inv;rewrite injectQ_inv_S.
    rewrite fact_simpl, mult_INR, Rinv_mult;reflexivity.
Qed.

Lemma sum_sum_f_R0 (g : nat -> R) n : sum g (S n) = sum_f_R0 g n.
Proof.
  induction n;[unfold sum;simpl;ring|].
  rewrite sumR_S, IHn;reflexivity.
Qed.

Theorem taylor_step_lagrange {d} (p : tuple (S d) (@mpoly R (S d))) (y : R -> tuple (S d) R)
  (a b : R) n t0 h i :
  is_pivp_solution_on a b p y -> (i < S d)%nat -> (0 < h)%R -> (a < t0)%R -> (t0 + h < b)%R ->
  exists xi, (t0 < xi < t0 + h)%R /\
    (tuple_nth i (y (t0 + h)%R) 0%R - tuple_nth i (taylor_step (pivp_F p n) (y t0) h) 0%R
     = h ^ (S n) / INR (fact (S n)) * eval_tuple (Dpoly p (S n) i) (y xi))%R.
Proof.
  intros Hsol Hi Hh Ha Hb.
  destruct (Taylor_Lagrange (fun s => tuple_nth i (y s) 0%R) n t0 (t0 + h)%R) as [xi [Hxi Heq]].
  - lra.
  - intros t Ht k Hk;apply (ex_derive_n_pivp p y a b Hsol);auto;split;lra.
  - exists xi;split;[lra|].
    rewrite Heq, taylor_step_sum by auto.
    replace (t0 + h - t0)%R with h by lra.
    rewrite <-sum_sum_f_R0.
    rewrite (sumR_ext (fun k => (inv_fact k * eval_tuple (Dpoly p k i) (y t0) * h ^ k)%R)
                      (fun m => (h ^ m / INR (fact m) * Derive_n (fun s => tuple_nth i (y s) 0%R) m t0)%R)).
    + rewrite (Derive_n_pivp p y a b Hsol (S n) i Hi xi) by lra.
      ring.
    + intros m Hm.
      rewrite (Derive_n_pivp p y a b Hsol m i Hi t0) by lra.
      rewrite inv_fact_R;unfold Rdiv;ring.
Qed.

(** * The accuracy statement used for the interval solver

    [taylor_step_accurate a b p order sf] says that the Taylor step of the exact
    algorithm approximates the solution within the error term the algorithm
    itself reports.  By [taylor_step_lagrange] this reduces to a bound on the
    single derivative [Dpoly p (S order) i] along the step. *)

Definition taylor_step_accurate (a b : R) {d} (p : tuple (S d) (@mpoly R (S d))) (order : nat) (sf : R) : Prop :=
  forall (y : R -> tuple (S d) R) (t0 h : R),
    is_pivp_solution_on a b p y ->
    (a < t0)%R -> (t0 + h < b)%R ->
    (0 <= h)%R -> (h <= approx_pivp_step_size p (y t0) sf)%R ->
    forall i, (i < S d)%nat ->
      (Rabs (tuple_nth i (y (t0 + h)%R) 0%R - tuple_nth i (taylor_step (pivp_F p order) (y t0) h) 0%R)
        <= snd (approx_pivp_step' p (y t0) (pivp_F p order) sf order))%R.

Definition remainder_bounded (a b : R) {d} (p : tuple (S d) (@mpoly R (S d))) (order : nat) (sf : R) : Prop :=
  forall (y : R -> tuple (S d) R) (t0 h : R),
    is_pivp_solution_on a b p y ->
    (a < t0)%R -> (t0 + h < b)%R ->
    (0 <= h)%R -> (h <= approx_pivp_step_size p (y t0) sf)%R ->
    forall xi i, (t0 <= xi <= t0 + h)%R -> (i < S d)%nat ->
      (Rabs (h ^ (S order) / INR (fact (S order)) * eval_tuple (Dpoly p (S order) i) (y xi))
        <= snd (approx_pivp_step' p (y t0) (pivp_F p order) sf order))%R.

Lemma sum_pow0 (f : nat -> R) n : sum (fun k => (f k * 0 ^ k)%R) (S n) = f 0%nat.
Proof.
  induction n;[unfold sum;simpl;ring|].
  rewrite sumR_S, IHn;simpl;ring.
Qed.

Lemma taylor_step_0 {d} (p : tuple (S d) (@mpoly R (S d))) order (y0 : tuple (S d) R) i :
  (i < S d)%nat -> tuple_nth i (taylor_step (pivp_F p order) y0 0%R) 0%R = tuple_nth i y0 0%R.
Proof.
  intros Hi.
  rewrite taylor_step_sum by auto.
  rewrite sum_pow0.
  rewrite Dpoly_0, poly_comp1_eval.
  change (@inv_fact R _ _ _ R_RawFieldOps 0) with 1%R.
  rewrite R_zeroE;ring.
Qed.

Theorem taylor_step_accurate_of_remainder (a b : R) {d} (p : tuple (S d) (@mpoly R (S d))) order sf :
  remainder_bounded a b p order sf -> taylor_step_accurate a b p order sf.
Proof.
  intros Hrem y t0 h Hsol Ha Hb Hh0 Hh i Hi.
  destruct (Rle_lt_or_eq_dec 0 h Hh0) as [Hpos|Heq].
  - destruct (taylor_step_lagrange p y a b order t0 h i Hsol Hi Hpos Ha Hb) as [xi [Hxi ->]].
    apply (Hrem y t0 h Hsol Ha Hb Hh0 Hh xi i);[lra|auto].
  - assert (h = 0%R) as -> by lra.
    rewrite Rplus_0_r, taylor_step_0 by auto.
    rewrite Rminus_diag, Rabs_R0.
    apply (Rle_trans _ (Rabs (0 ^ (S order) / INR (fact (S order)) * eval_tuple (Dpoly p (S order) i) (y t0)))).
    + rewrite pow_ne_zero by lia.
      unfold Rdiv;rewrite Rmult_0_l, Rmult_0_l, Rabs_R0;apply Rle_refl.
    + apply (Hrem y t0 0%R Hsol Ha Hb (Rle_refl _) Hh t0 i);[lra|auto].
Qed.

(** * The bounds computed by the step size heuristic

    Unfolding lemmas for [poly_norm], [poly_vec_bound], [poly_M] and the step
    size, so that they can be reasoned about without unfolding the tactic
    generated definitions. *)
Section PolyBounds.
  Context `{RawFieldOps}.

  Lemma poly_norm_0 (x : A) : poly_norm (d:=0) x = abs x.
  Proof. reflexivity. Qed.

  Lemma poly_norm_nil {d} : poly_norm (d := S d) [] = zero.
  Proof. reflexivity. Qed.

  Lemma poly_norm_cons {d} (a : @mpoly A d) (l : list (@mpoly A d)) :
    poly_norm (d := S d) (a :: l) = add (poly_norm (d := S d) l) (poly_norm a).
  Proof. reflexivity. Qed.

  Lemma poly_vec_bound_nil {d} (p : tuple 0 (@mpoly A (S d))) : poly_vec_bound p = zero.
  Proof. reflexivity. Qed.

  Lemma poly_vec_bound_cons {d e} (p0 : @mpoly A (S d)) (pt : tuple e (@mpoly A (S d))) :
    poly_vec_bound (tuple_cons p0 pt) = max (poly_norm p0) (poly_vec_bound pt).
  Proof. simpl;rewrite tuple_cons_destruct;reflexivity. Qed.

  Lemma poly_M_spec {d} (p : tuple (S d) (@mpoly A (S d))) (y0 : tuple (S d) A) :
    poly_M p y0 = max one (poly_vec_bound (shift_mpoly p y0)).
  Proof. reflexivity. Qed.

  Lemma poly_r_spec {d} (p : tuple d (@mpoly A d)) (y0 : tuple d A) : poly_r p y0 = one.
  Proof. reflexivity. Qed.

  Lemma step_size_unfold {d} (p : tuple (S d) (@mpoly A (S d))) (y0 : tuple (S d) A) (sf : A) :
    approx_pivp_step_size p y0 sf
    = mul (inv_approx (mul (mul (inject_nat (2 * S d)) (poly_M p y0)) one)) sf.
  Proof. reflexivity. Qed.

End PolyBounds.

(** * [inject_nat] and [inv_approx] over the reals *)

Lemma inject_natR n : @inject_nat R _ _ _ R_RawFieldOps n = INR n.
Proof.
  unfold inject_nat.
  change (@inject_Q R _ _ _ R_RawFieldOps) with Q2R.
  unfold Q2R, QArith_base.inject_Z;cbn [QArith_base.Qnum QArith_base.Qden].
  rewrite <-INR_IZR_INZ;simpl;lra.
Qed.

Lemma R_invE (x : R) : @inv_approx R _ _ _ R_RawFieldOps x = (/ x)%R.
Proof. reflexivity. Qed.

Lemma R_maxE (x y : R) : @max R _ _ _ R_RawFieldOps x y = Rmax x y.
Proof. reflexivity. Qed.

Lemma R_absE (x : R) : @abs R _ _ _ R_RawFieldOps x = Rabs x.
Proof. reflexivity. Qed.
