Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import polynomial.
Require Import powerseries.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import Classical.



 Open Scope diff_scope.

 Lemma tuple_nth_ext {n A} (x y : @tuple n A) d : (forall n, tuple_nth n x d = tuple_nth n y d) -> x = y.
 Proof.
   intros.
   destruct x, y.
   simpl in H.
   apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
   apply (nth_ext _ _ d d);auto;lia.
 Qed.


Section PIVP.
  Context `{CompositionalDiffAlgebra} .

 Definition derive_tuple {d} (y : @tuple d (A 1)) :  @tuple d (A 1).
 Proof.
   induction d.
   apply nil_tuple.
  destruct (destruct_tuple y) as [hd [tl P]].
   apply (tuple_cons (pdiff 0 hd) (IHd tl)).
 Defined.


 Definition nth_derivative {d} (y : @tuple d (A 1)) (n : nat) :  @tuple d (A 1).
 Proof.
   induction n.
   apply y.
   apply (derive_tuple IHn).
 Defined.


 Lemma derive_tuple_cons {m} x (y : @tuple m (A 1)) : derive_tuple (tuple_cons x y) = tuple_cons (pdiff 0 x) (derive_tuple y).

 Proof.
   induction m.
   destruct y;apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;auto.
   simpl.
   destruct (destruct_tuple (tuple_cons x y)) as [hd [tl P]].
   rewrite proj1_sig_tuple_cons in P.
   injection P;intros.
   rewrite H5.
   f_equal;auto.
   enough (y = tl) as -> by auto.
   apply eq_sig_hprop;auto.
   intros.
   apply proof_irrelevance. 
 Qed.

 Lemma derive_tuple_nth {m} n (y : @tuple m (A 1)) d   : (n < m)%nat -> tuple_nth n (derive_tuple y) d = pdiff 0 (tuple_nth n y d).
  Proof.
     intros.
     revert dependent n.
     induction m;intros; try lia.
     destruct (destruct_tuple y) as [hd [tl P]].
     replace y with (tuple_cons hd tl) by (destruct y;destruct tl;apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat;auto).
     rewrite derive_tuple_cons.
     destruct n.
     rewrite !tuple_nth_cons_hd;auto.
     rewrite !tuple_nth_cons_tl;auto.
     rewrite IHm;auto;lia.
  Qed.

  Definition is_IVP_solution_series {d} f (y : @tuple d (A 1)) := derive_tuple y = multi_composition f y.

   Definition tuple_choice_P {T d} P (Hp : (forall i, (i < d)%nat -> {x : T  | P x i})): forall x, {t : (@tuple d T) | forall i (lt : (i < d)%nat), tuple_nth i t x =  proj1_sig (Hp i lt) }.
   Proof.
     intros.
     revert dependent P.
     induction d;intros.
     exists nil_tuple.
     intros;lia.
     assert (forall i, i < d -> (S i) < (S d)) by lia.
     enough {t : (tuple d) | forall i (lt' : i < d), tuple_nth i t x = proj1_sig (Hp (S i) (H4 _ lt'))} as [t0 T0].
     {
       assert (0 < S d)%nat by lia.
       exists (tuple_cons (proj1_sig (Hp 0%nat H5)) t0).
       intros.
       destruct i.
       rewrite tuple_nth_cons_hd;simpl.
       replace H5 with lt by apply proof_irrelevance;auto.
       rewrite tuple_nth_cons_tl.
       assert (i < d)%nat by lia.
       rewrite (T0 _ H6).
       replace (H4 i H6) with lt by apply proof_irrelevance;auto.
     }
     assert (Hp' : forall i, i < d -> {x : T | forall lt', proj1_sig (Hp (S i) (H4 i lt')) = x}).
     {
       intros.
       destruct (Hp (S i) (H4 _ H5)) eqn:E.
       exists x0.
       intros.
       replace lt' with H5 by apply proof_irrelevance.
       rewrite E;auto.
     }
     destruct (IHd _ Hp').
     exists x0.
     intros.
     rewrite (e _ lt').
     destruct (Hp' i lt').
     simpl; rewrite e0;auto.
   Qed.
   Lemma tuple_nth_nth_derivative_S {d} n m (t : tuple d) x : (n < d)%nat -> tuple_nth n (nth_derivative t (S m)) x = pdiff 0 (tuple_nth n (nth_derivative t m) x).
   Proof.
     intros.
     simpl.
     rewrite derive_tuple_nth;auto.
   Defined.

   Fixpoint IVP_Di {d} (f : @tuple d (A d)) (n i : nat) :=
     match n with
     | 0%nat => (comp1 i)
     | (S n') => (sum (fun j => tuple_nth j f 0 * (D[j] (IVP_Di f n' i))) d)
   end.

   Definition IVP_Di_spec {d} f n: forall i y,  (i < d)%nat ->  @is_IVP_solution_series d f y -> ((IVP_Di f n i) \o y ) == tuple_nth i (nth_derivative y n) 0.
   Proof.
     intros.
     induction n.
     simpl.
     apply composition_id.
     rewrite tuple_nth_nth_derivative_S;auto.
     destruct d; try lia.
     pose proof (pdiff_chain (IVP_Di f n i) y (d := 0)).
     simpl.
     rewrite <-IHn.
     rewrite H6.
     rewrite composition_sum_comp.
     apply sum_ext; intros.
     rewrite composition_mult_comp.
     rewrite <- derive_tuple_nth; try lia.
     rewrite H5.
     rewrite tuple_nth_multicomposition;try lia.
     reflexivity.
  Defined.

   Definition IVP_D {d} (f :@tuple d (A d)) (n :nat) : @tuple d (A d).
   Proof.
     destruct (seq_to_tuple (IVP_Di f n) d (def := 0)).
     apply x.
   Defined.

   Lemma IVP_D_nth {d} f n i : i < d -> tuple_nth i (@IVP_D d f n) 0 = IVP_Di f n i. 
   Proof.
     intros.
     unfold IVP_D.
     destruct (seq_to_tuple _ _ ).
     rewrite e;auto.
   Qed.

  Definition IVP_D_spec {d} f :  forall n y, @is_IVP_solution_series d f y -> nth_derivative y n == (IVP_D f n) \o\ y.
  Proof.
     intros.
     apply (tuple_nth_ext' _ _ 0 0).
     intros.
     rewrite tuple_nth_multicomposition;try lia.
     unfold IVP_D.
     destruct (seq_to_tuple _ _).
     rewrite e;try lia.
     rewrite IVP_Di_spec;auto.
     reflexivity.
   Qed.
  

End PIVP.

Section PolynomialModel.
  Context `{comSemiRing}.
  Record AbstractPolynomialModel {d} := {
      p : @poly (@tuple d A);
      r : A;
      err : A
    }.
End PolynomialModel.

Section invfactorial.
  Context `{comSemiRing}.
  Class Sn_invertible := {
      inv_Sn  (n : nat) : A; 
      inv_Sn_spec : forall n, (ntimes (S n) 1) * inv_Sn n == 1
  }.

  Definition inv_factorial `{Sn_invertible} (n : nat) : A.
  Proof.
    induction n.
    apply 1.
    apply  (inv_Sn n  * IHn).
  Defined.
End invfactorial.
  Notation "![ n ]" := (inv_factorial n).
Section TaylorSequence.

  Open Scope fun_scope.
  Context `{AbstractFunction }.
  Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat))}.
  Context {d : nat} (f : A{d;d})  (y0 : A{d;0%nat}) (dom_f : y0 \in_dom f).



  Lemma dom_D : forall n, y0 \in_dom (IVP_D f n).
  Proof.
    intros.
    induction n;intros i Hi;rewrite IVP_D_nth;auto;[apply dom_id|].
    simpl.
    destruct d; try lia.
    apply dom_sum;intros.
    apply dom_mult.
    apply dom_f;lia.
    apply dom_diff.
    rewrite <- IVP_D_nth;try lia.
    apply IHn;lia.
  Qed.

  Definition ivp_solution_taylor (n : nat) : A{d;0%nat} := ![n] ** ((IVP_D f n) @ (y0; (dom_D n))).

  Definition is_IVP_solution y (Hy : 0 \in_dom y) := is_IVP_solution_series f y  /\ y @ (0;Hy) == y0.
   
  Lemma  is_IVP_solution_deriv_dom {y Hy}: is_IVP_solution y Hy -> forall n, 0 \in_dom (nth_derivative y n). 
  Proof.
    intros.
    induction n;[apply Hy|].
    intros i Hi.
    rewrite tuple_nth_nth_derivative_S;auto.
    apply dom_diff.
    apply IHn;auto.
  Qed.


  Lemma ivp_solution_taylor0 : ivp_solution_taylor 0 == y0.
  Proof.
    unfold ivp_solution_taylor, IVP_D.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite scalar_mult_spec.
    rewrite mulC, mul1.
    rewrite (evalt_spec _ _ H6).
    assert (in_domain (IVP_Di f 0 i) y0).
    {
      pose proof (dom_D 0 i H6).
      rewrite IVP_D_nth in H7;auto.
    }
    rewrite (algebra.eval_proper  _ (IVP_Di f 0 i) y0 y0 _ H7);try reflexivity.
    simpl;rewrite eval_id;auto;reflexivity.
    destruct (seq_to_tuple _ _).
    rewrite e;auto;reflexivity.
  Qed.

  Lemma ivp_solution_taylor_spec n y Hy (S :  is_IVP_solution y Hy) : ivp_solution_taylor n == ![n] ** ((nth_derivative y n) @ (0;(is_IVP_solution_deriv_dom S n))).
  Proof.
    unfold ivp_solution_taylor.
    setoid_replace (((IVP_D f n) @ (y0; dom_D n))) with ((nth_derivative y n) @ (0; is_IVP_solution_deriv_dom S n));try reflexivity.
    destruct S.
    pose proof (IVP_D_spec _ n _ i).
    assert (0 \in_dom (IVP_D f n) \o\ y).
    {
      apply (dom_composition _ y 0 Hy _ e).
      apply dom_D.
    }
    rewrite (meval_proper _ _ _ _ (is_IVP_solution_deriv_dom (conj i e) n) H7 H6);try reflexivity.
    assert ((y @ (0; Hy)) \in_dom (IVP_D f n)).
    {
      rewrite e.
      apply dom_D.
    }
    rewrite (eval_composition_compat  _ _ _ Hy H8).
    apply meval_proper;try rewrite e;reflexivity.
  Qed.

  Definition ivp_taylor_poly (n : nat)  : @poly A{d;0%nat}.
  Proof.
    induction n.
    apply [y0].
    apply (IHn ++ [ivp_solution_taylor (S n)]).
  Defined.

  Lemma ivp_taylor_poly_length : forall n, length (ivp_taylor_poly n) = (S n).
  Proof.
    intros.
    induction n.
    simpl;auto.
    simpl.
    rewrite app_length.
    rewrite IHn;simpl.
    lia.
  Qed.

  Lemma ivp_taylor_poly_spec : forall n i, (i <= n)%nat -> nth i (ivp_taylor_poly n) 0 == ivp_solution_taylor i.
  Proof.
    intros.
    induction n.
    - replace i with 0%nat by lia.
      rewrite ivp_solution_taylor0.
      simpl nth.
      reflexivity.
   - assert (i < S n \/ i = S n) by lia.
     destruct H7.
     + simpl nth.
       rewrite app_nth1; [|rewrite ivp_taylor_poly_length;lia].
       rewrite IHn;try lia;reflexivity.
     + rewrite H7.
       simpl nth.
       rewrite app_nth2; rewrite ivp_taylor_poly_length;try lia.
       rewrite Nat.sub_diag;simpl nth;reflexivity.
   Qed.
End TaylorSequence.

Section IVP_Record.
  Open Scope fun_scope.
  Context `{AbstractFunction }.
  Record IVP {d} := {
      f : A{d;d};
      y0 : A{d;0%nat}
    }.

End IVP_Record.
  (* Notation "![ n ]" := (inv_factorial n). *)
  
  
(* Section PolynomialModel. *)
(*   Open Scope fun_scope. *)
(*   Context `{AbstractFunction }. *)
(*   Context `{TotallyOrderedField (A := (A 0%nat)) (H := (H 0%nat)) (R_rawRing := (H0 0%nat)) (R_semiRing := (H1 0%nat))}. *)
(*   Context `{normed : (NormedSemiRing (A 0) (A 0) (H := (H 0)) (H0 := (H 0)) (R_rawRing := (H0 0%nat)) (R_rawRing0 := (H0 0%nat)) (R_TotalOrder := R_TotalOrder))}. *)
(*   Notation "| x |" := (norm x) (at level 10). *)
(*   Notation "y \_ i" := (tuple_nth i y 0) (at level 1). *)

(*   Definition in_box {d} (c : A{d;0%nat})  r   (x : A{d;0%nat}) := forall i, | x\_i - c\_i | <= r. *)

(*   Notation "x \in B( c , r )" := (in_box c r x) (at level 4). *)
(*   Context {d : nat} (f : A{d;d})  (y0 : A{d;0%nat}) (r : A 0) (dom_f :forall x,  x \in B(y0,r) -> x \in_dom f). *)
(*    Context (r_nonneg : 0 <= r). *)
(*    Lemma int_dom_D n  x (Hx : x \in B(y0, r)) : x \in_dom (IVP_D f n). *)
(*   Proof. *)
(*     apply dom_D. *)
(*     apply dom_f. *)
(*     exact Hx. *)
(*   Qed. *)

(*   Lemma y0_in_dom : y0 \in_dom f. *)
(*   Proof. *)
(*     apply dom_f. *)
(*     intros i. *)
(*     setoid_replace (y0\_i - y0\_i) with (0 : A 0). *)
(*     rewrite (proj2 (norm_zero 0));auto;reflexivity. *)
(*     unfold minus. *)
(*     rewrite addI;reflexivity. *)
(*   Qed. *)

(*   Context (bound : nat -> (A 0)) (bound_pos : forall n, 0 <= bound n /\ not (bound n == 0)) (bound_spec : forall n x (Hx : x \in B(y0, r)),  ![n] ** ((IVP_D f n) @ (x;(int_dom_D n x Hx)))  \in B(0,(bound n))). *)

(*   (* Definition IVP_solution_approx  (n : nat): AbstractPolynomialModel (A := A 0) (d:=d). *) *)
(*   (* Proof. *) *)
(*   (*   constructor. *) *)
(*   (*   apply (ivp_taylor_poly f y0 y0_in_dom n). *) *)
(*   (*   destruct (bound_pos 1). *) *)
(*   (*   apply (r *  inv H8). *) *)
(*   (*   apply  *) *)
(*   (* Definition T_y (i n : nat) H := ![n] * ((nth_derivative y n) @ (0;H)\_i). *) *)

(*   (* Definition taylor_polynomial  *) *)
(*   (* Context (y_dom : forall x, x \in B(0, r) -> x \in_dom y). *) *)
(*   (* Context (taylor_theorem : forall n t i x (domx : x \in B(0,r)), | [y](t;Dy)\_i - ![n]* [n_derivative y n](0;y_dom domx) | <= ). *) *)
(* End PolynomialModel. *)
