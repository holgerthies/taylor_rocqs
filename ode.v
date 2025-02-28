Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import functions.
Require Import polynomial.
Require Import powerseries.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import Classical.
Require Import tuple.


 Open Scope algebra_scope.

Section PIVP.
  Context `{CompositionalDiffAlgebra} .


  Definition is_IVP_solution_series {d} f (y : (A 1)^d) := D[0]y =  f \o y.

   (* Definition tuple_choice_P {T d} P (Hp : (forall i, (i < d)%nat -> {x : T  | P x i})): forall x, {t : (@tuple d T) | forall i (lt : (i < d)%nat), tuple_nth i t x =  proj1_sig (Hp i lt) }. *)
   (* Proof. *)
   (*   intros. *)
   (*   revert dependent P. *)
   (*   induction d;intros. *)
   (*   exists nil_tuple. *)
   (*   intros;lia. *)
   (*   assert (forall i, i < d -> (S i) < (S d)) by lia. *)
   (*   enough {t : (tuple d) | forall i (lt' : i < d), tuple_nth i t x = proj1_sig (Hp (S i) (H4 _ lt'))} as [t0 T0]. *)
   (*   { *)
   (*     assert (0 < S d)%nat by lia. *)
   (*     exists (tuple_cons (proj1_sig (Hp 0%nat H5)) t0). *)
   (*     intros. *)
   (*     destruct i. *)
   (*     rewrite tuple_nth_cons_hd;simpl. *)
   (*     replace H5 with lt by apply proof_irrelevance;auto. *)
   (*     rewrite tuple_nth_cons_tl. *)
   (*     assert (i < d)%nat by lia. *)
   (*     rewrite (T0 _ H6). *)
   (*     replace (H4 i H6) with lt by apply proof_irrelevance;auto. *)
   (*   } *)
   (*   assert (Hp' : forall i, i < d -> {x : T | forall lt', proj1_sig (Hp (S i) (H4 i lt')) = x}). *)
   (*   { *)
   (*     intros. *)
   (*     destruct (Hp (S i) (H4 _ H5)) eqn:E. *)
   (*     exists x0. *)
   (*     intros. *)
   (*     replace lt' with H5 by apply proof_irrelevance. *)
   (*     rewrite E;auto. *)
   (*   } *)
   (*   destruct (IHd _ Hp'). *)
   (*   exists x0. *)
   (*   intros. *)
   (*   rewrite (e _ lt'). *)
   (*   destruct (Hp' i lt'). *)
   (*   simpl; rewrite e0;auto. *)
   (* Qed. *)
   Lemma tuple_nth_nth_derivative_S {d} n m (t : (A m)^d) i : (n < d)%nat -> tuple_nth n (nth_derivative i t (S m)) 0 == pdiff i (tuple_nth n (nth_derivative i t m) 0).
   Proof.
     intros.
     simpl.
     rewrite pdiff_tuple_nth;auto.
     reflexivity.
   Defined.

  (* Fixpoint IVP_Di {d} (f : (A d)^d) (n i : nat) := *)
  (*    match n with *)
  (*    | 0%nat => (comp1 i) *)
  (*    | (S n') => (sum (fun j => tuple_nth j f 0 * (D[j] (IVP_Di f n' i))) d) *)
  (*  end. *)

  Definition id (d : nat) : (A d)^d := proj1_sig (seq_to_tuple (comp1 (m:=d)) d (def:=0)).

  Lemma id_nth {d} i: i < d -> tuple_nth i (id d) 0 = comp1 i.  
  Proof.
    intros.
    unfold id.
    destruct (seq_to_tuple (comp1 (m:=d)) d (def := 0)).
    simpl.
    rewrite e;auto;reflexivity.
  Qed.

  Lemma id_spec {d} (f : (A 1)^d) : ((id d) \o f) == f.
  Proof.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite tuple_nth_multicomposition;auto.
    rewrite id_nth;auto.
    rewrite composition_id.
    reflexivity.
  Qed.

  Fixpoint IVP_D {d} (f : (A d)^d) (n: nat) : (A d)^d :=
     match n with
     | 0%nat => (id d)
     | (S n') => (sum (fun j => (tuple_nth j f 0) ** (D[j] (IVP_D f n'))) d)
     end.

  Fixpoint IVP_Di {d} (f : (A d)^d) (n i : nat) : (A d) :=
     match n with
     | 0%nat => comp1 i
     | (S n') => (sum (fun j => (tuple_nth j f 0) * (D[j] (IVP_Di f n' i))) d)
     end.

  Definition IVP_D_spec {d} f :  forall n y, @is_IVP_solution_series d f y -> (nth_derivative 0 y n) == ((IVP_D f n) \o y).
  Proof.
     intros.
     induction n;[rewrite id_spec;simpl nth_derivative;reflexivity|].
     destruct d;[simpl;auto|].
     replace (nth_derivative 0 y (S n)) with  (D[0] (nth_derivative 0 y n)) by (simpl;auto).
     rewrite IHn.
     rewrite multicomposition_chain_rule.
      replace (IVP_D f (S n)) with (sum (fun j => (tuple_nth j f 0) ** (D[j] (IVP_D f n))) (S d)) by auto.
     rewrite multi_composition_sum_comp.
     apply sum_ext.
     intros.
     rewrite <-pdiff_tuple_nth;auto.
     rewrite H4.
     apply (tuple_nth_ext' _ _ 0 0).
     intros.
     rewrite !tuple_nth_multicomposition;auto.
     rewrite !scalar_mult_spec;auto.
     rewrite !tuple_nth_multicomposition;auto.
     rewrite composition_mult_comp.
     reflexivity.
   Qed.
  (*  Definition IVP_Di_spec {d} f n: forall i y,  (i < d)%nat ->  @is_IVP_solution_series d f y -> ((IVP_Di f n i) \o y ) == tuple_nth i ((D^n[0]y)  0. *)
  (*  Proof. *)
  (*    intros. *)
  (*    induction n. *)
  (*    simpl. *)
  (*    apply composition_id. *)
  (*    rewrite tuple_nth_nth_derivative_S;auto. *)
  (*    destruct d; try lia. *)
  (*    pose proof (pdiff_chain (IVP_Di f n i) y (d := 0)). *)
  (*    simpl. *)
  (*    rewrite <-IHn. *)
  (*    rewrite H6. *)
  (*    rewrite composition_sum_comp. *)
  (*    apply sum_ext; intros. *)
  (*    rewrite composition_mult_comp. *)
  (*    rewrite <- derive_tuple_nth; try lia. *)
  (*    rewrite H5. *)
  (*    rewrite tuple_nth_multicomposition;try lia. *)
  (*    reflexivity. *)
  (* Defined. *)

  (*  Definition IVP_D {d} (f :@tuple d (A d)) (n :nat) : @tuple d (A d). *)
  (*  Proof. *)
  (*    destruct (seq_to_tuple (IVP_Di f n) d (def := 0)). *)
  (*    apply x. *)
  (*  Defined. *)

   Lemma IVP_D_nth {d} f n i : i < d -> tuple_nth i (@IVP_D d f n) 0 == IVP_Di f n i.
   Proof.
     intros.
     induction n.
     simpl; unfold id.
     destruct (seq_to_tuple comp1 d);simpl.
     rewrite e;auto;reflexivity.

     simpl.
     rewrite tuple_nth_sum;auto.
     apply sum_ext.
     intros.
     rewrite scalar_mult_spec;auto.
     rewrite <- IHn.
     rewrite pdiff_tuple_nth;auto.
     reflexivity.
   Qed.

  

End PIVP.


Section invfactorial.
  Context `{SemiRing}.
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
  Context {d : nat} (f : (A d)^d)  (y0 : (A 0)^d) (dom_f : y0 \in_dom f).



  Lemma dom_D : forall n, y0 \in_dom (IVP_D f n).
  Proof.
    intros.
    induction n;intros i Hi;rewrite (dom_change_f _ _ _ (IVP_D_nth _ _  _ Hi));auto;[apply dom_id|].
    simpl.
    destruct d; try lia.
    apply dom_sum;intros.
    apply dom_mult.
    apply dom_f;lia.
    apply dom_diff.
    rewrite <-(dom_change_f _ _ _ (IVP_D_nth _ _  _ Hi)).
    apply IHn;lia.
  Qed.

  Definition ivp_solution_taylor (n : nat) : (A 0)^d  := ![n] ** ((IVP_D f n) @ (y0; (dom_D n))).

  Definition is_IVP_solution (y : (A 1)^d) (Hy : (0 : (A 0)^1) \in_dom y) := is_IVP_solution_series f y  /\ y @ (0;Hy) == y0.

  Lemma  is_IVP_solution_deriv_dom {y Hy}: is_IVP_solution y Hy -> forall n, (0 : (A 0)^1) \in_dom (nth_derivative 0 y n). 
  Proof.
    intros.
    induction n;[apply Hy|].
    intros i Hi.
    pose proof (tuple_nth_nth_derivative_S i n y 0 Hi).
    rewrite (dom_change_f  (0 : (A 0)^1) _ _ H7).
    apply dom_diff.
    apply IHn;auto.
  Qed.


  Lemma ivp_solution_taylor0 : ivp_solution_taylor 0 == y0.
  Proof.
    unfold ivp_solution_taylor, IVP_D.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite scalar_mult_spec;auto.
    rewrite mulC, mul1.
    simpl.
    rewrite (evalt_spec _ _ _ _ H6).
    assert (y0 \in_dom (IVP_Di f 0 i)).
    {
      rewrite <-(dom_change_f  _ _ _ (IVP_D_nth _ _ _ H6)).
      apply dom_D;auto.
    }
    rewrite (functions.eval_proper  _ (IVP_Di f 0 i) y0 y0 _ H7);try reflexivity.
    simpl;rewrite eval_id;auto;reflexivity.
    rewrite id_nth;auto.
    simpl;reflexivity.
  Qed.

  Lemma ivp_solution_taylor_spec n y Hy (S :  is_IVP_solution y Hy) : ivp_solution_taylor n == ![n] ** ((nth_derivative 0 y n) @ (0;(is_IVP_solution_deriv_dom S n))).
  Proof.
    unfold ivp_solution_taylor.
    setoid_replace (((IVP_D f n) @ (y0; dom_D n))) with ((nth_derivative 0 y n) @ (0; is_IVP_solution_deriv_dom S n));try reflexivity.
    destruct S.
    pose proof (IVP_D_spec _ n _ i).
    assert ((0 : (A 0)^1) \in_dom (IVP_D f n) \o y).
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
    rewrite (eval_composition_compat  _ _ _ Hy H8 H7).
    apply meval_proper;try rewrite e;reflexivity.
  Qed.

  Definition ivp_taylor_poly (n : nat)  : @poly ((A 0)^d).
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

(* Section Bounds. *)
(*   Open Scope fun_scope. *)
(*   Context `{AbstractFunction }. *)
(*   Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat))}. *)
(*   Context {d : nat} (f : A{d;d})  (y0 : A{d;0%nat}) (dom_f : y0 \in_dom f). *)
(*   Context `{TotallyOrderedField (A := (A 0%nat)) (H := (H 0%nat)) (R_rawRing := (H0 0%nat)) (R_semiRing := (H1 0%nat))}. *)
(*   Context `{normed : (NormedSemiRing (A 0) (A 0) (H := (H 0)) (H0 := (H 0)) (R_rawRing := (H0 0%nat)) (R_rawRing0 := (H0 0%nat)) (R_TotalOrder := R_TotalOrder))}. *)
(*   Add Ring TRing: (ComRingTheory (A := (A {d;0%nat}))). *)
(*   Lemma ivp_poly_diff n (t : A {d;0%nat}) : eval_poly (ivp_taylor_poly f y0 dom_f (S n)) t  == eval_poly (ivp_taylor_poly f y0 dom_f n) t + ivp_solution_taylor f y0 dom_f (S n) * npow t (S n). *)
(*   Proof. *)
(*     induction n. *)
(*     simpl eval_poly. *)
(*     simpl npow. *)
(*     ring_simplify;reflexivity. *)
(*     rewrite eval_eval2 at 1. *)
(*     simpl eval_poly2 at 1. *)
(*     rewrite eval_poly2_app1. *)
(*     rewrite app_length. *)
(*     rewrite ivp_taylor_poly_length. *)
(*     simpl length. *)
(*     ring_simplify. *)
(*     replace (S n + 1)%nat with (S (S n)) by lia. *)
(*     apply ring_eq_plus_eq; [reflexivity|]. *)
(*     rewrite eval_poly2_app1. *)
(*     rewrite <-eval_eval2. *)
(*     rewrite IHn. *)
(*     ring_simplify. *)
(*     rewrite ivp_taylor_poly_length. *)
(*     reflexivity. *)
(*   Qed. *)
(* End Bounds. *)
Section IVP_Record.
  Open Scope fun_scope.
  Context `{AbstractFunction }.
  Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat))}.
  Record IVP {d} := {
      f : (A d)^d;
      y0 : (A 0)^d;
      in_dom : y0 \in_dom f
    }.

  Definition IVP_taylor {d} (ivp : @IVP d) := ivp_taylor_poly ivp.(f) ivp.(y0) ivp.(in_dom). 

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
