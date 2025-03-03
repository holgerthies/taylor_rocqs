Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import powerseries.
Require Import functions.
Require Import polynomial.
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


Section factorial.
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
  Definition factorial  (n : nat) : A.
  Proof.
    induction n.
    apply 1.
    apply  ((ntimes (S n) 1)  * IHn).
  Defined.

End factorial.
  Notation "![ n ]" := (inv_factorial n).
  Notation "[ n ]!" := (factorial n).
 Section factorialFacts.
  Context `{SemiRing}.
  Context `{invSn : (Sn_invertible (A := A) (H:=_) (R_rawRing := _))}.
  Add Ring TRing: (ComSemiRingTheory (A := A)). 

  Lemma fact_invfact n : [n]! * ![n] == 1. 
  Proof.
    induction n.
    simpl.
    ring.
    simpl.
    ring_simplify.
    rewrite mulC.
    rewrite (mulC (ntimes  _ _)).
    rewrite <-!(mulA ![n]).
    rewrite (mulC ![n]).
    rewrite IHn.
    ring_simplify.
    rewrite mulA.
    rewrite IHn.
    ring_simplify.
    setoid_replace (ntimes n 1 * inv_Sn n + inv_Sn n ) with (ntimes (S n) 1 * inv_Sn n).
    rewrite inv_Sn_spec;reflexivity.
    simpl;ring.
  Qed.

 End factorialFacts.
Open Scope fun_scope.
Section TaylorSequence.

  Context `{AbstractFunctionSpace }.
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

Section Bounds. 
Context `{TotallyOrderedField}.
 Context `{normK : (NormedSemiRing A A (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }.
  Context `{invSn : Sn_invertible (A := A) (H := _) (R_rawRing := _)}. (* Replace by proof *)
 Context {norm1 : norm 1 == 1}.
 Context {M r : A}.

 Definition rising_factorial k n := [k+n-1]! * ![k-1].
 Notation "[ k ! n ]" := (rising_factorial k n).

 Add Ring KRing: (ComRingTheory (A := A)).
 Add Ring PRing: (ComSemiRingTheory (A :=(@mps A 1))).


 Lemma rising_factorial1 n : [1 ! n]  == [n]!.
 Proof.
   unfold rising_factorial.
   simpl.
   replace (n-0)%nat with n by lia.
   ring.
 Qed.

 Definition f_bound k := M * npow r k.
 Definition Fn_bound n k := [k+1!n]* npow M (n+1) * npow r (n + k).

 Notation "| a | <= b" := (forall k, norm (a k) <= b k) (at level 70).
 
  Lemma ntimes_nonneg x n: (0 <= x) -> 0 <= ntimes n x.
  Proof.
    intros.
    induction n.
    simpl;apply le_refl.
    simpl.
    setoid_replace 0 with (0 + 0) by ring.
    apply le_le_plus_le;auto.
 Qed.

  Lemma norm_n_le_n n : norm (ntimes n 1) <= ntimes n 1.
  Proof.
    induction n.
    simpl.
    assert (norm 0 == 0) as -> by (apply norm_zero;reflexivity).
    apply le_refl.
    simpl.
    apply (le_trans _ _ _ (norm_triangle _ _ )).
    rewrite norm1.
    apply le_le_plus_le;auto.
    apply le_refl.
  Qed.

  Lemma ps_mult_monotone a b a' b' : (|a| <= a') -> |b| <= b' -> |a*b| <= a' * b'.
  Proof.
   intros.
   generalize  dependent a'.
   generalize  dependent a.
   induction k;intros.
   simpl.
   unfold mult_ps, powerseries.convolution_coeff;simpl.
   ring_simplify.
   rewrite add0.
   apply (le_trans _ _ _ (norm_mult _ _)).
   apply (mul_le_le_compat_pos);try apply norm_nonneg;auto.
   simpl.
   rewrite !mult_ps_S.
   apply (le_trans _ _ _ (norm_triangle _ _ )).
   apply le_le_plus_le;auto.
   apply (le_trans _ _ _ (norm_mult _ _)).
   apply (mul_le_le_compat_pos);try apply norm_nonneg;auto.
   apply IHk.
   intros;auto.
  Qed.

  Lemma inv_Sn0 : inv_Sn 0 == 1.
  Proof.
    setoid_replace (inv_Sn 0) with (ntimes 1 1 * (inv_Sn 0)) by (simpl;ring).
    rewrite inv_Sn_spec.
    reflexivity.
  Qed.

  Lemma rising_factorial_s n k : [k+1!n+1] == ntimes (k+1) 1 * [(k+2) ! n].
  Proof.
    simpl.
    unfold rising_factorial.
    replace (k + 1 + (n+1) - 1)%nat with (S(k + n))%nat by lia.
    replace (k + 1 - 1)%nat with k by lia.
    replace (k + 2 + n- 1)%nat with (S (k + n))%nat by lia.
    replace (k + 2 - 1)%nat with (S k)%nat by lia.
    replace (k +1 )%nat with (S k)%nat by lia.
    enough (![k] == ntimes (S k) 1 * ![S k]) as -> by ring.
    simpl inv_factorial.
    rewrite <-mulA.
    rewrite inv_Sn_spec.
    ring.
  Qed.

  Definition DFn_bound n k :=  [(k+1)!n+1]* npow M (n+1) * npow r (n + (k + 1)).
   Lemma DFn_bound_spec (a : @mps A 1) n : |a| <= Fn_bound n -> |D[0] a| <= DFn_bound n.
   Proof.
   intros.
   simpl.
   unfold derive_ps.
   unfold DFn_bound.
   setoid_replace (a (k+1)%nat) with ((a (k+1)%nat) *1 ) by (rewrite mul1;reflexivity).
   rewrite ntimes_mult.
   apply (le_trans _ _ _  (norm_mult _ _)).
   apply (le_trans _ _ _  (mul_le_compat_pos (norm_nonneg _ ) (norm_n_le_n _ ))).
   rewrite rising_factorial_s.
   rewrite mulC.
   rewrite !mulA.
   apply mul_le_compat_pos.
   apply ntimes_nonneg.
   apply le_0_1.
   rewrite <-mulA.
   replace (k+2)%nat with ((k+1)+1)%nat by lia.
   apply H1.
 Qed.

  Lemma mul_ps_zero (a b : @mps A 1) :  (a*b) 0%nat == (a 0%nat) * (b 0%nat).
  Proof.
    simpl.
    unfold mult_ps, powerseries.convolution_coeff;simpl.
    ring.
  Qed.

  Lemma mul_ps_S (a b : @mps A 1) n :  (a*b) (S n) == (a 0%nat) * (b (S n)) + (((fun n => a (S n)) * b)  n).
  Proof.
    simpl.
    rewrite mult_ps_S.
    reflexivity.
  Qed.

 Lemma le_eq x y : (x == y) -> (x <= y).
 Proof.
   intros ->.
   apply le_refl.
 Qed.
  Lemma bound_prod  (a b : @mps A 1) n : |a| <= Fn_bound n -> |b| <= f_bound -> |(D[0] a) * b| <= Fn_bound (n+1). 
  Proof.
   intros.
   pose proof (DFn_bound_spec a n H1).
   pose proof (ps_mult_monotone _ _ _ _ H3 H2).
   apply (le_trans _ _ _ (H4 _)).
   induction k.
   - rewrite mul_ps_zero.
     unfold DFn_bound, f_bound, Fn_bound.
     simpl.
     assert ((n+1)%nat =  (S n)) as -> by lia.
     replace (S n + 1)%nat with (S (S n)) by lia.
     simpl.
     replace (n+0)%nat with n by lia.
     ring_simplify.
     apply le_eq.
     enough ([2 ! n] == [1 ! S n]) as -> by ring.
     unfold rising_factorial.
     replace (2 + n - 1)%nat with (1 + S n - 1)%nat by lia.
     replace (2-1)%nat with 1%nat by lia.
     replace (1-1)%nat with 0%nat by lia.
     enough (![1] == ![0]) as -> by ring.
     simpl.
     rewrite mulC.
     setoid_replace 1 with (ntimes (S 0) 1) at 1 by (simpl;ring).
     apply inv_Sn_spec.
  - rewrite mul_ps_S.
    unfold Fn_bound.
 Lemma dBound a n : (B n a) -> forall k, (D[0] a) k <= (ntimes (n+1)%nat 1) * M * r * npow r n.
 Proof.
   intros.
   simpl.
   unfold derive_ps.
   setoid_replace (a (n+1)%nat) with ((a (n+1)%nat) *1 ) by (rewrite mul1;reflexivity).
   rewrite ntimes_mult.
   apply (le_trans _ _ _  (norm_mult _ _)).
   apply (le_trans _ _ _  (mul_le_compat_pos (norm_nonneg _ ) (norm_n_le_n _ ))).
   rewrite mulC.
   rewrite !mulA.
   apply mul_le_compat_pos.
   apply ntimes_nonneg.
   apply le_0_1.
   assert (npow r (S n) == r * npow r n) as <- by (simpl;reflexivity).
   replace (n+1)%nat with (S n) by lia.
   apply B.
Qed.

Section Bounds. 

Context `{AbstractFunctionSpace} {d e : nat}.
Context `{TotallyOrderedField (A := (A 0)) (H:=(H 0)) (R_rawRing := (H0 0)) (R_semiRing := (H1 0))}.
 Context `{normK : (NormedSemiRing ((A 0)^e) (A 0) (H := _)  (H0 := (H 0))  (R_rawRing0 := (H0 0%nat)) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }. 
 (* Context {M R : A 0} {Mpos : 0 <= M} {Rpos : 0 <= R}. *)

  Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat))}.
 Definition D_bound (f : (A d)^e) x0 (B : nat -> (A 0)) := forall n i H, (i < d) -> norm ((nth_derivative i f n) @ (x0; H)) <= (B n).
 Definition D_boundi (f : (A d)^e) x0 (B : nat -> (A 0)) i := forall n H, norm ((nth_derivative i f n) @ (x0; H)) <= (B n).
 Definition Fi_bound M R n k := [n]! * [k+2*n]! * ![2*n] *  (npow (1+1) n) * (npow M (n+1)) * npow R (n+k). 
 Definition Fi_pbound M R n i k := ([n]! * [i]! * [k+2*n]! * ![2*n]) * (npow (1+1) n)* (npow M (n+2)) * (npow R (n+k +i )).

 Add Ring TRing: (ComRingTheory (A := (A 0))). 

  Lemma ntimes_pos x n: (0 <= x) -> (0 <= ntimes n x).
  Proof.
    intros.
    induction n.
    simpl;apply le_refl.
    simpl.
    setoid_replace (0 : (A 0)) with (0+0 : (A 0)) by ring.
    apply le_le_plus_le;auto.
  Qed.

  Lemma fact_pos n : 0 <= [n]!.
  Proof.
    induction n.
    simpl.
    apply le_0_1.
    simpl.
    apply mul_pos_pos;try apply IHn.
    setoid_replace (0 : (A 0)) with (0+0 : (A 0)) by ring.
    apply le_le_plus_le; [apply le_0_1|].
    apply ntimes_pos;apply le_0_1.
  Qed.
 Lemma npow_pos : forall x n, (0 <= x) -> 0 <= npow x n.
 Proof.
   intros.
   induction n.
   simpl;apply le_0_1.
   simpl.
   apply mul_pos_pos;auto.
 Qed.

 Lemma  Fi_pbound_spec M R n i k : (Fi_bound M R 0 i) * (Fi_bound M R n k) == Fi_pbound M R n i k.
 Proof.
   unfold Fi_bound, Fi_pbound.
   simpl.
   replace (i+0)%nat with i by lia.
   replace (n+0)%nat with n by lia.
   setoid_replace (npow M (n+2)) with (npow M (n+1) * M).
   setoid_replace (npow R (n+k+i)) with (npow R (n+k) * npow R i)  by (rewrite !npow_plus;ring).
   ring.
   rewrite !npow_plus.
   simpl.
   ring.
 Qed.

 (* Lemma Fi_bound_D M R n i k :  *)

 Lemma nth_derivative_S_prod_at (f g : (A d)^e)  (x0 : (A 0)^d) i n P: (x0 \in_dom f) -> (x0 \in_dom g) -> exists P1 P2, (nth_derivative i (f * g) (S n)) @ (x0; P) == (nth_derivative i (g * (pdiff i f) ) n) @ (x0; P1) + (nth_derivative i (f* (pdiff i g) ) n) @ (x0; P2). 
 Proof.
   intros.
   pose proof (nth_derivative_S_prod1 f g i n).
   destruct (eval_change_f  _ _ _ P H9) as [P' eq].
   assert (x0 \in_dom (nth_derivative i (g * pdiff i f) n)) as D1.
   {
    apply nth_derivative_dom.
    apply dom_mult;auto.
    intros j jle.
    simpl;rewrite pdiff_tuple_nth;auto.
    apply dom_diff;auto.
   }
   assert (x0 \in_dom (nth_derivative i (f * pdiff i g) n)) as D2.
   {
    apply nth_derivative_dom.
    apply dom_mult;auto.
    intros j jle.
    simpl;rewrite pdiff_tuple_nth;auto.
    apply dom_diff;auto.
   }
   exists D1;exists D2.
   rewrite eq.
   apply eval_plus_compat.
 Qed.

 Definition simple_bound (x : nat -> (A 0)^e) (C : A 0) n (r : (A 0))   := forall k, norm (x k) <= C * [k+n]! * npow r k.

 Definition derive_seq (x : nat -> (A 0)^e) k := (fun n => x (n+k)%nat).
 
 Notation "x ^ ( n )" := (derive_seq x n) (at level 2).
 Definition simple_bound_prod (x : nat -> (A 0)^e) (C : A 0) n (r : (A 0)) d1 d2  := forall k, norm (x k) <= (C * [(k+n+d1+d2)%nat]! * [(n+d2)%nat]! * [d1]! * ![(n+d1+d2)%nat]* npow r k).

 Lemma simpl_bound_deriv x C n r k  : simple_bound x C n r -> simple_bound (x ^(k)) (C*npow r k) (n+k) r.
 Proof.
   intros.
   induction k.
   - simpl.
     replace (n+0)%nat with n by lia.
     unfold simple_bound.
     setoid_replace (C*1) with C by ring.
     intros k.
     unfold derive_seq.
     replace (k+0)%nat with k by lia.
     apply H7.
   - intros i.
     replace (x ^ (S k) i) with (x ^ (k) (S i)).
     apply (le_trans _ _ _ (IHk  _)).
     replace (S i + (n+k))%nat with (S (i + n +k)) by lia.
     replace (i + (n+S k))%nat with (S (i + n +k)) by lia.
     simpl.
     ring_simplify.
     apply le_eq.
     ring.
     unfold derive_seq.
     simpl.
     f_equal.
     lia.
  Qed.

 Lemma simpl_bound_prod (f g : nat -> (A 0)^e) C M n r d1 d2 : simple_bound f M 0 r  -> simple_bound  g C n r -> simple_bound_prod (f ^ (d1) * g ^ (d2)) (C* M * npow r (d1+d2)) n r d1 d2.
 Proof.
   intros.
   intros k.
   induction k.
   -  specialize (H7 d1).
     specialize (H8 d2).
     unfold derive_seq.
     simpl.
     apply (le_trans _ _ _ (norm_mult _ _)).
     
     apply (le_trans _ _ _ (mul_le_le_compat_pos (norm_nonneg _) (norm_nonneg _) H7 H8)).
     rewrite npow_plus.
     replace (d1 + 0)%nat with d1 by lia.
     replace (d2 + n)%nat with (n+d2)%nat by lia.
     ring_simplify.
     rewrite !mulA.
     rewrite fact_invfact.
     apply le_eq.
     ring.
   - pose proof (nth_derivative_S_prod_at ((nth_derivative i f d1 * nth_derivative i g d2)) ).
     destruct (eval_change_f _ _ _ (nth_deriva) H8).
 Admitted.

 (* Lemma simple_bound_proper f g x0 x1 C0 C1  n r1 r2 i : f==g -> x0==x1 -> C0==C1 -> r1 == r2  -> simple_bound g x1 C1 n r2 i -> simple_bound f x0 C0 n r1 i. *)
 (* Proof. *)
 (*   intros. *)
 (*   unfold simple_bound, D_boundi. *)
 (*   intros. *)
 (*   rewrite H9. *)
 (*   enough ((nth_derivative i f n0)  == (nth_derivative i g n0)). *)
 (*   destruct (eval_change_f _ _ _ H12 H13). *)
 (*   rewrite H14. *)
 (*   pose proof x. *)
 (*   rewrite H8 in H15. *)
 (*   rewrite (functions.eval_proper _ _ _ _ x H15 );try reflexivity; try apply H8. *)
 (*   rewrite (npow_proper n0 _ _ H10). *)
 (*   apply H11;auto. *)
 (*   apply (nth_derivative_proper i n0 _ _ H7). *)
 (* Qed. *)

 (* Lemma simple_bound_properf {f g x0 C n r i} : f==g -> simple_bound g x0 C n r i -> simple_bound f x0 C n r i. *)
 (* Proof. *)
 (*   intros. *)
 (*   apply (simple_bound_proper f g x0 x0 C C n r r); try reflexivity;auto. *)
 (* Qed. *)


 (* Lemma simpl_bound_deriv f x0 C n r k i : simple_bound f x0 C n r i -> simple_bound (nth_derivative i f k) x0 (C*npow r k) (n+k) r i. *)
 (* Proof. *)
 (*   intros. *)
 (*   induction k. *)
 (*   - simpl. *)
 (*     replace (n+0)%nat with n by lia. *)
 (*     apply (simple_bound_proper f f x0 x0 (C*1) C n r r);try reflexivity;try ring;auto. *)
 (*   - intros j D. *)
 (*    enough (nth_derivative i (nth_derivative i f (S k)) j == nth_derivative i (nth_derivative i f k ) (j+1)%nat). *)
 (*     destruct (eval_change_f _ _ _ D H8). *)
 (*     rewrite H9. *)
 (*     specialize (IHk (j+1)%nat x). *)
 (*     apply (le_trans _ _ _ IHk). *)
 (*     replace (j+1)%nat with (S j) by lia. *)
 (*     replace (j+(n+ S k))%nat with (S (j + n + k)) by lia. *)
 (*     simpl. *)
 (*     apply le_eq. *)
 (*     replace (j+(n+k))%nat with (j+n+k)%nat by lia. *)
 (*     ring. *)
 (*     rewrite !nth_derivative_twice. *)
 (*     replace (S k + j)%nat with (k + (j+1))%nat by lia. *)
 (*     reflexivity. *)
 (*  Qed. *)
 (* Definition simple_bound_prod (f : (A d)^e) (x0 : (A 0)^d) (C : A 0) n (r : (A 0)) i d1 d2  := D_boundi f x0 (fun (k : nat) => (C * [(k+n+d1+d2)%nat]! * [(n+d2)%nat]! * [d1]! * ![(n+d1+d2)%nat]* npow r k)) i. *)

 Opaque eval.
 Lemma simpl_bound_prod (f g : (A d)^e) (x0 : (A 0)^d)  C M n r d1 d2 i : simple_bound f x0 M 0 r i -> simple_bound  g x0 C n r i -> simple_bound_prod ((nth_derivative i f d1) * (nth_derivative i g d2)) x0 (C* M * npow r (d1+d2)) n r i d1 d2.
 Proof.
   intros.
   intros k Hk.
   assert (forall n, x0 \in_dom (nth_derivative i f n)).
   admit.
   assert (forall n, x0 \in_dom (nth_derivative i g n)).
   admit.
   induction k.
   - simpl.
     rewrite (eval_mult_compat _ _ _ (H9 d1) (H10 d2)).
     specialize (H7 d1 (H9 d1)).
     simpl in H7.
     specialize (H8 d2 (H10 d2)).
     simpl in H8.
     apply (le_trans _ _ _ (norm_mult _ _)).
     
     apply (le_trans _ _ _ (mul_le_le_compat_pos (norm_nonneg _) (norm_nonneg _) H7 H8)).
     rewrite npow_plus.
     replace (d1 + 0)%nat with d1 by lia.
     replace (d2 + n)%nat with (n+d2)%nat by lia.
     ring_simplify.
     rewrite !mulA.
     rewrite fact_invfact.
     apply le_eq.
     ring.
   - pose proof (nth_derivative_S_prod_at ((nth_derivative i f d1 * nth_derivative i g d2)) ).
     destruct (eval_change_f _ _ _ (nth_deriva) H8).
 Admitted.

 Lemma D_bound_prod M R f g x0 n : (0 <= M) -> (0 <= R) -> (x0 \in_dom f) -> (x0 \in_dom g) -> D_bound f x0 (Fi_bound M R 0) -> D_bound  g x0 (fun i => Fi_bound M R n (i+1)) -> D_bound (f*g) x0 (Fi_bound M R (n+1)).
 Proof.
   intros Mpos Rpos D1 D2 B1 B2. 
   intros k i D3 ile.
   induction k;intros.
   - simpl nth_derivative.
     rewrite (eval_mult_compat f g x0  D1 D2 D3).
     apply (le_trans _ _ _ (norm_mult _ _)).
     specialize (B1 0%nat i D1 ile).
     specialize (B2 0%nat i D2 ile).
     simpl nth_derivative in B1, B2.
     apply (le_trans _ _ _ (mul_le_le_compat_pos (norm_nonneg _) (norm_nonneg _)  B1 B2)).
     Opaque ntimes Init.Nat.mul.
     rewrite Fi_pbound_spec.
     simpl.
     unfold Fi_pbound,Fi_bound.
     simpl.
     ring_simplify.
     rewrite mulC.
     rewrite !(mulA (npow R _)).
     apply mul_le_compat_pos;try (apply npow_pos;auto).
     replace (n+1+1)%nat with (n+2)%nat by lia.
     rewrite !(mulC _ (npow M _)).
     apply mul_le_compat_pos;try (apply npow_pos;auto).
     rewrite !(mulC _ (npow _ _ )).
     rewrite !mulA.
     rewrite !fact_invfact.
     ring_simplify.
     replace (n+1)%nat with (S n) by lia.
     simpl.
     rewrite (mulA (1+1)).
     rewrite (mulC (1+1)).
     rewrite !mulA.
     apply mul_le_compat_pos.
     apply npow_pos;auto; try apply lt_0_2.

     Transparent ntimes.
     simpl.
     rewrite ntimes_twice.
     rewrite !(mulC [n]!).
     rewrite <-!mulA.
     rewrite !(mulC _ [n]!).
     apply mul_le_compat_pos;try apply fact_pos.
     simpl in *.
     rewrite (mulC _ (1+1)), distrL.
     apply le_plus_compat.
     rewrite mul1.
     rewrite <-add0 at 1.
     rewrite addC.
     apply le_plus_compat.
     apply le_0_1.
  -  destruct (nth_derivative_S_prod_at f g x0 i k D3 D1 D2) as [D1' [D2' Heq]].
     rewrite Heq.
     
End  Bounds.
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
  Context `{AbstractFunctionSpace }.
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
