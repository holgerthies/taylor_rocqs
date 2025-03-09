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
 Section FactorialOrder.
  Context `{TotallyOrderedField}.
 Context `{normK : (NormedSemiRing A A (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }.
  Context `{invSn : Sn_invertible (A := A) (H := _) (R_rawRing := _)}. (* Replace by proof *)

  Add Ring TRing: (ComSemiRingTheory (A := A)). 
  Lemma ntimes_nonneg x n: (0 <= x) -> 0 <= ntimes n x.
  Proof.
    intros.
    induction n.
    simpl;apply le_refl.
    simpl.
    setoid_replace 0 with (0 + 0) by ring.
    apply le_le_plus_le;auto.
 Qed.
  Lemma fact_pos n : 0 <= [n]!.
  Proof.
    induction n.
    simpl.
    apply le_0_1.
    simpl.
    apply mul_pos_pos;try apply IHn.
    setoid_replace (0 : A) with (0+0 ) by ring.
    apply le_le_plus_le; [apply le_0_1|].
    apply ntimes_nonneg;apply le_0_1.
  Qed.

    
  Lemma inv_Sn_pos n : 0 <= inv_Sn n.
  Proof.
  Admitted.    

  Lemma invfact_pos n : 0 <= ![n].
  Proof.
    induction n.
    simpl.
    apply le_0_1.
    simpl.
    apply mul_pos_pos;try apply IHn.
    apply inv_Sn_pos.
   Qed.
End FactorialOrder.
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
  
 Context `{norm1 : norm 1 == 1}.
 Context {M r : A} {Mge0: 0 <= M} {rge0: 0 <= r}.
 

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

 Lemma rising_factorial0 n : [n ! 0]  == 1.
 Proof.
   unfold rising_factorial.
   replace (n+0-1)%nat with (n-1)%nat by lia.
   rewrite fact_invfact.
   reflexivity.
 Qed.
 
 Definition inv2  := inv_Sn 1.

 Notation "| a | <= b" := (forall k, norm (a k) <= b k) (at level 70).
 

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

  Lemma norm_ntimes_le n x : norm (ntimes n x) <= ntimes n 1 * norm x.
  Proof.
    induction n.
    simpl.
    assert (norm 0 == 0) as -> by (apply norm_zero;reflexivity).
    ring_simplify.
    apply le_refl.
    simpl.
    apply (le_trans _ _ _ (norm_triangle _ _ )).
    ring_simplify.
    rewrite addC.
    apply le_plus_compat.
    rewrite mulC.
    apply IHn.
  Qed.
  Lemma norm_ntimes_le_ntimes_norm n x : norm (ntimes n x) <= ntimes n (norm x).
  Proof.
    apply (le_trans _ _ _ (norm_ntimes_le _ _)).
    rewrite mulC, <-ntimes_mult.
    rewrite mul1.
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

  Notation "# n" := (ntimes n 1) (at level 2).
  Lemma rising_factorial_s n k : [k+1!n+1] == #(k+1) * [(k+2) ! n].
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

  Lemma rising_factorial_sk n k : [k+1!n] ==   #(k+1) *  inv_Sn (k+n) * [(k+2) ! n].
  Proof.
    simpl.
    unfold rising_factorial.
    replace (k + 1 + n - 1)%nat with (k + n)%nat by lia.
    replace (k + 1 - 1)%nat with k by lia.
    replace (k + 2 + n- 1)%nat with (S (k + n))%nat by lia.
    replace (k + 2 - 1)%nat with (S k)%nat by lia.
    replace (k + 1)%nat with (S k)%nat by lia.
    setoid_replace (#(S k) * inv_Sn (k + n) * ([S (k + n) ]! * ![ S k])) with ([k+n]!*![k] * (#(S (k+n))  * inv_Sn (k+n)) * (#(S k) * inv_Sn k)) by (simpl;ring).
    rewrite !inv_Sn_spec;ring.
  Qed.
  Lemma rising_factorial_sn n k : [S k! S n] ==   #(k+n+1) * [S k ! n].
  Proof.
    simpl.
    unfold rising_factorial.
    replace (S k + S n -1)%nat with (S (k + n))%nat by lia.
    replace (S k + n -1)%nat with (k + n )%nat by lia.
    replace (k+n+1)%nat with (S (k + n) )%nat by lia.
    simpl.
    ring.
  Qed.
 Lemma le_eq x y : (x == y) -> (x <= y).
 Proof.
   intros ->.
   apply le_refl.
 Qed.
   Definition f_bound C k := C * npow r k.
   Definition g_bound C n k := C * [(k+1)!2*n+1] * npow r k.
   Definition fg_bound C1 C2 n k := inv_Sn (2*n+1)  *  C1*C2 *  [(k+1)!2*n+2] * npow r k.


   Lemma f_bound_S C : (fun n => (f_bound C (S n))) == (f_bound (C*r)).
   Proof.
       intros n.
       unfold f_bound.
       simpl.
       ring.
   Qed.

    Lemma nat_plus_compat a b: #(a+b)%nat == #a + #b.
    Proof.
      induction b.
      replace (a+0)%nat with a by lia.
      simpl.
      ring.
      replace (a+S b)%nat  with (S (a+b)) by lia.
      simpl.
      rewrite IHb.
      ring.
    Qed.

    Lemma nat_mult_compat a b: #(a*b)%nat == #a * #b.
    Proof.
      induction b.
      replace (a*0)%nat with 0%nat by lia.
      simpl.
      ring.
      replace (a*S b)%nat  with (a+a*b)%nat by lia.
      rewrite nat_plus_compat.
      rewrite IHb.
      simpl.
      ring.
    Qed.

    Lemma rat_plus1 a b c : #a +  inv_Sn c * #b == #(a*(c+1) + b) * inv_Sn c.
    Proof.
     simpl.
     rewrite nat_plus_compat, nat_mult_compat.
     ring_simplify.
     replace (c+1)%nat with (S c) by lia.
     rewrite mulA.
     rewrite (mulC _ (# (S c))).
     rewrite inv_Sn_spec.
     ring.
   Qed.

   Lemma fg_bounded (a b : @mps A 1) C1 C2 n : |a| <= f_bound C1 -> |b| <= g_bound C2 n -> |a*b| <= fg_bound C1 C2 n.
   Proof.
     intros.
     pose proof (ps_mult_monotone _ _ _ _ H1 H2).
     apply (le_trans _ _ _ (H3 _)).
     apply le_eq.
     clear H1 H2 H3.
     generalize dependent C1.
     induction k;intros.
     - pose proof (mul_ps_zero (d:=0)  (f_bound C1) (g_bound C2 n)) as dzero.
       rewrite dzero.
       unfold f_bound, g_bound, fg_bound.
       simpl.
       ring_simplify.
       replace  (n + (n+0)+2)%nat with (S (2*n+1))%nat by lia.
       replace  (n + (n+0)+1)%nat with ((2*n + 1))%nat by lia.
       rewrite rising_factorial_sn.
       replace (0+(2*n+1)+1)%nat with (S (2*n+1)) by lia.
       rewrite !mulA.
       rewrite <-(mulA (inv_Sn _ )).
       rewrite (mulC (inv_Sn _ )).
       rewrite inv_Sn_spec.
       ring.
    - pose proof (mul_ps_S (d := 0)) as M0.
      rewrite !M0.
      pose proof (f_bound_S C1).
      assert (g_bound C2 n == g_bound C2 n) by reflexivity.
      pose proof (mul_proper _ _ H1 (g_bound C2 n) (g_bound C2 n) H2 k).
      rewrite H3.
      rewrite IHk.
      unfold f_bound, g_bound, fg_bound.
      Opaque Nat.mul.
      simpl.
      ring_simplify.
      replace (2 * n + 2)%nat with (S (2*n +1))%nat by lia.
      enough ([S (k+1)!2*n+1] + inv_Sn (2*n+1) * [k+1!S (2*n+1)] ==  inv_Sn (2 * n + 1) * [S (k + 1) ! S (2 * n + 1)]) by (rewrite !mulA, <-H4;ring).
      rewrite !rising_factorial_sn.
      replace (S (2*n+1)) with ((2*n+1)+1)%nat by lia.
      rewrite rising_factorial_s.
      ring_simplify.
      replace (k+2)%nat with (S (k+1)) by lia.
      replace (k+1 + (2*n+1)+1)%nat with (S (2*n + k +2)) by lia.
      rewrite !mulA.
      enough (1 + inv_Sn (2 * n + 1) * # (k + 1) ==  inv_Sn (2 * n + 1) * # (S (2 * n + k + 2))) as <- by ring.
      setoid_replace 1 with (#1) at 1 by (simpl;ring).
      rewrite rat_plus1.
      replace (1*(2*n+1+1) + (k+1))%nat with (S (2*n+k+2)) by lia.
      ring.
   Qed.
   Definition Fn_bound n k := npow (inv2) n * ![n] * [k+1!2*n]* npow M (n+1) * npow r (n + k).
   Definition DFn_bound n k :=  npow (inv2) n * ![n] * [(k+1)!2*n+1]* npow M (n+1) * npow r (n + (k + 1)).
     
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
   rewrite (mulC (npow _ _)).
   rewrite !mulA.
   rewrite (mulC ![n]).
   rewrite !mulA.
   apply mul_le_compat_pos.
   apply ntimes_nonneg.
   apply le_0_1.
   rewrite <-mulA.
   replace (k+2)%nat with ((k+1)+1)%nat by lia.
   apply (le_trans _ _ _ (H1 _)).
   unfold Fn_bound.
   apply le_eq.
   ring.
 Qed.

   Lemma DFn_boundg n : DFn_bound n == g_bound (npow (inv2) n * ![n] * (npow M (n+1)) * npow r (n+1) ) n. 
   Proof.
     intros k.
     unfold DFn_bound, g_bound.
     replace (n+(k+1))%nat with ((n +1) + k)%nat by lia.
     rewrite !npow_plus.
     ring.
  Qed.

   Lemma DFn_bound_spec' (a : @mps A 1) n : |a| <= Fn_bound n -> |D[0] a| <= g_bound (npow (inv2) n * ![n] * (npow M (n+1)) * npow r (n+1) ) n.
   Proof.
     intros.
     rewrite <-(DFn_boundg n k).
     apply DFn_bound_spec;auto.
  Qed.

  Lemma inv_Sn_unique a b : # (S a) * b == 1 <-> b == inv_Sn a.   
  Proof.
    split; [|intros ->;apply inv_Sn_spec].
    intros.
    setoid_replace (inv_Sn a) with (# (S a) * b * inv_Sn a) by (rewrite H1;ring).
    rewrite  mulA.
    rewrite (mulC b), <-mulA.
    rewrite inv_Sn_spec.
    ring.
  Qed.

  Lemma bound_prod  (a b : @mps A 1) n : |a| <= f_bound M -> |b| <= Fn_bound n -> |a * (D[0] b) | <= Fn_bound (n+1). 
  Proof.
  intros H1 H2.
   pose proof (DFn_bound_spec' b n H2).
   pose proof (fg_bounded _ _ _ _ _ H1 H3).
   intros k.
   apply (le_trans _ _ _ (H4 _)).
   apply le_eq.
   unfold fg_bound, Fn_bound.
   setoid_replace M with (npow M 1) at 1 by (simpl;ring).
   rewrite !npow_plus.
   replace (2*(n+1))%nat with (2*n+2)%nat by lia.
   replace (n+1)%nat with (S n) by lia.
   ring_simplify.
   rewrite !mulA.
   enough (npow inv2 1 * ![ S n] == inv_Sn (2*n + 1) * ![n]) as -> by ring.
   simpl.
   ring_simplify.
   enough (inv2 * inv_Sn n == inv_Sn (2*n+1)) as <- by ring.
   apply inv_Sn_unique.
   replace (S (2*n+1)) with (2 * (S n))%nat by lia.
   rewrite nat_mult_compat.
   setoid_replace (#2 * # (S n) * (inv2 * inv_Sn n)) with ((#2 * inv2 ) * (# (S n) * inv_Sn n)) by ring.
   unfold inv2.
   rewrite !inv_Sn_spec.
   ring.
 Qed.

  Lemma npow_mult x  y n : npow (x*y) n == npow x n * npow y n.
  Proof.
    induction n.
    simpl.
    ring.
    simpl.
    rewrite IHn.
    ring.
  Qed.

 Lemma npow_pos : forall x n, (0 <= x) -> 0 <= npow x n.
 Proof.
   intros.
   induction n.
   simpl;apply le_0_1.
   simpl.
   apply mul_pos_pos;auto.
 Qed.

 Lemma npow_inv m n : npow #(S m) n * npow (inv_Sn m) n == 1.
 Proof.
   induction n.
   simpl.
   ring.
   setoid_replace (npow # (S m) (S n) * npow (inv_Sn m) (S n)) with (# (S m) * inv_Sn m * ((npow (# (S m)) n) * (npow (inv_Sn m) n))) by (simpl;ring).
   rewrite IHn.
   ring_simplify.
   rewrite inv_Sn_spec.
   ring.
 Qed.


  Lemma ntimes_monotone  n m: (n <= m)%nat -> (# n <= # m). 
  Proof.
    simpl.
    induction m.
    intros.
    assert (n = 0)%nat as -> by lia.
    apply le_refl.
    intros.
    assert (n <= m \/ n = S m)%nat by lia.
    destruct H2.
    simpl.
    setoid_replace (#n) with (0 + #n) by ring.
    apply le_le_plus_le.
    apply le_0_1.
    apply IHm;auto.
    rewrite H2.
    apply le_refl.
  Qed.

  Lemma ntimes_pos_monotone  n m x : (0 <= x) ->  (n <= m)%nat -> (ntimes n x <= ntimes m x). 
  Proof.
    intros.
    setoid_replace (x) with (x*1) by ring.
    rewrite !ntimes_mult.
    apply mul_le_compat_pos;auto.
    apply ntimes_monotone;auto.
  Qed.

  Lemma ntimes_monotone2  n x y :  (x <= y) -> (ntimes n x <= ntimes n y). 
  Proof.
    simpl.
    intros.
    setoid_replace (x) with (x*1) by ring.
    setoid_replace (y) with (y*1) by ring.
    rewrite !ntimes_mult.
    rewrite (mulC x), (mulC y).
    apply mul_le_compat_pos;try apply ntimes_nonneg;try apply le_0_1;auto.
  Qed.
 Lemma Fn_bound0 : forall n, Fn_bound n 0 <= [n]! *  M * npow (#2*M*r) n.  
 Proof.
   intros.
   unfold Fn_bound.
   simpl.
   replace (n+0)%nat with n by lia.
   rewrite !npow_mult, npow_plus.
   simpl.
   ring_simplify.
   assert (  npow inv2 n * ![ n] * [1 ! 2 * n] * npow M n * M * npow r n ==  npow M n * M * npow r n * (npow inv2 n * ![ n] * [1 ! 2 * n] )) as -> by ring.
   rewrite !mulA.
   apply mul_le_compat_pos;try apply npow_pos;auto.
   apply mul_le_compat_pos;auto.
   apply mul_le_compat_pos;try apply npow_pos;auto.
   rewrite rising_factorial1.
   pose proof (npow_inv 1 n).
   rewrite (mulC [n]!).
   setoid_replace (npow inv2 n) with (npow #2 n * npow inv2 n * npow inv2 n) by (rewrite npow_inv;ring).
   rewrite !mulA.
   apply mul_le_compat_pos; try (apply npow_pos;apply ntimes_nonneg;apply le_0_1).
   rewrite <-!mulA.
   rewrite <-npow_plus.
   rewrite (mulC _ ![n]).
   clear H1.
   induction n.
   - simpl.
     replace (2*0)%nat with 0%nat by lia.
     simpl;ring_simplify.
     apply le_refl.
  - replace (S n + S n)%nat with (S (S (n+n))) by lia.
    replace (2*S n)%nat with (S (S (2*n))) by lia.
    setoid_replace (![S n] * npow inv2 (S (S (n+n))) * [S(S (2 *n))]!) with (((![n] * npow inv2 (n+n) * [2*n]!)) * (inv2 * inv2 * # (S (S (2 *n))) *# (S (2 * n)) * inv_Sn n)) by (simpl;ring).
    setoid_replace [S n]! with ([n]! * #(S n)) by (simpl;ring).
    apply mul_le_le_compat_pos.
    apply mul_pos_pos;try apply fact_pos.
    apply mul_pos_pos;try apply invfact_pos;apply npow_pos;apply inv_Sn_pos.
    apply mul_pos_pos; try apply mul_pos_pos; try apply mul_pos_pos; try apply ntimes_nonneg; try apply le_0_1; try apply inv_Sn_pos.
    apply mul_pos_pos; apply inv_Sn_pos.
    apply IHn.
    replace (S (S (2 *n))) with (2*(S n))%nat by lia. 
    rewrite nat_mult_compat.
    rewrite <-mulA.
    rewrite (mulC _ #2).
    rewrite <-mulA.
    unfold inv2.
    rewrite inv_Sn_spec.
    ring_simplify.
    setoid_replace (inv_Sn 1 * #(S n) * #(S(2*n)) * inv_Sn n) with ((#(S n) * inv_Sn n) * (inv_Sn 1 * #(S(2*n)))) by ring.
    rewrite inv_Sn_spec.
    ring_simplify.

    apply (le_trans _ (inv_Sn 1 * # (2*(S n)))).
    apply mul_le_compat_pos;try apply inv_Sn_pos.
    apply ntimes_monotone;lia.
    rewrite nat_mult_compat.
    rewrite <-mulA.
    rewrite (mulC _ (#2)).
    rewrite inv_Sn_spec.
    ring_simplify.
    apply le_refl.
  Qed.
End Bounds.

Section Multiindex.

  Context `{A_comRing : SemiRing}.

  #[global] Instance nat_setoid : Setoid nat.
  Proof.
    exists (fun x y => (x=y)).
    constructor; intros a; intros;try auto.
    rewrite H0, H1;auto.
  Defined.

  #[global] Instance nat_rawring : RawRing (A := nat).
  Proof.
    constructor.
    apply 0%nat.
    apply 1%nat.
    intros a b.
    apply (a+b)%nat.
    intros a b.
    apply (a*b)%nat.
  Defined.

  #[global] Instance nat_semiring : SemiRing (A := nat).
  Proof.
    constructor;intros;simpl;try lia;intros a b eq c d eq';lia.
  Defined.

 Definition ps_index {d} (n : nat^d) (a : @mps A d) : A.
 Proof.
   induction d.
   apply a.
   destruct (destruct_tuple_cons n) as [hd [tl P]].
   apply (IHd tl (a hd)).
 Defined.


 Definition order {d} (n : nat^d) : nat.
 Proof.
   induction d.      
   apply 0%nat.
   destruct (destruct_tuple_cons n) as [hd [tl P]].
   apply (hd + (IHd tl))%nat.
 Defined.

   #[global] Instance ps_index_proper d n : Proper (SetoidClass.equiv ==> SetoidClass.equiv) (@ps_index d n).
   Proof.
   Admitted.

    Lemma ps_index_0 {d} ix :  ps_index (d := d) ix 0 ==0.
    Proof.
      induction d.
      simpl.
      reflexivity.
      simpl.
      destruct (destruct_tuple_cons ix) as [hd [tl P]].
      apply IHd.
    Qed.

    Lemma ps_index_1 {d} ix :  ps_index (d := d) ix 1 == match (order ix) with  0 => 1 | _ => 0 end.
    Proof.
      induction d.
      simpl;reflexivity.
      simpl.
      destruct (destruct_tuple_cons ix) as [hd [tl ->]].
      destruct hd.
      simpl.
      apply IHd.
      simpl.
      rewrite ps_index_0.
      reflexivity.
    Qed.

    Lemma order_cons {d} hd tl : order (d:=S d) (tuple_cons hd tl) = (hd + order tl)%nat.
    Proof.
      simpl.
      destruct (destruct_tuple_cons (tuple_cons hd tl)) as [hd' [tl' P]].
      apply tuple_cons_ext in P.
      destruct P as [-> ->].
      lia.
    Qed.

    Lemma order_zero_split {d} hd tl : order (d:=S d) (tuple_cons hd tl) = 0%nat -> (hd = 0%nat /\ order tl = 0%nat).
    Proof.
      intros.
      rewrite order_cons in H0.
      lia.
    Qed.

    Lemma order_zero1 {d} n : (order (d:=d) n) = 0%nat -> (forall i, i< d -> tuple_nth i n 0%nat = 0%nat).
    Proof.
      intros.
      generalize dependent i.
      induction d;intros; try lia.
      destruct (destruct_tuple_cons n) as [hd [tl ->]].
      apply order_zero_split in H0.
      destruct i.
      rewrite tuple_nth_cons_hd.
      apply H0.
      rewrite tuple_nth_cons_tl.
      apply IHd;try lia.
    Qed.

    Lemma order_zero {d} n : (order (d:=d) n) = 0%nat -> (forall i,  tuple_nth i n 0%nat = 0%nat).
    Proof.
      intros.
      destruct (Nat.lt_ge_cases i d).
      apply order_zero1;auto.
      destruct n.
      simpl.
      rewrite nth_overflow;auto;lia.
     Qed.

    Lemma zero_order {d} : (order (d:=d) 0) = 0%nat.
    Proof.
      induction d.
      simpl;reflexivity.
      rewrite vec0_cons.
      rewrite order_cons.
      rewrite IHd.
      simpl.
      reflexivity.
    Qed.
End Multiindex.
Section MultiBounds.
  Context `{TotallyOrderedField}.
 Context `{normK : (NormedSemiRing A A (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }.
  Context `{invSn : Sn_invertible (A := A) (H := _) (R_rawRing := _)}. (* Replace by proof *)
  
 Context {norm1 : norm 1 == 1}.


 Add Ring KRing: (ComRingTheory (A := A)).
 Definition mps_bound {d} (a : @mps A d) (b : @mps A 1):= forall n, norm (ps_index n a) <= (b (order n)). 
 Definition mps_tuple_bound {d} {e} (a : (@mps A d)^e) (b : (@mps A 1)):= forall i n, i < e -> norm (ps_index n (tuple_nth i a 0)) <= b (order n). 
   Notation "| a | <= b" := (mps_bound a b) (at level 70).

   Instance mps_bound_proper d : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (@mps_bound d).
   Proof.
   Admitted.
   (* Lemma  index_mult {d} (a b : @mps A (S d)) (hd : nat) tl : ps_index tl ((a * b) hd) ==  ((fun (i : nat) => ps_index tl (a i)) * (fun i => ps_index tl (b i))) hd. *)
   (* Proof. *)
   (*   Opaque mul. *)
   (*   induction hd. *)
   (*   simpl. *)
   (*   assert ((a * b) 0%nat == (a 0%nat) * (b 0%nat)). *)
   (*   admit. *)
   (*   rewrite H1. *)
   (*   pose proof (mul_ps_zero (d := 0)) as M0. *)
   (*   rewrite M0. *)
   (*   rewrite mul_ps_zero. *)
   (*   destruct (destruct_tuple_cons tl) as [h' [t' P']]. *)
   (*   induction d. *)
   (*   enough (a == (fun i => a i) /\ (b == (fun i => b i))) as [H1 H2] by apply (mul_proper _ _ H1 _ _ H2 hd). *)
   (*   split;intros i;reflexivity. *)
   (*   simpl. *)

   (*   intros k. *)
   (*   apply a. *)
   (*   simpl. *)
   (*   rewrite a. *)
   (*   unfold mult_ps. *)
   (*   Search  mult_psProper. *)
   (*   rewrite H1. *)
   (*   simpl *)
   (*   auto. *)

  Lemma mps_bound_S {d} (a : @mps A (S d)) (b : (@mps A 1)): (forall i, mps_bound (a i) (fun n => b (i+n)%nat)) <-> mps_bound a b.
  Proof.
    split.
    - intros H2 k.
      simpl.
      destruct (destruct_tuple_cons k) as [hd [tl P]].
      specialize (H2 hd tl).
      simpl in H2.
      apply H2.
   -  intros.
      intros k.
      specialize (H1 (tuple_cons i k)).
      simpl in H1.
      destruct (destruct_tuple_cons (tuple_cons i k)) as [hd' [tl' P']].
      apply tuple_cons_ext in P'.
      destruct P' as [-> ->].
      apply H1.
  Qed.

   Lemma mult_ps_shift (a b : @mps A 1) i :forall n, (a * b) (i + n)%nat == ((fun j => (a (i + j)%nat)) * (fun j => (b (i + j)%nat))) n.
   Proof.
       intros.
    Admitted.

   Instance single_index_proper {d}  (n : nat) : Proper (SetoidClass.equiv ==> SetoidClass.equiv) (fun (a : @mps A (S d)) => (a n)).
   Proof.
     intros a b Heq.
     apply seq_A_setoid.
     rewrite Heq.
     reflexivity.
   Defined.
   Lemma ps_index_plus {d} (a b : @mps A d) n : ps_index n (a+b) == ps_index n a + ps_index n b. 
   Proof.
     induction d.
     simpl.
     reflexivity.
     Opaque add.
     simpl.
     destruct (destruct_tuple_cons n) as [hd [tl P]].
     enough ((a+b) hd == a hd + b hd) as ->.
     apply IHd.
     Transparent add.
     simpl.
     unfold sum_ps.
     reflexivity.
  Qed.
   Lemma zero_ps_le_zero {d} : |(0 : @mps A d)|  <= zero_ps.
   Proof.
     simpl.
     unfold zero_ps.
     intros k.
     induction d.
     simpl.
     setoid_replace (norm 0) with 0 by (rewrite norm_zero;reflexivity).
     apply le_refl.
     simpl.
     destruct (destruct_tuple_cons k) as [hd [tl P]].
     simpl.
     apply IHd.
   Qed.

   Lemma mps_sum_monotone {d} (a : nat -> @mps A d) (b: nat -> @mps A 1) N : (forall n, (n < N) -> |a n| <= b n) -> |(sum a N)| <= sum b N.
   Proof.
     intros.
     induction N.
     unfold sum.
     simpl.
     apply zero_ps_le_zero.
     rewrite !sum_S.
     intros k.
     rewrite !ps_index_plus.
     simpl;unfold sum_ps.
     apply (le_trans _ _ _ (norm_triangle _ _)).
     apply le_le_plus_le.
     apply IHN.
     intros;apply H1;lia.
     apply H1.
     lia.
   Qed.
   Lemma mps_sum_same {d} (a : nat -> @mps A d) (b: @mps A 1) N : (forall n, (n < N) -> |a n| <= b) -> |(sum a N)| <= ntimes N b. 
   Proof.
     intros.
     enough (ntimes N b == sum (fun _ => b) N) as ->.
     apply mps_sum_monotone.
     apply H1.
     induction N.
     simpl.
     intros.
     unfold sum.
     simpl.
     reflexivity.
     rewrite !sum_S.
     Opaque add.
     simpl ntimes.
     rewrite IHN.
     rewrite addC.
     reflexivity.
     intros.
     apply H1.
     lia.
  Qed.
   
  Lemma mps_mult_monotone {d} (a b : @mps A d) a' b' : (|a| <= a') -> |b| <= b' -> |a*b| <= a' * b'.
  Proof.
     intros.
     generalize dependent b'.
     generalize dependent a'.
   induction d; intros.
   - simpl.
     intros k.
     simpl.
     unfold mult_ps, powerseries.convolution_coeff.
     simpl.
     apply (le_trans _ _ _ (norm_mult _ _)).
     simpl.
     ring_simplify.
     specialize (H1 k).
     specialize (H2 k).
     simpl in H1, H2.
     apply (mul_le_le_compat_pos);try apply norm_nonneg;auto.
   - apply mps_bound_S.
     intros.
     intros k.
     rewrite  mult_ps_shift.
     induction i.
     + rewrite (mul_ps_zero (d:=d) a b).
       apply IHd.
       pose proof (proj2 (mps_bound_S a a') H1).
       apply H3.
       apply (proj2 (mps_bound_S b b') H2).
     +   rewrite (mul_ps_S   a b).
         Opaque mul.
         pose proof (mult_ps_shift (fun j => a' (i + j)%nat) (fun j => b' (i + j)%nat) 1 (order k)).
         simpl in H3.
        assert (((fun j => (a' (S i+ j)%nat)) * (fun j => (b' (S i + j)%nat)))  == ((fun j => (a' (i+ S j)%nat)) * (fun j => (b' (i+ S j)%nat)))  ).
        {
          apply mul_proper;apply seq_A_setoid;intros j;replace (i+ S j)%nat with (S i + j)%nat by lia;reflexivity.
        }
        rewrite (single_index_proper (d := 0) (order k) _ _ H4).
        rewrite <-H3.
        setoid_rewrite (mul_ps_S (d:=0)).
        rewrite ps_index_plus.
        apply (le_trans _ _ _ (norm_triangle _ _ )).
        apply le_le_plus_le;auto.
        assert (I0 : |a 0%nat| <= a') by (apply mps_bound_S;auto).
        assert (I1: |b (S i)| <= (fun n => b' ((S i) + n )%nat)) by (apply mps_bound_S;auto).
        specialize (IHd (a 0%nat) (b (S i)) _ I0 _ I1 k).
        apply (le_trans _ _ _ IHd).
        simpl.
     Admitted.
  

    Lemma IVP_Di_S {d :nat} (a : (@mps A d)^d) i n : IVP_Di a (S n) i == (sum (fun j => (tuple_nth j a 0) * (D[j] (IVP_Di a n i))) d).
    Proof.
      simpl;auto.
      reflexivity.
    Qed.


    Lemma ps_index_comp1 {d} ix i :  ps_index (d := d) ix (comp1  i) == match (order ix) with
                                                                         | 1 => match (tuple_nth i ix 0%nat) with
                                                                               |  1 => 1 | _ => 0  end
                                                                         | _ => 0
                                                                          end.
    Proof.
      generalize dependent d.
      induction i;intros;try (simpl;reflexivity).
      - simpl.
        destruct d;simpl;try reflexivity.
        destruct (destruct_tuple_cons ix) as [hd [tl P]].
        simpl.
        destruct hd eqn:E.
        simpl.
        rewrite ps_index_0.
        rewrite P.
        rewrite tuple_nth_cons_hd.
        destruct (order tl); try destruct n;try reflexivity.
        simpl.
        destruct n;simpl;[|rewrite ps_index_0;reflexivity].
        rewrite P.
        rewrite tuple_nth_cons_hd.
        rewrite ps_index_1.
        reflexivity.
      - simpl.
        destruct d; simpl; try reflexivity.
        destruct (destruct_tuple_cons ix) as [hd [tl P]].
        simpl.
        destruct hd.
        + simpl.
          rewrite P.
          rewrite tuple_nth_cons_tl.
          apply IHi.
        + rewrite ps_index_0.
          rewrite P.
          rewrite tuple_nth_cons_tl.
          simpl.
          destruct (order tl) eqn:E.
          simpl;rewrite order_zero; try lia; destruct hd; simpl;try reflexivity.
          destruct hd;simpl;try reflexivity.
    Qed.

    Lemma ntimes_index {d} (a : @mps A (S d)) n i : (ntimes n a) i == ntimes n (a i). 
    Proof.
      induction n.
      simpl.
      reflexivity.
      intros .
      simpl ntimes.
      Transparent add.
      simpl add.
      unfold sum_ps.
      rewrite IHn.
      reflexivity.
    Qed.

    Lemma ntimes_ps_index {d} (a : @mps A d) n i : ps_index i (ntimes n a) == ntimes n (ps_index i a ). 
    Proof.
      induction n.
      simpl.
      rewrite ps_index_0.
      reflexivity.
      simpl.
      rewrite ps_index_plus.
      rewrite IHn.
      reflexivity.
    Qed.
    Lemma norm_zero_eq : norm 0 == 0.
    Proof.
        setoid_replace (norm 0) with 0 by (rewrite norm_zero;reflexivity).
        apply reflexivity.
     Qed.

  Lemma mps_derive_monotone {d} (a : @mps A (S d)) b : |a| <= b ->  (|pdiff 0 a| <= derive_ps b).
  Proof.
       intros H2 k.
       simpl.
       destruct (destruct_tuple_cons k) as [hd [tl ->]].
       pose proof (proj2 (mps_bound_S a b)  H2 hd).
       unfold derive_ps.
       rewrite ntimes_ps_index.
       pose proof (proj2 (mps_bound_S a b) H2 (hd+1)%nat tl).
       simpl in H3.
       apply (le_trans _ _ _ (norm_ntimes_le _ _)).
       setoid_replace (b (hd + order tl + 1)%nat) with (b (hd+order tl + 1)%nat * 1) by (rewrite mul1;reflexivity). 
       rewrite ntimes_mult.
       rewrite mulC.
       apply (mul_le_le_compat_pos); try apply ntimes_nonneg; try apply le_0_1; try apply norm_nonneg.
       replace (hd+order tl + 1)%nat with (hd+1 + order tl)%nat by lia.
       apply H3.
       apply ntimes_monotone;lia.
 Qed.


  Lemma mps_bound_nonneg {d} (a : @mps A (S d)) b : (|a| <= b) -> forall i, 0 <= (b i). 
  Proof.
    intros.
    enough ({t : nat^(S d) | order t = i%nat}) as [t T].
    {
      specialize (H1 t).
      rewrite T in H1.
      apply (le_trans _ _ _ (norm_nonneg  _) H1).
    }
    clear a b H1.
    induction d.
    exists (tuple_cons i nil_tuple).
    simpl;lia.
    destruct IHd.
    exists (tuple_cons 0%nat x).
    rewrite order_cons.
    lia.
  Qed.
  
  Lemma mps_diff_monotone {d} (a : @mps A d) b i : (i <d) -> (|a| <= b) -> (|pdiff i a| <= pdiff 0 b).
    generalize dependent i .
    generalize dependent b .
    induction d;try lia.
    intros.
    revert H2.
    destruct i; [apply mps_derive_monotone|].
    intros H2 k.
    simpl.
    destruct (destruct_tuple_cons k) as [hd [tl P]].
    assert (i < d)%nat by lia.
    pose proof (proj2 (mps_bound_S a b)  H2 hd).
    specialize (IHd _ _ _ H3 H4 tl).
    apply (le_trans _ _ _ IHd).
    simpl.
    unfold derive_ps.
    replace (hd + (order tl +1))%nat with (hd + order tl + 1)%nat by lia.
    apply ntimes_pos_monotone.
    apply (mps_bound_nonneg a);auto.
    lia.
  Qed.

    Lemma IVP_D_bound {d :nat} (a : (@mps A d)^d) (b : (@mps A 1)^1) n : mps_tuple_bound a (tuple_nth 0 b 0) -> (mps_tuple_bound (IVP_D a n) (tuple_nth 0 (IVP_D (ntimes d b) n) 0)).
    Proof.
       intros.
       intros i.
       induction n.
       - simpl.
         intros k.
         intros.
         rewrite id_nth;auto.
         rewrite ps_index_comp1.
         unfold comp_one_ps.
         destruct (order k).
           rewrite norm_zero_eq.
           apply le_refl.
        +  destruct n; [|rewrite norm_zero_eq;apply le_refl].
           destruct (tuple_nth i k 0%nat).
           rewrite norm_zero_eq.
           apply le_0_1.
           destruct n.
           rewrite norm1.
           apply le_refl.
           rewrite norm_zero_eq.
           apply le_0_1.
       - intros  k.
         intros.
         rewrite !IVP_D_nth;auto.
         assert (0 < 1)%nat by lia.
         pose proof (IVP_D_nth (ntimes d b) (S n) _ H3).
         pose proof (single_index_proper (order k) _ _ H4).
         rewrite H5.
         rewrite !IVP_Di_S.
         (* pose proof (ntimes_proper d  _ _ (IVP_Di_S (ntimes d b) 0 n )). *)
         enough (forall j, j < d -> |(tuple_nth j a 0) * (D[j] (IVP_Di a n i))| <= (tuple_nth 0 b 0 * D[0] (IVP_Di (ntimes d b) n 0))).
         {
           pose proof (mps_sum_same (fun j => tuple_nth j a 0 * D[j] (IVP_Di a n i)) _ d H6).
           apply (le_trans _ _ _ (H7 _)).
           rewrite (single_index_proper (order k) _ _ ((IVP_Di_S _ _ _))).
           unfold sum.
           Opaque add zero pdiff.
           simpl fold_right.
           apply le_eq.
           apply (single_index_proper (d:=0) (order k)  ).
           rewrite add0.
           setoid_rewrite  <-(ntimes_nth b);auto.
           rewrite (mulC (ntimes _ _)).
           rewrite <-ntimes_mult.
           rewrite (mulC (D[0] _ )).
           reflexivity.
           Transparent add zero pdiff.
         }
         intros.
         apply mps_mult_monotone.
         intros k';apply H1;auto.
         apply mps_diff_monotone;auto.
         intros i0.
         specialize (IHn i0 H2).
         rewrite !IVP_D_nth in IHn;auto.
         apply (le_trans _ _ _ IHn).
         apply le_eq.
         apply (single_index_proper (d:=0)).
         rewrite (IVP_D_nth (ntimes d b));auto.
         reflexivity.
     Qed.
    
     (* Lemma mps_mult_monotone {d} (a b : @mps A d) a' b' : (|a| <= a') -> |b| <= b' -> |a*b| <= a' * b'. *)
  (*      apply IHd. *)
  (*    apply (le_trans _ _ _ (norm_mult _ _)). *)
  (*    pose proof (norm_triangle (ps_index k (a 0%nat * b (S i))) ((( (fun n => (a (S n))) : (@mps A (S d)) ) * b) i)). *)
  (*  apply le_le_plus_le;auto. *)
  (*  apply (le_trans _ _ _ (norm_mult _ _)). *)
  (*  apply (mul_le_le_compat_pos);try apply norm_nonneg;auto. *)
  (*  apply IHk. *)
  (*  intros;auto. *)
  (*    rewrite  *)
  (*    apply H3. *)
  (*    intros k. *)
  (*    specialize (H1 ). *)
  (*    intros k. *)

  (*     Opaque mul. *)
  (*     simpl. *)
  (*      destruct (destruct_tuple_cons k) as [hd [tl P]]. *)
       
  (*      pose proof (ps_mult_monotone (fun n => (ps_index tl ((a*b) n)))). *)
  (*      enough (|(a*b) hd| <= (fun k => a' (hd + k)%nat) * (fun k => b' (hd + k)%nat)). *)
  (*      { *)
  (*        specialize (H3 tl). *)
  (*        simpl in H3. *)
  (*        apply (le_trans _ _ _ H3). *)

  (*      } *)
  (*   unfold mult_ps, powerseries.convolution_coeff;simpl. *)
  (*    replace  *)
  (*  apply ps_mult_monotone. *)
  (*  simpl. *)
  (*  generalize  dependent a'. *)
  (*  generalize  dependent a. *)
  (*  induction k;intros. *)
  (*  simpl. *)
  (*  unfold mult_ps, powerseries.convolution_coeff;simpl. *)
  (*  ring_simplify. *)
  (*  rewrite add0. *)
  (*  apply (le_trans _ _ _ (norm_mult _ _)). *)
  (*  apply (mul_le_le_compat_pos);try apply norm_nonneg;auto. *)
  (*  simpl. *)
  (*  rewrite !mult_ps_S. *)
  (*  apply (le_trans _ _ _ (norm_triangle _ _ )). *)
  (*  apply le_le_plus_le;auto. *)
  (*  apply (le_trans _ _ _ (norm_mult _ _)). *)
  (*  apply (mul_le_le_compat_pos);try apply norm_nonneg;auto. *)
  (*  apply IHk. *)
  (*  intros;auto. *)
  (* Qed. *)
End MultiBounds.

Section PS_Eval.
  Context `{SemiRing}.
  Notation "A [[ x^ n ]]" := (@mps A n) (at level 2).
  Lemma ps_mult0 {n} (a b : A[[x^n]]): ps_index 0 (a * b) == ps_index 0 a * ps_index 0 b.
  Proof.
    induction n.
    simpl;reflexivity.
  Admitted.

  #[global] Instance EvalTrivial : forall n, HasEvaluation (A := A{{x^n}}) (B := A^n) (C := A).
  Proof.
    intros.
    exists (fun a x => x == 0) (fun a x P => (ps_index 0 a));intros;auto.
    intros a b eq c d ->; reflexivity.
    rewrite H1;reflexivity.
    rewrite ps_index_plus.
    reflexivity.
    apply ps_mult0.
  Defined.

End PS_Eval.
Section Bounded_PS.

  Context `{TotallyOrderedField}.
 Context `{normK : (NormedSemiRing A A (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }.
  Context `{invSn : Sn_invertible (A := A) (H := _) (R_rawRing := _)}. (* Replace by proof *)
  Context `{norm_abs : forall x, 0 <= x -> norm x == x}.

  Context {d : nat} {a : (@mps A d)^d}.
  Context {M r : A} {Mpos : 0 <= M} {rpos : 0 <= r}.

  Definition a_bound_series : (@mps A 1)  := fun n => M * (npow r n).

  Context {a_bound : mps_tuple_bound a (tuple_nth 0 t(a_bound_series) 0)}.
  
  Lemma zero_in_domain n : (0 : A^d) \in_dom (IVP_D a n).
  Proof.
  Admitted.

  Definition y (n : nat)   := ![n] ** ((IVP_D a n) @ (_; (zero_in_domain n))).

  Lemma norm1 : norm 1 == 1.  
  Proof.
    apply norm_abs.
    apply le_0_1.
  Qed.

  Lemma y_nth (n : nat) i : i < d -> tuple_nth i (y n) 0 == ![n] * (ps_index 0 (IVP_Di a n i)).
  Proof.
    intros.
    unfold y.
    rewrite scalar_mult_spec;auto.
    apply ring_eq_mult_eq;try reflexivity.
    unfold eval.
    simpl.
    rewrite (evalt_spec _ _ _ _ H1).
    simpl.
    rewrite IVP_D_nth;auto.
    reflexivity.
  Qed.

  Add Ring TRing: (ComRingTheory (A := A)). 

  Lemma Di1_bound n k :  norm (IVP_Di (ntimes d t(a_bound_series))  (S n) 0 k) <= Fn_bound (r := r) (M := (ntimes d M)) n k.
 Proof.
   revert k.
   induction n; intros.
   - assert (IVP_Di (ntimes d t(a_bound_series)) 1 0 == (ntimes d ( fun n : nat => M * npow r n))).
     {
       rewrite IVP_Di_S.
       rewrite sum_1.
       simpl IVP_Di.
       assert (pdiff (A:=(@mps A 1)) 0 comp_one_ps == 1) as ->.
       {
         simpl;intros.
         unfold derive_ps, one_ps, comp_one_ps.
         destruct n.
         simpl;ring.
         destruct n.
         simpl.
         ring.
         simpl.
         rewrite ntimes_zero.
         ring.
       }
       rewrite mul1.
       rewrite <-ntimes_nth;try lia.
       rewrite tuple_nth_cons_hd.
       reflexivity.
     }
     (* pose proof (IVP_Di_S (d:=1)  bounder 0 0 ). *)
     rewrite (single_index_proper _ _ _ H1).
     setoid_rewrite (ntimes_index (d:=0)).
     unfold Fn_bound.
     simpl.
     ring_simplify.
     simpl.
     rewrite rising_factorial0.
     ring_simplify.
     apply (le_trans _ _ _ (norm_ntimes_le_ntimes_norm _ _)).
     rewrite norm_abs.
     rewrite mulC.
     rewrite ntimes_mult.
     rewrite mulC;apply le_refl.
     apply mul_pos_pos;auto.
     apply npow_pos;auto.
   - pose proof (IVP_Di_S (d:=1)  (ntimes d t(a_bound_series)) 0 (S n) ).
     rewrite (single_index_proper _ _ _ H1).
     rewrite single_index_proper;try apply sum_1.
     replace (S n) with (n+1)%nat by lia.
     apply (bound_prod (norm1 := norm1)).
     + intros.
       unfold f_bound.
       rewrite single_index_proper; try (rewrite <-ntimes_nth;try lia;rewrite tuple_nth_cons_hd;reflexivity ).
       unfold a_bound_series.
       setoid_rewrite (ntimes_index (d:=0)).
       apply (le_trans _ _ _ (norm_ntimes_le_ntimes_norm _ _)).
       rewrite norm_abs; [rewrite mulC,ntimes_mult,mulC; apply le_refl|].
       apply mul_pos_pos;auto.
       apply npow_pos;auto.
    + intros.
      replace (n+1)%nat with (S n) by lia.
       apply IHn.
  Qed.

  Lemma le_norm x : x <= norm x.
  Proof.
     destruct (le_total x 0).
     apply (le_trans _ _ _ H1).
     apply norm_nonneg.
     rewrite norm_abs;auto.
     apply le_refl.
   Qed.

  Lemma y_bound_Fn i n: i < d -> norm (tuple_nth i (y (S n)) 0 ) <= ![S n] * Fn_bound (r := r) (M := (ntimes d M)) n 0.  
  Proof.
   intros.
   assert (dneg0 : d = S (pred d)) by lia.
   pose proof (IVP_D_bound (norm1 := norm1) a _ (S n) a_bound ).
   rewrite y_nth;auto.
   specialize (H2 i 0 H1).
   rewrite zero_order in H2.
   apply (le_trans _ _ _ (norm_mult _ _)).
   assert ( tuple_nth 0 (IVP_D (ntimes d t(a_bound_series)) (S n)) 0 0
 == IVP_Di (ntimes d t(a_bound_series)) (S n) 0 0).
   {
     rewrite dneg0.
     apply (single_index_proper 0%nat (tuple_nth 0 (IVP_D (ntimes (S (pred d)) t( fun n : nat => M * npow r n)) (S n)) 0)).
     setoid_rewrite (IVP_D_nth (d:=1));try lia.
     reflexivity.
   }
   rewrite H3 in H2.
   rewrite IVP_D_nth in H2;auto.
   rewrite norm_abs;try apply invfact_pos.
   apply mul_le_compat_pos;try apply invfact_pos.
   apply (le_trans _ _ _ H2).
   apply (le_trans _ _ _ (le_norm _ )).
   apply Di1_bound.
 Qed.

  Lemma y0 i : i < d -> tuple_nth i (y 0) 0 == 0.
  Proof.
    intros.
    unfold y.
    rewrite scalar_mult_spec;auto.
    simpl inv_factorial.
    rewrite mulC,mul1.
    unfold IVP_D.
    simpl.
    rewrite (evalt_spec _ _ _ _ H1).
    rewrite id_nth;auto.
    Opaque comp1.
    simpl.
    rewrite (ps_index_comp1).
    Transparent comp1.
    rewrite zero_order;reflexivity.
  Defined.

  Lemma y_bound i n: i < d -> norm (tuple_nth i (y (S n)) 0 ) <= ntimes d M  * npow (ntimes 2 1 * ntimes d M * r) n.
  Proof.
     intros.
     (* destruct n. *)
     (* - simpl. *)
     (*   rewrite y0;auto. *)
     (*   rewrite norm_abs; try apply le_refl. *)
     (*   rewrite mul1. *)
     (*   apply ntimes_nonneg;auto. *)
     apply (le_trans _ _ _ (y_bound_Fn _ _ H1)).
     assert (0 <= ntimes d M )by (apply ntimes_nonneg;auto).
    pose proof (mul_le_compat_pos (invfact_pos (S n)) (Fn_bound0 (rge0 := rpos) (Mge0 := H2)  n)).
       apply (le_trans _ _ _ H3).
       rewrite <-!mulA.
       enough (![ S n] * [n ]! * ntimes d M * npow (ntimes 2 1 * ntimes d M * r) n  <= ( [S n ]! * ![ S n]) * ntimes d M * npow (ntimes 2 1 * ntimes d M * r) n ).
       {
         apply (le_trans _ _ _ H4).
         rewrite fact_invfact.
         ring_simplify.
         apply le_refl.
       }
       setoid_replace (([S n ]! * ![ S n]) * ntimes d M * npow (ntimes 2 1 * ntimes d M * r) n ) with (![ S n] * ([S n ]! * (ntimes d M * npow (ntimes 2 1 * ntimes d M * r) n ))) by ring.
       rewrite !mulA.
       apply mul_le_compat_pos; try apply invfact_pos.
       rewrite mulC.
       rewrite (mulC [S n]!).
       apply mul_le_compat_pos; try apply invfact_pos.
       apply mul_pos_pos.
       apply ntimes_nonneg;auto.
       apply npow_pos.
       apply mul_pos_pos;auto.
       apply mul_pos_pos; apply ntimes_nonneg;auto.
       apply le_0_1.
       simpl.
       rewrite mulC.
       setoid_replace ([n]!) with ([n]!*1) at 1 by ring.
       apply mul_le_compat_pos.
       apply fact_pos.
       rewrite addC.
       setoid_replace 1 with (0 + 1) at 1 by ring.
       apply le_plus_compat.
       apply ntimes_nonneg.
       apply le_0_1.
   Qed.
Section Uniqueness.
  Context `{AbstractFunctionSpace} {d : nat}.
  Context {f g : (A (S d))^(S d)} {y0 : (A 0)^(S d)}  {in_dom_f : y0 \in_dom f} {in_dom_g : y0 \in_dom g}.

  Lemma dom_Dif : forall n i, y0 \in_dom (IVP_Di f n i).
  Admitted.
  Lemma dom_Dig : forall n i, y0 \in_dom (IVP_Di g n i).
  Admitted.

  Lemma Di_unique : (forall (n : nat^d) P1 P2, (derive_rec f n) @ (y0; P1)  == (derive_rec g n) @ (y0;P2)) -> forall (k : nat^d)  (n i : nat) P1 P2, (derive_rec (IVP_Di f n i) k) @ (y0; P1) == (derive_rec (IVP_Di g n i) k) @ (y0; P2).
  Proof.
    intros.
    revert dependent k.
    induction n;intros.
    - simpl;apply functions.eval_proper; reflexivity.
    - simpl.
      pose proof (derive_rec_sum k (fun j : nat => tuple_nth j f 0 * D[ j] (IVP_Di f n i)) d).
      pose proof (derive_rec_sum k (fun j : nat => tuple_nth j g 0 * D[ j] (IVP_Di g n i)) d).
      destruct  (eval_change_f _ _ _ P1 H7) as [P1' ->].
      destruct  (eval_change_f _ _ _ P2 H8) as [P2' ->].
      clear P1 P2 H7 H8.

      destruct  (eval_change_f _ _ _ P1' H7) as [P1 ->].
      destruct  (eval_change_f _ _ _ P2' H8) as [P2 ->].
      clear P1' P2' H7 H8.
    Admitted.
End Uniqueness.
Section Analytic.
Context `{AbstractFunctionSpace} {d : nat}.
Context `{TotallyOrderedField (A := (A 0)) (H:=(H 0)) (R_rawRing := (H0 0)) (R_semiRing := (H1 0))}.
 Context `{normK : (NormedSemiRing ((A 0)^d) (A 0) (H := _)  (H0 := (H 0))  (R_rawRing0 := (H0 0%nat)) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }. 
  Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat))}.
  Context {M R : A 0} {Mpos : 0 <= M} {Rpos : 0 <= R}.
  Context {f : (A d)^d} {y0 : (A 0)^d}  {in_dom : y0 \in_dom f}.
  Definition derivative {e :nat} (n : nat^e) (i  : (A d)^d.
  Proof.
    
  Definition to_ps {e} (g : (A e)) : @mps (A 0) e.
  Proof.
     revert e g.
     induction e;intros.
     apply g.
     intros n.
     
 Context {p : (@mps (A 0) d)^e}.

 Definition D_bound (f : (A d)^e) x0 (B : nat -> (A 0)) := forall n i H, (i < d) -> norm ((nth_derivative i f n) @ (x0; H)) <= (B n).
 Definition D_boundi (f : (A d)^e) x0 (B : nat -> (A 0)) i := forall n H, norm ((nth_derivative i f n) @ (x0; H)) <= (B n).
 Definition Fi_bound M R n k := [n]! * [k+2*n]! * ![2*n] *  (npow (1+1) n) * (npow M (n+1)) * npow R (n+k). 
 Definition Fi_pbound M R n i k := ([n]! * [i]! * [k+2*n]! * ![2*n]) * (npow (1+1) n)* (npow M (n+2)) * (npow R (n+k +i )).

 Add Ring TRing: (ComRingTheory (A := (A 0))). 

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
