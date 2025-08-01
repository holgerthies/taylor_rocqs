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

 Open Scope algebra_scope.

Section ODE_basic.
  Context `{CompositionalDiffAlgebra} .

  Definition ODE_solution {d} f (y : (A 1)^d) := D[0]y ==  f \o y.
  Lemma ODE_solution_ith {d} f (y : (A 1)^d) : ODE_solution f y <-> forall i, i < d -> D[0]y\_i == (f \o y)\_i.
  Proof.
    unfold ODE_solution.
    split;intros.
    - pose proof (tuple_nth_ext2 _ _ 0 0 H4).
      specialize (H6 _ H5).
      rewrite <-pdiff_tuple_nth;auto.
    -  apply (tuple_nth_ext' _ _ 0 0).
       intros.
       simpl.
       rewrite pdiff_tuple_nth;auto.
  Qed.
  
  Fixpoint F {d} (f : (A d)^d) (n: nat) : (A d)^d :=
     match n with
     | 0%nat => (id d)
     | (S n') => (sum (fun j => f\_j ** (D[j] (F f n'))) d)
     end.

  Fixpoint Fi {d} (f : (A d)^d) (n i : nat) : (A d) :=
     match n with
     | 0%nat => comp1 i
     | (S n') => (sum (fun j => (tuple_nth j f 0) * (D[j] (Fi f n' i))) d)
     end.

  Definition F_spec {d} f (id_spec : forall (y : (A 1)^d), (id d) \o y == y): forall n y,  @ODE_solution d f y -> (nth_derivative 0 y n) == ((F f n) \o y).
  Proof.
     intros.
     induction n;[rewrite id_spec;simpl nth_derivative;reflexivity|].
     destruct d;[simpl;auto|].
     replace (nth_derivative 0 y (S n)) with  (D[0] (nth_derivative 0 y n)) by (simpl;auto).
     rewrite IHn.
     rewrite multicomposition_chain_rule.
      replace (F f (S n)) with (sum (fun j => (tuple_nth j f 0) ** (D[j] (F f n))) (S d)) by auto.
     rewrite multi_composition_sum_comp.
     apply sum_ext.
     intros.
     rewrite <-pdiff_tuple_nth;auto.
     unfold ODE_solution in H4.
     rewrite H4.
     apply (tuple_nth_ext' _ _ 0 0).
     intros.
     rewrite !tuple_nth_multicomposition;auto.
     rewrite !scalar_mult_spec;auto.
     rewrite !tuple_nth_multicomposition;auto.
     rewrite composition_mult_comp.
     reflexivity.
   Qed.

   Lemma F_nth {d} f n i : i < d -> (@F d f n)\_i  == Fi f n i.
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

  
   Lemma  IVP_F1 {d} f k: k < d -> (@Fi d f 1 k) == f\_k. 
   Proof.
     intros.
     simpl.
     setoid_rewrite (sum_single _ k); try lia.
     rewrite diff_id_same;auto.
     apply mul1.
     intros.
     rewrite diff_id_distinct;auto.
     rewrite mul0.
     reflexivity.
  Qed.


End ODE_basic.

Open Scope fun_scope.
Section TaylorSequence.
  Context `{AbstractFunctionSpace }.
  Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat)) (H0 := _)}.
  Context {d : nat} (f : (A d)^d)  (y0 : (A 0)^d) (dom_f : y0 \in_dom f).


  Lemma dom_F : forall n, y0 \in_dom (F f n).
  Proof.
    intros.
    induction n;intros i Hi;rewrite (dom_change_f _ _ _ (F_nth _ _  _ Hi));auto;[apply dom_id|].
    simpl.
    destruct d; try lia.
    apply dom_sum;intros.
    apply dom_mult.
    apply dom_f;lia.
    apply dom_diff.
    rewrite <-(dom_change_f _ _ _ (F_nth _ _  _ Hi)).
    apply IHn;lia.
  Qed.

  Lemma dom_Fi : forall n i, i<d -> y0 \in_dom (Fi f n i).
  Proof.
    intros.
    induction n.
    simpl.
    apply dom_id.
    destruct d; try lia.
    apply dom_sum;intros.
    apply dom_mult.
    apply dom_f;lia.
    apply dom_diff.
    apply IHn.
  Qed.
  Definition ivp_solution_taylor (n : nat) : (A 0)^d  := ![n] ** ((F f n) @ (y0; (dom_F n))).

  Definition ivp_solution_taylor_i (n : nat) i (ile : i < d) : (A 0)  := ![n] * ((Fi f n i) @ (y0; (dom_Fi n i ile))).
  Definition is_IVP_solution (y : (A 1)^d) (Hy : (0 : (A 0)^1) \in_dom y) := ODE_solution f y  /\ y @ (0;Hy) == y0.

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
    unfold ivp_solution_taylor, F.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    rewrite scalar_mult_spec;auto.
    rewrite mulC, mul1.
    simpl.
    rewrite (evalt_spec _ _ _ _ H6).
    assert (y0 \in_dom (Fi f 0 i)).
    {
      rewrite <-(dom_change_f  _ _ _ (F_nth _ _ _ H6)).
      apply dom_F;auto.
    }
    rewrite (functions.eval_proper  _ (Fi f 0 i) y0 y0 _ H7);try reflexivity.
    simpl;rewrite eval_id;auto;reflexivity.
    rewrite id_nth;auto.
    simpl;reflexivity.
  Qed.

  (* Lemma ivp_solution_taylor_spec n y Hy (S :  is_IVP_solution y Hy) : ivp_solution_taylor n == ![n] ** ((nth_derivative 0 y n) @ (0;(is_IVP_solution_deriv_dom S n))). *)
  (* Proof. *)
  (*   unfold ivp_solution_taylor. *)
  (*   setoid_replace (((F f n) @ (y0; dom_F n))) with ((nth_derivative 0 y n) @ (0; is_IVP_solution_deriv_dom S n));try reflexivity. *)
  (*   destruct S as [i e]. *)
  (*   pose proof (F_spec _ n _ i). *)
  (*   assert ((0 : (A 0)^1) \in_dom (F f n) \o y). *)
  (*   { *)
  (*     apply (dom_composition _ y 0 Hy _ e). *)
  (*     apply dom_F. *)
  (*   } *)
  (*   rewrite (meval_proper _ _ _ _ (is_IVP_solution_deriv_dom (conj i e) n) H7 H6);try reflexivity. *)
  (*   assert ((y @ (0; Hy)) \in_dom (F f n)). *)
  (*   { *)
  (*     rewrite e. *)
  (*     apply dom_F. *)
  (*   } *)
  (*   rewrite (eval_composition_compat  _ _ _ Hy H8 H7). *)
  (*   apply meval_proper;try rewrite e;reflexivity. *)
  (* Qed. *)

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
    rewrite length_app.
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

Section PowerSeriesSolution.
  
  Context `{ArchimedeanField}.

  Add Ring ARing: (ComSemiRingTheory (A := A)). 
  Context {d : nat} {f : (nat^(S d) -> A)^(S d)}.


  Definition y_i (n : nat) (i : nat) : A  :=  ![n] * ((Fi f n i) 0).
  Definition yt := (proj1_sig (seq_to_tuple (def := 0) (fun i (n : nat^1) => (y_i (n)\_0 i)) (S d))).

  Lemma yt_spec i k : (i < (S d))%nat -> yt\_i t(k) == y_i k i.
  Proof.
    intros.
    unfold yt.
    destruct (seq_to_tuple _  _).
    simpl.
    rewrite e;auto.
    simpl.
    reflexivity.
  Qed.

  Lemma yt_spec' i : (i < (S d))%nat -> yt\_i  == (fun k => y_i k\_0 i).
  Proof.
    intros.
    intros k.
    rewrite <-yt_spec;auto.
    unfold yt.
    destruct (seq_to_tuple _  _).
    simpl.
    rewrite e;auto.
    simpl.
    reflexivity.
  Qed.
  Lemma index1_add (n m : nat): t(n) + t(m) = t(n+m). 
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma yi_spec : forall k n i, i < (S d) -> ((Fi f n i) \o1 yt) t(k)  == Dx[t(n)] (yt\_i) t(k).
  Proof.
    intros k.
    enough (forall k0, (k0 <= k)%nat ->  forall n i : nat, (i < (S d)) -> ((Fi f n i) \o1 yt) t(k0)  == Dx[t(n)] (yt\_i) t(k0)) by (intros;apply H1;lia).
    intros.
    rewrite ps_derive.
    rewrite index1_add.
    rewrite yt_spec;auto.
    replace (add n k0)%nat with (n+k0)%nat by (simpl;auto).
    generalize dependent i.
    generalize dependent n.
    generalize dependent k0.
    induction k.
    - intros.
      assert (k0 = 0)%nat as -> by lia.
      rewrite ps_comp0.
      replace (n+0)%nat with n by lia.
      unfold y_i.
      simpl.
      rewrite rising_factorial1.
      ring_simplify.
      rewrite mulA.
      rewrite fact_invfact.
      ring.
   -  intros.
      assert ((k0 <= k)%nat \/ (k0 = S k)%nat) by lia.
      destruct H3; [apply IHk;auto|].
      rewrite H3.
      replace (n+ S k)%nat with (S n+k)%nat by lia.
      simpl rising_factorialt in *.
      replace (S (k+1))%nat with (k+2)%nat by lia.
      rewrite rising_factorial_s'.
      replace (n+1)%nat with (S n) by lia.
      setoid_replace ( inv_Sn k * [k + 1 ! S n] * 1 * y_i (S n + k) i) with ( inv_Sn k * ([k + 1 ! S n] * 1 * y_i (S n + k) i)) by ring.
      rewrite <-IHk;try lia.
      setoid_replace ((Fi f n i) \o1 yt t( S k)) with (inv_Sn k *  ((ntimes  (S k) 1) * (Fi f n i) \o1 yt t( S k))) by (rewrite <-mulA, (mulC (inv_Sn k)); rewrite inv_Sn_spec;ring).

      replace (S k) with (k+1)%nat by lia.
      rewrite <-ntimes_embed.
      rewrite <-deriv_next.
      apply ring_eq_mult_eq; try reflexivity.
      pose proof (pdiff_chain (d:=0) (Fi f n i) yt).
      rewrite index_proper;try apply H4; try reflexivity.
      clear H4.
      simpl Fi.
      pose proof (composition_sum_comp (fun j : nat => f \_ j * D[ j] (Fi (H3 := (ps_diffAlgebra )) f n i)) yt d t(k)).
      rewrite H4.
      setoid_replace (sum (A := nat^1 -> A) (fun i0 : nat => (f \_ i0 * D[ i0] (Fi  (H3 := ps_diffAlgebra) f n i)) \o1 yt) (S d) t(k)) with (sum (A := nat^1 -> A) (fun i0 : nat => (f \_ i0 \o1 yt  * (D[ i0] (Fi  (H3 := ps_diffAlgebra) f n i)) \o1 yt)) (S d) t(k)) by (apply index_proper;[apply sum_ext;intros; rewrite composition_mult_comp|];reflexivity).
      rewrite !index_sum.
      apply sum_ext.
      intros.
      apply exchange_ps_factor.
      intros.

      pose proof (IVP_F1 f n0 H5 ).
      setoid_replace ((f \_n0 \o1 yt) t(i0)) with (((Fi  f 1 n0) \o1 yt) t(i0)) by (apply index_proper;try rewrite composition_proper; try rewrite <-H7; try reflexivity).
      setoid_rewrite deriv_next.
      rewrite yt_spec;auto.
      replace (i0+1)%nat with (1 + i0)%nat by lia.
      rewrite IHk;auto.
      rewrite rising_factorialn1.
      replace (i0+1)%nat with (S i0) by lia.
      simpl.
      ring.
  Qed.

  Lemma y_is_solution : ODE_solution f yt.
  Proof.     
    unfold ODE_solution.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    pose proof (tuple_nth_multicomposition i 0 f yt ).
    setoid_rewrite H2;auto.
    setoid_rewrite (pdiff_tuple_nth yt);auto.
    setoid_replace (D[0] yt\_i) with (derive_rec yt\_i t(1)) by (rewrite deriv_rec_1;simpl; reflexivity).
    intros k.
    pose proof (yi_spec (k\_0) 1%nat i H1).
    assert (k == t(k\_0)).
    {
      apply (tuple_nth_ext' _ _ 0 0).
      intros.
      assert (i0 = 0)%nat as ->  by lia.
      simpl.
      reflexivity.
    }
    assert (Dx[t(1)] yt \_i k == Dx[t(1)] yt \_ i t(k\_0)) as -> by  (apply index_proper;try reflexivity;auto).
    rewrite <- H3.
    apply index_proper;try rewrite H4;try reflexivity.
    pose proof (IVP_F1 f i  H1).
    rewrite composition_proper; try apply H5; try reflexivity.
 Qed.

 Lemma solution_is_unique y1 y2 : (forall i, i < (S d) -> y1\_i 0 == y2\_i 0) ->  ODE_solution f y1 -> ODE_solution f y2 -> y1 == y2.
 Proof.
  intros Hy0 H1 H2.
  apply (tuple_nth_ext' _ _ 0 0).
  intros.
  apply ps_eq_order.
  enough (forall n i k  , i<  S d ->  (order k <= n)%nat -> y1 \_i k == y2 \_i k).
  intros;apply (H4 (order k));auto.
  intros n.
  induction n.
  - intros.
    assert (order k = 0)%nat by lia.
    apply order_zero_eq_zero in H6.
     rewrite idx_index, (idx_index y2\_i0), H6, <-!idx_index.
     apply Hy0;auto. 
  -  intros.
     assert (order k <= n \/ order k = S n)%nat by lia.
     destruct H6;[apply IHn;auto|].
     destruct (tuple_pred_spec' k); [rewrite H6;simpl;lia|].
     rewrite idx_index, (idx_index y2\_i0), H8, <-!idx_index.
     rewrite !deriv_next_backward_full; try (apply order_pos_pred_index_lt;lia ).
     apply ring_eq_mult_eq; [reflexivity | ].
     assert (pred_index k = 0)%nat as ->.
     {
       enough (pred_index k <= 0)%nat by lia.
       apply pred_index_spec2.
       intros Hk.
       destruct (destruct_tuple_cons k) as [k0 [kt ->]].
       rewrite tuple_nth_cons_hd in Hk.
       rewrite Hk in H6.
       rewrite order_cons in H6.
       rewrite zero_tuple_zero in H6.
       rewrite zero_order in H6.
       simpl in H6.
       lia.
     }
     rewrite idx_index, (idx_index (D[0] y2\_i0)).
     setoid_rewrite (proj1 (ODE_solution_ith f y1) H1 _ H4).
     setoid_rewrite (proj1 (ODE_solution_ith f y2) H2 _ H4).
     pose proof (tuple_nth_multicomposition  i0 zero f y1).
     setoid_rewrite H9;auto.
     pose proof (tuple_nth_multicomposition  i0 zero f y2).
     setoid_rewrite H10;auto.
      rewrite <-!idx_index.
      apply ps_composition_exchange.
      intros.
      rewrite tuple_pred_order in H11.
      apply IHn;auto;lia.
 Qed.
   
End PowerSeriesSolution.
