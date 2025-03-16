Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import abstractpowerseries.
Require Import functions.
Require Import polynomial.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import Classical.
Require Import tuple.
Require Import combinatorics.

 Open Scope algebra_scope.

Section ODE_basic.
  Context `{CompositionalDiffAlgebra} .

  Definition ODE_solution {d} f (y : (A 1)^d) := D[0]y ==  f \o y.


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

  Definition F_spec {d} f :  forall n y, @ODE_solution d f y -> (nth_derivative 0 y n) == ((F f n) \o y).
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

  
  (* Definition Fi_spec {d} f i:  (i< d)%nat -> forall n y, @ODE_solution d f y -> (nth_derivative 0 y\_i n) == ((Fi f n i) \o1 y). *)
  (* Proof. *)
  (*   intros. *)
  (* Admitted. *)
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
  Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat))}.
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

  Lemma ivp_solution_taylor_spec n y Hy (S :  is_IVP_solution y Hy) : ivp_solution_taylor n == ![n] ** ((nth_derivative 0 y n) @ (0;(is_IVP_solution_deriv_dom S n))).
  Proof.
    unfold ivp_solution_taylor.
    setoid_replace (((F f n) @ (y0; dom_F n))) with ((nth_derivative 0 y n) @ (0; is_IVP_solution_deriv_dom S n));try reflexivity.
    destruct S as [i e].
    pose proof (F_spec _ n _ i).
    assert ((0 : (A 0)^1) \in_dom (F f n) \o y).
    {
      apply (dom_composition _ y 0 Hy _ e).
      apply dom_F.
    }
    rewrite (meval_proper _ _ _ _ (is_IVP_solution_deriv_dom (conj i e) n) H7 H6);try reflexivity.
    assert ((y @ (0; Hy)) \in_dom (F f n)).
    {
      rewrite e.
      apply dom_F.
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

Section PowerSeriesSolution.
  
  Context `{AbstractPowerSeries}.
  Context `{SemiRing (A := A) (H:=H) (R_rawRing := R_rawRing)}.

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
    enough (forall k0, (k0 <= k)%nat ->  forall n i : nat, (i < (S d)) -> ((Fi f n i) \o1 yt) t(k0)  == Dx[t(n)] (yt\_i) t(k0)) by (intros;apply H6;lia).
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
      destruct H8; [apply IHk;auto|].
      rewrite H8;clear H8 H6.
      replace (n+ S k)%nat with (S n+k)%nat by lia.
      simpl rising_factorialt in *.
      replace (S (k+1))%nat with (k+2)%nat by lia.
      rewrite rising_factorial_s'.
      replace (n+1)%nat with (S n) by lia.
      setoid_replace ( inv_Sn k * [k + 1 ! S n] * 1 * y_i (S n + k) i) with ( inv_Sn k * ([k + 1 ! S n] * 1 * y_i (S n + k) i)) by ring.
      rewrite <-IHk;try lia.
      setoid_replace ((Fi f n i) \o1 yt t( S k)) with (inv_Sn k *  (# (S k) * (Fi f n i) \o1 yt t( S k))) by (rewrite <-mulA, (mulC (inv_Sn k)); rewrite inv_Sn_spec;ring).

      replace (S k) with (k+1)%nat by lia.
      rewrite <-deriv_next.
      apply ring_eq_mult_eq; try reflexivity.
      pose proof (pdiff_chain (d:=0) (Fi f n i) yt).
      rewrite index_proper;try apply H6; try reflexivity.
      clear H6.
      simpl Fi.
      pose proof (composition_sum_comp (fun j : nat => f \_ j * D[ j] (Fi (H3 := H4) f n i)) yt d t(k)).
      rewrite H6.
      setoid_replace (sum (A := nat^1 -> A) (fun i0 : nat => (f \_ i0 * D[ i0] (Fi  (H3 := H4) f n i)) \o1 yt) (S d) t(k)) with (sum (A := nat^1 -> A) (fun i0 : nat => (f \_ i0 \o1 yt  * (D[ i0] (Fi  (H3 := H4) f n i)) \o1 yt)) (S d) t(k)) by (apply index_proper;[apply sum_ext;intros; rewrite composition_mult_comp|];reflexivity).
      rewrite !index_sum.
      apply sum_ext.
      intros.
      apply exchange_ps_factor.
      intros.

      pose proof (IVP_F1 f n0 H8 ).
      setoid_replace ((f \_n0 \o1 yt) t(i0)) with (((Fi  f 1 n0) \o1 yt) t(i0)) by (apply index_proper;try rewrite composition_proper; try rewrite <-H10; try reflexivity).
      rewrite deriv_next.
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
    setoid_rewrite H7;auto.
    setoid_rewrite (pdiff_tuple_nth yt);auto.
    setoid_replace (D[0] yt\_i) with (derive_rec yt\_i t(1)) by (rewrite deriv_rec_1;simpl; reflexivity).
    intros k.
    pose proof (yi_spec (k\_0) 1%nat i H6).
    assert (k == t(k\_0)).
    {
      apply (tuple_nth_ext' _ _ 0 0).
      intros.
      assert (i0 = 0)%nat as ->  by lia.
      simpl.
      reflexivity.
    }
    assert (Dx[t(1)] yt \_i k == Dx[t(1)] yt \_ i t(k\_0)) as -> by  (apply index_proper;try reflexivity;auto).
    rewrite <- H8.
    apply index_proper;try rewrite H9;try reflexivity.
    pose proof (IVP_F1 f i  H6).
    rewrite composition_proper; try apply H10; try reflexivity.
 Qed.

  (* Lemma yi_is_unique z  i: i < (S d) -> z\_i 0 == yt\_i 0 -> ODE_solution f z -> forall (k : nat),  z\_i t(k) == yt\_i t(k).  *)
  (* Proof. *)
  (*   intros. *)
  (*   induction k. *)
  (*   apply H7. *)
  (*   rewrite !deriv_next_backwards. *)
  (*   apply (ring_eq_mult_eq); try reflexivity. *)
  (*   pose proof (Fi_spec _ i H6 1 _ H8 ). *)
  (*   apply (tuple_nth_ext' _ _ 0 0). *)
  (*   intros. *)
    
  (*   apply deriv_eq_ps_equal1. *)
  (*   intros. *)
  (*   induction k. *)
    
  (*   rewrite (Fi_spec _ i H8 k _ y_is_solution ). *)
  (*   induction k. *)
  (*   simpl. *)
  (*   rewrite ps_comp0. *)
  (*   pose proof (F_spec _ k _ y_is_solution ). *)
  (*   induction k. *)

  (*   simpl. *)
  (*   Search nth_derivative  *)
  (*   pose proof  *)
  (*   intros k. *)
  (*   rewrite <-yi_spec;auto. *)
  (*   rewrite ps_property_backwards. *)
  (*   rewrite (ps_property_backwards  yt\_i ). *)
  (*   apply ring_eq_mult_eq; try reflexivity. *)
  (*   destruct (destruct_tuple_cons k) as [k0 [N ->]]. *)
  (*   enough (N = nil_tuple) as ->. *)
  (*   setoid_rewrite (index_proper (Dx[ t( k0)] yt \_ i) (Dx[ t( k0)] yt \_ i) _ 0 t(0));try reflexivity. *)
  (*   rewrite <-yi_spec;auto. *)
  (*   rewrite index_proper; [ | apply deriv_rec_1 | reflexivity ]. *)
    
  (*   rewrite <-yi_spec. *)
  (*   rewrite deriv_rec_1. *)
  (*   setoid_rewrite <- yi_spec;auto. *)
  (*   rewrite !ps_ *)
  (*   rewrite yt_spec';auto. *)
  (*   simpl. *)
  (*   intros k. *)
  (*   destruct (destruct_tuple_cons k). *)
  (*   rewrite (yt_spec k i). *)
  (*   specialize (F_spec _ 1 _ H6). *)
End PowerSeriesSolution.

(* Section Taylorindex. *)

(*   Context `{A_comRing : SemiRing}. *)


(*  Definition ps_index {d} (n : nat^d) (a : @mps A d) : A. *)
(*  Proof. *)
(*    induction d. *)
(*    apply a. *)
(*    destruct (destruct_tuple_cons n) as [hd [tl P]]. *)
(*    apply (IHd tl (a hd)). *)
(*  Defined. *)



(*    #[global] Instance ps_index_proper d n : Proper (SetoidClass.equiv ==> SetoidClass.equiv) (@ps_index d n). *)
(*    Proof. *)
(*    Admitted. *)

(*     Lemma ps_index_0 {d} ix :  ps_index (d := d) ix 0 ==0. *)
(*     Proof. *)
(*       induction d. *)
(*       simpl. *)
(*       reflexivity. *)
(*       simpl. *)
(*       destruct (destruct_tuple_cons ix) as [hd [tl P]]. *)
(*       apply IHd. *)
(*     Qed. *)

(*     Lemma ps_index_1 {d} ix :  ps_index (d := d) ix 1 == match (order ix) with  0 => 1 | _ => 0 end. *)
(*     Proof. *)
(*       induction d. *)
(*       simpl;reflexivity. *)
(*       simpl. *)
(*       destruct (destruct_tuple_cons ix) as [hd [tl ->]]. *)
(*       destruct hd. *)
(*       simpl. *)
(*       apply IHd. *)
(*       simpl. *)
(*       rewrite ps_index_0. *)
(*       reflexivity. *)
(*     Qed. *)


(*    Instance single_index_proper {d}  (n : nat) : Proper (SetoidClass.equiv ==> SetoidClass.equiv) (fun (a : @mps A (S d)) => (a n)). *)
(*    Proof. *)
(*      intros a b Heq. *)
(*      apply seq_A_setoid. *)
(*      rewrite Heq. *)
(*      reflexivity. *)
(*    Defined. *)
(*    Lemma ps_index_plus {d} (a b : @mps A d) n : ps_index n (a+b) == ps_index n a + ps_index n b.  *)
(*    Proof. *)
(*      induction d. *)
(*      simpl. *)
(*      reflexivity. *)
(*      Opaque add. *)
(*      simpl. *)
(*      destruct (destruct_tuple_cons n) as [hd [tl P]]. *)
(*      enough ((a+b) hd == a hd + b hd) as ->. *)
(*      apply IHd. *)
(*      Transparent add. *)
(*      simpl. *)
(*      unfold sum_ps. *)
(*      reflexivity. *)
(*   Qed. *)

(*     Lemma ps_index_comp1 {d} ix i :  ps_index (d := d) ix (comp1  i) == match (order ix) with *)
(*                                                                          | 1 => match (tuple_nth i ix 0%nat) with *)
(*                                                                                |  1 => 1 | _ => 0  end *)
(*                                                                          | _ => 0 *)
(*                                                                           end. *)
(*     Proof. *)
(*       generalize dependent d. *)
(*       induction i;intros;try (simpl;reflexivity). *)
(*       - simpl. *)
(*         destruct d;simpl;try reflexivity. *)
(*         destruct (destruct_tuple_cons ix) as [hd [tl P]]. *)
(*         simpl. *)
(*         destruct hd eqn:E. *)
(*         simpl. *)
(*         rewrite ps_index_0. *)
(*         rewrite P. *)
(*         rewrite tuple_nth_cons_hd. *)
(*         destruct (order tl); try destruct n;try reflexivity. *)
(*         simpl. *)
(*         destruct n;simpl;[|rewrite ps_index_0;reflexivity]. *)
(*         rewrite P. *)
(*         rewrite tuple_nth_cons_hd. *)
(*         rewrite ps_index_1. *)
(*         reflexivity. *)
(*       - simpl. *)
(*         destruct d; simpl; try reflexivity. *)
(*         destruct (destruct_tuple_cons ix) as [hd [tl P]]. *)
(*         simpl. *)
(*         destruct hd. *)
(*         + simpl. *)
(*           rewrite P. *)
(*           rewrite tuple_nth_cons_tl. *)
(*           apply IHi. *)
(*         + rewrite ps_index_0. *)
(*           rewrite P. *)
(*           rewrite tuple_nth_cons_tl. *)
(*           simpl. *)
(*           destruct (order tl) eqn:E. *)
(*           simpl;rewrite order_zero; try lia; destruct hd; simpl;try reflexivity. *)
(*           destruct hd;simpl;try reflexivity. *)
(*     Qed. *)

(*     Lemma ntimes_index {d} (a : @mps A (S d)) n i : (ntimes n a) i == ntimes n (a i).  *)
(*     Proof. *)
(*       induction n. *)
(*       simpl. *)
(*       reflexivity. *)
(*       intros . *)
(*       simpl ntimes. *)
(*       Transparent add. *)
(*       simpl add. *)
(*       unfold sum_ps. *)
(*       rewrite IHn. *)
(*       reflexivity. *)
(*     Qed. *)

(*     Lemma ntimes_ps_index {d} (a : @mps A d) n i : ps_index i (ntimes n a) == ntimes n (ps_index i a ).  *)
(*     Proof. *)
(*       induction n. *)
(*       simpl. *)
(*       rewrite ps_index_0. *)
(*       reflexivity. *)
(*       simpl. *)
(*       rewrite ps_index_plus. *)
(*       rewrite IHn. *)
(*       reflexivity. *)
(*     Qed. *)
(* End Taylorindex. *)


Section IVP_Record.
  Open Scope fun_scope.
  Context `{AbstractFunctionSpace }.
  Context `{invSn : Sn_invertible (A := (A 0%nat)) (H := (H 0)) (R_rawRing := (H0 0%nat))}.
  Record IVP {d} := {
      f : (A d)^d;
      y0 : (A 0)^d;
      in_dom : y0 \in_dom f
    }.
End IVP_Record.
