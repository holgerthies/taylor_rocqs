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

 Open Scope algebra_scope.
Section Analytic.

  Open Scope fun_scope.
  Context `{AbstractFunctionSpace }.
  Context `{ArchimedeanField (A:=A 0) (H:=H 0) (R_rawRing := H0 0) (R_semiRing := H1 0) }.



   Add Ring KRing: (ComRingTheory (A := (A 0))).
  (* Context `{AbstractPowerseries (A := (A 0)) (H := (H 0))  (H1 := _)   }. *)
  (* Context `{norm_abs : forall x, 0 <= x -> norm x == x}. *)
  Context {d : nat}.
  Context {y0 : (A 0)^(S d)}.
  Context {in_dom : forall f, y0 \in_dom f}.

  Definition eval0 f := f @ (y0; in_dom f).

  Notation "f {y0}" := (eval0 f) (at level 2).

  Definition is_pos (x : A 0):= 0 <= x /\ not (x == 0). 
   Definition fun_ps (f : (A (S d))) (k : nat^(S d)) :=  t![k] * (Dx[k] (f)){y0}.
  Record Analytic  := {
      f : (A (S d))^(S d);
      M : (A 0);
      r : (A 0);
      M_pos : 1 <= M;
      r_pos : 1 <= r;
      deriv_bound : forall i , i<(S d) -> strong_bound (fun_ps f\_i) (a_bound_series M r)
    }.

   Definition fi_to_ps (F : Analytic) i (k : nat^(S d)) :=  fun_ps (F.(f)\_i) k.

   Definition f_to_ps  (F : (Analytic))  :=  proj1_sig (seq_to_tuple (fi_to_ps F) (S d) (def := 0)).

   Lemma f_to_ps_spec F  : forall i, i < (S d) -> (f_to_ps F)\_i = fi_to_ps F i.
   Proof.
     intros.
     unfold f_to_ps.
     destruct (seq_to_tuple (fi_to_ps F) (S d) (def := 0)).
     simpl.
     rewrite e;auto.
   Qed.

   Lemma derive_rec_helper0 {n m} (a : A n) i  :  derive_rec_helper i (d := m)  a 0 == a.
   Proof.
     revert i.
     induction m;intros.
     simpl.
     reflexivity.
     simpl.
     destruct (destruct_tuple_cons 0) as [h0 [tl0 P]].
     setoid_rewrite vec0_cons in P.
     apply tuple_cons_ext in P.
     destruct P as [<- <-].
     simpl.
     apply IHm.
   Qed.
   Lemma derive_rec_0 {n m} (a : A n)  :  derive_rec (d := m)  a 0 == a.
   Proof.
     apply derive_rec_helper0.
   Qed.

   Definition analytic_solution_ps  (F : Analytic) (i : nat) (n : nat)  : (A 0)  :=  ![n] * (Fi F.(f) n i){y0}.
  Definition powerseries_yi (F : Analytic) := @y_i (A 0) (H 0) (H0 0) (Ropp) (H1 0) _ _ _ _  d  (f_to_ps F).


  Lemma eval_sum_compat f N :  (sum f N){y0} == (sum (fun n => (f n){y0}) N).
  Proof.  
   intros.
   unfold eval0.
   induction N.
   apply eval_0.
   rewrite functions.eval_proper; try apply sum_S; try reflexivity.
   rewrite sum_S.
   rewrite <-IHN;try lia.
   rewrite eval_plus_compat.
   reflexivity.
   Unshelve.
   apply in_dom.
  Qed.

  Lemma eval_mul_compat f g : (f * g){y0} == f{y0} * g{y0}.
  Proof.
   unfold eval0.
   apply eval_mult_compat.
 Qed.

  Lemma eval_plus_compat f g : (f + g){y0} == f{y0} + g{y0}.
  Proof.
   unfold eval0.
   apply eval_plus_compat.
 Qed.
  Instance eval0_proper : Proper (SetoidClass.equiv ==> SetoidClass.equiv) eval0.
  Proof.
    intros a b Heq.
     unfold eval0.
     apply functions.eval_proper;auto.
     reflexivity.
  Qed.

  Lemma fi_to_ps_0 F  i : i < S d -> (fi_to_ps F i 0) == F.(f)\_i{y0}.
  Proof.
    intros.
    unfold fi_to_ps.
    unfold fun_ps.
    rewrite inv_factt0.
    setoid_rewrite derive_rec_0.
    ring_simplify.
    reflexivity.
  Qed.
   Definition ps_add_y0 (F: Analytic) k i:= match k with
                                            | 0 => y0\_i
                                            | (S k') => powerseries_yi F k i
                                            end.
   

  #[global] Instance derive_helper_proper_full `{PartialDifferentialRing } {e} j : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (derive_rec_helper j (d:=e)).
  Proof.
    intros a b eq n n' eq'.
    rewrite derive_helper_proper; try apply eq.
    revert j.
    induction e.
    simpl;reflexivity.
    simpl.
    destruct (destruct_tuple_cons n) as [n0 [nt ->]].
    destruct (destruct_tuple_cons n') as [n'0 [n't ->]].
    apply (tuple_cons_equiv) in eq'.
    destruct eq'.
    rewrite H9.
    intros.
    specialize (IHe _ _ H10 (S j)).
    rewrite nth_derivative_proper; try apply IHe.
    reflexivity.
  Defined.

  #[global] Instance derive_rec_proper_full `{PartialDifferentialRing } {e}  : Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (derive_rec (d:=e)).
  Proof.
     unfold derive_rec.
     apply derive_helper_proper_full.
   Defined.

  Instance fun_ps_proper : Proper (SetoidClass.equiv ==> SetoidClass.equiv) fun_ps. 
  Proof.
    intros a b eq.
    unfold fun_ps.
    intros k.
    rewrite eq.
    reflexivity.
  Defined.

  Lemma fun_ps_sum (f : nat -> (A (S d))) N : fun_ps (sum f (S N)) == sum (fun n=> (fun_ps (f n))) (S N).
  Proof.
    intros k.
    unfold fun_ps.
    rewrite index_sum.
    rewrite derive_rec_sum.
    rewrite eval_sum_compat.
    induction N.
    rewrite !sum_1.
    ring.
    rewrite sum_mult.
    reflexivity.
  Qed.

  Lemma   inv_factt_nth1 {m} (k : nat^m) j : j < m -> t![ k] == # (S k \_ j) * t![ k + nth1 m j].
  Proof.
    intros.
    generalize dependent j.
    induction m;intros.
    lia.
    destruct (destruct_tuple_cons k) as [k0 [kt ->]].
    rewrite !inv_factt_cons.
    destruct j.
    - rewrite !tuple_nth_cons_hd.
      simpl nth1.
      rewrite tuple_cons_plus.
      rewrite !inv_factt_cons.
      rewrite <-mulA.
      rewrite add0.
      replace (k0 + 1)%nat  with (S k0) by lia.
      apply ring_eq_mult_eq;try reflexivity.
      replace (![ S k0]) with (inv_Sn k0 * ![k0]) by reflexivity.
      rewrite <-mulA.
      rewrite ntimes_embed.
      rewrite inv_Sn_spec.
      ring.
    - rewrite !tuple_nth_cons_tl.
      simpl nth1.
      rewrite tuple_cons_plus.
      replace (k0 +0)%nat with k0 by lia.
      rewrite !inv_factt_cons.
      rewrite <-mulA, (mulC (# _)), mulA.
      apply ring_eq_mult_eq;try reflexivity.
      apply IHm;lia.
  Qed.

  Lemma   inv_factt_nth1' {m} (k : nat^m) j : j < m -> inv_Sn k\_j * t![ k] == t![ k + nth1 m j].
  Proof.
    intros.
    rewrite (inv_factt_nth1 k j);auto.
    rewrite <-mulA, (mulC (inv_Sn _)).
    rewrite ntimes_embed.
    rewrite inv_Sn_spec.
    ring.
  Qed.
  Lemma fun_ps_mult  (f : (A (S d))) (g : (A (S d))) : (fun_ps (f*g)) == (fun_ps f) * (fun_ps g).
  Proof.
    unfold fun_ps.
    intros.
    apply ps_eq_order.
    intros.
    generalize dependent f.
    generalize dependent g.
    generalize dependent k.
    induction n;intros.
    - apply order_zero_eq_zero in H7.
      rewrite idx_index, (idx_index (_ * _)), !H7, <-!idx_index.
      rewrite ps_mul0.
      rewrite !derive_rec_0.
      rewrite eval_mul_compat.
      rewrite inv_factt0.
      ring.
    - destruct (tuple_pred_spec' k);try (rewrite H7;simpl;lia).
      rewrite idx_index, (idx_index (_ * _)), !H9, <-!idx_index.
      rewrite <-deriv_rec_next_pdiff;auto.
      symmetry.
      rewrite deriv_next_backward_full;auto.
      symmetry.
      rewrite <-inv_factt_nth1';auto.
      rewrite !mulA.
      apply ring_eq_mult_eq; try reflexivity.
      rewrite pdiff_mult.
      rewrite !derive_rec_plus.
      rewrite eval_plus_compat.
      ring_simplify.
      rewrite !IHn;auto;try (rewrite tuple_pred_order;lia).
      symmetry.
      rewrite index_proper.
      3:reflexivity.
      2:{
        apply pdiff_mult.
      }
      apply ring_eq_plus_eq.
      apply index_proper;try reflexivity.
      apply ring_eq_mult_eq; try reflexivity.
      intros j.
      rewrite deriv_next_full;auto.
      rewrite <-mulA.
      replace (j \_ (pred_index k) + 1)%nat with (S (j\_ (pred_index k))) by lia.
      rewrite <-(inv_factt_nth1 _ (pred_index k));auto.
      apply ring_eq_mult_eq; try reflexivity;auto.
      rewrite <-deriv_rec_next_pdiff;try rewrite tuple_pred_order; try lia;reflexivity.
      apply index_proper;try reflexivity.
      apply ring_eq_mult_eq; try reflexivity.
      intros j.
      rewrite deriv_next_full;auto.
      rewrite <-mulA.
      replace (j \_ (pred_index k) + 1)%nat with (S (j\_ (pred_index k))) by lia.
      rewrite <-(inv_factt_nth1 _ (pred_index k));auto.
      apply ring_eq_mult_eq; try reflexivity.
      rewrite <-deriv_rec_next_pdiff;try rewrite tuple_pred_order; try lia;reflexivity.
  Qed.
    
  Lemma fun_ps_D0  (f : (A (S d))):  (fun_ps (D[0] f)) == D[0] (fun_ps f).
  Proof.
    unfold fun_ps.
    intros k.
    destruct (destruct_tuple_cons k) as [i [t ->]].
    setoid_rewrite deriv_next.
    rewrite <-!mulA.
    replace (i+1)%nat with (S i) at 2 by lia.
    rewrite inv_factt_S_reverse.
    apply ring_eq_mult_eq; try reflexivity.
    rewrite deriv_rec_next.
    replace (S i) with (i+1)%nat by lia.
    reflexivity.
  Qed.

  Lemma fun_ps_D  (f : (A (S d)))  j: (j < (S d)) -> (fun_ps (D[j] f)) == D[j] (fun_ps f).
  Proof.
    unfold fun_ps.
    intros.
    intros k.
    setoid_rewrite deriv_next_full;auto.
    rewrite <-mulA.
    replace (k\_j+1)%nat with (S k\_j) at 1 by lia.
    apply ring_eq_mult_eq.
    apply inv_factt_nth1;auto.
    rewrite deriv_rec_next_pdiff;auto.
    reflexivity.
 Qed.

  Lemma F_ps_same (F : Analytic): forall n  i , (i < S d) ->  (fun_ps (Fi F.(f) (S n) i))  ==  (Fi (d:=(S d)) (A := ps) (f_to_ps F) (S n) i).
  Proof.
    intros n.
    induction n.
    - intros.
      intros k.
      unfold fun_ps.
      rewrite IVP_F1;auto.
      setoid_rewrite (index_proper (A := (A 0)));  try rewrite IVP_F1; try reflexivity;auto.
      rewrite f_to_ps_spec;auto.
      unfold fi_to_ps, fun_ps.
      reflexivity.
    - intros.
       assert ((Fi (f F) (S (S n)) i) == (sum (fun j => (f F)\_j * (D[j] (Fi (f F) (S n) i))) (S d))) by (simpl;reflexivity).
       rewrite H8.
       rewrite Fi_S.
       rewrite fun_ps_sum.
       apply sum_ext.
       intros.
       rewrite fun_ps_mult.
       rewrite f_to_ps_spec;auto.
       unfold fi_to_ps.
       apply ring_eq_mult_eq; try reflexivity.
       rewrite fun_ps_D;auto.
       apply pdiff_proper.
       apply IHn;auto.
  Qed.

  Lemma y_ps_same (F : Analytic): forall i k, (i < S d) ->   analytic_solution_ps F i k  == ps_add_y0 F k i.
   Proof.  
     intros.
     unfold ps_add_y0.
     unfold analytic_solution_ps.
     unfold powerseries_yi.
     destruct k.
     - simpl.
       ring_simplify.
       unfold eval0.
       rewrite eval_id;auto.
       reflexivity.
     - 
       unfold y_i.
       pose proof (F_ps_same F k i H7 0).
       rewrite <-H8.
       apply ring_eq_mult_eq;try reflexivity.
       unfold fun_ps.
       rewrite inv_factt0.
       rewrite derive_rec_0.
       ring.
  Qed.

   Lemma fast_cauchy_neighboring_proper f g: (forall n, f n == g n) -> fast_cauchy_neighboring f <-> fast_cauchy_neighboring g. 
   Proof.
     intros.
     split;unfold fast_cauchy_neighboring;intros.
     rewrite <-!H7.
     apply H8.
     rewrite !H7; apply H8.
   Qed.

   Lemma fast_cauchy_neighboring_ps_proper f g x: (forall n, f n == g n) -> fast_cauchy_neighboring (fun n => (partial_sum (to_ps f) x n)) <-> fast_cauchy_neighboring (fun n => (partial_sum (to_ps g) x n)). 
   Proof.
     intros.
     apply fast_cauchy_neighboring_proper.
     intros.
     unfold partial_sum.
     apply sum_ext.
     intros.
     rewrite !to_ps_simpl.
     rewrite H7.
     reflexivity.
   Qed.
   (* Local Lemma calc1 F :   # 2 * ntimes (S d) # (M F) * # (r F) <= # (Init.Nat.max 1 (2 * S d * M F * r F)). *)
   (* Proof. *)
   (*   setoid_replace (ntimes (A := A 0)( S d) # (M F)) with (ntimes (A := A 0) (S d) 1 * # (M F)). *)
   (*   rewrite <-ntimes_embed. *)
   (*   rewrite <-!(nat_mult_compat (A := A 0)). *)
   (*   apply ntimes_monotone;lia. *)
   (*   rewrite ntimes_embed. *)
   (*   setoid_replace (ntimes (A := (A 0)) (M F) 1) with ((ntimes (A := (A 0)) (M F) 1) * 1) at 1 by ring. *)
   (*   rewrite ntimes_mult. *)
   (*   ring. *)
   (* Qed. *)

   (* Local Lemma calc2 F :  ntimes (S d) # (M F) <= npow # 2 (Nat.log2_up (S d * M F)). *)
   (* Proof. *)
   (*    rewrite nat_pow_compat. *)
   (*   setoid_replace (ntimes (A := A 0)( S d) # (M F)) with (ntimes (A := A 0) (S d) 1 * # (M F)). *)
   (*   rewrite <-ntimes_embed. *)
   (*   rewrite <-!(nat_mult_compat (A := A 0)). *)
   (*   rewrite !ntimes_embed. *)
   (*   destruct (M F). *)
   (*   simpl. *)
   (*   replace (d * 0)%nat with 0%nat by lia. *)
   (*   simpl. *)
   (*   ring_simplify. *)
   (*   apply le_0_1. *)
   (*   rewrite <-!ntimes_embed. *)
   (*   apply ntimes_monotone. *)
   (*   apply Nat.log2_up_le_pow2; try lia. *)
   (*   rewrite !ntimes_embed. *)
   (*   setoid_replace (ntimes (A := (A 0)) (M F) 1) with ((ntimes (A := (A 0)) (M F) 1) * 1) at 1 by ring. *)
   (*   rewrite ntimes_mult. *)
   (*   ring. *)
   (* Qed. *)
   (* Definition analytic_solution_M F := # (S d) * F.(M). *)
   Definition analytic_solution_M (Mf rf : (A 0)) : (A 0) := 1.
   Definition analytic_solution_r (Mf rf : (A 0)) := (# (2*(S d))) * Mf * rf.

   (* Definition analytic_solution_r F : {ry : nat | #2 * (ntimes (S d) #F.(M)) * #F.(r) <= #ry /\ 0 < ry   }. *)
   (* Proof. *)
   (*   exists (Nat.max 1 (2*(S d) * F.(M) * F.(r)))%nat. *)
   (*   split;try lia. *)
   (*   pose proof (ntimes_int (S d ) (M F)). *)
   (*   apply calc1. *)
   (* Defined. *)
   (* Definition analytic_solution_logM (F : Analytic) : {logM : nat | ntimes (S d) #F.(M) <= npow (#2) logM }. *)
   (*  Proof. *)
   (*    exists (Nat.log2_up ((S d) * F.(M))). *)
   (*    apply calc2. *)
   (*  Defined. *)


   Definition to_ps_remove0 (f : nat -> A 0) := to_ps (fun n => match n with 0 => 0 | _ => f n end).

   Lemma to_ps_rz0 f : (to_ps_remove0 f t(0)) == 0.
   Proof.
     reflexivity.
   Qed.
   Lemma to_ps_rzs f k : (to_ps_remove0 f t(S k)) == to_ps f t(S k).
   Proof.
   reflexivity.
   Qed.
   Lemma f_mps_bound F :tuple_bound_strong (f_to_ps F) t( a_bound_series F.(M) F.(r))\_0.
   Proof.
      unfold tuple_bound_strong.
      intros;auto.
      pose proof (deriv_bound F).
      rewrite f_to_ps_spec;auto.
      apply H8;auto.
   Qed.

   (* Definition bound_ps F := (a_bound_series (A := (A 0)) (analytic_solution_M F)  (analytic_solution_r F)). *)
   Definition bound_ps F := (a_bound_series (A := (A 0)) 1  (analytic_solution_r F.(M) F.(r))).

   Lemma bound_solution F : forall i, i < (S d) -> (mps_bound (to_ps_remove0 ( (analytic_solution_ps F i))) (bound_ps F) ).
   Proof.
     Opaque ntimes embNat.
     intros.
     unfold mps_bound.
     intros k.
     destruct (destruct_tuple1 k) as [k0 ->].
     destruct k0.
     { rewrite to_ps_rz0.
       rewrite norm_zero_eq.
       rewrite order1d.
       simpl; unfold bound_ps.
       unfold analytic_solution_r.
       (* destruct (analytic_solution_logM F). *)
       (* destruct (analytic_solution_r F). *)
       unfold a_bound_series.
       unfold to_ps.
       simpl.

       ring_simplify.
       simpl.
       apply le_0_1.
       (* apply mul_pos_pos. *)
       (* rewrite ntimes_embed. *)
       (* apply le_0_n. *)
       (* apply F. *)
     }
     setoid_rewrite y_ps_same;try (simpl;lia).
     assert (rpos : 0 <= F.(r))
      by (apply (le_trans _ _ _ (le_0_1)); apply F).
     assert (Mpos : 0 <= F.(M))
      by (apply (le_trans _ _ _ (le_0_1)); apply F).
     (* rewrite ntimes_embed. *)
     (* apply ntimes_nonneg;apply le_0_1. *)
     (* assert (Mpos : 0 <= #F.(M)). *)
     (* rewrite ntimes_embed. *)
     (* apply ntimes_nonneg;apply le_0_1. *)
     (* destruct (destruct_tuple1 (S k0)) as [k0 ->]. *)
     pose proof (y_bound (f_bounded := (f_mps_bound F)) (rpos := rpos) (Mpos := Mpos)   i k0 H7).
     unfold powerseries_yi.
     rewrite yt_spec in H8;auto.
     apply (le_trans _ _ _ H8).
     unfold bound_ps.
     rewrite order1d.
     unfold a_bound_series.
     rewrite to_ps_simpl.
     unfold analytic_solution_r.
     (* Transparent ntimes. *)
     ring_simplify.
     Opaque Nat.mul.
     simpl.
     Transparent Nat.mul.

     apply mul_le_le_compat_pos;  try apply npow_pos; try apply mul_pos_pos;try rewrite !ntimes_embed;try apply ntimes_nonneg; try apply ntimes_nonneg;try apply mul_pos_pos;try rewrite !ntimes_embed; try apply ntimes_nonneg;try apply le_0_1;try apply le_0_n; try apply F;auto.
     rewrite <-ntimes_embed.
     rewrite ntimes_spec.
     rewrite nat_mult_compat.
     rewrite !mulA,(mulC #2),!mulA, <-mulA.
     setoid_replace (# (S d) * M F) with ((  # (S d) * M F ) * 1) at 1 by ring.
     apply mul_le_compat_pos.
     apply mul_pos_pos; [rewrite ntimes_embed;apply ntimes_nonneg;apply le_0_1|apply Mpos].
     setoid_replace (1 : A 0) with ((1 : A 0) * 1) by ring.
     apply mul_le_le_compat_pos; try apply le_0_1; try apply F.
     Transparent ntimes.
     setoid_replace (1 : A 0) with (# 1) by rewrite ntimes_embed;simpl;try ring.
     apply ntimes_monotone;lia.
     apply le_eq.
     apply npow_proper.
    rewrite !ntimes_spec, <-mulA, <-nat_mult_compat; reflexivity.
     
     (* apply l. *)
     (* enough (#1 <= #x0). *)
     (* simpl in H11. *)
     (* ring_simplify in H11. *)
     (* apply (le_trans _ (npow #x0 k0 * 1)). *)
     (* ring_simplify;apply npow_monotone;auto. *)
     (* apply mul_pos_pos; try apply mul_pos_pos;try apply mul_pos_pos; try rewrite !ntimes_embed; try apply npow_pos; try apply ntimes_nonneg;try apply ntimes_nonneg;try apply le_0_1. *)

     (* rewrite (mulC #x0). *)
     (* apply mul_le_compat_pos;try apply npow_pos;try rewrite !ntimes_embed;try apply le_0_n;auto. *)
     (* rewrite !ntimes_embed in H11. *)
     (* simpl in H11; ring_simplify in H11;auto. *)
     (* destruct x0; try lia;auto. *)
     (* apply ntimes_monotone;lia. *)

  Qed.

  Lemma fast_cauchy_neighboring_r0 f x  : fast_cauchy_neighboring (fun n => partial_sum (to_ps_remove0 f) x ( n + 1)) -> fast_cauchy_neighboring (fun n => partial_sum (to_ps f) x (n + 1)%nat).
  Proof.
    intros C n.
    specialize (C (n)%nat).
    simpl.
    replace ( S n + 1)%nat with (S ( n +1))%nat by lia.
    rewrite partial_sum_neighboring.
    simpl in C.
    replace (S n + 1)%nat with (S ( n +1))%nat in C by lia.
    rewrite partial_sum_neighboring in C.
    replace (n+1)%nat with (S (n)) by lia.
    rewrite <-to_ps_rzs.
    replace (S n)%nat with (n+1)%nat by lia.
    apply C.
  Qed.

  Definition solution_rinv (Mf Mr : A 0) := (inv_approx (analytic_solution_r Mf Mr)).
  Lemma solution_rinv_spec (Mf Mr : A 0) : analytic_solution_r Mf Mr  * solution_rinv Mf Mr == 1.
  Admitted.

     Transparent npow.
   Definition analytic_modulus (F : Analytic) (t : (A 0)) i  : i<(S d) -> abs (t) <= inv2 * (solution_rinv F.(M) F.(r)) -> fast_cauchy_neighboring (fun n => partial_sum (to_ps (analytic_solution_ps F i)) t ( n + 1)).
   Proof.
     intros.
     pose proof (bound_solution F i H7).
     unfold bound_ps in H9.
     apply fast_cauchy_neighboring_r0.
     (* destruct (analytic_solution_logM F) as [logM PM]. *)
     (* destruct (analytic_solution_r F) as [r pr]. *)
     Opaque ntimes.
     simpl in *.
     (* (* assert (#(S r) * inv_Sn r == 1) by (rewrite ntimes_embed; apply inv_Sn_spec). *) *)
     (*  assert (mps_bound (to_ps_remove0 ( analytic_solution_ps F i)) (a_bound_series (npow #2 logM) # (S r))). *)
     (* { *)
     (*   intros k. *)
     (*   apply (le_trans _ _ _ (H9 k)). *)
     (*   unfold a_bound_series. *)
       
     (*   rewrite !to_ps_simpl. *)
     (*   unfold bound_ps; simpl. *)
     (*   apply mul_le_compat_pos; try apply npow_pos;try rewrite !ntimes_embed; try apply le_0_n. *)
     (*   apply npow_monotone; try rewrite ntimes_embed;try apply le_0_n. *)
     (*   rewrite <-ntimes_embed. *)
     (*   apply ntimes_monotone;lia. *)
     (* } *)

     intros n.
     pose proof (bounded_ps_modulus_spec  (to_ps_remove0  (analytic_solution_ps F i)) 1 (analytic_solution_r F.(M) F.(r))  (solution_rinv F.(M) F.(r)) 0 t (solution_rinv_spec F.(M) F.(r))  (le_refl _ ) H8 H9 n).
     simpl in H10.
     unfold bps_modulus in H10.
     replace (S n + 1)%nat with (((S n) + 1 + 0))%nat by lia.
     replace (n +1)%nat with ((n+1 + 0))%nat  by lia.
     simpl.
     apply H10.
 Qed.

  Definition taylor_poly (F : Analytic) (i : nat) (n : nat)  : @poly ((A 0)).
  Proof.
    induction n.
    apply [analytic_solution_ps F i 0%nat].
    apply (IHn ++ [analytic_solution_ps F i (S n)]).
  Defined.


  (* Definition taylor_error (F: Analytic) (k : nat) (n : nat) : (A 0). *)
  (* Proof. *)
  (*    remember (ntimes (S d) F.(M)) as M. *)
  (*    remember (inv_Sn (k*r+1)) as x. *)
  (*    remember (1 - x) as y. *)
  (*    assert (not (y == 0)). *)
  (*    { *)
  (*      intros Hy. *)
  (*      rewrite Heqy in Hy. *)
  (*      assert (x == 1) by (setoid_replace x with (x + (1 - x)) by rewrite Hy;ring). *)
  (*      rewrite Heqx in H7. *)
  (*      rewrite <-inv_Sn0 in H7. *)
  (*      apply inv_Sn_injective in H7. *)
  (*      lia. *)
  (*    } *)
  (*    apply (M * npow x (S n) * y). *)
  (* Defined. *)

  (* From Coq Require Import QArith. *)
  (* Definition tail_error (F: Analytic) (q : Q) (n : nat) : Q. *)
  (* Proof. *)
  (*    destruct (analytic_solution_r F) as [r [pr1 pr2]]. *)
  (*    remember ((S d) * F.(M))%nat as M. *)
  (*    remember (q / (inject_Z (Z.of_nat r)) ) as x. *)
  (*    remember (1 - x) as y. *)
  (*    apply (inject_Z (Z.of_nat M) * (x ^ (Z.of_nat (S n))) * y). *)
  (* Defined. *)
End Analytic.

