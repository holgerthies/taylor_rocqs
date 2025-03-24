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
Require Import ode.
Require Import polynomial.
Require Import odebounds.

 Open Scope algebra_scope.
Section Completeness.
  Class ConstrComplete `{ArchimedeanField} :=
  {
    has_limit : forall (xn : nat -> A), fast_cauchy_neighboring xn -> { x | forall n, norm (x - xn n) <= npow inv2 n}
  }.

End Completeness.
Section Analytic.

  Open Scope fun_scope.
  Context `{AbstractFunctionSpace }.
  Context `{ArchimedeanField (A:=A 0) (H:=H 0) (R_rawRing := H0 0) (R_semiRing := H1 0) }.


  Context `{CompositionalDiffAlgebra (A := (ps (A := (A 0)))) (H := (ps_set)) }.
  Context `{@AbstractPowerSeries (A 0) (H 0) (H0 0) (H1 0) H7 H8 H9 H10 invSn}.

  Context `{cs_exists : CoeffSum (A := A 0) (H:= _ ) (R_rawRing := _) (H0 := _) (H1 := _) (H2 := _) (H3 := _) (H4 := _ ) (invSn := _) (A_Ring := _) (R_TotalOrder := _) (normK := _) (R_Field := R_Field) (R_Field0 := R_Field0) (H5 := _) }.
   Add Ring KRing: (ComRingTheory (A := (A 0))).
  (* Context `{AbstractPowerseries (A := (A 0)) (H := (H 0))  (H1 := _)   }. *)
  (* Context `{norm_abs : forall x, 0 <= x -> norm x == x}. *)
  Context {d : nat}.
  Context {y0 : (A 0)^(S d)}.
  Context {in_dom : forall f, y0 \in_dom f}.

  Definition eval0 f := f @ (y0; in_dom f).

  Notation "f {y0}" := (eval0 f) (at level 2).

   Definition fun_ps (f : (A (S d))) (k : nat^(S d)) :=  t![k] * (Dx[k] (f)){y0}.
  Record Analytic  := {
      f : (A (S d))^(S d);
      M : nat;
      r : nat;
      deriv_bound : forall i , i<(S d) -> strong_bound (fun_ps f\_i) (a_bound_series #M #r)
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


  Definition powerseries_yi (F : Analytic) := @y_i (A 0) (H 0) (H0 0) (H1 0) H7 H8 H9 H10 invSn d  (f_to_ps F).


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
    rewrite H14.
    intros.
    specialize (IHe _ _ H15 (S j)).
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

  Lemma fun_ps_mult  (f : (A (S d))) (g : (A (S d))) : (fun_ps (f*g)) == (fun_ps f) * (fun_ps g).
  Proof.
    intros k.
    unfold fun_ps.
  Admitted.

  Lemma fun_ps_D0  (f : (A (S d))):  (fun_ps (D[0] f)) == D[0] (fun_ps f).
  Proof.
    unfold fun_ps.
    intros k.
    destruct (destruct_tuple_cons k) as [i [t ->]].
    rewrite deriv_next.
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
    intros.
    destruct j.
    apply fun_ps_D0.
    intros k.
    unfold fun_ps.
 Admitted.

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
       rewrite H13.
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
       pose proof (F_ps_same F k i H12 0).
       rewrite <-H13.
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
     rewrite <-!H12.
     apply H13.
     rewrite !H12; apply H13.
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
     rewrite H12.
     reflexivity.
   Qed.
   Lemma calc1 F :   # 2 * ntimes (S d) # (M F) * # (r F) <= # (Init.Nat.max 1 (2 * S d * M F * r F)).
   Proof.
     setoid_replace (ntimes (A := A 0)( S d) # (M F)) with (ntimes (A := A 0) (S d) 1 * # (M F)).
     rewrite <-!(nat_mult_compat (A := A 0)).
     apply ntimes_monotone;lia.
     setoid_replace (ntimes (A := (A 0)) (M F) 1) with ((ntimes (A := (A 0)) (M F) 1) * 1) at 1 by ring.
     rewrite ntimes_mult.
     ring.
   Qed.

   Lemma calc2 F :  ntimes (S d) # (M F) <= npow # 2 (Nat.log2_up (S d * M F)).
   Proof.
      rewrite nat_pow_compat.
     setoid_replace (ntimes (A := A 0)( S d) # (M F)) with (ntimes (A := A 0) (S d) 1 * # (M F)).
     rewrite <-!(nat_mult_compat (A := A 0)).
     destruct (M F).
     simpl.
     replace (d * 0)%nat with 0%nat by lia.
     simpl.
     ring_simplify.
     apply le_0_1.
     apply ntimes_monotone.
     apply Nat.log2_up_le_pow2; try lia.
     setoid_replace (ntimes (A := (A 0)) (M F) 1) with ((ntimes (A := (A 0)) (M F) 1) * 1) at 1 by ring.
     rewrite ntimes_mult.
     ring.
   Qed.

   Definition analytic_solution_r F : {ry : nat | #2 * (ntimes (S d) #F.(M)) * #F.(r) <= #ry /\ 0 < ry   }.
   Proof.
     exists (max 1 (2*(S d) * F.(M) * F.(r)))%nat.
     split;try lia.
     pose proof (ntimes_int (S d ) (M F)).
     apply calc1.
   Defined.
   Definition analytic_solution_logM (F : Analytic) : {logM : nat | ntimes (S d) #F.(M) <= npow (#2) logM }.
    Proof.
      exists (Nat.log2_up ((S d) * F.(M))).
      apply calc2.
    Defined.


   Definition to_ps_remove0 (f : nat -> A 0) := to_ps (fun n => match n with 0 => 0 | _ => f n end).

   Lemma to_ps_rz0 f : (to_ps_remove0 f t(0)) == 0.
   Proof.
     reflexivity.
   Qed.
   Lemma to_ps_rzs f k : (to_ps_remove0 f t(S k)) == to_ps f t(S k).
   Proof.
   reflexivity.
   Qed.
   Lemma f_mps_bound F :tuple_bound_strong (f_to_ps F) t( a_bound_series #F.(M) #F.(r))\_0.
   Proof.
      unfold tuple_bound_strong.
      intros;auto.
      pose proof (deriv_bound F).
      rewrite f_to_ps_spec;auto.
      apply H13;auto.
   Qed.

   Definition bound_ps F := (a_bound_series (A := (A 0)) (npow #2 (proj1_sig (analytic_solution_logM F))) #(proj1_sig (analytic_solution_r F))).

   Lemma bound_solution F : forall i, i < (S d) -> (mps_bound (to_ps_remove0 ( (analytic_solution_ps F i))) (bound_ps F) ).
   Proof.
     Opaque ntimes.
     intros.
     unfold mps_bound.
     intros k.
     destruct (destruct_tuple1 k) as [k0 ->].
     destruct k0.
     { rewrite to_ps_rz0.
       rewrite norm_zero_eq.
       rewrite order1d.
       simpl; unfold bound_ps.
       destruct (analytic_solution_logM F).
       destruct (analytic_solution_r F).
       unfold a_bound_series.
       unfold to_ps.
       simpl.
       ring_simplify.
       simpl.
       apply npow_pos.
       apply le_0_n.
     }
     setoid_rewrite y_ps_same;try (simpl;lia).
     assert (rpos : 0 <= #F.(r)).
     apply ntimes_nonneg;apply le_0_1.
     assert (Mpos : 0 <= #F.(M)).
     apply ntimes_nonneg;apply le_0_1.
     (* destruct (destruct_tuple1 (S k0)) as [k0 ->]. *)
     pose proof (y_bound (f_bounded := (f_mps_bound F)) (rpos := rpos) (Mpos := Mpos) (normK := normK)  i k0 H12).
     unfold powerseries_yi.
     rewrite yt_spec in H13;auto.
     apply (le_trans _ _ _ H13).
     unfold bound_ps.
     rewrite order1d.
     unfold a_bound_series.
     rewrite to_ps_simpl.
     destruct (analytic_solution_logM F).
     destruct (analytic_solution_r F).
     simpl.
     Transparent ntimes.
     destruct a.
     apply mul_le_le_compat_pos; try apply npow_pos; try apply mul_pos_pos;try apply ntimes_nonneg; try apply ntimes_nonneg;try apply mul_pos_pos; try apply ntimes_nonneg;try apply le_0_1;try apply le_0_n.
     apply l.
     enough (#1 <= #x0).
     simpl in H16.
     ring_simplify in H16.
     apply (le_trans _ (npow #x0 k0 * 1)).
     ring_simplify;apply npow_monotone;auto.
     apply mul_pos_pos; try apply mul_pos_pos;try apply mul_pos_pos; try apply npow_pos; try apply ntimes_nonneg;try apply ntimes_nonneg;try apply le_0_1.
     rewrite (mulC #x0).
     apply mul_le_compat_pos;try apply npow_pos;try apply le_0_n;auto.
     destruct x0; try lia;auto.
     apply ntimes_monotone;lia.

  Qed.

  Lemma fast_cauchy_neighboring_r0 f x g : fast_cauchy_neighboring (fun n => partial_sum (to_ps_remove0 f) x (g  + n + 1)) -> fast_cauchy_neighboring (fun n => partial_sum (to_ps f) x (g + n + 1)%nat).
  Proof.
    intros C n.
    specialize (C (n)%nat).
    simpl.
    replace (g + S n + 1)%nat with (S (g + n +1))%nat by lia.
    rewrite partial_sum_neighboring.
    simpl in C.
    replace (g + S n + 1)%nat with (S (g + n +1))%nat in C by lia.
    rewrite partial_sum_neighboring in C.
    replace (g+n+1)%nat with (S (g+n)) by lia.
    rewrite <-to_ps_rzs.
    replace (S (g+n))%nat with (g+n+1)%nat by lia.
    apply C.
  Qed.

   Definition analytic_modulus (F : Analytic) (t : (A 0)) i  : i<(S d) -> norm (t) <= inv2 * (inv_Sn (proj1_sig (analytic_solution_r F))) -> fast_cauchy_neighboring (fun n => partial_sum (to_ps (analytic_solution_ps F i)) t ((proj1_sig (analytic_solution_logM F)) + n + 1)).
   Proof.
     intros.
     apply fast_cauchy_neighboring_r0.
     pose proof (bound_solution F i H12).
     unfold bound_ps in H14.
     destruct (analytic_solution_logM F) as [logM PM].
     destruct (analytic_solution_r F) as [r pr].
       Opaque ntimes.
     simpl in *.
     assert (#(S r) * inv_Sn r == 1) by apply inv_Sn_spec.
      assert (mps_bound (to_ps_remove0 ( analytic_solution_ps F i)) (a_bound_series (npow #2 logM) # (S r))). 
     {
       intros k.
       apply (le_trans _ _ _ (H14 k)).
       unfold a_bound_series.

       rewrite !to_ps_simpl.
       apply mul_le_compat_pos; try apply npow_pos; try apply le_0_n.
       apply npow_monotone; try apply le_0_n.
       apply ntimes_monotone;lia.
     }

     intros n.
     pose proof (bounded_ps_modulus_spec  (to_ps_remove0  (analytic_solution_ps F i)) (npow #2 logM) #(S r) (inv_Sn r) logM t H15  (le_refl _ ) H13 H16 n).
     simpl in H17.
     unfold bps_modulus in H17.
     replace (logM + S n + 1)%nat with (((S n) + 1 + logM))%nat by lia.
     replace (logM + n +1)%nat with ((n+1 + logM))%nat  by lia.
     apply H17.
 Qed.

  Definition taylor_poly (F : Analytic) (i : nat) (n : nat)  : @poly ((A 0)).
  Proof.
    induction n.
    apply [analytic_solution_ps F i 0%nat].
    apply (IHn ++ [analytic_solution_ps F i (S n)]).
  Defined.
End Analytic.

Section AnalyticPoly.
  Context `{ArchimedeanField}.
  Context `{ConstrComplete (A := A) (H := _) (R_rawRing := _) (R_semiRing := _) (A_Ring := _ ) (R_Field0 := _) (R_Field := R_Field) (R_TotalOrder := _) (normK := _)  (H0 := H0) (invSn := _)}.
  Context `{AbstractPowerSeries (A := A) (H := H) (R_rawRing := R_rawRing) (H0 := _) (invSn := invSn) }.

  Context `{cs_exists : CoeffSum (A := A) (H:= _ ) (R_rawRing := _) (H0 := _) (H1 := _) (H2 := _) (H3 := _) (H4 := _ ) (invSn := _) (A_Ring := _) (R_TotalOrder := _) (normK := _) (R_Field := R_Field) (R_Field0 := R_Field0) (H5 := _) }.
   Add Ring KRing: (ComRingTheory (A :=A)).
  Lemma poly_tot {d} (y0 : A^(S d)) : forall (f : @mpoly A (S d)), y0 \in_dom f.
  Proof.
    intros.
    apply poly_total.
  Qed.

 Definition poly_norm {d} (p : A{x^d}) : A.
 Proof.
   induction d.
   apply (norm p).
   induction p.
   apply 0.
   apply ((IHd a) + IHp).
 Defined.

 Definition bounding_poly {d} (p : A{x^d}) : A{x^d}.
 Proof.
   induction d.
   apply (norm p).
   induction p.
   apply 0.
   apply ([IHd a] ++  IHp).
 Qed.

 Definition norm_plus_1 {d} (x : A^d) : A^d.
 Proof.
   induction d.
   apply 0.
   destruct (destruct_tuple_cons x) as [h [t P]].
   apply (tuple_cons ((norm h) + 1) (IHd t)).
 Defined.


   Definition poly_bound {d} (p : A{x^S d}) (y0 : A^(S d)) : A.  
   Proof.
     pose proof (bounding_poly p) as pb.
     pose proof (norm_plus_1 y0) as yb.
      apply (p @ (0; (poly_tot 0 p))). 
     (* apply (pb @ (yb; (poly_tot yb pb))). *)
   Defined.

   Definition poly_vec_bound {d} {e} (p : A{x^S d}^e) (y0 : A^(S d)) : A.  
   Proof.
     induction e.
     apply 0.
     destruct (destruct_tuple_cons p) as [p0 [tl P]].
     apply ((poly_bound p0 y0) +  (IHe tl)).
   Defined.
   Lemma poly_bound_spec {d} (p : A{x^S d}^S d)  (y0 : A^(S d)) i : i < S d -> strong_bound (fun_ps (A := @mpoly A) (in_dom := poly_tot y0) (y0 := y0) p\_i) (to_ps (fun n => #(proj1_sig (upper (poly_vec_bound p y0)))  * npow #1 n)).
   Admitted.


  Definition analytic_poly {d} (p : (@mpoly A (S d))^(S d)) y0  : Analytic (A := mpoly) (d := d) (y0 := y0) (in_dom := poly_tot y0) .
  Proof.
    unshelve eapply Build_Analytic.
    apply p.
    apply (proj1_sig (upper (poly_vec_bound p y0))).
    apply 1.
    intros.
    apply poly_bound_spec;auto.
  Defined.

   (* Definition ivp_solution_i  (F : (Analytic (A := mpoly))) (t : A) (i : nat)  :  norm t <=inv2 * inv_Sn (proj1_sig (analytic_solution_r (A := mpoly) F)) -> A 0. *)
   (* Proof. *)
   (*   intros. *)
   (*   pose proof (has_limit (ConstrComplete := H7) (approx F t i)). *)
   (*   destruct (X (fast_cauchy_neighboring_approx F t i H15 H14 )). *)
   (*   apply x. *)
   (* Defined. *)
   Definition approx {d} {y0 in_dom} (F : (Analytic (d:=d) (A := @mpoly A ) (y0 := y0) (in_dom := in_dom))) (t : A) i n :=  partial_sum (H := H) (R_rawRing := R_rawRing) (A := A)  (to_ps  (analytic_solution_ps (invSn := invSn) (A := mpoly) (H3 := mpoly_comp_diff_algebra) (F ) i)) t ((proj1_sig (analytic_solution_logM  F )) + n + 1).



   Lemma fast_cauchy_neighboring_approx {d} {y0 in_dom} (F : (Analytic (d:=d) (A := @mpoly A ) (y0 := y0) (in_dom := in_dom))) t i : norm t <=inv2 * inv_Sn (proj1_sig (analytic_solution_r   F))-> i < S d -> fast_cauchy_neighboring (approx F t i).
   Proof.
     intros.
     apply (analytic_modulus (H3 := mpoly_comp_diff_algebra));auto.
   Qed.

   (* Lemma fast_cauchy_neighboring_approx F t i : norm t <=inv2 * inv_Sn (proj1_sig (analytic_solution_r F))-> i < S d -> fast_cauchy_neighboring (approx F t i). *)
   (* Proof. *)
   (*   intros. *)
   (*   apply analytic_modulus;auto. *)
   (* Qed. *)
   Definition ivp_r_max {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly))   := ((inv2 * inv_Sn (proj1_sig (analytic_solution_r (A := @mpoly A)  F)))).

   Definition ivp_solution_i {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly))  (i : nat) t  :  norm t <= (ivp_r_max F)  -> A.
   Proof.
     intros.
     destruct (le_lt_dec i d); [|apply 0].
     assert (  fast_cauchy_neighboring  (approx  F t i)).
     {
       apply fast_cauchy_neighboring_approx;try lia.
       apply (le_trans _ _ _ H7).
       apply le_refl.
     }
     pose proof (has_limit (approx F t i)).
     destruct (X H8).
     apply x.
   Defined.

   Definition ivp_solution_i_max {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly))  (i : nat)  : A * A.
   Proof.
     assert (norm (ivp_r_max F) <= ivp_r_max F).
     {
       rewrite norm_abs;try apply le_refl.
       apply mul_pos_pos.
       apply inv2_pos.
       apply inv_Sn_pos.
     }
     apply ((ivp_r_max F), (ivp_solution_i F i (ivp_r_max F)) H7).
   Defined.

   Definition ivp_solution_max  {d} {y0} (F : Analytic (d:=d) (y0 :=y0) (in_dom := poly_tot y0) (A := mpoly)) : (A * ( A^(S d))).
   Proof.
     destruct (seq_to_tuple ((fun i => snd (ivp_solution_i_max F i))) (S d) (def := 0)).
     apply ((ivp_r_max F) , x).
   Defined.
   Record PIVP {d} := {
       pf : ((@mpoly A d)^d);
       py0 : A^d
     }.

   Definition pivp_solution_ith {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) (t : A) i := ivp_solution_i (analytic_poly p y0) i t.

   Definition pivp_solution_ith_max {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) i := ivp_solution_i_max (analytic_poly p y0) i.
   

   (* Definition pivp_solution_max {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) :  ((A * A)^(S d)). *)
   (* Proof. *)
   (*   destruct (seq_to_tuple (pivp_solution_ith_max p y0) (S d) (def := (0,0))). *)
   (*   apply x. *)
   (* Defined. *)

   Definition pivp_solution_max {d} (p : (@mpoly A (S d))^(S d)) (y0 : A^(S d)) :  (A * ( A^(S d))).
   Proof.
     destruct (seq_to_tuple ((fun i => snd (pivp_solution_ith_max p y0 i))) (S d) (def := 0)).
     apply ((ivp_r_max (analytic_poly p y0)) , x).
   Defined.

   Definition pivp_trajectory {d} (p : (@mpoly A (S d))^(S d)) (t0 : A) (y0 : A^(S d)) (steps : nat) :  list (A * (A^(S d))).
   Proof.
     revert t0 y0.
     induction steps;intros.
     apply [(t0,y0)].
     pose proof (pivp_solution_max p y0).
     apply ((t0, y0) :: (IHsteps (t0 + fst X) (snd X))).
   Defined.
End AnalyticPoly.
