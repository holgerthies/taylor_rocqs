Require Import Psatz.
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
  Section Polynomial.
  Context {A : Type} `{setoidA : Setoid A}.
  Context {A_comRing : comSemiRing}.

  Fixpoint npow (x : A) (n : nat) : A :=
    match n with
    | O => 1
    | S m => x * (npow x m)
    end.


  Add Ring ARing: ComSemiRingTheory.

  Definition poly := list A.
  
  Fixpoint eval_poly (a : poly) (x : A) :=
    match a with
    | nil => 0
    | h :: t => h + x * (eval_poly t x)  
    end.

  Fixpoint eval_poly_rec (a : poly) (x : A) (n : nat) :=
    match n with
    | 0 => 0
    | (S n') => last a 0  * (npow x n') + eval_poly_rec (removelast a) x n'
    end.

  Definition eval_poly2 a x := eval_poly_rec a x (length a).

  Lemma eval_poly2_app1 a an x : eval_poly2 (a ++ [an]) x = an * (npow x (length a)) + eval_poly2 a x.
  Proof.
    unfold eval_poly2 at 1.
    replace (length (a ++ [an])) with (S (length a)) by (rewrite app_length;simpl;lia).
    simpl.
    rewrite last_last.
    rewrite removelast_last.
    auto.
  Qed.

  Lemma eval_poly2_app a b x : eval_poly2 (a ++ b) x  == eval_poly2 a x  + npow x (length a) * eval_poly2 b x. 
  Proof.
  revert a.
  induction b as [| b0 b IH];intros.
  rewrite app_nil_r;unfold eval_poly2;simpl;ring.
  replace (a ++ b0 :: b) with ((a ++ [b0]) ++ b) by (rewrite <-app_assoc;auto).
  rewrite IH.
  rewrite eval_poly2_app1.
  rewrite app_length.
  simpl.
  rewrite addA, !(addC (eval_poly2 a x)), <-addA.
  apply ring_eq_plus_eq;auto.
  replace (length a + 1)%nat with (S (length a)) by lia.
  simpl.
  setoid_replace (b0 * npow x (length a) + x *npow x (length a)*eval_poly2 b x) with (npow x (length a) * (b0 + x * eval_poly2 b x)) by ring.
  apply ring_eq_mult_eq;auto.
  ring.
  replace (b0 :: b) with ([b0]++b) by auto.
  rewrite IH.
  simpl.
  unfold eval_poly2.
  simpl.
  ring.
  ring.
  Qed.

  Lemma eval_eval2 a x : eval_poly a x == eval_poly2 a x.
  Proof.
    induction a as [| a0 a]; [unfold eval_poly2;simpl;ring|].
    replace (a0 :: a) with ([a0]++a) by auto.
    rewrite eval_poly2_app.
    simpl.
    rewrite IHa.
    unfold eval_poly2.
    simpl;ring.
  Qed.

 Lemma smul_poly lambda p1: {p2 | forall x, eval_poly p2 x == lambda * eval_poly p1 x}.
 Proof.
   induction p1 as [| a0 p1' IH]; [exists []; intros;simpl;ring |].
   destruct IH as [p2' H].
   exists ((lambda * a0) :: p2' ).
   intros.
   simpl.
   setoid_replace (lambda * (a0 + x*eval_poly p1' x)) with (lambda*a0 + x * (lambda * eval_poly p1' x)) by ring.
   rewrite H;auto.
   ring.
 Defined.

  Definition sum_polyf  : poly -> poly -> poly.
  Proof.
    intros p1.
    induction p1 as [|a0 p1' S]; intros p2.
    apply p2.
    destruct p2 as [|b0 p2'].
    apply (a0 :: p1').
    apply ((a0 + b0) :: (S p2')).
  Defined.

  Lemma sum_polyf_spec p1 p2 x: eval_poly (sum_polyf p1 p2) x == eval_poly p1 x + eval_poly p2 x.
  Proof.
    revert p2.
    induction p1 as [| a0 p1'];intros; [simpl;ring|].
     destruct p2 as [| b0 p2'];[simpl;ring|].
     simpl.
     assert (forall y z u, y == z + u -> a0 + b0 + y == a0+z+(b0+u)) by (intros;rewrite H;ring).
     apply H.
     rewrite <-distrL.
     apply ring_eq_mult_eq;auto.
     ring.
  Qed.
 Lemma length_sum_coefficients a b : length (sum_polyf a b) = Nat.max (length a) (length b).
 Proof.
   revert b.
   induction a;simpl;auto.
   intros.
   destruct b;simpl; auto.
 Qed.

 Lemma sum_coefficient_nth a b n : nth n (sum_polyf a b) 0 == nth n a 0 + nth n b 0.
 Proof.
 revert n b.
 induction a;intros;simpl.
 destruct n;auto;ring.
 destruct b;destruct n;simpl; try ring;auto.
 Qed.

 Lemma sum_poly p1 p2 : {p3 | forall x, eval_poly p3 x == eval_poly p1 x + eval_poly p2 x}.
 Proof.
   exists (sum_polyf p1 p2).
   apply sum_polyf_spec.
 Defined.

 Lemma sum_poly_ext p1 p2 l1 l2 : {p3 | forall x, eval_poly p3 x == l1 * eval_poly p1 x + l2 * eval_poly p2 x}.
 Proof.
   destruct (smul_poly l1 p1) as [lp1 H1].
   destruct (smul_poly l2 p2) as [lp2 H2].
   destruct (sum_poly lp1 lp2) as [p3 H3].
   exists p3.
   intros.
   rewrite H3, H2, H1;auto.
   ring.
 Defined.


 Fixpoint convolution_coeff_rec (a b : list A) n i :=
   nth (n-i)%nat a 0 * nth i b 0 + match i with
     | 0 => 0
     | S i' => convolution_coeff_rec a b n i'
    end.

 Definition convolution_coeff (a b : list A) n := convolution_coeff_rec a b n n.

   Lemma convolution_coeff_rec_cons a b a0 n i  :(i <= n)%nat -> convolution_coeff_rec (a0 :: a) b (S n) i == convolution_coeff_rec a b n i.
  Proof.
   intros.
   induction i.
   - simpl.
     rewrite Nat.sub_0_r;unfold nth;simpl.
     ring.
   - simpl.
     assert (i < n)%nat by lia.
     destruct (n-i)%nat eqn: E; [lia|].
     rewrite IHi; try lia.
     assert ((n - S i)%nat = n0) as -> by lia.
     ring.
 Qed. 

 Lemma convolution_coeff_cons a b a0 n : convolution_coeff (a0 :: a) b (S n) == a0 * nth (S n) b 0 + convolution_coeff a b n.
 Proof.
   unfold convolution_coeff.
   simpl.
   destruct (n-n)%nat eqn:E;rewrite convolution_coeff_rec_cons;try lia;auto.
   ring.
 Qed.
   
 Fixpoint mult_coefficients_rec (a b : list A) n :=
   match n with
    | 0 => []
    | S n' =>  convolution_coeff a b ((length a + length b - 1) - n)%nat :: mult_coefficients_rec a b n'
     end.

 Definition mult_coefficients_rec_spec a b n m : (n < m)%nat -> nth n (mult_coefficients_rec a b m) 0 == convolution_coeff a b (length a + length b - 1  + n - m)%nat .
 Proof.
   revert n.
   induction m; intros; try lia.
   destruct n; simpl;try rewrite Nat.add_0_r;auto;try ring.
   rewrite IHm;try lia.
   assert (length a + length b - 1 + S n - S m = length a + length b - 1 + n - m)%nat as -> by lia.
   auto;ring.
 Qed.

 Definition mult_coefficients a b := mult_coefficients_rec a b (length a + length b - 1).

 Definition mult_coefficients_spec a b n : (n < length a + length b - 1)%nat -> nth n (mult_coefficients a b) 0 == convolution_coeff a b n.
 Proof.
   intros.
   unfold mult_coefficients.
   rewrite mult_coefficients_rec_spec; auto.
   assert (length a + length b - 1 + n - (length a + length b - 1) = n)%nat as -> by lia.
   reflexivity.
 Qed.

 Lemma length_mult_coefficients a b : length (mult_coefficients a b) = (length a + length b - 1)%nat.
 Proof.
   unfold mult_coefficients.
   induction (length a + length b - 1)%nat; simpl; try lia.
 Qed.

 Lemma convolution_coeff_rec_nil b i j : convolution_coeff_rec [] b j i == 0.
 Proof.
   induction i;intros.
   simpl.
   destruct (j-0)%nat;ring.
   simpl.
   rewrite IHi.
   destruct (j - S i)%nat;ring.
 Qed.    
 Lemma convolution_coeff_rec_nil2 a i j : convolution_coeff_rec a [] j i == 0.
 Proof.
   induction i;intros.
   simpl.
   destruct (j-0)%nat;ring.
   simpl.
   rewrite IHi.
   destruct (j - S i)%nat;ring.
 Qed.    

 Lemma mult_coefficients_single a0 b n : nth n (mult_coefficients [a0] b) 0 == a0 * (nth n b 0).
 Proof.
   destruct (Nat.le_gt_cases (n+1) ((length b))%nat).
   - rewrite mult_coefficients_spec; simpl;try rewrite Nat.sub_0_r;try lia.
     destruct n;unfold convolution_coeff;simpl.
     ring.
     rewrite Nat.sub_diag.
     rewrite convolution_coeff_rec_cons; try lia.
     rewrite convolution_coeff_rec_nil.
     ring.
   - assert (length (mult_coefficients [a0] b) <= n)%nat.
    {
     rewrite length_mult_coefficients.
     simpl.
     lia.
    }
    rewrite !nth_overflow;try ring;try lia;auto.
 Qed.
 Instance list_A_setoid : Setoid (list A).
 Proof.
   exists  (eqlistA SetoidClass.equiv).
   apply eqlistA_equiv.
   apply setoid_equiv.
 Defined.
 Lemma nth_ext_A_iff l1 l2 d1 d2 : (l1 == l2) <-> (length l1 = length l2 /\ forall n, n < length l1 -> nth n l1 d1 == nth n l2 d2).
 Proof.
   intros.
   split;intros;[split|].
   - apply (@eqlistA_length A SetoidClass.equiv);auto.
   - intros.
     generalize dependent n.
     induction H.
     intros.
     simpl in H0;lia.
     destruct n.
     simpl;auto.
     intros.
     simpl.
     apply IHeqlistA.
     simpl in H1;lia.
  - destruct H.
    generalize dependent l1.
    induction l2;intros.
    + simpl in H.
      apply length_zero_iff_nil in H.
      rewrite H.
      reflexivity.
    + destruct l1.
      simpl in H.
      lia.
      apply eqlistA_cons.
      specialize (H0 0%nat).
      simpl in H0.
      apply H0;lia.
      apply IHl2.
      simpl in H;lia.
      intros.
      specialize (H0 (S n)).
      simpl in H0.
      apply H0.
      lia.
  Qed.
 Lemma nth_ext_A l1 l2 d1 d2 : length l1 = length l2 -> (forall n, n < length l1 -> nth n l1 d1 == nth n l2 d2) -> l1 == l2.
 Proof.
   intros.
   rewrite (nth_ext_A_iff _ _ d1 d2).
   split;auto.
 Qed.

 Instance nth_proper : forall n l, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun (d :A) => nth n l d)).
 Proof.
   intros.
   intros x y H.
   destruct (Nat.lt_ge_cases n (length l) ).
   rewrite (nth_indep _ _ y);auto;reflexivity.
   rewrite !nth_overflow;auto.
 Defined.

 Lemma mult_coefficients_single_list a0 b : mult_coefficients [a0] b == map (fun x => a0 * x) b.
 Proof.
   apply (nth_ext_A _ _ 0 0).
   - rewrite length_mult_coefficients, map_length.
     simpl; lia.
  - intros.
    rewrite mult_coefficients_single.

    assert (0 == ((fun x => a0 * x) 0)) as R by ring.
    pose proof (nth_proper n (map (fun x => a0 * x) b) _ _ R).
    simpl in H0.
    rewrite H0.
    rewrite map_nth.
    reflexivity.
 Qed.

 Lemma nil_equiv a : a == [] -> a = [].
 Proof.
   intros.
   apply length_zero_iff_nil.
   apply eqlistA_length in H;auto.
 Qed.

  Lemma eqlistA_destruct a0 a b0 b: a0 :: a == b0 :: b -> a0 == b0 /\ a == b.  
  Proof.
   intros.
   apply eqlistA_altdef in H.
   apply Forall2_cons_iff in H.
   destruct H.
   split;auto.
   apply eqlistA_altdef;auto.
 Qed.

 Instance eval_proper : forall x, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun l => eval_poly l x)).
 Proof.
   intros.
   intros a b H.
   generalize dependent a.
   induction b;intros.
   - apply nil_equiv in H.
     rewrite H.
     simpl;reflexivity.
   -  destruct a0.
      symmetry in H.
      apply nil_equiv in H.
      discriminate H.
      simpl.
      destruct (eqlistA_destruct _ _ _ _ H).
      rewrite IHb;auto.
      rewrite H0;ring.
 Qed.

 Lemma mult_coefficients_eval_single a0 b x : eval_poly (mult_coefficients [a0] b) x == a0 * eval_poly b x.
 Proof.
   pose proof (eval_proper x). 
   rewrite H;[|apply mult_coefficients_single_list].
   induction b;simpl;try ring.
   rewrite IHb.
   ring.
 Qed.

 Lemma mult_coefficients_nil b n : nth n (mult_coefficients [] b) 0 == 0.
 Proof.
   destruct (Nat.le_gt_cases (n+1) ((length b-1))%nat).
   - rewrite mult_coefficients_spec; simpl; try lia.
     unfold convolution_coeff.
     apply convolution_coeff_rec_nil.
  - rewrite nth_overflow;auto;try ring.
    rewrite length_mult_coefficients.
    simpl;lia.
 Qed.

 Lemma mult_coefficients_nil_list b : mult_coefficients [] b == repeat 0 (length b - 1)%nat.
 Proof.
    apply (nth_ext_A _ _ 0 0).
    rewrite length_mult_coefficients, repeat_length.
    simpl;lia.
    intros.
    rewrite mult_coefficients_nil, nth_repeat;auto;reflexivity.
 Qed.

 Lemma mult_coefficients_eval_nil b x : eval_poly (mult_coefficients [] b) x == 0.
 Proof.
    pose proof (eval_proper x). 
    rewrite H; try apply mult_coefficients_nil_list.
    induction (length b - 1)%nat;simpl;try reflexivity;auto.
    rewrite IHn.
    ring.
 Qed.

 Lemma convolution_coeff_zero a b n: (length a + length b - 1<= n)%nat  -> convolution_coeff a b n == 0.
 Proof.
   revert n.
   induction a;intros.
   unfold convolution_coeff.
   rewrite convolution_coeff_rec_nil;auto;try ring.
   simpl in H.
   destruct n; try ring.
   - assert (b = []) as -> by (apply length_zero_iff_nil;lia).
     unfold convolution_coeff.
     simpl;ring.
   - rewrite convolution_coeff_cons.
     rewrite IHa; simpl in H;try lia.
      rewrite nth_overflow; [ring | lia].
 Qed.

 Lemma mult_coefficients_cons_nth a0 a b n : nth (S n) (mult_coefficients (a0 :: a) b) 0 == a0 * nth (S n) b 0 + convolution_coeff a b n.
 Proof.
   destruct (Nat.le_gt_cases (S n) ((length a+length b - 1))%nat).
   - rewrite mult_coefficients_spec; simpl; try lia.
     rewrite convolution_coeff_cons;auto;ring.
  - rewrite !nth_overflow;try rewrite length_mult_coefficients;simpl; try lia.
    rewrite convolution_coeff_zero;  [ring | lia].
 Qed.

 
 Lemma convolution_coeff_rec_inv_S a b n i : (i < n)%nat -> convolution_coeff_rec a b n (n-i) == convolution_coeff_rec a b n (n - S i) + nth i a 0 * nth (n-i)%nat b 0.
 Proof.
   simpl.
   destruct (n-i)%nat eqn:E.
   lia.
   intros.
   simpl.
   rewrite <-E.
   replace (n - (n-i))%nat with i by lia.
   destruct (n - S i)%nat eqn:E'.
   replace n0 with 0%nat by lia.
   simpl.
   ring.
   replace n0 with (S n1) by lia.
   ring.
 Qed.

 Lemma convolution_coeff_rec_opp a b n i: (i < n)%nat -> convolution_coeff_rec a b n n == convolution_coeff_rec a b n (n-S i)%nat + convolution_coeff_rec b a n i.
 Proof.
   intros.
   induction i.
   - destruct n; try lia.
     simpl.
     rewrite Nat.sub_diag.
     rewrite Nat.sub_0_r.
     ring.
   - rewrite IHi; try lia.
     rewrite convolution_coeff_rec_inv_S.
     simpl.
     ring.
     lia.
Qed.
 Lemma convolution_coeff_sym a b n : convolution_coeff a b n == convolution_coeff b a n.
 Proof.
  unfold convolution_coeff.
  destruct n; [simpl; ring | ].
  rewrite (convolution_coeff_rec_opp _ _ _ (n-1)%nat);try lia.
  destruct n; [simpl;ring|].
  replace (S (S n) - S (S n - 1))%nat with 1%nat by lia.
  simpl.
  rewrite Nat.sub_0_r, Nat.sub_diag.
  ring_simplify.
  destruct n.
  ring.
  replace (S n - n)%nat with 1%nat by lia.
  ring.
 Qed.

 Lemma mult_coefficients_sym a b : mult_coefficients a b  == mult_coefficients b a.
 Proof.
   apply (nth_ext_A _ _ 0 0).
   rewrite !length_mult_coefficients;lia.
   intros.
   rewrite length_mult_coefficients in H.
   rewrite !mult_coefficients_spec; try lia.
   apply convolution_coeff_sym.
  Qed.

 Instance nth_proper_list : forall n d, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun l => nth n l d)).
 Proof.
   intros.
   intros a b H.
   destruct (Nat.lt_ge_cases n (length a)).
   apply nth_ext_A_iff;auto.
   rewrite !nth_overflow;try reflexivity;auto.
   rewrite <-(eqlistA_length H);auto.
 Qed.

 Lemma mult_coefficients_cons a b a0 b0 : mult_coefficients (a0 :: a) (b0 :: b) == sum_polyf (mult_coefficients [a0] (b0 :: b)) (0 :: mult_coefficients a (b0 :: b)).
 Proof.
   apply (nth_ext_A _ _ 0 0).
   - rewrite length_sum_coefficients.
     rewrite !length_mult_coefficients;simpl.
     rewrite length_mult_coefficients;simpl.
     rewrite max_r;try lia.
   - intros.
     rewrite length_mult_coefficients in H.
     simpl in H.
     rewrite mult_coefficients_spec; try (simpl;lia).
     rewrite sum_coefficient_nth;try ring.
     rewrite nth_proper_list; try apply mult_coefficients_single_list.
     destruct n;simpl; [unfold convolution_coeff;simpl;ring|].
     rewrite convolution_coeff_cons.
     rewrite mult_coefficients_spec; try (simpl;lia).
     assert (0 == a0 * 0) as R by ring.
     rewrite (nth_proper n); try apply R.
     rewrite map_nth.
     simpl;reflexivity.
 Qed.

 Lemma mult_coefficients_eval_cons a b a0 x : eval_poly (mult_coefficients (a0 :: a) b) x == a0 * eval_poly b x + x*eval_poly (mult_coefficients a b) x.
 Proof.
   rewrite <-mult_coefficients_eval_single.
   destruct b.
   - rewrite eval_proper; try apply mult_coefficients_sym.
     rewrite !mult_coefficients_eval_nil.
     rewrite eval_proper; try apply mult_coefficients_sym.
     rewrite !mult_coefficients_eval_nil.
     rewrite eval_proper; try apply mult_coefficients_sym.
     rewrite !mult_coefficients_eval_nil.
     ring.
   - rewrite eval_proper; try apply mult_coefficients_cons.
     rewrite sum_polyf_spec;simpl.
     ring.
 Qed.

 Lemma mult_coeff_spec a b x : eval_poly (mult_coefficients a b) x == eval_poly a x * eval_poly b x.
 Proof.
   induction a; [rewrite mult_coefficients_eval_nil;simpl;ring |].
   simpl.
   rewrite mult_coefficients_eval_cons.
   rewrite IHa.
   ring.
 Qed.

 Lemma mult_poly p1 p2 : {p3 | forall x, eval_poly p3 x == eval_poly p1 x * eval_poly p2 x}.
 Proof.
   exists (mult_coefficients p1 p2).
   apply mult_coeff_spec.
 Defined.

 (*  Lemma shift_poly p1 c : {p2 | forall x, eval_poly p2 x = eval_poly p1 (x-c)}. *)
 (*  Proof. *)
 (*    induction p1 as [| a0 p1' IH]; [exists []; intros; simpl; ring | ]. *)
 (*    destruct IH as [p2 IH]. *)
 (*    destruct (mult_poly [-c; 1] p2) as [q Q]. *)
 (*    destruct (sum_poly [a0] q) as [q' Q']. *)
 (*    exists q'. *)
 (*    intros. *)
 (*    rewrite Q', Q, IH. *)
 (*    simpl. *)
 (*    ring. *)
 (* Qed. *)
   
  Lemma split_poly p d : {qu | (length (fst qu)) = (min d (length p)) /\ (length (snd qu)) = (length p - d)%nat /\ forall x, eval_poly p x == eval_poly (fst qu) x + npow x d * eval_poly (snd qu) x}.
  Proof.
    exists (firstn d p, skipn d p).
    split; [apply firstn_length|split;[apply skipn_length|]].
    intros.
    simpl.
    revert d.
    induction p; intros;[rewrite firstn_nil, skipn_nil;simpl;ring |].
    destruct d; [simpl;ring|].
    rewrite firstn_cons, skipn_cons.
    simpl.
    rewrite (IHp d).
    ring.
 Defined.


 
 (*  Lemma derivative_monomial n : forall x, uniform_derivative_fun (fun x => (npow x (S n))) (fun x => (Nreal (S n) * npow x n)) x. *)
 (* Proof. *)
 (*   intros. *)
 (*   induction n. *)
 (*   - simpl. *)
 (*     replace ((real_1+0)*real_1) with real_1 by ring. *)
 (*     replace (fun x => x*real_1) with (fun (x : ^Real) => x) by (apply fun_ext;intros;ring). *)
 (*     apply derivative_id_fun. *)
 (*  - replace (fun x => Nreal (S (S n)) * npow x (S n)) with (fun (x : ^Real) => x*(Nreal (S n) * npow x n) + real_1 * npow x ((S n))) by (apply fun_ext;intros;simpl;ring). *)
 (*    simpl. *)
 (*    apply product_rule. *)
 (*    apply derivative_id_fun. *)
 (*    apply IHn. *)
 (* Qed. *)

 Lemma monomial_poly a n : {p : poly | forall x, eval_poly p x == a * npow x n}.
 Proof.
   exists ((repeat 0 n) ++ [a]).
   intros.
   induction n; [simpl; ring|].
   simpl.
   rewrite IHn.
   ring.
 Defined.

 (* Lemma derive_poly_helper p1 p2 p1' p2' r : uniform_derivative_fun (eval_poly p1) (eval_poly p1') r -> uniform_derivative_fun (fun x => (npow x (length p1)) * (eval_poly p2 x)) (eval_poly p2') r -> uniform_derivative_fun (eval_poly (p1++p2)) (fun x => (eval_poly p1' x + eval_poly p2' x)) r. *)
 (* Proof. *)
 (*   intros H1 H2. *)
 (*   apply (derive_ext_fun _ (fun x => eval_poly p1 x + npow x (length p1) * eval_poly p2 x)); [intros;rewrite !eval_eval2;apply eval_poly2_app | ]. *)
 (*   apply sum_rule;auto. *)
 (* Qed. *)

 Fixpoint ntimes (n : nat) x := 
   match n with
    | 0 => 0
    | (S n') => x + ntimes n' x
   end. 

 Lemma ntimes_zero n : ntimes n 0 == 0.
 Proof.
   induction n;simpl;auto;try ring.
   rewrite IHn; ring.
 Qed.

 Lemma derive_monomial (a : A) (n : nat) : poly.
 Proof.
   destruct n; [apply []|].
   destruct (monomial_poly (ntimes (S n) a) n) as [p P].
   apply p.
 Defined.

 (* Lemma derive_monomial_spec a n : (projT1  (derive_monomial a (S n))) = (pr1 _ _ (monomial_poly (a * Nreal (S n)) n)).  *)
 (* Proof. *)
 (*   induction n;simpl;auto. *)
 (* Qed. *)
 Lemma rev_app1 {X : Type} (l : list X) a : (rev (l ++ [a])) = a :: (rev l).
 Proof.
   induction l.
   simpl;auto.
   simpl.
   rewrite IHl;auto.
 Defined.
 Lemma rev_involutive' {X : Type} (l : list X) : (rev (rev l)) = l.
 Proof.
   induction l.
   simpl;auto.
   simpl.
   rewrite rev_app1.
   simpl.
   rewrite IHl;auto.
 Defined.

 Lemma poly_rev_ind : forall (P : poly -> Type),
  P [] -> (forall (x : A) (l : poly), P l -> P (l ++ [x])) -> forall l : poly, P l.
 Proof.
   intros.
   replace l with (rev (rev l)) by (apply rev_involutive').
   induction (rev l).
   simpl.
   apply X.
   simpl.
   apply X0;auto.
 Defined.
  
 Lemma poly_deriv_exists (p : poly) : {p' : poly | length p' = (length p - 1)%nat /\ forall n,  nth n p' 0 == ntimes (S n) (nth (S n) p 0) }.
 Proof.
 induction p using poly_rev_ind;[exists [];split;auto; intros;rewrite nth_overflow;simpl;[rewrite ntimes_zero;ring | lia]|].
   destruct p.
   - exists [].
     split; auto.
     intros; rewrite nth_overflow; simpl; try lia.
     destruct n;simpl;try rewrite ntimes_zero; ring.
   - destruct IHp as [p' [P1 P2]].
     simpl in P1.
     rewrite Nat.sub_0_r in P1.
     exists (p' ++ [(ntimes (S (length p))) x]).
     split; [rewrite !app_length, P1;simpl;lia|].
     intros n.
     destruct (Nat.lt_ge_cases n (length p')).
     + rewrite app_nth1;auto.
       rewrite P2.
       simpl.
       rewrite app_nth1;try rewrite <-P1;auto.
       ring.
    + destruct H; [simpl;rewrite nth_middle, P1, nth_middle;ring|].
      simpl.
      rewrite !nth_overflow; try rewrite ntimes_zero; try ring; rewrite app_length;simpl; lia.
 Defined.

 Definition derive_poly p := (proj1_sig  (poly_deriv_exists p)).
 (* Lemma derive_poly_app p a : forall x, eval_poly (derive_poly (p ++ [a])) x  == eval_poly (derive_poly p) x + eval_poly (derive_monomial a (length p)) x. *)
 (* Proof. *)
 (*   intros. *)
 (*   unfold derive_poly. *)
 (*   destruct (poly_deriv_exists p) as [p1 [H1 H2]]. *)
 (*   destruct (poly_deriv_exists (p ++ [a])) as [p2 [H1' H2']]. *)
 (*   assert (p1 = [] /\ p2 = [] \/ (length p > 0)%nat /\ p2 = p1 ++ [ntimes (S (length p1)) a]). *)
 (*   { *)
 (*     destruct p; [left;rewrite length_zero_iff_nil in H1;rewrite length_zero_iff_nil in H1';auto|right]. *)
 (*     split;[simpl;lia|]. *)
 (*     apply (nth_ext _ _ 0 0); [rewrite H1', !app_length, H1;simpl;lia|]. *)
 (*     intros. *)
 (*     rewrite H2'. *)
 (*     simpl. *)
 (*     assert (length p1 = length p) by (simpl in H1;lia). *)
 (*     rewrite app_length in H1'; simpl in H1'. *)
 (*     destruct (Nat.lt_ge_cases n (length p)). *)
 (*     rewrite !app_nth1;try lia;rewrite H2;auto. *)
 (*     destruct H3. *)
 (*     rewrite <-H0 at 4. *)
 (*     rewrite !nth_middle. *)
 (*     rewrite H0;auto. *)

 (*     rewrite !nth_overflow; try rewrite ntimes_zero; try ring; try lia. *)

 (*   } *)
 (*   destruct H as [[-> ->] | [H ->]]; [simpl; replace (length p) with 0%nat;simpl;[ring|simpl in H1';rewrite H1';rewrite app_length;simpl;lia]|]. *)
 (*   simpl. *)
 (*   rewrite eval_eval2, eval_poly2_app, <-!eval_eval2. *)
 (*   rewrite !(addC (eval_poly p1 x)). *)
 (*   apply ring_eq_plus_eq;auto. *)
 (*   destruct (length p);try lia. *)
 (*   unfold  derive_monomial. *)
 (*   destruct (monomial_poly (ntimes (S n) a) n) as [m M]. *)
 (*   simpl;rewrite M. *)
 (*   rewrite H1. *)
 (*   simpl. *)
 (*   replace (n-0)%nat with n by lia. *)
 (*   ring. *)
 (* Qed. *)

(*  Lemma derive_poly_spec p : forall r, uniform_derivative_fun (eval_poly p) (eval_poly (derive_poly p)) r. *)
(*  Proof. *)
(*    unfold derive_poly. *)
(*    induction p as [| a p IH] using poly_rev_ind. *)
(*    - intros. *)
(*      destruct (poly_deriv_exists []) as [p' [H1 H2]]. *)
(*      simpl;replace p' with (@nil ^Real) by (rewrite length_zero_iff_nil in H1;auto). *)
(*      simpl;apply derivative_const_fun. *)
(*    - intros x. *)
(*      pose proof (derive_poly_app p a). *)
(*      apply (derive_ext_fun2 _  (fun x =>  eval_poly (derive_poly p) x + *)
(*       eval_poly (projT1 (derive_monomial a (length p))) x *)
(* )  _ x);auto. *)
(*      apply derive_poly_helper;auto. *)
(*      intros. *)
(*      destruct (derive_monomial a (length p)) as [m M]. *)
(*      simpl. *)
(*      apply (derive_ext_fun _ (fun x => a * npow x (length p))); [intros;ring|]. *)
(*      apply M. *)
(*  Qed. *)

 Definition mult_polyf a b := match (a,b) with
                                      | ([], _) => []
                                      | (_, []) => []
                                      |  (_, _) => mult_coefficients a b end.

   Lemma mult_coefficients0 a b : nth 0 (mult_coefficients a b) 0 == nth 0 a 0 * nth 0 b 0.
   Proof.
     destruct a.
     rewrite mult_coefficients_nil.
     simpl;ring.
     simpl.
     rewrite nth_proper_list; try apply mult_coefficients_sym.
     destruct b;[rewrite mult_coefficients_nil;simpl;ring|].
     rewrite nth_proper_list; try apply mult_coefficients_cons.
     rewrite sum_coefficient_nth.
     rewrite nth_proper_list; try apply mult_coefficients_single_list.
     simpl;ring.
  Qed.

  Lemma mult_coefficient_cons' a0 a b : b <> nil -> mult_coefficients (a0 :: a) b == sum_polyf (mult_coefficients [a0] b) (0 :: (mult_coefficients a b)).
  Proof.
    destruct b;intros;[contradict H;auto |].
    apply mult_coefficients_cons.
  Qed.

  Lemma mult_poly_sym a b:  mult_polyf a b== mult_polyf b a.
  Proof.
    destruct a;destruct b;unfold mult_polyf;simpl;auto.
    apply mult_coefficients_sym.
  Qed.

  Lemma mult_poly1 a :  mult_polyf a [1]==  a.
  Proof.
    destruct a;unfold mult_polyf;auto;try reflexivity.
    apply (nth_ext_A _ _ 0 0);[rewrite length_mult_coefficients;simpl;lia|].
    intros.
    rewrite nth_proper_list; try apply mult_coefficients_sym.
    rewrite mult_coefficients_single.
    ring.
  Qed.

  Lemma mult_coefficients_convolution: forall (a b : list A) (n : nat), nth n (mult_coefficients a b) 0 == convolution_coeff a b n.
  Proof.
    intros.
    destruct (Nat.lt_ge_cases n (length a + length b - 1)).
    apply mult_coefficients_spec;auto.
    rewrite convolution_coeff_zero; try lia.
    rewrite nth_overflow; [reflexivity |].
    rewrite length_mult_coefficients;lia.
  Qed.

  Lemma mult_coeffs_distr a b c : mult_coefficients a (sum_polyf b c) == sum_polyf (mult_coefficients a b) (mult_coefficients a c).

  Proof.
    apply (nth_ext_A _ _ 0 0).
    rewrite length_mult_coefficients, !length_sum_coefficients, !length_mult_coefficients;lia.
    intros.
    rewrite sum_coefficient_nth.
    rewrite length_mult_coefficients, length_sum_coefficients in H.
    rewrite !mult_coefficients_convolution.
    clear H.
    revert n.
    induction a.
    intros.
    unfold convolution_coeff; rewrite !convolution_coeff_rec_nil;ring.
    destruct n.
    unfold convolution_coeff.
    simpl.
    rewrite sum_coefficient_nth.
    ring.
    rewrite !convolution_coeff_cons.
    rewrite IHa.
    rewrite sum_coefficient_nth.
    ring.
  Qed.

  Lemma mult_poly_distr a b c : mult_polyf a (sum_polyf b c) == sum_polyf (mult_polyf a b) (mult_polyf a c).
  Proof.
     unfold mult_polyf.
     destruct a; destruct b; destruct c;  try (simpl;reflexivity);auto.
     simpl.
     apply (nth_ext_A _ _ 0 0).
     rewrite !length_mult_coefficients, length_sum_coefficients, length_mult_coefficients;simpl;lia.
     intros.
     rewrite sum_coefficient_nth.
     rewrite (nth_overflow nil); [ring |simpl;lia].
     apply mult_coeffs_distr.
  Qed.

  Lemma convolution_coeff_mult a b c n :  convolution_coeff (map (fun x : A => c * x) a) b n ==  c * convolution_coeff a b n.
  Proof.
    revert a.
    induction n.
    - intros.
      unfold convolution_coeff.
      simpl.
      rewrite (nth_proper _ _ 0 (c*0)); try ring.
      rewrite map_nth.
      ring.
    - intros.
      destruct a.
      simpl.
      unfold convolution_coeff.
      rewrite convolution_coeff_rec_nil;ring.
      simpl.
      rewrite convolution_coeff_cons.
      rewrite IHn.
      rewrite convolution_coeff_cons.
      ring.
  Qed.
  Lemma mult_coefficients_nonempty l1 l2 a b : mult_coefficients (a :: l1) (b :: l2) <> [].
  Proof.
    rewrite <- length_zero_iff_nil.
    rewrite length_mult_coefficients.
    simpl.
    lia.
  Qed.
 Instance convolution_coeff_proper : forall n, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun a b => convolution_coeff a b n)).
 Proof.
   intros n.
   induction n.
   intros a b H x y H0.
   destruct a;destruct b;destruct x; destruct y;unfold mult_polyf;try reflexivity; try (apply eqlistA_length in H;contradict H;simpl;lia); try (apply eqlistA_length in H0;contradict H0;simpl;lia).
   unfold convolution_coeff;rewrite !convolution_coeff_rec_nil;reflexivity.
   unfold convolution_coeff;rewrite !convolution_coeff_rec_nil2;reflexivity.
   destruct (eqlistA_destruct _ _ _ _ H).
   destruct (eqlistA_destruct _ _ _ _ H0).
   unfold convolution_coeff;simpl.
   rewrite H1, H3.
   ring.
   intros a b H x y H0.
   destruct a; destruct b;try (apply eqlistA_length in H;contradict H;simpl;lia).
   unfold convolution_coeff;rewrite !convolution_coeff_rec_nil;reflexivity.
   rewrite !convolution_coeff_cons.
   destruct (eqlistA_destruct _ _ _ _ H).
   rewrite IHn; try apply H2; try apply H0.
   rewrite H1.
   rewrite nth_proper_list; try apply H0.
   reflexivity.
 Qed.
 Instance mult_coefficients_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) mult_coefficients).
 Proof.
   intros a b H x y H0.
   apply (nth_ext_A _ _ 0 0).
   - apply eqlistA_length in H.
     apply eqlistA_length in H0.
     rewrite !length_mult_coefficients;lia.
   - intros.
     rewrite !mult_coefficients_convolution.
     apply convolution_coeff_proper;auto.
 Qed.

 Instance mult_poly_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) mult_polyf).
 Proof.
   intros a b H x y H0.
   destruct a;destruct b;destruct x; destruct y;unfold mult_polyf;try reflexivity; try (apply eqlistA_length in H;contradict H;simpl;lia); try (apply eqlistA_length in H0;contradict H0;simpl;lia).
   apply mult_coefficients_proper;auto.
 Qed.
 Instance sum_coefficients_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) sum_polyf).
 Proof.
   intros a b H x y H0.
   apply (nth_ext_A _ _ 0 0).
   - apply eqlistA_length in H.
     apply eqlistA_length in H0.
     rewrite !length_sum_coefficients;lia.
   - intros.
     rewrite !sum_coefficient_nth.
     rewrite nth_proper_list;try apply H.
     rewrite (nth_proper_list _ _ _ _ H0).
     reflexivity.
  Qed.

  Lemma mult_polyf_convolution a b n : nth n (mult_polyf a b) 0 == convolution_coeff a b n.
  Proof.
    unfold mult_polyf.
    destruct a; destruct b; try (unfold convolution_coeff; try rewrite convolution_coeff_rec_nil;try rewrite convolution_coeff_rec_nil2;destruct n;simpl;ring).
    apply mult_coefficients_convolution.
  Qed.

  Lemma convolution_coeff_add a b c  n : convolution_coeff (sum_polyf a b) c n == convolution_coeff a c n + convolution_coeff b c n.
  Proof.
    rewrite <-!mult_coefficients_convolution.
    rewrite nth_proper_list; try apply mult_coefficients_sym.
    rewrite nth_proper_list; try apply mult_coeffs_distr.
    rewrite sum_coefficient_nth.
    rewrite nth_proper_list; try apply (mult_coefficients_sym c);auto.
    rewrite (nth_proper_list n _ (mult_coefficients c b)); try apply (mult_coefficients_sym c);auto.
    ring.
  Qed.


  Lemma convolution_coeff_zero_list a n m : convolution_coeff (repeat 0 m) a n == 0. 
  Proof.
    destruct m.
    - simpl.
      unfold convolution_coeff; rewrite convolution_coeff_rec_nil;ring.
    - simpl.
      revert m.
      induction n;intros.
      unfold convolution_coeff;simpl;ring.
      rewrite convolution_coeff_cons.
      destruct m.
      unfold convolution_coeff; rewrite convolution_coeff_rec_nil;ring.
      simpl;rewrite IHn;ring.
  Qed.

  Lemma mult_polyf_nil1 a : mult_polyf a [] = [].
  Proof.
    simpl;unfold mult_polyf;destruct a;auto.
  Qed.
  Lemma mult_polyf_nil2 a : mult_polyf [] a = [].
  Proof.
    simpl;unfold mult_polyf;destruct a;auto.
  Qed.

  Lemma mult_poly_assoc a b c:  mult_polyf (mult_polyf a b) c == mult_polyf a (mult_polyf b c).
  Proof.
    apply (nth_ext_A _ _ 0 0).
    - destruct a;[rewrite !mult_polyf_nil2|destruct b; [rewrite mult_polyf_nil2, !mult_polyf_nil1|destruct c; [rewrite !mult_polyf_nil1|]]];simpl;auto.
      unfold mult_polyf.
      destruct (mult_coefficients (a :: a0) (a1 :: b)) eqn:E; [contradict E; apply mult_coefficients_nonempty|];rewrite <-E;clear E.
      destruct (mult_coefficients (a1 :: b) (a2 :: c)) eqn:E; [contradict E; apply mult_coefficients_nonempty|]; rewrite <-E; clear E.
      rewrite !length_mult_coefficients;simpl;lia.
    - intros.
      rewrite !mult_polyf_convolution.
      clear H.
      destruct a.
      unfold mult_polyf at 1;unfold convolution_coeff; rewrite !convolution_coeff_rec_nil;ring.
      unfold mult_polyf.
      destruct b.
      unfold mult_polyf, convolution_coeff; rewrite convolution_coeff_rec_nil, convolution_coeff_rec_nil2;ring.
      destruct c.
      unfold convolution_coeff, mult_polyf; rewrite !convolution_coeff_rec_nil2;ring.
      revert a a0 a1 b a2 c.
      induction n;intros.
      + unfold convolution_coeff.
        simpl.
        rewrite !mult_coefficients0;simpl.
        ring.
      + rewrite convolution_coeff_proper; try apply mult_coefficient_cons'; try reflexivity; try discriminate.
        rewrite convolution_coeff_add.
        rewrite convolution_coeff_cons.
        ring_simplify.
        rewrite convolution_coeff_cons.
        rewrite mult_coefficients_convolution.
        rewrite convolution_coeff_proper; try apply mult_coefficients_single_list; try reflexivity.
        rewrite convolution_coeff_mult.
        destruct a0;[|rewrite IHn;ring].
        enough (convolution_coeff (mult_coefficients [] (a1 :: b)) (a2 :: c) n == convolution_coeff [] (mult_coefficients (a1 :: b) (a2 :: c)) n) as -> by ring.
       rewrite convolution_coeff_proper; try apply mult_coefficients_nil_list; try reflexivity.
       rewrite convolution_coeff_zero_list.
       unfold convolution_coeff; rewrite convolution_coeff_rec_nil;ring.
   Qed.


  Lemma poly_comSemiRing : @comSemiRing poly _.
  Proof.
    exists [] [1] (sum_polyf) (mult_polyf); intros; try (apply (nth_ext_A _ _ 0 0);[intros;rewrite !length_sum_coefficients;simpl;lia|intros;rewrite !sum_coefficient_nth;destruct n; simpl;ring]); try (simpl;reflexivity).
    apply sum_coefficients_proper.
    apply mult_poly_proper.
    apply mult_poly_assoc.
    apply mult_poly_sym.
    unfold mult_polyf;destruct a;auto;try reflexivity.
    apply mult_poly1.
    apply mult_poly_distr.
 Defined.

End Polynomial.

Section MultiPoly.
  Context `{R : Type} `{R_setoid : Setoid R} `{R_semiRing : @comSemiRing R R_setoid}.
  Fixpoint mpoly n :=
    match n with
    | 0 => R
    | (S n) => @poly (mpoly n)
    end.

  Lemma mpoly_setoid : forall n, Setoid (mpoly n).
  Proof.
    intros.
    induction n.
    apply R_setoid.
    apply list_A_setoid.
  Defined.

  Lemma mpoly_comSemiRing : forall n, @comSemiRing (mpoly n) (mpoly_setoid n).
  Proof.
    intros.
    induction n.
    apply R_semiRing.
    apply poly_comSemiRing.
  Defined.

  Fixpoint const_to_mpoly n x : (mpoly n) := 
    match n with
    | 0 => x
    | (S n) => [const_to_mpoly n x]
   end.

  Definition eval_mpoly {n} (p : mpoly (S n)) x :=  @eval_poly _ _ (mpoly_comSemiRing n) p (const_to_mpoly n x).

End MultiPoly.

 Notation "p .{ x }" := (eval_mpoly  p x) (at level 2, left associativity).
From mathcomp Require Import  tuple.
Definition eval_tuple {R} {R_setoid : Setoid R} {R_semiRing : (@comSemiRing R R_setoid)} {n} (p : @mpoly R n) (t : n.-tuple R) : R. 
Proof.
   induction n.
   apply p.
   pose proof (p.{thead t}) as p0.
   apply (IHn p0 (behead_tuple t)).
Defined.

 Notation "p .[ x ]" := (eval_tuple  p x) (at level 2, left associativity).

Section DifferentialRing.
  Context {R : Type} {R_setoid : Setoid R} {R_comSemiRing : @comSemiRing R R_setoid}.
  Instance setoid_poly : Setoid (@poly R).
  Proof.
    apply list_A_setoid.
  Defined.

  Add Ring RRing: ComSemiRingTheory.
  Add Ring PRing: (@ComSemiRingTheory (@poly R) _ (@poly_comSemiRing R R_setoid R_comSemiRing)).

  Lemma ntimes_plus n x y : ntimes n (x+y) == ntimes n x + ntimes n y.
  Proof.
    induction n;simpl;[ring|].
    rewrite IHn;ring.
  Qed.

  Lemma ntimes_mult n x y : ntimes n (x*y) == x * ntimes n y.
  Proof.
    induction n;simpl;[ring|].
    rewrite IHn;ring.
  Qed.

  Lemma ntimes_0 n  : ntimes n 0 == 0.
  Proof.
    induction n;simpl;[ring|].
    rewrite IHn;ring.
  Qed.

  Lemma derive_poly_length (a : (@poly R)) : length (derive_poly a) = (length a - 1)%nat.
  Proof.
    unfold derive_poly; simpl.
    destruct (poly_deriv_exists a);simpl.
    lia.
  Qed.
  Lemma derive_poly_nth (a : @poly R) (n : nat) : nth n (derive_poly a) 0  == ntimes (S n) (nth (S n) a 0).
  Proof.
    unfold derive_poly; simpl.
    destruct (poly_deriv_exists a);simpl.
    apply a0.
  Qed.

  Lemma derive_poly_cons a0 a1 a : derive_poly (a0 :: a1 :: a) == sum_polyf (a1 :: a) (0 :: (derive_poly (a1 :: a))).
  Proof.
    apply (nth_ext_A _ _ 0 0).
    rewrite length_sum_coefficients;simpl; rewrite !derive_poly_length;simpl;lia.
    intros.
    rewrite sum_coefficient_nth.
    destruct n;simpl; rewrite !derive_poly_nth;simpl;ring.
  Qed.
  Instance cons_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun a0 a => a0 :: a)). 
  Proof.
    intros a b H a0 b0 H0.
    apply eqlistA_cons;auto.
  Defined.
  Instance sum_poly2_proper a : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (sum_polyf a)).
  Proof.
    apply sum_coefficients_proper.
    reflexivity.
  Defined.
  Instance sum_poly1_proper a : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (fun b => sum_polyf b a)).
  Proof.
    intros b b' H.
    apply sum_coefficients_proper.
    apply H.
    reflexivity.
  Defined.
  Instance mult_poly2_proper a : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (mult_polyf a)).
  Proof.
    apply mult_poly_proper.
    reflexivity.
  Defined.

 Instance convolution_coeff_proper2 n a:  (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun b => convolution_coeff a b n)).
 Proof.
   apply convolution_coeff_proper;reflexivity.
 Defined.
 Instance mult_coefficients2_proper a : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (mult_coefficients a)).
 Proof.
   apply mult_coefficients_proper.
   reflexivity.
  Defined.

  Lemma mult_poly_cons a0 (a b : poly) : mult_polyf (a0 :: a) b == sum_polyf (mult_polyf [a0] b) (mult_polyf (0 :: a) b).

  Proof.
     rewrite !(mult_poly_sym _ b).
     rewrite sum_coefficients_proper; try apply (mult_poly_sym _ b).
     rewrite <-mult_poly_distr.
     enough (sum_polyf [a0] (0 :: a) == a0 :: a) as ->;try reflexivity.
     apply (nth_ext_A _ _ 0 0).
     rewrite length_sum_coefficients;simpl;lia.
     intros.
     rewrite sum_coefficient_nth.
     destruct n; simpl;try ring.
     destruct n;ring.
  Qed.
  Lemma derive_nil : derive_poly [] = [].
  Proof.
    apply length_zero_iff_nil.
    rewrite derive_poly_length.
    simpl;lia.
  Qed.

  Lemma derive_const  a : derive_poly [a] = [].
  Proof.
    apply length_zero_iff_nil.
    rewrite derive_poly_length; simpl; lia.
  Qed.
  Instance ntimes_proper n : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (ntimes n)).
  Proof.
    intros a b H.
    induction n.
    simpl;ring.
    simpl.
    rewrite IHn, H.
    ring.
  Defined.

  Instance derive_poly_proper : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) derive_poly).
  Proof.
    intros a b H.
    apply (nth_ext_A _ _ 0 0).
    rewrite !derive_poly_length.
    apply eqlistA_length in H.
    lia.
    intros.
    rewrite !derive_poly_nth.
    apply ntimes_proper.
    apply nth_proper_list;auto.
  Defined.

  Lemma poly_scalar_mult_deriv a b : derive_poly (mult_polyf [a] b) == mult_polyf [a] (derive_poly b).
  Proof.
    destruct b.
    rewrite mult_polyf_nil1.
    rewrite derive_nil.
    rewrite mult_polyf_nil1;reflexivity.
    destruct b.
    rewrite derive_const.
    unfold mult_polyf.
    apply eqlistA_nil.
    apply (nth_ext_A _ _ 0 0).
    unfold mult_polyf.
    destruct (derive_poly (r :: r0 :: b)) eqn:E.
    apply length_zero_iff_nil in E;rewrite derive_poly_length in E; simpl in E;lia.
    rewrite <-E; clear E.
    rewrite derive_poly_length.
    rewrite !length_mult_coefficients.
    rewrite derive_poly_length.
    simpl;lia.
    intros.
    rewrite derive_poly_nth.
    rewrite !mult_polyf_convolution.
    rewrite convolution_coeff_cons.
    unfold convolution_coeff at 1.
    rewrite convolution_coeff_rec_nil.
    rewrite <-mult_coefficients_convolution.
    rewrite mult_coefficients_single.
    rewrite derive_poly_nth.
    rewrite ntimes_plus, ntimes_0, ntimes_mult.
    ring.
  Qed.

  Lemma derive_poly_const_independent a0 a : derive_poly (a0 :: a) == derive_poly (0 :: a).
  Proof.
    destruct a.
    rewrite !derive_const;auto; try reflexivity.
    rewrite !derive_poly_cons;try reflexivity.
  Qed.

  Lemma poly_sum_rule a b : derive_poly (sum_polyf a b) == sum_polyf (derive_poly a) (derive_poly b).
  Proof.
    apply (nth_ext_A _ _ 0 0).
     rewrite derive_poly_length;unfold add;simpl;rewrite !length_sum_coefficients, !derive_poly_length; lia.
    intros;rewrite derive_poly_nth.
    rewrite !sum_coefficient_nth,  !derive_poly_nth, ntimes_plus;ring.
  Qed.

  Lemma sum_poly0 a : sum_polyf a [] == a.
  Proof.
    apply (nth_ext_A _ _ 0 0).
    rewrite length_sum_coefficients;simpl;lia.
    intros.
    
    rewrite sum_coefficient_nth.
    destruct n;simpl;ring.
  Qed.

    Lemma mult_polyf_shift_switch a0 a b0 b : mult_polyf (0 :: (a0 :: a)) (b0 :: b) ==  mult_polyf (a0 :: a) (0 :: (b0 :: b)). 
  Proof.
    apply (nth_ext_A _ _ 0 0).
    unfold mult_polyf; rewrite !length_mult_coefficients;simpl;lia.
    intros.
    rewrite !mult_polyf_convolution.
    destruct n.
    unfold convolution_coeff.
    simpl.
    ring.
    rewrite (convolution_coeff_sym  (a0 :: a)).
    rewrite !convolution_coeff_cons.
    rewrite convolution_coeff_sym;ring.
  Qed.

  Lemma sum_poly_assoc a b c : sum_polyf (sum_polyf a b) c == sum_polyf a (sum_polyf b c).
  Proof.
    apply (nth_ext_A _ _ 0 0).
    rewrite !length_sum_coefficients;simpl;lia.
    intros.
    rewrite !sum_coefficient_nth;ring.
  Qed.

  Lemma sum_poly_sym a b : sum_polyf a b == sum_polyf b a.
  Proof.
    apply (nth_ext_A _ _ 0 0).
    rewrite !length_sum_coefficients;simpl;lia.
    intros.
    rewrite !sum_coefficient_nth;ring.
  Qed.


  Lemma poly_product_rule a b :  derive_poly (mult_polyf a b) == sum_polyf (mult_polyf a (derive_poly b)) (mult_polyf b (derive_poly a)).
  Proof.
    revert b.
    induction a.
    - intros;simpl.
      unfold derive_poly.
      simpl.
      rewrite mult_polyf_nil1;auto.
    - intros;destruct a0.
      rewrite poly_scalar_mult_deriv, derive_const, mult_polyf_nil1,sum_poly0;auto;reflexivity.
      destruct b.
      rewrite  derive_nil,mult_polyf_nil1, mult_polyf_nil2, derive_nil, sum_poly0;auto;reflexivity.
      destruct b.
      {
        rewrite mult_poly_sym, derive_const.
        rewrite poly_scalar_mult_deriv, mult_polyf_nil1, sum_poly_sym, sum_poly0;auto;reflexivity.
      }
      destruct a0.
      {
        remember (r0 :: r1 :: b) as p1.
        rewrite derive_poly_cons.
        rewrite derive_const.
        apply (nth_ext_A _ _ 0 0).
        rewrite Heqp1.
        unfold mult_polyf.
        rewrite derive_poly_length, length_sum_coefficients, !length_mult_coefficients.
        unfold sum_polyf.
        destruct (derive_poly (r0 :: r1 :: b)) eqn:E.
        apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia.
        rewrite <-E; clear E.
        remember mult_coefficients as f.
        simpl.
        rewrite Heqf.
        rewrite !length_mult_coefficients, derive_poly_length;simpl.
        destruct (length b + 1)%nat eqn:e; simpl; try lia.
        intros.
        rewrite derive_poly_nth, sum_coefficient_nth, !mult_polyf_convolution,<-!mult_coefficients_convolution.
        rewrite ntimes_proper; [|apply nth_proper_list;apply mult_coefficient_cons';rewrite Heqp1;discriminate].
        rewrite (nth_proper_list n);[|apply mult_coefficient_cons';try (rewrite Heqp1;rewrite <-length_zero_iff_nil; rewrite derive_poly_length;simpl;lia )].

        rewrite !sum_coefficient_nth.
        assert ( nth n (mult_coefficients p1 (sum_polyf [r] [0])) 0
 ==  nth n (mult_coefficients (sum_polyf [r] [0]) p1) 0) as -> by (rewrite nth_proper_list; try apply mult_coefficients_sym;ring).
        simpl.
        rewrite !mult_coefficients_single.
        rewrite !derive_poly_nth.
        destruct n;simpl;try ring.
        rewrite mult_coefficients_single.
        rewrite !derive_poly_nth.
        simpl.
        rewrite !ntimes_plus, !ntimes_mult.
        ring.
      }
      remember (r1 :: b) as b1.
      remember (r2 :: a0) as a1.
      rewrite mult_poly_cons.
      rewrite poly_sum_rule.
      rewrite sum_coefficients_proper; [|apply poly_scalar_mult_deriv | reflexivity].
      rewrite mult_polyf_shift_switch.
      rewrite IHa.
            pose proof (mult_poly_cons a (r :: a1)).

      rewrite (sum_poly1_proper (mult_polyf (r0::b1) _ )); try apply H.

      rewrite sum_poly_assoc.
      apply sum_coefficients_proper; try reflexivity.
      rewrite (derive_poly_const_independent a).
      rewrite sum_poly1_proper; [| apply mult_poly2_proper;try apply derive_poly_cons].
      rewrite (sum_poly2_proper (mult_polyf (0 :: r :: a1) _)); [| apply mult_poly2_proper;try apply derive_poly_cons].
      rewrite sum_poly1_proper; [| apply mult_poly_distr].
      rewrite !mult_poly_distr.
      rewrite <-(sum_poly_assoc (mult_polyf (0 :: _) _)).
      rewrite (sum_poly1_proper (mult_polyf (r0 :: b1) _));try apply (sum_poly_sym _ (mult_polyf (r0 :: b1) (r :: a1))).
      rewrite !sum_poly_assoc.
      apply sum_coefficients_proper.
      rewrite mult_poly_sym;reflexivity.
      rewrite Heqb1.
      apply sum_coefficients_proper.
      destruct (derive_poly (r0 :: r1 :: b)) eqn:E.
      apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia.
      clear E.
      rewrite <-mult_polyf_shift_switch;reflexivity.
      rewrite Heqa1.
      destruct (derive_poly (r :: r2 :: a0)) eqn:E.
      apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia.
      rewrite mult_polyf_shift_switch;reflexivity.
  Qed.

  Lemma differentialRingPoly : @differentialRing _ _ (poly_comSemiRing).
  Proof.
    exists (derive_poly);intros; [apply poly_sum_rule|].
    simpl (_ + _).
    rewrite sum_poly_sym.
    apply poly_product_rule.
  Defined.
End DifferentialRing.
