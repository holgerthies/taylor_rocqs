Require Import Psatz.
Require Import ZArith.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import algebra.
Require Import functions.
Require Import List.
Require Import tuple.
Require Import combinatorics.
Import ListNotations.
 #[global] Instance list_A_setoid {A} {A_setoid : Setoid A} : Setoid (list A).
 Proof.
   exists  (eqlistA SetoidClass.equiv).
   apply eqlistA_equiv.
   apply setoid_equiv.
 Defined.

 Section RawPolynomial.
  Context `{A_rawRing : RawRing}.

  Definition poly := list A.
  
  Fixpoint eval_poly (a : poly) (x : A) :=
    match a with
    | nil => 0
    | h :: t => h + x * (eval_poly t x)  
    end.

  Definition sum_polyf  : poly -> poly -> poly.
  Proof.
    intros p1.
    induction p1 as [|a0 p1' S]; intros p2.
    apply p2.
    destruct p2 as [|b0 p2'].
    apply (a0 :: p1').
    apply ((a0 + b0) :: (S p2')).
  Defined.

 Fixpoint convolution_coeff_rec (a b : list A) n i :=
   nth (n-i)%nat a 0 * nth i b 0 + match i with
     | 0 => 0
     | S i' => convolution_coeff_rec a b n i'
    end.
 Definition convolution_coeff (a b : list A) n := convolution_coeff_rec a b n n.
 Fixpoint mult_coefficients_rec (a b : list A) n :=
   match n with
    | 0 => nil 
    | S n' =>  convolution_coeff a b ((length a + length b - 1) - n)%nat :: mult_coefficients_rec a b n'
     end.

 Definition mult_coefficients a b := mult_coefficients_rec a b (length a + length b - 1).
 Definition mult_polyf a b := match (a,b) with
                                      | (nil, _) =>nil 
                                      | (_, nil) =>nil 
                                      |  (_, _) => mult_coefficients a b end.
  #[global] Instance poly_rawRing: RawRing (A := poly).
  Proof.
    constructor.
    apply []. apply [1]. apply (sum_polyf). apply (mult_polyf).
  Defined.
  End RawPolynomial.
  Section Polynomial.
  Context `{A_semiRing : SemiRing}.



  Add Ring ARing: ComSemiRingTheory.


  Fixpoint eval_poly_rec (a : poly) (x : A) (n : nat) :=
    match n with
    | 0 => 0
    | (S n') => last a 0  * (npow x n') + eval_poly_rec (removelast a) x n'
    end.

  Definition eval_poly2 a x := eval_poly_rec a x (length a).

  Lemma eval_poly2_app1 a an x : eval_poly2 (a ++ cons an nil) x = an * (npow x (length a)) + eval_poly2 a x.
  Proof.
    unfold eval_poly2 at 1.
    replace (length (a ++ cons an nil)) with (S (length a)) by (rewrite app_length;simpl;lia).
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
  replace (a ++ b0 :: b) with ((a ++ cons b0 nil) ++ b) by (rewrite <-app_assoc;auto).
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
  replace (b0 :: b) with ((cons b0 nil )++b) by auto.
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
    replace (a0 :: a) with (cons a0 nil ++a) by auto.
    rewrite eval_poly2_app.
    simpl.
    rewrite IHa.
    unfold eval_poly2.
    simpl;ring.
  Qed.

 Lemma smul_poly lambda p1: {p2 | forall x, eval_poly p2 x == lambda * eval_poly p1 x}.
 Proof.
   induction p1 as [| a0 p1' IH]; [exists []; intros;simpl;ring |].
   destruct IH as [p2' H0].
   exists ((lambda * a0) :: p2' ).
   intros.
   simpl.
   setoid_replace (lambda * (a0 + x*eval_poly p1' x)) with (lambda*a0 + x * (lambda * eval_poly p1' x)) by ring.
   rewrite H0;auto.
   ring.
 Defined.


  Lemma sum_polyf_spec p1 p2 x: eval_poly (sum_polyf p1 p2) x == eval_poly p1 x + eval_poly p2 x.
  Proof.
    revert p2.
    induction p1 as [| a0 p1'];intros; [simpl;ring|].
     destruct p2 as [| b0 p2'];[simpl;ring|].
     simpl.
     assert (forall y z u, y == z + u -> a0 + b0 + y == a0+z+(b0+u)) by (intros;rewrite H0;ring).
     apply H0.
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
   

 Definition mult_coefficients_rec_spec a b n m : (n < m)%nat -> nth n (mult_coefficients_rec a b m) 0 == convolution_coeff a b (length a + length b - 1  + n - m)%nat .
 Proof.
   revert n.
   induction m; intros; try lia.
   destruct n; simpl;try rewrite Nat.add_0_r;auto;try ring.
   rewrite IHm;try lia.
   assert (length a + length b - 1 + S n - S m = length a + length b - 1 + n - m)%nat as -> by lia.
   auto;ring.
 Qed.


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
 Lemma convolution_coeff_rec_nil b i j : convolution_coeff_rec nil b j i == 0.
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
 Lemma mult_coefficients_single a0 b n : nth n (mult_coefficients (cons a0 nil) b) 0 == a0 * (nth n b 0).
 Proof.
   destruct (Nat.le_gt_cases (n+1) ((length b))%nat).
   - rewrite mult_coefficients_spec; simpl;try rewrite Nat.sub_0_r;try lia.
     destruct n;unfold convolution_coeff;simpl.
     ring.
     rewrite Nat.sub_diag.
     rewrite convolution_coeff_rec_cons; try lia.
     rewrite convolution_coeff_rec_nil.
     ring.
   - assert (length (mult_coefficients (cons a0 nil) b) <= n)%nat.
    {
     rewrite length_mult_coefficients.
     simpl.
     lia.
    }
    rewrite !nth_overflow;try ring;try lia;auto.
 Qed.
 Lemma nth_ext_A_iff l1 l2 d1 d2 : (l1 == l2) <-> (length l1 = length l2 /\ forall n, n < length l1 -> nth n l1 d1 == nth n l2 d2).
 Proof.
   intros.
   split;intros;[split|].
   - apply (@eqlistA_length A SetoidClass.equiv);auto.
   - intros.
     generalize dependent n.
     induction H0.
     intros.
     simpl in H1;lia.
     destruct n.
     simpl;auto.
     intros.
     simpl.
     apply IHeqlistA.
     simpl in H2;lia.
  - destruct H0.
    generalize dependent l1.
    induction l2;intros.
    + simpl in H0.
      apply length_zero_iff_nil in H0.
      rewrite H0.
      reflexivity.
    + destruct l1.
      simpl in H0.
      lia.
      apply eqlistA_cons.
      specialize (H1 0%nat).
      simpl in H1.
      apply H1;lia.
      apply IHl2.
      simpl in H0;lia.
      intros.
      specialize (H1 (S n)).
      simpl in H1.
      apply H1.
      lia.
  Qed.
 Lemma nth_ext_A l1 l2 d1 d2 : length l1 = length l2 -> (forall n, n < length l1 -> nth n l1 d1 == nth n l2 d2) -> l1 == l2.
 Proof.
   intros.
   rewrite (nth_ext_A_iff _ _ d1 d2).
   split;auto.
 Qed.

 #[global] Instance nth_proper : forall n l, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun (d :A) => nth n l d)).
 Proof.
   intros.
   intros x y H0.
   destruct (Nat.lt_ge_cases n (length l) ).
   rewrite (nth_indep _ _ y);auto;reflexivity.
   rewrite !nth_overflow;auto.
 Defined.

 Lemma mult_coefficients_single_list a0 b : mult_coefficients (cons a0 nil) b == map (fun x => a0 * x) b.
 Proof.
   apply (nth_ext_A _ _ 0 0).
   - rewrite length_mult_coefficients, map_length.
     simpl; lia.
  - intros.
    rewrite mult_coefficients_single.

    assert (0 == ((fun x => a0 * x) 0)) as R by ring.
    pose proof (nth_proper n (map (fun x => a0 * x) b) _ _ R).
    simpl in H1.
    rewrite H1.
    rewrite map_nth.
    reflexivity.
 Qed.
 Lemma nil_equiv a : a == nil -> a = nil.
 Proof.
   intros.
   apply length_zero_iff_nil.
   apply eqlistA_length in H0;auto.
 Qed.

  Lemma eqlistA_destruct a0 a b0 b: a0 :: a == b0 :: b -> a0 == b0 /\ a == b.  
  Proof.
   intros.
   apply eqlistA_altdef in H0.
   apply Forall2_cons_iff in H0.
   destruct H0.
   split;auto.
   apply eqlistA_altdef;auto.
 Qed.

 #[global] Instance eval_proper : forall x, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun l => eval_poly l x)).
 Proof.
   intros.
   intros a b H0.
   generalize dependent a.
   induction b;intros.
   - apply nil_equiv in H0.
     rewrite H0.
     simpl;reflexivity.
   -  destruct a0.
      symmetry in H0.
      apply nil_equiv in H0.
      discriminate H0.
      simpl.
      destruct (eqlistA_destruct _ _ _ _ H0).
      rewrite IHb;auto.
      rewrite H1;ring.
 Qed.

 Lemma mult_coefficients_eval_single a0 b x : eval_poly (mult_coefficients (cons  a0 nil) b) x == a0 * eval_poly b x.
 Proof.
   pose proof (eval_proper x). 
   rewrite H0;[|apply mult_coefficients_single_list].
   induction b;simpl;try ring.
   rewrite IHb.
   ring.
 Qed.

 Lemma mult_coefficients_nil b n : nth n (mult_coefficients nil b) 0 == 0.
 Proof.
   destruct (Nat.le_gt_cases (n+1) ((length b-1))%nat).
   - rewrite mult_coefficients_spec; simpl; try lia.
     unfold convolution_coeff.
     apply convolution_coeff_rec_nil.
  - rewrite nth_overflow;auto;try ring.
    rewrite length_mult_coefficients.
    simpl;lia.
 Qed.

 Lemma mult_coefficients_nil_list b : mult_coefficients nil b == repeat 0 (length b - 1)%nat.
 Proof.
    apply (nth_ext_A _ _ 0 0).
    rewrite length_mult_coefficients, repeat_length.
    simpl;lia.
    intros.
    rewrite mult_coefficients_nil, nth_repeat;auto;reflexivity.
 Qed.

 Lemma mult_coefficients_eval_nil b x : eval_poly (mult_coefficients nil b) x == 0.
 Proof.
    pose proof (eval_proper x). 
    rewrite H0; try apply mult_coefficients_nil_list.
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
   simpl in H0.
   destruct n; try ring.
   - assert (b = nil) as -> by (apply length_zero_iff_nil;lia).
     unfold convolution_coeff.
     simpl;ring.
   - rewrite convolution_coeff_cons.
     rewrite IHa; simpl in H0;try lia.
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
   rewrite length_mult_coefficients in H0.
   rewrite !mult_coefficients_spec; try lia.
   apply convolution_coeff_sym.
  Qed.

 #[global] Instance nth_proper_list : forall n d, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun l => nth n l d)).
 Proof.
   intros.
   intros a b H0.
   destruct (Nat.lt_ge_cases n (length a)).
   apply nth_ext_A_iff;auto.
   rewrite !nth_overflow;try reflexivity;auto.
   rewrite <-(eqlistA_length H0);auto.
 Qed.
 Lemma mult_coefficients_cons a b a0 b0 : mult_coefficients (a0 :: a) (b0 :: b) == sum_polyf (mult_coefficients [a0] (b0 :: b)) (0 :: mult_coefficients a (b0 :: b)).
 Proof.
   apply (nth_ext_A _ _ 0 0).
   - rewrite length_sum_coefficients.
     rewrite !length_mult_coefficients;simpl.
     rewrite length_mult_coefficients;simpl.
     rewrite max_r;try lia.
   - intros.
     rewrite length_mult_coefficients in H0.
     simpl in H0.
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


 
 Lemma monomial_poly a n : {p : poly | forall x, eval_poly p x == a * npow x n}.
 Proof.
   exists ((repeat 0 n) ++ [a]).
   intros.
   induction n; [simpl; ring|].
   simpl.
   rewrite IHn.
   ring.
 Defined.


 Lemma derive_monomial (a : A) (n : nat) : (poly (A:=A)).
 Proof.
   destruct n; [apply []|].
   destruct (monomial_poly (ntimes (S n) a) n) as [p P].
   apply p.
 Defined.

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
    + destruct H0; [simpl;rewrite nth_middle, P1, nth_middle;ring|].
      simpl.
      rewrite !nth_overflow; try rewrite ntimes_zero; try ring; rewrite app_length;simpl; lia.
 Defined.

 Definition derive_poly p := (proj1_sig  (poly_deriv_exists p)).

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
    destruct b;intros;[contradict H0;auto |].
    apply mult_coefficients_cons.
  Qed.

  Lemma mult_polyf_spec a b x: eval_poly (mult_polyf a b) x == (eval_poly a x) * (eval_poly b x). 
  Proof.
    destruct a; destruct b;try (simpl;ring).
    unfold mult_polyf.
    apply mult_coeff_spec.
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
    rewrite length_mult_coefficients, length_sum_coefficients in H0.
    rewrite !mult_coefficients_convolution.
    clear H0.
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
 #[global] Instance convolution_coeff_proper : forall n, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun a b => convolution_coeff a b n)).
 Proof.
   intros n.
   induction n.
   intros a b P x y H0.
   destruct a;destruct b;destruct x; destruct y;unfold mult_polyf;try reflexivity; try (apply eqlistA_length in P;contradict P;simpl;lia); try (apply eqlistA_length in H0;contradict H0;simpl;lia).
   unfold convolution_coeff;rewrite !convolution_coeff_rec_nil;reflexivity.
   unfold convolution_coeff;rewrite !convolution_coeff_rec_nil2;reflexivity.
   destruct (eqlistA_destruct _ _ _ _ P).
   destruct (eqlistA_destruct _ _ _ _ H0).
   unfold convolution_coeff;simpl.
   rewrite H1, H3.
   ring.
   intros a b P x y H0.
   destruct a; destruct b;try (apply eqlistA_length in P;contradict P;simpl;lia).
   unfold convolution_coeff;rewrite !convolution_coeff_rec_nil;reflexivity.
   rewrite !convolution_coeff_cons.
   destruct (eqlistA_destruct _ _ _ _ P).
   rewrite IHn; try apply H2; try apply H0.
   rewrite H1.
   rewrite nth_proper_list; try apply H0.
   reflexivity.
 Qed.
 Instance mult_coefficients_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) mult_coefficients).
 Proof.
   intros a b P x y H0.
   apply (nth_ext_A _ _ 0 0).
   - apply eqlistA_length in P.
     apply eqlistA_length in H0.
     rewrite !length_mult_coefficients;lia.
   - intros.
     rewrite !mult_coefficients_convolution.
     apply convolution_coeff_proper;auto.
 Qed.

 #[global] Instance mult_poly_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) mult_polyf).
 Proof.
   intros a b P x y H0.
   destruct a;destruct b;destruct x; destruct y;unfold mult_polyf;try reflexivity; try (apply eqlistA_length in P;contradict P;simpl;lia); try (apply eqlistA_length in H0;contradict H0;simpl;lia).
   apply mult_coefficients_proper;auto.
 Qed.
 #[global] Instance sum_coefficients_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) sum_polyf).
 Proof.
   intros a b P x y H0.
   apply (nth_ext_A _ _ 0 0).
   - apply eqlistA_length in P.
     apply eqlistA_length in H0.
     rewrite !length_sum_coefficients;lia.
   - intros.
     rewrite !sum_coefficient_nth.
     rewrite nth_proper_list;try apply P.
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
      clear H0.
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


  #[global] Instance poly_SemiRing : SemiRing (A := poly).
  Proof.

  constructor;intros; try (simpl;apply (nth_ext_A _ _ 0 0);[intros;rewrite !length_sum_coefficients;simpl;lia|intros;rewrite !sum_coefficient_nth;destruct n; simpl;ring]); try (simpl;reflexivity).
     apply sum_coefficients_proper.
    apply mult_poly_proper.
    apply mult_poly_assoc.
    apply mult_poly_sym.
    unfold mult_polyf;destruct a;auto;try reflexivity.
    apply mult_poly1.
    apply mult_poly_distr.
 Defined.

  Lemma shift_poly p1 (c : A) : {p2 | forall x, eval_poly p2 x == eval_poly p1 (x + c)}.
  Proof.
    induction p1 as [| a0 p1' IH]; [exists []; intros; simpl; try ring | ].
    destruct IH as [p2 IH].
    destruct (mult_poly [c; 1] p2) as [q Q].
    destruct (sum_poly [a0] q) as [q' Q'].
    exists q'.
    intros.
    rewrite Q', Q, IH.
    simpl.
    ring.
 Qed.
   
End Polynomial.

Section MultiRawPoly.
  Context `{R_rawRing : RawRing }.
  Fixpoint mpoly n :=
    match n with
    | 0 => A
    | (S n) => @poly (mpoly n)
    end.

  #[global] Instance mpoly_setoid n : Setoid (mpoly n).
  Proof.
    intros.
    induction n.
    apply H.
    apply list_A_setoid.
  Defined.

  #[global] Instance mpoly_rawRing n: RawRing (A := (mpoly n)).
  Proof.
    induction n.
    apply R_rawRing.
    apply poly_rawRing.
  Defined.

  Fixpoint const_to_mpoly n x : (mpoly n) := 
    match n with
    | 0 => x
    | (S n) => [const_to_mpoly n x]
   end.
  Definition eval_mpoly {n} (p : mpoly (S n)) x := eval_poly p (const_to_mpoly n x).
  End MultiRawPoly.

  Section MultiPoly.
  Context `{R_semiRing : SemiRing}.
  #[global] Instance mpoly_SemiRing n:  SemiRing (A := (mpoly n)).
  Proof.
    intros.
    induction n.
    apply R_semiRing.
    apply poly_SemiRing.
  Defined.

End MultiPoly.
Section Composition.

  Context `{R_semiRing : SemiRing }.

  Definition to_poly_poly (p : @poly A) : (@poly (@poly A)).
  Proof.
    induction p.
    apply [].
    apply ([a] :: IHp).
  Defined.
  Instance poly_setoid : Setoid (@poly A).
  Proof. apply list_A_setoid. Defined.
  Instance ppoly_setoid : Setoid (@poly (@poly A)).
  Proof. apply list_A_setoid. Defined.


  Definition composition (p1 p2 : @poly A) : @poly A.
  Proof.
    pose proof (to_poly_poly p1).
    apply (eval_poly X p2).
 Defined.

End Composition.  

 Notation "p .{ x }" := (eval_mpoly  p x) (at level 3, left associativity).

Definition eval_tuple {R} `{R_rawRing : RawRing (A:=R)} {n} (p : @mpoly R n) (t : @tuple n R) : R. 
Proof.
   induction n.
   apply p.
   destruct (destruct_tuple t) as [hd [tl P]].
   pose proof (p.{hd}) as p0.
   apply (IHn p0 tl).
Defined.

 Notation "p .[ x ]" := (eval_tuple  p x) (at level 3, left associativity).

Section MultiPolyComposition.
  Context `{R_semiRing : SemiRing }.
  Definition to_mmpoly {n} m (p : @mpoly A n) : (@mpoly (@mpoly A m ) n).
  Proof.
    induction n.
    apply (const_to_mpoly m p).
    simpl in p.
    induction p.
    apply [].
    apply ((IHn a) :: IHp).
  Defined.

  Definition mpoly_composition {n m} (p : @mpoly A n) (qs : @tuple n (@mpoly A m)) : (@mpoly A m).
  Proof.
    pose proof (to_mmpoly m p).
    apply (eval_tuple (n:=n) X qs).
  Defined.


  Definition eval_tuple_rec {n m} (ps : @tuple n (@mpoly A m)) (xs : @tuple m A) : @tuple n A.
  Proof.
    induction n.
    exists [];simpl;reflexivity.
    destruct (destruct_tuple_cons ps) as [hd [tl P]].
    specialize (IHn tl).
    apply (tuple_cons (eval_tuple hd xs) IHn).
  Defined.

  Add Ring RRing: ComSemiRingTheory.

  #[global] Instance pmeval_proper n t : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun p => eval_tuple (n := n) p t)).
  Proof.
    intros a b H0.
    induction n; simpl;auto.
    destruct (destruct_tuple t) as [x0 [tl P]].
    apply IHn.
    apply eval_proper;auto.
  Defined.
  #[global] Instance pmeval_proper2 n : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (eval_tuple (n := n))).
  Proof.
  Admitted.
  Lemma const_to_mpoly_spec n p x0 : (eval_poly p (const_to_mpoly n x0)) == p.{x0}.
  Proof.
    induction n;simpl;reflexivity.
  Defined.

  Lemma mpoly_add_spec {n} (p1 p2 : (@mpoly A n)) x : (p1 + p2).[x] == p1.[x]+p2.[x].
  Proof.
    revert x.
    induction n;intros;simpl; try ring.
    destruct (destruct_tuple x) as [x0 [tl P]].
    unfold eval_mpoly at 1.
    rewrite pmeval_proper; try apply sum_polyf_spec.
    rewrite IHn.
    simpl.
    apply add_proper;rewrite pmeval_proper;try apply const_to_mpoly_spec;reflexivity.
  Qed.

  Lemma mpoly_mul_spec {n} (p1 p2 : (@mpoly A n)) x : (p1 * p2).[x] == p1.[x]*p2.[x].
  Proof.
    revert x.
    induction n;intros;simpl; try ring.
    destruct (destruct_tuple x) as [x0 [tl P]].
    rewrite pmeval_proper; try apply mult_polyf_spec.
    rewrite IHn.
    simpl.
    apply mul_proper;rewrite pmeval_proper;try apply const_to_mpoly_spec;reflexivity.
  Qed.


  Lemma zero_poly_eval {n} (x : @tuple n A)  : 0.[x] == 0.
  Proof.
    revert x.
    induction n;intros;simpl; try ring.
    destruct (destruct_tuple x) as [x0 [tl P]].
    rewrite IHn;ring.
  Qed.

  Lemma const_to_mpoly_eval (n :nat) (a : A) x : (const_to_mpoly n a).[x] == a.
  Proof.
    revert a x.
    induction n;intros;simpl;try ring.
    destruct (destruct_tuple x) as [x0 [tl P]].
    unfold eval_mpoly.
    simpl.
    rewrite mpoly_add_spec.
    rewrite mpoly_mul_spec.
    rewrite !IHn.
    rewrite zero_poly_eval;ring.
  Qed.

  Lemma proj1_sig_tuple_cons {R n} (a : R) (x : @tuple n R): proj1_sig (tuple_cons a x) = a :: proj1_sig x.
  Proof.
    destruct x.
    simpl;auto.
  Qed.

  Lemma mpoly_composition_spec {n m} (p : @mpoly A n) (qs : @tuple n (@mpoly A m)) xs : eval_tuple (mpoly_composition p qs) xs == eval_tuple p (eval_tuple_rec qs xs). 
  Proof.
  induction n.
  - simpl.
    simpl in p.
    unfold mpoly_composition, to_mmpoly.
    simpl.
    rewrite const_to_mpoly_eval;ring.
  - 
    + 
      simpl.
      destruct (destruct_tuple qs) as [q0 [qt P]] eqn:E.

  Admitted.

End MultiPolyComposition.



(* Infix "\o" := mpoly_composition (at level 2). *)
Section DifferentialRing.
  Context `{R_semiRing : SemiRing }.

  Add Ring RRing: ComSemiRingTheory.
  Add Ring PRing: (ComSemiRingTheory (A := @poly A)).

  Lemma derive_poly_length (a : (@poly A)) : length (derive_poly a) = (length a - 1)%nat.
  Proof.
    unfold derive_poly; simpl.
    destruct (poly_deriv_exists a);simpl.
    lia.
  Qed.
  Lemma derive_poly_nth (a : @poly A) (n : nat) : nth n (derive_poly a) 0  == ntimes (S n) (nth (S n) a 0).
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
  #[global] Instance cons_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun a0 a => a0 :: a)). 
  Proof.
    intros a b H0 a0 b0 H1.
    apply eqlistA_cons;auto.
  Defined.
  #[global] Instance sum_poly2_proper a : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (sum_polyf a)).
  Proof.
    apply sum_coefficients_proper.
    reflexivity.
  Defined.
  #[global] Instance sum_poly1_proper a : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (fun b => sum_polyf b a)).
  Proof.
    intros b b' H0.
    apply sum_coefficients_proper.
    apply H0.
    reflexivity.
  Defined.
  #[global] Instance mult_poly2_proper a : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) (mult_polyf a)).
  Proof.
    apply mult_poly_proper.
    reflexivity.
  Defined.

 #[global] Instance convolution_coeff_proper2 n a:  (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun b => convolution_coeff a b n)).
 Proof.
   apply convolution_coeff_proper;reflexivity.
 Defined.
 #[global] Instance mult_coefficients2_proper a : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (mult_coefficients a)).
 Proof.
   apply mult_coefficients_proper.
   reflexivity.
  Defined.

  Lemma mult_poly_cons a0 (a b : poly) : mult_polyf (a0 :: a) b == sum_polyf (mult_polyf [a0] b) (mult_polyf (0 :: a) b).

  Proof.
     rewrite !(mult_poly_sym _ b).
     (* rewrite sum_coefficients_proper; try apply (mult_poly_sym _ b). *)
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

  #[global] Instance derive_poly_proper : (Proper (SetoidClass.equiv ==> SetoidClass.equiv) derive_poly).
  Proof.
    intros a b H0.
    apply (nth_ext_A _ _ 0 0).
    rewrite !derive_poly_length.
    apply eqlistA_length in H0.
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
    destruct (derive_poly (a0 :: a1 :: b)) eqn:E.
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
    rewrite ntimes_plus, ntimes_zero, ntimes_mult.
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
    induction a as [|a0 a].
    - intros;simpl.
      unfold derive_poly.
      simpl.
      rewrite mult_polyf_nil1;auto.
    - intros;destruct a as [| r a].
      rewrite poly_scalar_mult_deriv, derive_const, mult_polyf_nil1,sum_poly0;auto;reflexivity.
      destruct b as [|r0 b].
      rewrite  derive_nil,mult_polyf_nil1, mult_polyf_nil2, derive_nil, sum_poly0;auto;reflexivity.
      destruct b as [|r1 b].
      {
        rewrite mult_poly_sym, derive_const.
        rewrite poly_scalar_mult_deriv, mult_polyf_nil1, sum_poly_sym, sum_poly0;auto;reflexivity.
      }
      destruct a as [| a1 a].
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
      remember (a1:: a) as a1'.
      rewrite mult_poly_cons.
      rewrite poly_sum_rule.
      rewrite sum_coefficients_proper; [|apply poly_scalar_mult_deriv | reflexivity].
      rewrite mult_polyf_shift_switch.
      rewrite IHa.
            pose proof (mult_poly_cons a0 (r :: a1')).

      rewrite (sum_poly1_proper (mult_polyf (r0::b1) _ )); try apply H0.

      rewrite sum_poly_assoc.
      apply sum_coefficients_proper; try reflexivity.
      rewrite (derive_poly_const_independent a0).
      rewrite sum_poly1_proper; [| apply mult_poly2_proper;try apply derive_poly_cons].
      rewrite (sum_poly2_proper (mult_polyf (0 :: r :: a1') _)); [| apply mult_poly2_proper;try apply derive_poly_cons].
      rewrite sum_poly1_proper; [| apply mult_poly_distr].
      rewrite !mult_poly_distr.
      rewrite <-(sum_poly_assoc (mult_polyf (0 :: _) _)).
      rewrite (sum_poly1_proper (mult_polyf (r0 :: b1) _));try apply (sum_poly_sym _ (mult_polyf (r0 :: b1) (r :: a1'))).
      rewrite !sum_poly_assoc.
      apply sum_coefficients_proper.
      rewrite mult_poly_sym;reflexivity.
      rewrite Heqb1.
      apply sum_coefficients_proper.
      destruct (derive_poly (r0 :: r1 :: b)) eqn:E.
      apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia.
      clear E.
      rewrite <-mult_polyf_shift_switch;reflexivity.
      rewrite Heqa1'.
      destruct (derive_poly (r :: a1 :: a)) eqn:E.
      apply length_zero_iff_nil in E; rewrite derive_poly_length in E;simpl in E;lia.
      rewrite mult_polyf_shift_switch;reflexivity.
  Qed.

(*   #[global] Instance differentialRingPoly : differentialRing (A := poly). *)
(*   Proof. *)
(*     exists (derive_poly);intros; [apply poly_sum_rule| |]. *)
(*     simpl (_ + _). *)
(*     rewrite sum_poly_sym. *)
(*     apply poly_product_rule. *)
(*     apply derive_poly_proper. *)
(*   Defined. *)
 End DifferentialRing.

Section PartialDiffAlgebra.

  Context `{SemiRing}.
  Add Ring ARing: ComSemiRingTheory.
  Definition poly_pdiff {n} (d : nat) (p : (@mpoly A n )) : (@mpoly A n).
  Proof.
    generalize dependent n.
    induction d;intros.
    destruct n.
    simpl.
    apply 0.
    apply (derive_poly p).
    destruct n.
    apply 0.
    apply (map (IHd n) p).
 Defined.

  Lemma poly_pdiff0  n d : @poly_pdiff n d 0 = 0.
  Proof.
    induction d;destruct n;simpl;try ring;auto.
  Qed.

  #[global] Instance mpoly_pdiff_proper : forall n d, Proper (SetoidClass.equiv ==> SetoidClass.equiv)  (@poly_pdiff n d).
  Proof.
    intros.
    intros a b H'.
    induction d;destruct n;try (simpl;ring).
    rewrite H';reflexivity.
    apply (nth_ext_A _ _ 0 0).
    unfold poly_pdiff.
    simpl.
    rewrite !map_length.
 Admitted.
  Lemma poly_pdiff_mult m : forall (p : (mpoly m)) q n, poly_pdiff n (p * q) == q * poly_pdiff n p + p * poly_pdiff n q.
  Admitted.                                                                    
  Lemma poly_pdiff_switch d : forall (p : (mpoly d)) m n, poly_pdiff n (poly_pdiff m p) == poly_pdiff m (poly_pdiff n p).
  Admitted.                                                                    

  #[global] Instance mpoly_pdiffring n : PartialDifferentialRing (A := (mpoly n)).
  Proof.
    exists poly_pdiff.
    - intros.
      revert n r1 r2.
      induction d;intros; destruct n;try (simpl;ring).
      apply poly_sum_rule.
      apply (nth_ext_A _ _ 0 0).
      simpl.
      rewrite map_length,!length_sum_coefficients, !map_length;auto.
      intros.
      rewrite (nth_indep _ _ (poly_pdiff d zero));auto.
      simpl.
      rewrite !map_nth.
      rewrite !sum_coefficient_nth.
      assert (forall r, nth n0 (map (@poly_pdiff n d) r) 0 = poly_pdiff d (nth n0 r 0)).
      {
        intros.
        replace 0 with (@poly_pdiff n d 0) by apply poly_pdiff0.
        rewrite map_nth.
        rewrite poly_pdiff0;auto.
      }
      simpl.
      rewrite !H2.
      apply IHd.
  - intros; apply poly_pdiff_mult.
  - intros; apply poly_pdiff_switch.
  - apply mpoly_pdiff_proper.
Defined.

  Definition poly_comp1 {m} (n : nat) : @mpoly A m .
  Proof.
    revert m.
    induction n;intros.
    destruct m.
    apply 0.
    apply [0;1].
    destruct m.
    apply 0.
    apply [IHn m].
 Defined.

  Lemma poly_comp1_composition {m n} (f : @tuple n (mpoly (S m))) (i : nat) : mpoly_composition (poly_comp1 i) f == tuple_nth i f 0.
  Admitted.
  Lemma poly_composition_plus_comp : forall {m n} x y (z :@tuple m (mpoly (S n))) , mpoly_composition (x+y) z == (mpoly_composition x z) + (mpoly_composition y z).
  Admitted.
  Lemma poly_composition_mult_comp : forall {m n} x y (z :@tuple m (mpoly (S n))) , mpoly_composition (x*y) z == (mpoly_composition x z) * (mpoly_composition y z).
  Admitted.

  Lemma poly_id_spec {m} hd (tl : A^m) :   ([0; 1] : mpoly (S m)) .[ tuple_cons hd tl] == hd. 
    simpl.
    destruct (destruct_tuple (tuple_cons hd tl)) as [h0 [t0 P0]].
    unfold eval_mpoly.
    simpl.
    rewrite mul0,add0,mul1,addC,add0.
    rewrite const_to_mpoly_eval.
    rewrite proj1_sig_tuple_cons in P0.
    injection P0; intros _ ->;reflexivity.
  Qed.

  Lemma eval_tuple_emb {m} (p : mpoly m) hd (tl : A^m) : eval_tuple ([p] : mpoly (S m)) (tuple_cons hd tl) == eval_tuple p tl.
  Proof.
    simpl.
    destruct (destruct_tuple (tuple_cons hd tl)) as [h0 [t0 P0]].
    setoid_replace t0 with tl.
    simpl.
    setoid_replace (p + const_to_mpoly m h0 * 0) with p.
    reflexivity.
    rewrite mul0.
    rewrite add0;reflexivity.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    destruct t0; destruct tl.
    simpl in *.
    injection P0.
    intros -> _.
    reflexivity.
  Qed.

  Lemma poly_comp1_eval {m} :forall x n,  (@poly_comp1 m n) .[ x] == tuple_nth n x 0.
  Proof.
    generalize dependent m.
    induction n;intros.
    - simpl;destruct m.
      simpl.
      rewrite tuple_nth_nil;reflexivity.
      destruct (destruct_tuple_cons x) as [hd [tl P]].
      rewrite P.
      rewrite poly_id_spec.
      rewrite tuple_nth_cons_hd;reflexivity.
    - simpl;destruct m.
      simpl.
      rewrite tuple_nth_nil;reflexivity.
   Admitted.
  
  Definition mpoly_comp'  {n m} := mpoly_composition (n := n) (m := (S m)).

  #[global] Instance mpoly_composition_proper {n m}: (Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (mpoly_composition (n := n) (m := m))).
  Admitted.

    Lemma mpoly_pdiff_chain : forall {m n d} (x : mpoly m) (y : @tuple m (mpoly (S n))), pdiff d (mpoly_composition x y) == (sum (fun i => (pdiff d (tuple_nth i y zero)) * mpoly_composition (poly_pdiff i x) y) m).
    Admitted.

      
  #[global] Instance mpoly_comp_diff_algebra : CompositionalDiffAlgebra (A := (@mpoly A) ).
  Proof.
  exists @mpoly_comp' @poly_comp1;unfold mpoly_comp'.
   - intros; apply poly_comp1_composition.
   - intros;apply poly_composition_plus_comp.
   - intros;apply poly_composition_mult_comp.
   - intros;apply mpoly_pdiff_chain.
   - intros;  apply mpoly_composition_proper.
  Defined. 
End PartialDiffAlgebra.
Notation "A {x ^ d }" := (@mpoly A d) (at level 2).
Section Evaluation.
  Context `{A_semiRing : SemiRing}.
  Add Ring ARing: ComSemiRingTheory.
  #[global] Instance poly_eval {n} : HasEvaluation (A := (mpoly n)) (B := A^n) (C:=A).
  Proof.
  exists (fun p x => True) (fun p x H => eval_tuple p x); try (intros;auto).
   - intros a b Heq d e Heq'.
     simpl;split;auto.
   - simpl.
     intros.
     rewrite H0, H1.
     reflexivity.
   - apply zero_poly_eval.
   - simpl.
     apply mpoly_add_spec.
    - simpl.
      apply mpoly_mul_spec.
  Defined.

  Lemma poly_total {n } (p : A{x^n}) (x : A^n) : (in_domain  p x).
  Proof.
    simpl;auto.
  Qed.

  Lemma mpoly_total {n m} (p : A{x^n}^m) (x : A^n) : (in_domain (HasEvaluation := HasMultiEval) p x).
  Proof.
    intros i Hi; simpl;auto.
  Qed.


  (* Lemma shift_mpoly_composer {d} (c : A^(S d))  :  {p | forall x, eval_poly_rec p x == x + c}. *)
  (* Lemma shift_mpoly_composer {d} (c : A^(S d))  :  {p | forall x, eval_tuple_rec p x == (x + c)}. *)
  (* Proof. *)
  (*   induction d.  *)
  (*   exists t([c\_0;1]). *)
  (*   intros. *)
  (*   simpl. *)
  (*   destruct (destruct_tuple_cons x) as [hx [tx Px]]. *)
  (*   destruct (destruct_tuple_cons c) as [hc [tc Pc]]. *)
  (*   destruct (destruct_tuple x) as [h [t X]]. *)
  (*   apply eqlistA_cons;auto. *)
  (*   unfold eval_mpoly. *)
  (*   simpl. *)
  (*   rewrite Pc. *)
  (*   rewrite tuple_nth_cons_hd. *)
  (*   simpl. *)
  (*   rewrite Px in X. *)
  (*   rewrite proj1_sig_tuple_cons in X. *)
  (*   injection X; intros. *)
  (*   rewrite H1;ring. *)
  (*   destruct (destruct_tuple_cons c) as [hd [tl P]]. *)
  (*   destruct (IHd tl) as [p0 P0]. *)
    
  (*   exists [(const_to_mpoly _ c\_i) ; 1]. *)
  (*   intros. *)
  (*   simpl. *)
  (*   unfold eval_mpoly. *)
  (*   setoid_rewrite (vec_plus_spec x c);auto. *)
  (*   simpl. *)
  (*   destruct (destruct_tuple x) as [hd [tl P]]. *)
  (*   rewrite mpoly_add_spec. *)
  (*   rewrite const_to_mpoly_eval. *)
  (*   rewrite addC. *)

  (*   rewrite  *)
  Lemma eval_tuple_rec_spec {n m} (g : A{x^n}^m) x Px : eval_tuple_rec g x == g @ (x;Px).
  Proof.
      Opaque SetoidClass.equiv.
      simpl.
      induction m.
      simpl; reflexivity.
      simpl.
      destruct (destruct_tuple_cons g) as [hd [tl ->]].
      rewrite (IHm tl (mpoly_total _ _)).
      apply tuple_cons_equiv_equiv; try reflexivity.
      apply meval_proper;reflexivity.
  Qed.
  #[global] Instance poly_function : AbstractFunctionSpace (A := mpoly).
  Proof.
     exists const_to_mpoly (fun m c x => (@poly_total m (const_to_mpoly m c ) x)); intros; try reflexivity.
    - intros; simpl;apply const_to_mpoly_eval.
    - simpl.
      apply poly_comp1_eval.
    - intros i Hi;simpl;auto.
    - apply (tuple_nth_ext' _ _ 0 0).
      intros.
      simpl eval.
      rewrite !(evalt_spec _ _ _ _ H0).
      unfold eval, poly_eval, algebra.composition, mpoly_comp_diff_algebra.
      rewrite (tuple_nth_multicomposition i 0 f g);auto.
      unfold eval,poly_eval, algebra.composition, mpoly_comp_diff_algebra.
      unfold mpoly_comp'.
      rewrite mpoly_composition_spec.
      setoid_replace (eval_tuple_rec g x) with (evalt g x Px).
      reflexivity.
      apply eval_tuple_rec_spec.
Defined.

End Evaluation.

Section Bounds.
  Context `{TotallyOrderedField}.
 Context `{normK : (NormedSemiRing A A (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }.

 (* Fixpoint poly_norm {d} (p : A{x^d}) := *)
 (*   match d with *)
 (*     | 0 => 0 *)
 (*   | (S n) => match p with *)
 (*             | nil => 0 *)
 (*             | hd :: tl => poly_norm hd + poly_norm tl *)
 (*             end *)
 (*     end. *)
                     
End Bounds.
