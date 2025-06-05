From Coq Require Import Psatz.
From Coq Require Import ZArith.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import Coq.Lists.SetoidList.
Require Import algebra.
Require Import functions.
From Coq Require Import List.
Require Import tuple.
Require Import combinatorics.
Import ListNotations.
 #[global] Instance list_A_setoid {A} {A_setoid : Setoid A} (d : A) : Setoid (list A).
 Proof.
   exists (fun a b => forall n, nth n a d == nth n b d).
   split.
   intros a n; reflexivity.
   intros a b H0 n.
   rewrite H0.
   reflexivity.
   intros a b c H0 H1 n.
   rewrite H0, H1.
   reflexivity.
 Defined.

 Section RawPolynomial.
  Context `{A_rawRing : RawRing}.

  Definition poly := list A.
  
   #[global] Instance poly_A_setoid  : (Setoid poly) := (list_A_setoid 0).

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

 Lemma poly_deriv_exists (p : poly) : {p' : poly | length p' = (length p - 1)%nat /\ forall n, n < length p' -> nth n p' 0 == ntimes (S n) (nth (S n) p 0) }.
 Proof.
 induction p using poly_rev_ind;[exists [];split;auto; simpl;lia|].
   destruct p.
   - exists [].
     split; auto;simpl;lia.
   - destruct IHp as [p' [P1 P2]].
     simpl in P1.
     rewrite Nat.sub_0_r in P1.
     exists (p' ++ [(ntimes (S (length p))) x]).
     split; [rewrite !length_app, P1;simpl;lia|].
     intros n Hn.
     destruct (Nat.lt_ge_cases n (length p')).
     + rewrite app_nth1;auto.
       rewrite P2;auto.
       simpl.
       rewrite app_nth1;try rewrite <-P1;auto.
       reflexivity.
     + 
       rewrite length_app in Hn.
       simpl in *.
       assert (n = length p') as -> by lia.
       rewrite nth_middle, P1, nth_middle.
       reflexivity.
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
    replace (length (a ++ cons an nil)) with (S (length a)) by (rewrite length_app;simpl;lia).
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
  rewrite length_app.
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
 (* Lemma nth_ext_A_iff l1 l2 d1 d2 : (l1 == l2) <-> (length l1 = length l2 /\ forall n, n < length l1 -> nth n l1 d1 == nth n l2 d2). *)
 (* Proof. *)
 (*   intros. *)
 (*   split;intros;[split|]. *)
 (*   - apply (@eqlistA_length A SetoidClass.equiv);auto. *)
 (*   - intros. *)
 (*     generalize dependent n. *)
 (*     induction H0. *)
 (*     intros. *)
 (*     simpl in H1;lia. *)
 (*     destruct n. *)
 (*     simpl;auto. *)
 (*     intros. *)
 (*     simpl. *)
 (*     apply IHeqlistA. *)
 (*     simpl in H2;lia. *)
 (*  - destruct H0. *)
 (*    generalize dependent l1. *)
 (*    induction l2;intros. *)
 (*    + simpl in H0. *)
 (*      apply length_zero_iff_nil in H0. *)
 (*      rewrite H0. *)
 (*      reflexivity. *)
 (*    + destruct l1. *)
 (*      simpl in H0. *)
 (*      lia. *)
 (*      apply eqlistA_cons. *)
 (*      specialize (H1 0%nat). *)
 (*      simpl in H1. *)
 (*      apply H1;lia. *)
 (*      apply IHl2. *)
 (*      simpl in H0;lia. *)
 (*      intros. *)
 (*      specialize (H1 (S n)). *)
 (*      simpl in H1. *)
 (*      apply H1. *)
 (*      lia. *)
 (*  Qed. *)

 (* (* for compability with old version *) *)
 Lemma nth_ext_A l1 l2 d1 d2 : length l1 = length l2 -> (forall n, n < length l1 -> nth n l1 d1 == nth n l2 d2) -> l1 == l2.
 Proof.
   intros.
   intros n.
   assert (n < length l1 \/ length l1 <= n)%nat by lia.
   destruct H2.
   rewrite (nth_indep _ _ d1);auto.
   rewrite (nth_indep _ 0 d2);try lia.
   apply H1;auto.
   rewrite !nth_overflow;try lia;reflexivity.
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
  
  - intros n.
    rewrite mult_coefficients_single.

    assert (0 == ((fun x => a0 * x) 0)) as R by ring.
    pose proof (nth_proper n (map (fun x => a0 * x) b) _ _ R).
    simpl in H0.
    rewrite H0.
    rewrite map_nth.
    reflexivity.
 Qed.

 Lemma nil_eval a x : a == nil -> eval_poly a x == 0.
 Proof.
   intros.
   induction a.
   simpl.
   reflexivity.
   simpl.
   setoid_replace a with 0.
   rewrite IHa.
   ring.
   intros n.
   specialize (H0 (S n)).
   simpl in H0.
   rewrite H0.
   destruct n;simpl;reflexivity.
   specialize (H0 0).
   simpl in H0.
   apply H0.
Qed.

  Lemma eqlistA_destruct a0 a b0 b: a0 :: a == b0 :: b -> a0 == b0 /\ a == b.  
  Proof.
   intros.
   pose proof (H0 0).
   simpl in H1.
   split;auto.
   intros n.
   specialize (H0 (S n)).
   simpl in H0;auto.
 Qed.

 #[global] Instance eval_proper : forall x, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun l => eval_poly l x)).
 Proof.
   intros.
   intros a b H0.
   generalize dependent a.
   induction b;intros.
   - rewrite nil_eval;auto.
     simpl;reflexivity.
   -  destruct a0.
      symmetry in H0.
      simpl.
      rewrite nil_eval.
      setoid_replace a with 0.
      ring.
      specialize (H0 0).
      simpl in H0;auto.
      intros n.
      specialize (H0 (S n)).
      simpl in H0;auto.
      rewrite H0.
      simpl;destruct n; reflexivity.
      simpl.
      destruct (eqlistA_destruct _ _ _ _ H0).
      rewrite IHb;auto.
      rewrite H1;ring.
 Qed.
 #[global] Instance eval_proper2 : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (eval_poly)).
 Proof.
   intros.
   intros a b H0 c d H1.
   generalize dependent a.
   induction b;intros.
   - rewrite nil_eval;auto.
     simpl;reflexivity.
   -  destruct a0.
      symmetry in H0.
      rewrite nil_eval;auto; try reflexivity.
      rewrite nil_eval;auto;reflexivity.
      simpl.
      destruct (eqlistA_destruct _ _ _ _ H0).
      rewrite IHb;auto.
      rewrite H1.
      rewrite H2.
      ring.
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

 Lemma mult_coefficients_nil_equiv b : (mult_coefficients 0 b) == 0.
 Proof.
   intros n0.
   rewrite mult_coefficients_nil.
   destruct n0; reflexivity.
 Qed.
 Lemma mult_coefficients_nil_list b : mult_coefficients nil b == repeat 0 (length b - 1)%nat.
 Proof.
    intros n.
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

 Lemma mult_coefficients_nil_equiv2 b : (mult_coefficients b 0) == 0.
 Proof.
   rewrite mult_coefficients_sym.
   apply mult_coefficients_nil_equiv.
 Qed.
 #[global] Instance nth_proper_list : forall n, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun l => nth n l 0)).
 Proof.
   intros.
   intros a b H0.
   apply H0.
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
    split; [apply length_firstn|split;[apply length_skipn|]].
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
    destruct a;destruct b;unfold mult_polyf;intros n;destruct n;simpl;try reflexivity.
    apply mult_coefficients_sym.
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

 Lemma convolution_coeff_rec_equiv_nil a b i j : a == [] -> convolution_coeff_rec a b j i == 0.
 Proof.
   intros.
   induction i;intros.
   simpl.
   replace (j-0)%nat with j by lia.
   rewrite (H0 j).
   destruct j; simpl;ring.
   simpl.
   rewrite IHi.
   rewrite (H0 (j - S i)%nat).
   destruct (j - S i)%nat;simpl;ring.
 Qed.    

 Lemma convolution_coeff_rec_equiv_nil2 a b i j : b == [] -> convolution_coeff_rec a b j i == 0.
 Proof.
   intros.
   induction i;intros.
   simpl.
   replace (j-0)%nat with j by lia.
   rewrite (H0 0%nat).
   destruct j; simpl;ring.
   simpl.
   rewrite IHi.
   rewrite (H0 (S i)).
   simpl;ring.
 Qed.    

 #[global] Instance convolution_coeff_proper : forall n, (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun a b => convolution_coeff a b n)).
 Proof.
   intros n.
   induction n.
   - intros a b P x y H0.
     unfold convolution_coeff.
     simpl.
     ring_simplify.
     specialize (P 0).
     specialize (H0 0).
     rewrite P, H0.
     reflexivity.
   - intros a b P x y H0.
     destruct a; destruct b.
      unfold convolution_coeff;rewrite !convolution_coeff_rec_nil;reflexivity.
      unfold convolution_coeff;rewrite !convolution_coeff_rec_nil.
      rewrite convolution_coeff_rec_equiv_nil;try reflexivity;symmetry;auto.
      unfold convolution_coeff;rewrite !convolution_coeff_rec_nil.
      rewrite convolution_coeff_rec_equiv_nil;try reflexivity;auto.
      rewrite !convolution_coeff_cons.
      assert (a0 == b) by (intros m; specialize (P (S m)); simpl in P;auto).
      rewrite IHn;  try apply H0; try apply H1.
     rewrite nth_proper_list; try apply H0.
     specialize (P 0).
     simpl in P.
     rewrite P.
     reflexivity.
  Qed.
 Instance mult_coefficients_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) mult_coefficients).
 Proof.
   intros a b P x y H0.
   intros n.
   rewrite !mult_coefficients_convolution.
   apply convolution_coeff_proper;auto.
 Qed.

  Lemma mult_polyf_convolution a b n : nth n (mult_polyf a b) 0 == convolution_coeff a b n.
  Proof.
    unfold mult_polyf.
    destruct a; destruct b; try (unfold convolution_coeff; try rewrite convolution_coeff_rec_nil;try rewrite convolution_coeff_rec_nil2;destruct n;simpl;ring).
    apply mult_coefficients_convolution.
  Qed.

 #[global] Instance mult_poly_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) mult_polyf).
 Proof.
   intros a b P x y H0.
   intros n.
   rewrite !mult_polyf_convolution.
   apply convolution_coeff_proper;auto.
 Qed.

 #[global] Instance sum_coefficients_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) sum_polyf).
 Proof.
   intros a b P x y H0.
   intros n.
   rewrite !sum_coefficient_nth.
   rewrite nth_proper_list;try apply P.
   rewrite (nth_proper_list _ _ _ H0).
   reflexivity.
  Qed.


  Lemma convolution_coeff_add a b c  n : convolution_coeff (sum_polyf a b) c n == convolution_coeff a c n + convolution_coeff b c n.
  Proof.
    rewrite <-!mult_coefficients_convolution.
    rewrite nth_proper_list; try apply mult_coefficients_sym.
    rewrite nth_proper_list; try apply mult_coeffs_distr.
    rewrite sum_coefficient_nth.
    rewrite nth_proper_list; try apply (mult_coefficients_sym c);auto.
    rewrite (nth_proper_list n (mult_coefficients c b)); try apply (mult_coefficients_sym c);auto.
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
  Context `{R_rawRing : RawRing  }.
  Fixpoint mpoly n :=
    match n with
    | 0 => A
    | (S n) => @poly (mpoly n)
    end.

  Lemma mpoly_setoid_rawring n : {H : Setoid (mpoly n) & RawRing (A := mpoly n)}.
  Proof.
    induction n.
    exists H.
    apply R_rawRing.
    exists (poly_A_setoid (H := (projT1 IHn)) (A_rawRing := (projT2 IHn))).
    apply poly_rawRing.
  Defined.

  #[global] Instance mpoly_setoid n : Setoid (mpoly n) := (projT1 (mpoly_setoid_rawring n)).
  #[global] Instance mpoly_rawRing n: RawRing (A := (mpoly n)) := (projT2 (mpoly_setoid_rawring n)).
  Lemma mpoly_setoid_spec n  : mpoly_setoid (S n) = (poly_A_setoid (A := (mpoly n))).
  Proof.
    induction n.
    simpl.
    unfold poly_A_setoid.
    reflexivity.
    unfold poly_A_setoid.
    unfold mpoly_setoid.
    simpl.
    reflexivity.
  Defined.



  Fixpoint const_to_mpoly n x : (mpoly n) := 
    match n with
    | 0 => x
    | (S n) => [const_to_mpoly n x]
   end.
  Definition eval_mpoly {n} (p : mpoly (S n)) x := eval_poly p (const_to_mpoly n x).
  End MultiRawPoly.
Section MultiPolySemiRing.
  Context `{R_semiRing : SemiRing }.
  Lemma mpoly_semiring n :  SemiRing (A := mpoly n).
  Proof.
    induction n.
    apply R_semiRing.
    apply (poly_SemiRing (A_semiRing := IHn)).
  Defined.

  #[global] Instance mpoly_SemiRing n:  SemiRing (A := (mpoly n)) := mpoly_semiring n.
  End MultiPolySemiRing.
(* Section MultiPolySemiRing. *)
(*   Context `{R_semiRing : SemiRing }. *)
(*   Fixpoint mpoly n := *)
(*     match n with *)
(*     | 0 => A *)
(*     | (S n) => @poly (mpoly n) *)
(*     end. *)

(*   Lemma mpoly_setoid_rawring n : {H : Setoid (mpoly n) & {H1 : RawRing (A := mpoly n) & SemiRing (A := mpoly n)}}. *)
(*   Proof. *)
(*     induction n. *)
(*     exists H. *)
(*     exists R_rawRing. *)
(*     apply R_semiRing. *)
(*     exists (poly_A_setoid (H := (projT1 IHn)) (A_rawRing := (projT1 (projT2 IHn)))). *)
(*     exists poly_rawRing. *)
(*     apply (poly_SemiRing (A_semiRing := (projT2 (projT2 IHn)))). *)
(*   Defined. *)

(*   #[global] Instance mpoly_setoid n : Setoid (mpoly n) := (projT1 (mpoly_setoid_rawring n)). *)
(*   #[global] Instance mpoly_rawRing n: RawRing (A := (mpoly n)) := (projT1 (projT2 (mpoly_setoid_rawring n))). *)
(*   #[global] Instance mpoly_SemiRing n:  SemiRing (A := (mpoly n)) := (projT2 (projT2 (mpoly_setoid_rawring n))). *)
(*   Lemma mpoly_setoid_spec n  : mpoly_setoid (S n) = (poly_A_setoid (A := (mpoly n))). *)
(*   Proof. *)
(*     induction n. *)
(*     simpl. *)
(*     unfold poly_A_setoid. *)
(*     reflexivity. *)
(*     unfold poly_A_setoid. *)
(*     unfold mpoly_setoid. *)
(*     simpl. *)
(*     reflexivity. *)
(*   Defined. *)



(*   Fixpoint const_to_mpoly n x : (mpoly n) :=  *)
(*     match n with *)
(*     | 0 => x *)
(*     | (S n) => [const_to_mpoly n x] *)
(*    end. *)
(*   Definition eval_mpoly {n} (p : mpoly (S n)) x := eval_poly p (const_to_mpoly n x). *)
(*   End MultiRawPoly. *)

Section Composition.

  Context `{R_semiRing : SemiRing }.

  Definition to_poly_poly (p : @poly A) : (@poly (@poly A)).
  Proof.
    induction p.
    apply [].
    apply ([a] :: IHp).
  Defined.
  (* Instance poly_setoid : Setoid (@poly A). *)
  (* Proof. apply list_A_setoid. Defined. *)
  (* Instance ppoly_setoid : Setoid (@poly (@poly A)). *)
  (* Proof. apply list_A_setoid. Defined. *)


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

  #[global] Instance pmeval_proper {R} `{R_semiRing : SemiRing (A:=R)} n t : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv) (fun p => eval_tuple (n := n) p t)).
  Proof.
    intros a b H0.
    induction n; simpl;auto.
    destruct (destruct_tuple t) as [x0 [tl P]].
    apply IHn.
    apply eval_proper;auto.
  Defined.

  #[global] Instance const_to_mpoly_proper {R} `{R_semiRing : SemiRing (A:=R)}  n : (Proper  (SetoidClass.equiv ==>  SetoidClass.equiv) (const_to_mpoly n)).
  Proof.
     intros a b eq.
     induction n;simpl;auto.
     intros n0.
     destruct n0;auto.
     destruct n0;auto;reflexivity.
   Qed.
  #[global] Instance pmeval_proper2 {R} `{R_semiRing : SemiRing (A:=R)}  n : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (eval_tuple (n := n))).
  Proof.
     intros a b H0 c d H1.
     generalize dependent c.
     generalize dependent d.
     induction n;intros.
     simpl;auto.
     simpl.
     destruct (destruct_tuple c) as [c0 [ctl Pc]].
     destruct (destruct_tuple d) as [d0 [dtl Pd]].
     destruct (destruct_tuple_cons c) as [ch [t0 ->]].
     destruct (destruct_tuple_cons d) as [dh [t1 ->]].
     rewrite <-proj1_sig_tuple_cons in Pc.
     rewrite <-proj1_sig_tuple_cons in Pd.
     apply Subset.subset_eq in Pc.
     apply Subset.subset_eq in Pd.
     apply tuple_cons_ext in Pc.
     apply tuple_cons_ext in Pd.
     destruct Pc as [eq1 ->].
     destruct Pd as [eq2 ->].
     apply tuple_cons_equiv in H1.
     enough (a.{c0} == b.{d0}).
     apply IHn;auto.
     apply H1.
     unfold eval_mpoly.
     apply eval_proper2;auto.
     rewrite <-eq1, <-eq2.
     apply const_to_mpoly_proper;auto.
     apply H1.
  Qed.

  Lemma const_to_mpoly_spec {R} `{R_semiRing : SemiRing (A:=R)}  n p x0 : (eval_poly p (const_to_mpoly n x0)) == p.{x0}.
  Proof.
    induction n;simpl;reflexivity.
  Defined.

  Lemma mpoly_add_spec {R} `{R_semiRing : SemiRing (A:=R)}  {n} (p1 p2 : (@mpoly R n)) x : eval_tuple (p1 + p2) x == eval_tuple p1 x +eval_tuple p2 x.
  Proof.
    revert x.
    induction n;intros;simpl; try ring; try reflexivity.
    destruct (destruct_tuple x) as [x0 [tl P]].
    unfold eval_mpoly at 1.
    rewrite pmeval_proper; try apply sum_polyf_spec.
    rewrite IHn.
    simpl.
    apply add_proper;rewrite pmeval_proper;try apply const_to_mpoly_spec;reflexivity.
  Qed.

  Lemma mpoly_mul_spec {R} `{R_semiRing : SemiRing (A:=R)}  {n} (p1 p2 : (@mpoly R n)) x : eval_tuple (p1 * p2) x == eval_tuple p1 x * eval_tuple p2 x.
  Proof.
    revert x.
    induction n;intros;simpl; try ring; try reflexivity.
    destruct (destruct_tuple x) as [x0 [tl P]].
    rewrite pmeval_proper; try apply mult_polyf_spec.
    rewrite IHn.
    simpl.
    apply mul_proper;rewrite pmeval_proper;try apply const_to_mpoly_spec;reflexivity.
  Qed.

  Lemma zero_poly_eval {R} `{R_semiRing : SemiRing (A:=R)}  {n} (x : @tuple n R)  : eval_tuple 0 x == 0.
  Proof.
    revert x.
    induction n;intros;simpl; try ring;try reflexivity.
    destruct (destruct_tuple x) as [x0 [tl P]].
    rewrite IHn;reflexivity.
  Qed.

  Lemma const_to_mpoly_eval  {R} `{R_semiRing : SemiRing (A:=R)}  (n :nat) (a : R) x : eval_tuple (const_to_mpoly n a) x == a.
  Proof.
    revert a x.
    induction n;intros;simpl;try reflexivity.
    destruct (destruct_tuple x) as [x0 [tl P]].
    unfold eval_mpoly.
    simpl.
    rewrite mpoly_add_spec.
    rewrite mpoly_mul_spec.
    rewrite !IHn.
    rewrite zero_poly_eval.
    rewrite mul0.
    rewrite add0.
    reflexivity.
  Qed.

  Lemma eval_tuple_cons {R} `{R_semiRing : SemiRing (A:=R)} {m} (p0 : @mpoly R m) (p : @mpoly R (S m)) hd (tl : R^m) : eval_tuple ((p0 :: p) : mpoly (S m)) (tuple_cons hd tl) == eval_tuple p0 tl + hd * (eval_tuple p (tuple_cons hd tl)).
  Proof.
    simpl.
    destruct (destruct_tuple (tuple_cons hd tl)) as [h0 [t0 P0]].
    setoid_replace t0 with tl.
    unfold eval_mpoly.
    simpl.
    rewrite mpoly_add_spec.
    apply ring_eq_plus_eq; try reflexivity.
    rewrite mpoly_mul_spec.
    apply ring_eq_mult_eq;try reflexivity.
    rewrite const_to_mpoly_eval.
    rewrite proj1_sig_tuple_cons in P0.
    injection P0.
    intros _ ->;reflexivity.
    apply (tuple_nth_ext' _ _ 0 0).
    intros.
    destruct t0; destruct tl.
    simpl in *.
    injection P0.
    intros -> _.
    reflexivity.
  Qed.
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

  Lemma proj1_sig_tuple_cons {R n} (a : R) (x : @tuple n R): proj1_sig (tuple_cons a x) = a :: proj1_sig x.
  Proof.
    destruct x.
    simpl;auto.
  Qed.

  Lemma const_to_mpoly_zero n : (const_to_mpoly n 0) == 0.
  Proof.
    induction n.
    simpl.
    reflexivity.
    simpl const_to_mpoly.
    intros k.
    destruct k.
    simpl.
    apply IHn.
    simpl.
    destruct k; reflexivity.
  Qed.
  
  Lemma const_to_mpoly_one n : (const_to_mpoly n 1) == 1.
  Proof.
    induction n.
    simpl.
    reflexivity.
    simpl const_to_mpoly.
    intros k.
    destruct k.
    simpl.
    apply IHn.
    simpl.
    destruct k; reflexivity.
  Qed.
  Lemma const_to_mpoly_zero_equiv {m} n (a : mpoly m) : a == 0 -> (const_to_mpoly n a) == 0.
  Proof.
    revert a.
    induction n;intros.
    simpl.
    apply H0.
    simpl const_to_mpoly.
    intros k.
    destruct k.
    simpl.
    apply IHn.
    apply H0.
    simpl.
    destruct k; reflexivity.
  Qed.
  
  Lemma const_to_mpoly_plus n p1 p2 : (const_to_mpoly n (p1 + p2)) == const_to_mpoly n p1 + const_to_mpoly n p2.
  Proof.
    induction n.
    simpl.
    reflexivity.
    simpl const_to_mpoly.
    intros k.
    destruct k.
    simpl.
    apply IHn.
    simpl.
    destruct k; reflexivity.
  Qed.
  Lemma const_to_mpoly_mult n p1 p2 : (const_to_mpoly n (p1 * p2)) == const_to_mpoly n p1 * const_to_mpoly n p2.
  Proof.
    induction n.
    simpl.
    reflexivity.
    simpl const_to_mpoly.
    intros k.
    destruct k.
    simpl.
    unfold convolution_coeff.
    simpl.
    rewrite add0.
    apply IHn.
    simpl.
    destruct k; reflexivity.
  Qed.
  Lemma to_mmpoly_cons {n} m (p0 : mpoly n) (p : @mpoly A (S n)) : (to_mmpoly m ((p0 :: p) : @mpoly A (S n))) = (to_mmpoly m p0) :: (to_mmpoly m p).
  Proof.
    simpl to_mmpoly.
    reflexivity.
  Qed.

  Lemma to_mmpoly_zero {n} m : (to_mmpoly m (0 : (@mpoly A n)))  == 0.
  Proof.
    simpl to_mmpoly.
    induction n.
    simpl.
    apply const_to_mpoly_zero.
    intros k.
    destruct k;simpl;reflexivity.
  Qed.

  Lemma to_mmpoly_one {n} m : (to_mmpoly m (1 : (@mpoly A n)))  == 1.
  Proof.
    simpl to_mmpoly.
    induction n.
    simpl.
    apply const_to_mpoly_one.
    intros k.
    destruct k;simpl.
    apply IHn.
    destruct k;reflexivity.
  Qed.
  Lemma to_mmpoly_zero_equiv {n} m (a : mpoly n) : a == 0 -> (to_mmpoly m a)  == 0.
  Proof.
    intros.
    induction n.
    simpl.
    pose proof (const_to_mpoly_zero_equiv m a).
    rewrite H1; try reflexivity;auto.
    induction a.
    rewrite to_mmpoly_zero.
    reflexivity.
    rewrite to_mmpoly_cons.
    intros k.
    destruct k.
    simpl.
    apply IHn.
    specialize (H0 0).
    simpl in H0.
    apply H0.
    Opaque to_mmpoly.
    simpl.
    Transparent to_mmpoly.
    assert (a0 == 0).
    intros k0.
    specialize (H0 (S k0)).
    simpl in H0.
    rewrite H0.
    destruct k0; reflexivity.
    specialize (IHa H1).
    specialize (IHa k).
    rewrite IHa.
    destruct k; reflexivity.
  Qed.

  #[global] Instance to_mmpoly_proper {n} m : Proper (SetoidClass.equiv ==> SetoidClass.equiv) (to_mmpoly (n := n) m).
  Proof.
    induction n.
    intros a b eq.
    simpl.
    rewrite eq.
    reflexivity.
    intros a.
    induction a;intros b eq.
    rewrite to_mmpoly_zero.
    rewrite to_mmpoly_zero_equiv; try reflexivity.
    rewrite eq; reflexivity.
    rewrite to_mmpoly_cons.
    destruct b.
    + rewrite to_mmpoly_zero.
      intros k.
      destruct k.
      simpl.
      rewrite to_mmpoly_zero_equiv;try reflexivity.
      specialize (eq 0).
      simpl in eq.
      apply eq.
      Opaque to_mmpoly. simpl. Transparent to_mmpoly.
      assert (a0 == 0).
      {
        intros j.
        specialize (eq (S j)).
        simpl in eq.
        rewrite eq.
        destruct j;reflexivity.
      }
      pose proof (to_mmpoly_zero_equiv m (a0 : (mpoly (S n))) H0 k).
      rewrite H1. 
      destruct k;reflexivity.
   + rewrite to_mmpoly_cons.
     intros k.
     destruct k.
     simpl.
     apply IHn.
     specialize (eq 0).
     simpl in eq.
     apply eq.
      Opaque to_mmpoly. simpl. Transparent to_mmpoly.
      assert (a0 == b).
      {
         intros j.
         specialize (eq (S j)).
         simpl in eq.
         apply eq.
      }
      specialize (IHa b H0 k ).
      apply IHa.
  Qed.

  Lemma mpoly_composition_cons {n m}  (p0 : @mpoly A n) (p : @mpoly A (S n)) (q0 : @mpoly A m) (qs : @tuple n (@mpoly A m)) : mpoly_composition (p0 :: p : (@mpoly A (S n))) (tuple_cons q0 qs) == mpoly_composition p0 qs + q0 * mpoly_composition p (tuple_cons q0 qs).
  Proof.
    unfold mpoly_composition.
    rewrite to_mmpoly_cons.
    rewrite eval_tuple_cons.
    reflexivity.
  Qed.

  Definition eval_tuple_rec_cons {n m} p0 (ps : @tuple n (@mpoly A m)) (xs : @tuple m A) : eval_tuple_rec (tuple_cons p0 ps) xs = tuple_cons (eval_tuple p0 xs) (eval_tuple_rec ps xs).
  Proof.
    simpl.
    destruct (destruct_tuple_cons (tuple_cons p0 ps)) as [hd [tl P]].
    apply tuple_cons_ext in P.
    destruct P as [-> ->].
    reflexivity.
  Qed.

  Lemma mpoly_composition_spec {n m} (p : @mpoly A n) (qs : @tuple n (@mpoly A m)) xs : eval_tuple (mpoly_composition p qs) xs == eval_tuple p (eval_tuple_rec qs xs). 
  Proof.
  induction n.
  - simpl.
    simpl in p.
    unfold mpoly_composition, to_mmpoly.
    simpl.
    rewrite const_to_mpoly_eval;ring.
  -  destruct (destruct_tuple_cons qs) as [q0 [qt ->]].
     induction p.
     + unfold mpoly_composition.
       rewrite to_mmpoly_zero.
       rewrite !zero_poly_eval.
       reflexivity.
     +  rewrite mpoly_composition_cons.
        rewrite mpoly_add_spec.
        rewrite eval_tuple_rec_cons.
        rewrite eval_tuple_cons.
        apply ring_eq_plus_eq.
        apply IHn.
        rewrite mpoly_mul_spec.
        apply ring_eq_mult_eq;try reflexivity.
        rewrite IHp.
        rewrite eval_tuple_rec_cons.
        reflexivity.
  Qed.

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
    assert (n < length x \/ length x <= n)%nat by lia.
    destruct H0.
    apply a0;auto.
    rewrite !nth_overflow;auto;try lia.
    rewrite ntimes_zero;ring.
  Qed.

  Lemma derive_poly_cons a0 a1 a : derive_poly (a0 :: a1 :: a) == sum_polyf (a1 :: a) (0 :: (derive_poly (a1 :: a))).
  Proof.
    apply (nth_ext_A _ _ 0 0).
    rewrite length_sum_coefficients;simpl; rewrite !derive_poly_length;simpl;lia.
    intros.
    rewrite sum_coefficient_nth.
    destruct n;simpl; rewrite !derive_poly_nth;simpl;ring.
  Qed.
  Lemma derive_poly_cons1 a0 a : derive_poly (a0 :: a) == sum_polyf a (0 :: (derive_poly a)).
  Proof.
    intros n0.
    rewrite sum_coefficient_nth.
    destruct n0;simpl; rewrite !derive_poly_nth;simpl;ring.
  Qed.
  #[global] Instance cons_proper : (Proper  (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (fun a0 a => a0 :: a)). 
  Proof.
    intros a b H0 a0 b0 H1.
    intros n.
    destruct n.
    simpl;auto.
    simpl;auto.
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
    intros a b H0 n.
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
    intros n.
    destruct n;simpl;reflexivity.
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

    Lemma mult_polyf_shift_switch a0 a  b0 b : mult_polyf (0 :: (a0 :: a)) (b0 :: b) ==  mult_polyf (a0 :: a) (0 :: (b0 :: b)). 
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
      intros n;reflexivity.
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
 ==  nth n (mult_coefficients (sum_polyf [r] [0]) p1) 0) as -> by (rewrite nth_proper_list; try apply mult_coefficients_sym;try reflexivity).
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
      rewrite mult_polyf_shift_switch.
      rewrite IHa.
      pose proof (mult_poly_cons a0 (r :: a1')).
      intros n.
      rewrite sum_coefficients_proper; [|apply poly_scalar_mult_deriv | reflexivity].

      rewrite (sum_poly1_proper (mult_polyf (r0::b1) _ )); try apply H0.
      apply nth_proper_list.
      clear n.
      rewrite sum_poly_assoc.
      apply sum_coefficients_proper; try reflexivity.
      rewrite (derive_poly_const_independent a0).
      intros n.
      rewrite sum_poly1_proper; [| apply mult_poly2_proper;try apply derive_poly_cons].
      rewrite (sum_poly2_proper (mult_polyf (0 :: r :: a1') _)); [| apply mult_poly2_proper;try apply derive_poly_cons].
      rewrite sum_poly1_proper; [| apply mult_poly_distr].
      apply nth_proper_list.
      clear n.
      rewrite !mult_poly_distr.
      rewrite <-(sum_poly_assoc (mult_polyf (0 :: _) _)).
      intros n.
      rewrite (sum_poly1_proper (mult_polyf (r0 :: b1) _));try apply (sum_poly_sym _ (mult_polyf (r0 :: b1) (r :: a1'))).
      apply nth_proper_list; clear n.
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

  Lemma poly_pdiff1  n d : @poly_pdiff n d 1 == 0.
  Proof.
    generalize dependent n.
    induction d;destruct n;simpl;try ring;try reflexivity;auto.
    intros m.
    destruct m.
    rewrite IHd;reflexivity.
    destruct m;reflexivity.
  Qed.

  Lemma poly_pdiff_const  n d x : @poly_pdiff n d (const_to_mpoly n x) == 0.
  Proof.
    generalize dependent n.
    induction d;destruct n;simpl;try ring;try reflexivity;auto.
    intros m.
    destruct m.
    rewrite IHd;reflexivity.
    destruct m;reflexivity.
  Qed.
  #[global] Instance mpoly_pdiff_proper : forall n d, Proper (SetoidClass.equiv ==> SetoidClass.equiv)  (@poly_pdiff n d).
  Proof.
    intros.
    intros a b H'.
    generalize dependent n.
    induction d;intros;destruct n;try (simpl;reflexivity).
    rewrite H';reflexivity.
    intros m.
    simpl.
    assert (m < length a \/ length a <= m)%nat by lia.
    assert (m < length b \/ length b <= m)%nat by lia.
    destruct H1, H2.
    - rewrite  (nth_indep _ _ (poly_pdiff d 0));auto.
      rewrite (nth_indep  (map (poly_pdiff d) b) _ (poly_pdiff d 0));auto.
      rewrite !map_nth.
      apply IHd.
      apply H'.
      rewrite length_map;auto.
      rewrite length_map;auto.
   - rewrite  (nth_indep _ _ (poly_pdiff d 0));auto.
     rewrite (nth_overflow (map (poly_pdiff d) b)).
     rewrite map_nth.
     assert (nth m a 0 == 0).
     {
       specialize (H' m).
       rewrite H'.
       rewrite nth_overflow;auto;reflexivity.
     }
     rewrite (IHd _ _ _ H3).
     rewrite poly_pdiff0;reflexivity.
     rewrite length_map;auto.
     rewrite length_map;auto.
   - rewrite nth_overflow.
     rewrite  (nth_indep _ _ (poly_pdiff d 0));auto;try (rewrite length_map;auto).
     rewrite map_nth.
     assert (nth m b 0 == 0).
     {
       specialize (H' m).
       rewrite <-H'.
       rewrite nth_overflow;auto;reflexivity.
     }
     rewrite (IHd _ _ _ H3).
     rewrite poly_pdiff0; reflexivity.
     rewrite length_map;auto.
   - rewrite !nth_overflow; try rewrite length_map; auto.
     reflexivity.
  Defined.


  Lemma mult_polyf_length_compat {n} (a b c d : mpoly (S n)) : length a = length b -> length c = length d -> length (mult_polyf a c) = length (mult_polyf b d).
  Proof.
    intros.
    unfold mult_polyf.
    destruct c;destruct d.
    destruct a; destruct b; simpl;auto.
    simpl in H2;lia.
    destruct a.
    -  simpl in H1.
       symmetry in H1.
       apply length_zero_iff_nil in H1.
       rewrite H1;simpl;auto.
   - simpl in H2;lia.
  - destruct a; destruct b; simpl;auto.
     simpl in H1;lia.
     simpl in H1;lia.
     rewrite !length_mult_coefficients.
     lia.
   Qed.

  Lemma poly_pdiff_plus m : forall (p : (mpoly m)) q n, poly_pdiff n (p + q) ==  poly_pdiff n p +  poly_pdiff n q.
  Proof.
      induction m;intros; destruct n;try (simpl; rewrite add0;reflexivity).
      apply poly_sum_rule.
      intros n0.
      simpl.
      setoid_rewrite <- (poly_pdiff0 _ n) at 1.
      rewrite !map_nth.
      rewrite !sum_coefficient_nth.
      assert (forall r, nth n0 (map (@poly_pdiff m n) r) 0 = poly_pdiff n (nth n0 r 0)).
      {
        intros.
        replace 0 with (@poly_pdiff m n 0) by apply poly_pdiff0.
        rewrite map_nth.
        rewrite poly_pdiff0;auto.
      }
      simpl.
      rewrite !H1.
      apply IHm.
  Qed.

  Lemma poly_pdiff_mult m : forall (p : (mpoly m)) q n, poly_pdiff n (p * q) == q * poly_pdiff n p + p * poly_pdiff n q.
  Proof.
    intros.
    generalize dependent m.
    induction n;intros.
    - destruct m.
      simpl.
      rewrite !mul0.
      rewrite add0.
      reflexivity.
      simpl poly_pdiff.
      rewrite addC.
      apply poly_product_rule.
   -  destruct m.
      simpl.
      rewrite !mul0.
      rewrite add0.
      reflexivity.
      simpl poly_pdiff.
      intros n0.
     setoid_rewrite <- (poly_pdiff0 _ n) at 1.
     simpl; rewrite !map_nth. 
    rewrite sum_coefficient_nth.
     rewrite !mult_polyf_convolution.
     revert n0.
     induction p;intros.
     + unfold convolution_coeff.
       simpl.
       rewrite !convolution_coeff_rec_nil.
       rewrite !convolution_coeff_rec_nil2.
       rewrite poly_pdiff0;rewrite add0;reflexivity.
     +  simpl.
       destruct n0.
      unfold convolution_coeff.
      simpl.
      rewrite add0.
      rewrite IHn.
      rewrite !add0.
      apply ring_eq_plus_eq;try reflexivity.
      rewrite ring_eq_mult_eq;try reflexivity.
      setoid_rewrite <- (poly_pdiff0 _ n) at 2.
      simpl; rewrite !map_nth. 
      reflexivity.
      rewrite !convolution_coeff_cons.
      rewrite poly_pdiff_plus.
      rewrite IHn.
      rewrite IHp.
      rewrite <-!addA.
      apply ring_eq_plus_eq; try reflexivity.
      rewrite (convolution_coeff_sym _ (poly_pdiff n a :: _)).
      rewrite convolution_coeff_cons.
      rewrite !addA.
      apply ring_eq_plus_eq.
      rewrite mulC;reflexivity.
      rewrite addC.
      apply ring_eq_plus_eq.
      rewrite convolution_coeff_sym; reflexivity.
      apply ring_eq_mult_eq; try reflexivity.
     setoid_rewrite <- (poly_pdiff0 _ n) at 2.
     rewrite map_nth.
     reflexivity.
  Qed.

  Lemma poly_pdiff_ntimes d n m (p : (mpoly d)): poly_pdiff n (ntimes m p) == ntimes m (poly_pdiff n p).
  Proof.
   induction m.
   simpl.
   rewrite poly_pdiff0.
   reflexivity.
   simpl.
   rewrite poly_pdiff_plus.
   rewrite IHm.
   reflexivity.
  Qed.

  Lemma poly_pdiff_switch d : forall (p : (mpoly d)) m n, poly_pdiff n (poly_pdiff m p) == poly_pdiff m (poly_pdiff n p).
  Proof.
    intros.
    generalize dependent d.
    generalize dependent n.
    induction m.
    - destruct d.
      simpl.
      rewrite poly_pdiff0; reflexivity.
      simpl.
      intros.
      apply nth_proper_list.
      induction n.
      + simpl.
        intros n1; rewrite !derive_poly_nth.
        reflexivity.
     + simpl.
       intros n1.
       setoid_rewrite <- (poly_pdiff0 _ n) at 1.
       rewrite !map_nth.
        rewrite !derive_poly_nth.
       setoid_rewrite <- (poly_pdiff0 _ n) at 2.
       rewrite map_nth.
        rewrite poly_pdiff_ntimes.
        reflexivity.
   - intros.
      destruct d.
      simpl.
       rewrite poly_pdiff0;reflexivity.
      simpl.
      intros n0.
      setoid_rewrite <- (poly_pdiff0 _ m) at 2.
     rewrite map_nth.
     destruct n.
     + simpl.
       rewrite !derive_poly_nth.
        setoid_rewrite <- (poly_pdiff0 _ m) at 1.
        rewrite map_nth.
        rewrite poly_pdiff_ntimes.
        reflexivity.
    +  simpl.
        setoid_rewrite <- (poly_pdiff0 _ n).
        rewrite !map_nth.
        rewrite <-IHm.
        apply mpoly_pdiff_proper.
        setoid_rewrite <- (poly_pdiff0 _ m) at 1.
        rewrite !map_nth.
        reflexivity.
  Qed.

  #[global] Instance mpoly_pdiffring n : PartialDifferentialRing (A := (mpoly n)).
  Proof.
  exists poly_pdiff.
  - intros; apply poly_pdiff_plus.
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

  #[global] Instance mpoly_composition_proper {n m}: (Proper (SetoidClass.equiv ==> SetoidClass.equiv ==> SetoidClass.equiv) (mpoly_composition (n := n) (m := m))).
  Proof.
    intros a b eq c d eq'.
    unfold mpoly_composition.
    rewrite eq'.
    apply pmeval_proper.
    rewrite eq.
    reflexivity.
  Defined.

  Lemma poly_comp1_composition {m n} (f : @tuple n (mpoly (S m))) (i : nat) : mpoly_composition (poly_comp1 i) f == tuple_nth i f 0.
  Proof.
    generalize dependent m.
    generalize dependent n.
    induction i;intros.
    - destruct n.
      simpl mpoly_composition.
      setoid_rewrite to_mmpoly_zero_equiv; try reflexivity.
      intros n0.
      rewrite tuple_nth_nil.
      reflexivity.
      simpl poly_comp1.
      destruct (destruct_tuple_cons f) as [f0 [t ->]].
      rewrite tuple_nth_cons_hd.
      rewrite mpoly_composition_cons.
      unfold mpoly_composition.
      rewrite to_mmpoly_zero.
      rewrite zero_poly_eval.
      rewrite addC,add0.
      setoid_replace ([1 : mpoly n]) with (1 : mpoly (S n)) by reflexivity.
      pose proof (to_mmpoly_one (n:=(S n)) (S m)).
      rewrite H1.
      rewrite <-const_to_mpoly_one.
      rewrite const_to_mpoly_eval.
      rewrite mul1; reflexivity.
   - destruct n.
      simpl mpoly_composition.
      setoid_rewrite to_mmpoly_zero_equiv; try reflexivity.
      intros n0.
      rewrite tuple_nth_nil.
      reflexivity.
      simpl mpoly_composition.
      
      destruct (destruct_tuple_cons f) as [f0 [t ->]].
      rewrite tuple_nth_cons_tl.
      rewrite mpoly_composition_cons.
      rewrite IHi.
      unfold mpoly_composition.
      setoid_rewrite to_mmpoly_zero_equiv; try reflexivity.
      rewrite zero_poly_eval.
      rewrite mul0, add0.
      reflexivity.
   Qed.

  Lemma poly_composition_plus_comp : forall {m n} x y (z :@tuple m (mpoly (S n))) , mpoly_composition (x+y) z == (mpoly_composition x z) + (mpoly_composition y z).
  Proof.
    intros.
    induction m.
    - simpl.
      intros [].
      apply const_to_mpoly_plus.
      destruct n0;reflexivity.
   - destruct (destruct_tuple_cons z) as [z0 [t ->]].
     generalize dependent x.
     induction y;intros.
     rewrite add0.
     unfold mpoly_composition at 3.
     rewrite to_mmpoly_zero.
     rewrite zero_poly_eval.
     rewrite add0.
     reflexivity.
     destruct x.
     rewrite addC.
     rewrite add0.
     unfold mpoly_composition at 2.
     rewrite to_mmpoly_zero.
     rewrite zero_poly_eval.
     rewrite addC, add0.
     reflexivity.
     simpl mpoly_composition.
     rewrite !mpoly_composition_cons.
     rewrite IHm.
     rewrite !addA.
     apply ring_eq_plus_eq; try reflexivity.
     rewrite (addC _ (_ + _)).
     rewrite !addA.
     apply ring_eq_plus_eq; try reflexivity.
     rewrite <-distrL.
     apply ring_eq_mult_eq; try reflexivity.
     specialize (IHy x).
     rewrite IHy.
     rewrite addC.
     reflexivity.
  Qed.


  Lemma nth_S {T : Type} n a0 (a : list T)  : nth (S n) (cons a0 a) = nth n a.
  Proof.
    simpl;reflexivity.
  Qed.

  Lemma mult_poly_shift  {n} (x y : mpoly (S n)) : (0 :: x) * y  == 0 :: (x * y).
  Proof.
    revert x.
    destruct y;intros.
    rewrite !mul0.
    intros [];simpl; try destruct n0; try reflexivity.
    rewrite mulC.
    simpl (_ * _).
    unfold mult_polyf at 1.
    rewrite mult_coefficients_cons.
    rewrite mult_coefficients_single_list.
    rewrite map_cons.
    rewrite <-mult_coefficients_single_list.
    simpl sum_polyf.
    rewrite mul0, add0.
    destruct x.
     setoid_replace ([0 : mpoly n] ) with (0 : mpoly (S n)) by  (intros [];simpl;try destruct n0;try reflexivity).
    rewrite !mult_coefficients_nil_equiv2.
    simpl.
    intros []; try destruct n0; try reflexivity.
    rewrite mult_poly_sym.
    rewrite mult_poly_cons.
    intros n0.
    destruct n0; try reflexivity.
    rewrite !nth_S.
    apply nth_proper_list.
    apply sum_poly2_proper.
    rewrite mult_coefficients_sym.
    destruct y.
    setoid_replace ([0 : mpoly n] ) with (0 : mpoly (S n)) by  (intros [];simpl;try destruct n1;try reflexivity).
    simpl mult_polyf.
    rewrite mult_polyf_nil2.
    rewrite !mult_coefficients_nil_equiv2;reflexivity.
    rewrite mult_polyf_shift_switch.
    rewrite mult_poly_sym.
    reflexivity.
  Qed.

  Lemma poly_composition_mult_comp : forall {m n} x y (z :@tuple m (mpoly (S n))) , mpoly_composition (x*y) z == (mpoly_composition x z) * (mpoly_composition y z).
  Proof.
    intros.
    induction m.
    - simpl.
      intros []; try destruct n0;try reflexivity.
      unfold convolution_coeff.
      simpl.
      rewrite add0.
      simpl.
      apply const_to_mpoly_mult.
   - destruct (destruct_tuple_cons z) as [z0 [t ->]].
     generalize dependent y.
     induction x;intros.
     +  setoid_rewrite mult_polyf_nil2.
        unfold mpoly_composition; rewrite !to_mmpoly_zero; rewrite !zero_poly_eval; rewrite mulC,mul0.
        reflexivity.
     + setoid_rewrite mult_poly_cons.
       setoid_rewrite poly_composition_plus_comp.
       rewrite !mpoly_composition_cons.
       rewrite mulC.
       rewrite distrL.
       apply ring_eq_plus_eq.
       * induction y.
         rewrite mult_polyf_nil1.
        unfold mpoly_composition; rewrite !to_mmpoly_zero; rewrite !zero_poly_eval; rewrite mulC,mul0;reflexivity.
        unfold mult_polyf.
        rewrite mult_coefficients_single_list.
        rewrite map_cons.
        rewrite !(mpoly_composition_cons).
        rewrite <-mult_coefficients_single_list.
        rewrite !IHm.
        rewrite (mulC _ (mpoly_composition a t)), distrL.
        apply ring_eq_plus_eq;try reflexivity.
        rewrite <-mulA, (mulC _ z0).
        rewrite mulA.
        apply ring_eq_mult_eq;try reflexivity.
        destruct y.
        rewrite mult_coefficients_nil_equiv2.
        unfold mpoly_composition; rewrite !to_mmpoly_zero; rewrite !zero_poly_eval, mul0;reflexivity.
        rewrite IHy.
        rewrite mulC;reflexivity.
       * setoid_rewrite mult_poly_shift.
        rewrite mpoly_composition_cons.
        unfold mpoly_composition at 1; setoid_rewrite to_mmpoly_zero; rewrite !zero_poly_eval, addC,add0.
        rewrite IHx.
        rewrite <-mulA.
        rewrite (mulC z0).
        rewrite mulC.
        reflexivity.
     Qed.

  Lemma poly_comp_diff1 {m}  (i : nat) : i < m -> D[i] (@poly_comp1 m i) == 1.
  Proof.
    simpl.
    revert m.
    induction i.
    - intros.
      destruct m; try lia.
      simpl.
      unfold derive_poly.
      simpl.
      intros n.
      destruct n;simpl.
      rewrite add0.
      reflexivity.
      destruct n; reflexivity.
   - intros.
      destruct m; try lia.
      simpl.
      intros n.
      destruct n;simpl.
      rewrite IHi; try lia;reflexivity.
      destruct n; reflexivity.
  Qed.

  Lemma poly_comp_diff0 {m}  (i : nat) (j : nat) : (i <> j)%nat -> D[i] (@poly_comp1 m j) == 0.
  Proof.
    simpl.
    intros.
    revert m.
    generalize dependent i.
    induction j.
    intros.
    destruct m.
    simpl.
    rewrite poly_pdiff0;reflexivity.
    intros n.
    simpl.
    destruct i; try lia.
    simpl.
    destruct n.
    rewrite poly_pdiff0.
    reflexivity.
    destruct n.
    rewrite poly_pdiff1;reflexivity.
    destruct n; reflexivity.
    intros.
    simpl.
    destruct m.
    rewrite poly_pdiff0;reflexivity.
    destruct i.
    simpl.
    intros n.
    reflexivity.
    simpl.
    intros n.
    destruct n;try reflexivity.
    rewrite IHj; try reflexivity; try lia.
    destruct n; reflexivity.
  Qed.

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
    intros.
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
      destruct (destruct_tuple_cons x) as [hd [tl ->]].
      rewrite eval_tuple_emb.
      rewrite tuple_nth_cons_tl.
      apply IHn.
   Qed.
  
  Definition mpoly_comp'  {n m} := mpoly_composition (n := n) (m := (S m)).
  Lemma mpoly_pdiff_comp_cons : forall {m n d} (x0 : mpoly m) (x : mpoly (S m)) y0 (y : @tuple m (mpoly (S n))), poly_pdiff d (mpoly_composition (x0 :: x : mpoly (S m)) (tuple_cons y0 y)) == poly_pdiff d (mpoly_composition x0 y) + mpoly_composition x (tuple_cons y0 y) * poly_pdiff d y0  + y0 * poly_pdiff d (mpoly_composition x (tuple_cons y0 y)).
  Proof.
    intros.
    rewrite mpoly_composition_cons.
    rewrite poly_pdiff_plus.
    rewrite poly_pdiff_mult.
    rewrite !addA.
    reflexivity.
  Qed.
  
  Lemma mpoly_pdiff_comp_nil : forall {m n d} (y : @tuple m (mpoly (S n))), poly_pdiff d (mpoly_composition (0: mpoly m) y) == 0.
  Proof.
    intros.
    unfold mpoly_composition.
    rewrite to_mmpoly_zero.
    rewrite zero_poly_eval.
    rewrite poly_pdiff0.
    reflexivity.
  Qed.
    Lemma composition_zero :forall {m n} (x : mpoly m) (y : @tuple m (mpoly (S n))) , x == 0 -> mpoly_composition x y == 0.
    Proof.
      intros.
      unfold mpoly_composition.
      rewrite to_mmpoly_zero_equiv; auto.
      rewrite zero_poly_eval; reflexivity.
    Qed.

  Lemma mpoly_comp_cons0 : forall {m n} (x : mpoly (S m)) y0 (y : @tuple m (mpoly (S n))), mpoly_composition (0:: x : mpoly (S m)) (tuple_cons y0 y) == y0 * (mpoly_composition x (tuple_cons y0 y)).
  Proof.
    intros.
    rewrite mpoly_composition_cons.
    rewrite composition_zero; try reflexivity.
   Qed.
  Lemma mpoly_pdiff_comp_cons0 : forall {m n d} (x : mpoly (S m)) y0 (y : @tuple m (mpoly (S n))), poly_pdiff d (mpoly_composition (0:: x : mpoly (S m)) (tuple_cons y0 y)) == mpoly_composition x (tuple_cons y0 y) * poly_pdiff d y0  + y0 * poly_pdiff d (mpoly_composition x (tuple_cons y0 y)).
  Proof.
    intros.
    rewrite mpoly_pdiff_comp_cons.
    rewrite composition_zero; try reflexivity.
    rewrite poly_pdiff0.
    rewrite addC, <-addA, add0.
    rewrite addC; reflexivity.
  Qed.


    Lemma mpoly_pdiff_chain0 : forall {n d} (x : mpoly 0) (y : @tuple 0 (mpoly (S n))), poly_pdiff d (mpoly_composition x y) == (sum (fun i => (poly_pdiff d (tuple_nth i y zero)) * mpoly_composition (poly_pdiff i x) y) 0).
    Proof.
      intros.
      replace (mpoly_composition x y) with (const_to_mpoly (S n) x) by reflexivity.
      rewrite poly_pdiff_const.
      reflexivity.
    Qed.

    Lemma mpoly_pdiff_chain_nil : forall {m n d}  (y : @tuple (S m) (mpoly (S n))), poly_pdiff d (mpoly_composition 0 y) == (sum (fun i => (poly_pdiff d (tuple_nth i y 0)) * mpoly_composition (poly_pdiff i 0) y) (S m)).
    Proof.
      intros.
      pose proof (mpoly_pdiff_comp_nil (d:=d) (n:=n) (m:=(S m)) y).
      simpl pdiff.
      rewrite H1.
      rewrite sum_zero; try reflexivity.
      intros.
      rewrite poly_pdiff0.
      rewrite composition_zero;try reflexivity.
      rewrite mul0;reflexivity.
    Qed.

    Lemma mpoly_pdiff_chain : forall {m n d} (x : mpoly m) (y : @tuple m (mpoly (S n))), poly_pdiff d (mpoly_composition x y) == (sum (fun i => (poly_pdiff d (tuple_nth i y zero)) * mpoly_composition (poly_pdiff i x) y) m).
    Proof.
    simpl pdiff.
    induction m.
    intros;apply mpoly_pdiff_chain0.
    induction x.
    - intros.
      apply mpoly_pdiff_chain_nil.
   -  intros.
      destruct (destruct_tuple_cons y) as [y0 [yt ->]].
      pose proof ( mpoly_pdiff_comp_cons (d := d) (n:=n) (m:=m) a x y0 yt) as He.
      simpl pdiff.
      rewrite He.
      rewrite sum_S_fun.
      rewrite tuple_nth_cons_hd.
      setoid_rewrite derive_poly_cons1.
      setoid_rewrite poly_composition_plus_comp.
      rewrite distrL.
      rewrite addA, addC, !addA.
      apply ring_eq_plus_eq.
      rewrite mulC;apply ring_eq_mult_eq; try reflexivity.
      rewrite mpoly_comp_cons0.
      setoid_rewrite IHx.
      rewrite sum_S_fun.
      rewrite distrL.
      rewrite tuple_nth_cons_hd.
      rewrite !addA.
      apply ring_eq_plus_eq.
      rewrite !(mulC y0), !mulA; reflexivity.
      setoid_rewrite IHm.
      rewrite sum_mult.
      rewrite sum_plus.
      apply sum_ext.
      intros.
      rewrite tuple_nth_cons_tl.
      simpl poly_pdiff.
      rewrite mpoly_composition_cons.
      rewrite distrL.
      rewrite addC.
      apply ring_eq_plus_eq; try reflexivity.
      rewrite !(mulC y0), !mulA; reflexivity.
  Qed.
      
  #[global] Instance mpoly_comp_diff_algebra : CompositionalDiffAlgebra (A := (@mpoly A) ).
  Proof.
  exists @mpoly_comp' @poly_comp1;unfold mpoly_comp'.
   - intros; apply poly_comp1_composition.
   - intros;apply poly_composition_plus_comp.
   - intros;apply poly_composition_mult_comp.
   - intros;apply mpoly_pdiff_chain.
   - intros;  apply mpoly_composition_proper.
   - intros.
     apply poly_comp_diff1;auto.
   - intros. apply poly_comp_diff0;auto.
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

