Require Import algebra.
From Coq Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import tuple.
From Coq Require Import Psatz.

From Coq Require Import Classical.
Require Import combinatorics.


Section Evaluation.
  Context {A B C : Type} `{SemiRing A} `{SemiRing B} `{SemiRing C}.
  Class HasEvaluation := {
      in_domain  (f : A) (x : B):  Prop;
      eval f x (P : in_domain f x) :  C;
      in_domain_proper  :: Proper (equiv ==> equiv ==> equiv) in_domain;
      eval_proper  : forall f1 f2 x1 x2 P1 P2, f1 == f2 -> x1 == x2 -> eval f1 x1 P1 == eval f2 x2 P2;
      eval_0  (x : B) P : eval 0 x P == 0;
      dom_plus (f g : A) (x : B) : in_domain f x -> in_domain g x  -> in_domain (f+g) x;
      eval_plus_compat (f g : A) (x : B) P1 P2 P3: eval (f + g) x P3  == eval f x P1 +  eval g x P2;
      dom_mult  (f g : A) (x : B) : in_domain f x -> in_domain g x -> in_domain (f*g) x;
      eval_mult_compat (f g : A) (x : B) P1 P2 P3: eval (f * g) x P3  == eval f x P1 * eval g x P2;
    }.
End Evaluation.

Section MultiEvaluation.
  Context {A B C : Type} `{SemiRing A} `{SemiRing B} `{SemiRing C}.
  Context `{HasEvaluation (A := A) (B := B) (C := C) (H := H) (H1 := H1) (H3 := H3) (R_rawRing := R_rawRing) (R_rawRing1 := R_rawRing1) }.

 Lemma eval_change_f  (f g : A) (x0 : B) P :  (f == g) -> exists P', eval f x0 P == eval g x0 P'. 
 Proof.
   intros.
   assert (in_domain g x0).
   {
     apply (in_domain_proper (A:=A) (B:=B) f g H6 x0 x0 );auto.
     reflexivity.
   }
   exists H7.
   apply eval_proper;auto.
   reflexivity.
 Qed.
  Definition in_domaint {d}  (f : A^d) (x : B) := forall i, i< d ->  in_domain (tuple_nth i f 0) x.

  Lemma in_domaint_cons {d}  (hd : A) (tl : A^d) (x : B) : in_domaint (tuple_cons hd tl) x <-> (in_domain hd x) /\ (in_domaint tl x).
  Proof.
    split.
    - intros Hd.
      rewrite <-(tuple_nth_cons_hd hd tl 0).
      split.
      apply Hd;lia.

      unfold in_domaint.
      intros i Hi. 
      rewrite <-(tuple_nth_cons_tl i hd tl 0).
      apply Hd;lia.
   - intros [].
     unfold in_domaint;intros.
     destruct i.
     rewrite tuple_nth_cons_hd;auto.
     rewrite tuple_nth_cons_tl;auto.
     apply H7;lia.
  Qed.

  Lemma in_domaint_cons_impl {d}  f (hd : A) (tl : A^d) (x : B) :  (f = tuple_cons hd tl) -> in_domaint f x -> (in_domain hd x) /\ (in_domaint tl x).
  Proof.
  intros ->.
  apply in_domaint_cons.
  Qed.
  (* Lemma in_domaint_cons_impl {m n :nat} (hd : A n) (tl : @tuple m (A n)) f (x : @tuple n (A 0)) : f = tuple_cons hd tl -> in_domaint f x -> (in_domain hd x) /\ (in_domaint tl x). *)
  (* Proof. intros Hf; rewrite Hf; apply in_domaint_cons. Qed. *)
(* Definition evalt_hd {A B C d def} (f : A^(S d)) `{E : forall n, n < (S d) -> @HasEvaluation A B C (tuple_nth n f def)} (x : B) (P : in_domaint f x) :{E0 : @HasEvaluation A B C (tuple_nth 0 f def)  | in_domain (HasEvaluation := E0) x /\ forall H lt, eval (HasEvaluation := E0) x H = eval _ (P 0%nat lt)}. *)
(* Proof. *)
(*     destruct (destruct_tuple_cons f) as [hd [tl ->]]. *)
(*     assert (0 < S d) by lia. *)
(*     exists (E _ H). *)
(*     split. *)
(*     apply P. *)
(*     intros. *)
(*     replace lt with H by apply proof_irrelevance. *)
(*     replace H0 with (P _ H) by apply proof_irrelevance;auto. *)
(* Defined. *)
  (* Lemma in_domaint_cons {A B C d def} {f: A^d } (hd : A) (tl : A^d) `{E0 :  @HasEvaluation A B C hd} `{E : forall (n:nat), n < d  -> @HasEvaluation A B C (tuple_nth n tl def)} (x : B) : forall H, in_domaint (E := H) (tuple_cons hd tl) x <-> (in_domain (f := hd) x) /\ (in_domaint tl x). *)
  (* Proof. *)
  (*   split. *)
  (*   - intros. *)
  (*     rewrite <-(tuple_nth_cons_hd hd tl 0). *)
  (*     split. *)
  (*     apply H5;lia. *)

  (*     unfold in_domaint. *)
  (*     intros. *)
  (*     rewrite <-(tuple_nth_cons_tl i hd tl 0). *)
  (*     apply H5;lia. *)
  (*  - intros []. *)
  (*    unfold in_domaint;intros. *)
  (*    destruct i. *)
  (*    rewrite tuple_nth_cons_hd;auto. *)
  (*    rewrite tuple_nth_cons_tl;auto. *)
  (*    apply H6;lia. *)
     
  (* Qed. *)

  (* Lemma in_domaint_cons_impl {m n :nat} (hd : A n) (tl : @tuple m (A n)) f (x : @tuple n (A 0)) : f = tuple_cons hd tl -> in_domaint f x -> (in_domain hd x) /\ (in_domaint tl x). *)
  (* Proof. intros Hf; rewrite Hf; apply in_domaint_cons. Qed. *)
(* Definition evalt_hd {A B C d def} (f : A^(S d)) `{E : forall n, n < (S d) -> @HasEvaluation A B C (tuple_nth n f def)} (x : B) (P : in_domaint f x) :{E0 : @HasEvaluation A B C (tuple_nth 0 f def)  | in_domain (HasEvaluation := E0) x /\ forall H lt, eval (HasEvaluation := E0) x H = eval _ (P 0%nat lt)}. *)
(* Proof. *)
(*     destruct (destruct_tuple_cons f) as [hd [tl ->]]. *)
(*     assert (0 < S d) by lia. *)
(*     exists (E _ H). *)
(*     split. *)
(*     apply P. *)
(*     intros. *)
(*     replace lt with H by apply proof_irrelevance. *)
(*     replace H0 with (P _ H) by apply proof_irrelevance;auto. *)
(* Defined. *)

(* Definition evalt_tl {A B C d def} (f : A^(S d)) `{E : forall n, n < (S d) -> @HasEvaluation A B C (tuple_nth n f def)} (x : B) (P : in_domaint f x) : {tl & {E':  forall n, n< d -> @HasEvaluation A B C (tuple_nth n tl def) | in_domaint (E := E') tl x /\ forall n lt0 lt1 H H', n < d -> eval (HasEvaluation := (E (S n) lt0)) x H = eval (HasEvaluation:= (E' n lt1)) x H'}}. *)
(* Proof. *)
(*     destruct (destruct_tuple_cons f) as [hd [tl ->]]. *)
(*     exists tl. *)
(*     enough (forall n, n < d -> {E':  @HasEvaluation A B C (tuple_nth n tl def) | in_domain (HasEvaluation := E')  x /\ forall lt0 H H', eval (HasEvaluation := (E (S n) lt0)) x H = eval (HasEvaluation:=E') x H'}). *)
(*     { *)
(*       exists (fun n H => proj1_sig (X n H)). *)
(*       split. *)
(*       intros n H;destruct (X n H) as [E1 [A1 A2]];auto. *)
(*       intros. *)
(*       destruct (X n lt1) as [E1 [A1 A2]];auto. *)
(*     } *)
(*     intros. *)
(*     rewrite <-(tuple_nth_cons_tl _ hd). *)
(*     assert (S n < S d) by lia. *)
(*     exists (E _ H0);auto. *)
(*     split. *)
(*     apply P. *)
(*     intros. *)
(*     assert (lt0 = H0) as -> by apply proof_irrelevance. *)
(*     assert (H1 = H') as -> by apply proof_irrelevance. *)
(*     reflexivity. *)
(*  Defined. *)

(* Definition evalt {d} {def} (f : A^d) (x : B) (P : in_domaint (def := def) f x) : C^d. *)
(*   Proof. *)
(*     induction d. *)
(*     apply nil_tuple. *)
(*     destruct (destruct_tuple_cons f) as [hd [tl Pf]]. *)
(*     destruct (evalt_hd f x P) as [e0 [A0 A1]]. *)
(*     destruct (evalt_tl f x P) as [tl [e1 [B0 B1]]]. *)
(*     apply (tuple_cons (eval (HasEvaluation := e0) x A0) (IHd tl e1 B0)). *)
(*   Defined. *)

Definition evalt {d}  (f : A^d) (x : B) (P : in_domaint f x) : C^d.
  Proof.
    induction d.
    apply nil_tuple.
    destruct (destruct_tuple_cons f) as [hd [tl P0]].
    apply (tuple_cons (eval hd x (proj1 (in_domaint_cons_impl f hd tl x P0 P))) (IHd tl (proj2 (in_domaint_cons_impl f hd tl x P0 P)))).
  Defined.

    Lemma evalt_spec {d} (f : A^d) x (P : in_domaint f x) i (lt : i < d) : tuple_nth i (evalt f x P) 0 == (eval (tuple_nth i f 0) x (P i lt)).
  Proof.
    generalize dependent i.
    induction d;intros; try lia.
    simpl;auto.
    destruct (destruct_tuple_cons f) as [hd [tl ->]].
    simpl.
    destruct i.
    - rewrite !tuple_nth_cons_hd.
      apply eval_proper; try rewrite tuple_nth_cons_hd; reflexivity.
    - rewrite !tuple_nth_cons_tl.
      assert (i < d) by lia.
      rewrite (IHd _ _ _ H6).
      apply eval_proper;try reflexivity.
      rewrite tuple_nth_cons_tl.
      reflexivity.
    Qed.

   #[global] Instance in_domt_proper {n}  :Proper (equiv ==> equiv ==> equiv)  (in_domaint (d := n)).
    Proof.
    intros a b eq0 c d eq1.
    simpl.
    unfold in_domaint.
    split;intros.
    rewrite <-eq0, <-eq1.
    apply H6;auto.
    
    rewrite eq0,eq1.
    apply H6;auto.
   Defined.

    Lemma meval_proper {n} : forall (f1 f2 : A^n)  (x1 x2 : B) P1 P2, f1 == f2 -> x1 == x2 -> evalt f1 x1 P1 == evalt f2 x2 P2.
    Proof.
      intros.
      apply (tuple_nth_ext' _ _ 0 0).
      intros.
      rewrite !(evalt_spec _ _ _ _ H8).
      apply eval_proper;auto.
      rewrite H6;reflexivity.
   Defined.

    Lemma meval_mult_compat {n} (f : A^n) (g : A^n) (x : B) P1 P2 P3: evalt (f * g) x P3  == evalt f x P1 * evalt  g x P2.
    Proof.
      apply (tuple_nth_ext' _ _ 0 0).
      intros.
      rewrite vec_mult_spec;auto.
      simpl.
      rewrite !(evalt_spec _ _ _ _ H6).
      pose proof (vec_mult_spec f g i H6).
      assert (in_domain ((tuple_nth i f 0) * (tuple_nth i g 0)) x).
      {
        apply dom_mult;auto.
      }
      rewrite (eval_proper _ _ x x (P3 i H6) H8 H7);try reflexivity.
      rewrite eval_mult_compat; try reflexivity.
    Qed.

    Lemma meval_plus_compat {n} (f : A^n) (g : A^n) (x : B) P1 P2 P3: evalt (f + g) x P3  == evalt f x P1 + evalt  g x P2.
    Proof.
      apply (tuple_nth_ext' _ _ 0 0).
      intros.
      rewrite vec_plus_spec;auto.
      simpl.
      rewrite !(evalt_spec _ _ _ _ H6).
      pose proof (vec_plus_spec f g i H6).
      assert (in_domain ((tuple_nth i f 0) + (tuple_nth i g 0)) x).
      {
        apply dom_plus;auto.
      }
      rewrite (eval_proper _ _ x x (P3 i H6) H8 H7);try reflexivity.
      rewrite eval_plus_compat; try reflexivity.
    Qed.

    Lemma meval_0 {n}  (x : B) P : evalt (d := n) 0 x P  == 0.
    Proof.
      apply (tuple_nth_ext' _ _ 0 0).
      intros.
      rewrite !(evalt_spec _ _ _ _ H6).
      rewrite !vec0_nth.
      assert ((0 : A^n)\_i == 0) by (rewrite vec0_nth;reflexivity).
      destruct (eval_change_f _ _ _ (P i H6) H7).
      rewrite H8.
      apply eval_0.
    Qed.

  #[global] Instance HasMultiEval {d} : (HasEvaluation (A := (A ^ d)) (B:=B) (C := (C^d))).
  Proof.
    exists (in_domaint ) evalt.
    - apply in_domt_proper.
    - apply meval_proper.
    - intros.
      apply meval_0.
    - intros.
      intros i n.
      rewrite vec_plus_spec;auto.
      apply dom_plus;auto.
    - apply meval_plus_compat. 
    - intros.
      intros i n.
      rewrite vec_mult_spec;auto.
      apply dom_mult;auto.
   - apply meval_mult_compat.
  Defined.

 End MultiEvaluation.
Open Scope fun_scope.
  Notation "x \in_dom f" := (in_domain f x) (at level 5) : fun_scope.
  Notation " f @ ( x ; p )" := (eval f x p) (at level 5):fun_scope.  
(*  Section MultiEvalLemmas. *)
(*     Context {d} {A B C : Type} `{SemiRing (A := A)} `{SemiRing (A := C)} (f : A^d) `{E : forall n, n < d -> @HasEvaluation A B C (tuple_nth n f 0)}. *)
(*     Lemma evalt_spec0 {x : B} (P : in_domain (f := f) x)  i (lt : i < d): tuple_nth i (eval (f := f) x P) 0 = (eval (f := (tuple_nth i f 0)) x (P i lt)). *)
(*   Proof. *)
(*     generalize dependent i. *)
(*     induction d;intros; try lia. *)
(*     simpl;auto. *)
(*     destruct (evalt_hd f x P) as [e0 [A0 A1]]. *)
(*     destruct (evalt_tl f x P) as [tl [e1 [B0 B1]]]. *)
(*     destruct i. *)
(*     - rewrite !tuple_nth_cons_hd. *)
(*       specialize (A1 A0 lt). *)
(*       rewrite A1. *)
(*       reflexivity. *)
(*     - rewrite !tuple_nth_cons_tl. *)
(*       assert (i < n) by lia. *)
(*       specialize (IHn tl e1). *)
(*       simpl in IHn. *)
(*       rewrite (IHn _ _ H3). *)
(*       apply eq_sym. *)
(*       apply B1;auto. *)
(*     Qed. *)
(* End MultiEvalLemmas. *)

Section FunctionSpace.

  Context `{CompositionalDiffAlgebra} `{forall n, HasEvaluation (A := (A n)) (B := (A 0%nat)^n) (C := A 0%nat)}.

  (* Lemma evalt_dom_proof_irrelev m n (f : @tuple m (A n)) x P1 P2 : f @ (x;P1) == f @ (x;P2). *)
  (* Proof. *)
  (*   replace P1 with P2;try reflexivity. *)
    
  (*   apply proof_irrelevance. *)
  (* Qed. *)

  (* Context `{normK : (NormedSemiRing (A 0) (A 0) (H := (H 0)) (H0 := (H 0)) (R_rawRing := (H0 0%nat)) (R_rawRing0 := (H0 0%nat)) (R_TotalOrder := R_TotalOrder))} *)
  Class AbstractFunctionSpace := {
      const {m} (c : A 0): (A m);
      const_dom {m} : forall c (x : (A 0)^m), x \in_dom (const (m := m) c);
      const_eval {m} : forall c x,  (const (m := m) c) @ (x ;(const_dom (m:=m) c x)) == c;
      dom_id {m} (n : nat): forall (x : (A 0)^m), x \in_dom (comp1 (m :=m) n);
      eval_id {m} n : forall x H, (n < m) -> (comp1 (m := m) n) @ (x; H) == tuple_nth n x 0;
      dom_diff {n} (f : A n) (x : (A 0)^n) i : x \in_dom f -> x \in_dom (D[i] f);
      dom_composition {r m n} (f : (A n)^r) (g : (A (S m))^n) (x : (A 0)^(S m)) P gx : g @ (x;P) == gx -> (gx \in_dom f) -> (x \in_dom (f \o g));
      eval_composition_compat {r m n : nat} (f : (A n)^r) (g : (A (S m))^n) (x : (A 0)^(S m)) (Px : (x \in_dom g)) (Py : (g @ (x;Px) \in_dom f)) (Pz : x \in_dom (f \o g)) : f \o g @ (x;Pz)  == f @ (g @ (x;Px);Py)
    }.

End FunctionSpace.
Section AbstractFunctionTheory.

  Context `{AbstractFunctionSpace}.


  Instance dom_change_f {n} : forall (x : (A 0)^n),  Proper (equiv ==> equiv) (fun f => (x \in_dom f)).
  Proof.
    intros x a b Heq.
    rewrite Heq.
    reflexivity.
  Defined.

  Lemma dom_sum {n} (fs : nat -> A n) (x : (A 0)^n) d : (forall i, (i <= d)%nat -> x \in_dom (fs i)) -> x \in_dom (sum fs (S d)).
  Proof.
    intros.
    induction d.
    - unfold sum;simpl.
      rewrite add0.
      apply H6;auto.
    - pose proof (sum_S fs (S d)).
      apply (dom_change_f x _ _ H7).
      apply dom_plus;auto.
  Qed.

  Lemma nth_derivative_dom {m p} (f : (A m)^p) (x0 : (A 0)^m) : forall n i, x0 \in_dom f ->  x0 \in_dom (nth_derivative i f n).
  Proof.
  intros.
  induction n.
  simpl;auto.
  simpl.
  intros j jle.
  rewrite pdiff_tuple_nth;auto.
  apply dom_diff.
  apply IHn;auto.
  Qed.
  
   (* #[global] Instance in_domt_proper {n m} :Proper (equiv ==> equiv ==> equiv) (fun f x => (in_domain (A := (A n)^m) (f := f) x)). *)
   (*  Proof. *)
   (*  intros a b eq0 c d eq1. *)
   (*  simpl. *)
   (*  unfold in_domaint. *)
   (*  split;intros. *)
   (*  assert (tuple_nth  i a 0 == tuple_nth i b 0) by (rewrite eq0;reflexivity). *)
   (*  pose proof (dom_proper (tuple_nth i a 0) (tuple_nth i b 0) H8 c d eq1). *)
   (*  simpl in H9. *)
   (*  apply H9. *)
   (*  apply H6;auto. *)

   (*  assert (tuple_nth  i b 0 == tuple_nth i a 0) by (rewrite eq0;reflexivity). *)
   (*  assert (d == c) by (rewrite eq1; reflexivity). *)
   (*  pose proof (dom_proper (tuple_nth i b 0) (tuple_nth i a 0) H8 d c H9). *)
   (*  apply H10. *)
   (*  apply H6;auto. *)
   (* Defined. *)

   (*  Lemma meval_proper {n m} : forall (f1 f2 : (A n)^m)  (x1 x2 : (A 0)^n) P1 P2, f1 == f2 -> x1 == x2 -> (f1 @ (x1;P1)) == f2 @ (x2;P2).   *)
   (*  Proof. *)
   (*    intros. *)
   (*    apply (tuple_nth_ext' _ _ 0 0). *)
   (*    intros. *)
   (*    rewrite !(evalt_spec _ _ H8). *)
   (*    apply eval_proper;auto. *)
   (*    rewrite H6;reflexivity. *)
   (* Defined. *)

    Definition scalar_multf {n} (x : A 0) (f : A n) := const x * f.
    Definition scalar_addf {n} (x : A 0) (f : A n) := const x + f.

End AbstractFunctionTheory.

Infix "[*]" := scalar_multf (at level 2).
Infix "[+]" := scalar_addf (at level 2).

