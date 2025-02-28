Require Import algebra.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import tuple.
Require Import Psatz.

Require Import Classical.

Section Evaluation.
  Context {A B C : Type} `{SemiRing A} `{SemiRing B} `{SemiRing C}.
  Class HasEvaluation := {
      in_domain  (f : A) (x : B):  Prop;
      eval f x (P : in_domain f x) :  C;
      in_domain_proper  :: Proper (equiv ==> equiv ==> equiv) in_domain;
      eval_proper  : forall f1 f2 x1 x2 P1 P2, f1 == f2 -> x1 == x2 -> eval f1 x1 P1 == eval f2 x2 P2;
    }.

End Evaluation.

Section MultiEvaluation.
  Context {A B C : Type} `{SemiRing A} `{SemiRing B} `{SemiRing C}.
  Context `{HasEvaluation (A:=A) (B := B) (C:=C) (H := H) (H1 := H1) (H3 := H3)}.
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

  #[global] Instance HasMultiEval {d} : (HasEvaluation (A := (A ^ d)) (B:=B) (C := (C^d))).
  Proof.
    exists (in_domaint ) evalt.
    apply in_domt_proper.
    apply meval_proper.
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
      dom_plus {n} (f g : A n) (x : (A 0)^n) : x \in_dom f -> x \in_dom g  -> x \in_dom (f+g);
      dom_mult {n} (f g : A n) (x : (A 0)^n) : x \in_dom f -> x \in_dom g -> x \in_dom (f*g);
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


(* Section Interval. *)
(*   Context `{K : Type}. *)
(*   Context `{ofieldK : TotallyOrderedField K}. *)
(*   Context `{normK : (NormedSemiRing K K (H := H) (H0 := H) (R_rawRing := R_rawRing) (R_rawRing0 := R_rawRing) (R_TotalOrder := R_TotalOrder))}. *)

(*   Add Ring TRing: ComRingTheory. *)
(*   Definition cinterval := (K * K)%type. *)
(*   Definition in_cinterval x i := (normK.(norm) (x-(fst i))) <= snd i. *)
(*   Definition in_cintervalt {n} (x : @tuple n K) (i : @tuple n cinterval) : Prop. *)
(*   Proof. *)
(*     induction n. *)
(*     apply True. *)
(*     destruct (destruct_tuple x) as [x0 [xt P1]]. *)
(*     destruct (destruct_tuple i) as [i0 [it P2]]. *)
(*     apply ((in_cinterval x0 i0) /\ (IHn xt it)). *)
(*   Defined. *)
(* End Interval. *)
  (* Class differentialRing `{R_semiRing : comSemiRing} := *)
  (*   { *)
  (*   derivation : A -> A; *)
  (*   derivation_plus : forall r1 r2, derivation (add r1 r2) == add (derivation r1) (derivation r2); *)
  (*   derivation_mult : forall r1 r2, derivation (mul r1 r2) == add (mul r2 (derivation r1)) (mul r1  (derivation r2)); *)
  (*   derivation_proper :> Proper (equiv ==> equiv) derivation; *)
  (*   }. *)

(* Section DifferentialAlgebra. *)
(*   Context {K V : Type} . *)
  
(*   Class differentialAlgebra `{K_field : Field (A := K)} `{R_differentialRing : (differentialRing (A := V))} := { *)
(*       smult : K -> V -> V; *)
(*       smult1 : forall v, smult one v == v; *)
(*       smult_proper :> Proper (equiv ==> equiv ==> equiv) smult; *)
(*       smult_plus_distr : forall a u v, smult a (u+v) == smult a u + smult a v; *)
(*       splus_mult_dist : forall a b v, smult (a+b) v == smult a v + smult b v; *)
(*       smult_mult_compat : forall a b v, smult a (smult b v) == smult (a*b) v *)
(*     }.  *)

(* End DifferentialAlgebra. *)

(* Local Infix "[*]" := smult (at level 2, left associativity). *)

(* Section DifferentialAlgebraTheory. *)
(*   Context {K V : Type}  `{DA : differentialAlgebra (K:=K) (V := V)}. *)
(*   Add Ring RRing: (ComSemiRingTheory (A:=V)). *)
(*   Add Ring RRing: (ComRingTheory (A:=K)). *)
(*   Lemma smult_zero  a : a [*] 0 == 0. *)
(*   Proof. *)
(*     enough (0 [*] 0 == 0). *)
(*     rewrite <-H1. *)
(*     rewrite smult_mult_compat. *)
(*     setoid_replace (a*0) with (0 : K) by ring;auto. *)
(*     reflexivity. *)
(*     pose proof (smult1 0). *)
(*     rewrite <- H1 at 2. *)
(*     setoid_replace (1 : K) with (0+1 : K) by ring. *)
(*     rewrite splus_mult_dist. *)
(*     rewrite smult1. *)
(*     rewrite add0;reflexivity. *)
(*   Qed. *)

(* End DifferentialAlgebraTheory. *)
Section Analytic.

Context `{AbstractFunctionSpace} {d e : nat} {f : (A d)^e} {x0 : (A 0%nat)^d} {dom : x0 \in_dom f}.
Context `{TotallyOrderedField (A := (A 0)) (H:=(H 0)) (R_rawRing := (H0 0)) (R_semiRing := (H1 0))}.
 Context `{normK : (NormedSemiRing (A 0) (A 0) (H := (H 0)) (H0 := (H 0)) (R_rawRing := (H0 0%nat)) (R_rawRing0 := (H0 0%nat)) (R_TotalOrder := R_TotalOrder))}. 
Lemma nth_derivative_dom : forall n i,  x0 \in_dom (nth_derivative i f n).
Proof.
  intros.
  induction n.
  simpl;apply dom.
  simpl.
  intros j Hj.
  simpl.
  rewrite pdiff_tuple_nth;auto.
  apply dom_diff.
  apply IHn;auto.
Qed.

Class Analytic := {
    M : (A 0);
    R : (A 0);
    derivative_bound : forall n i, (i < d) -> norm ((nth_derivative i f n) @ (x0; (nth_derivative_dom n i))) <= M * npow R n
  }.
End Analytic.
