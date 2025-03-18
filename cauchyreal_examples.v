Require Import polynomial.
Require Import Coq.Reals.Abstract.ConstructiveReals.
Require Import coqreals.
Require Import examples.
Require Import tuple.
Require Import List.
Require Import Coq.Classes.SetoidClass.
From Coq.Reals Require Import ConstructiveCauchyReals.
From Coq.Reals.Cauchy Require Import ConstructiveRcomplete.
Require Import QArith.
Require Import Qpower.
Require Import Qabs.
Require Import Qround.
Require Import odebounds.
Require Import realanalytic.
Require Import abstractpowerseries.
Require Import ConstructiveCauchyAbs.
Open Scope algebra_scope.
Open Scope fun_scope.
Open Scope Q_scope.
Definition q (x : Z) (y : positive) := ({| Qnum := x; Qden := y |}).
Definition RQ := CRcarrier CRealConstructive.
  Context `{AbstractPowerSeries (A := RQ) (H := (R_setoid )) (R_rawRing := R_rawRing) (H0 := _) (invSn := invSn) }.

   Lemma magic : False.
   Admitted.
  Lemma cauchy_neighboring_to_mod   (xn : nat -> RQ) : fast_cauchy_neighboring xn ->  (Un_cauchy_mod xn).
  Proof.
    intros H k.
    exists (Nat.log2_up ((Pos.to_nat (k+1)))).
    intros.
    contradict magic.
   Defined.

  #[global] Instance ArchimedeanFieldRQ : algebra.ArchimedeanField (A := RQ).
  Proof.
    unshelve eapply algebra.Build_ArchimedeanField.
    - intros.
      simpl.

      apply CReal_abs_right.
      apply H0.
   -  intros.
      pose proof (seq x (-1)).
      exists (Z.to_nat (Qceiling H0+1)).
      contradict magic.
  Defined.
  #[global] Instance constrComplete : (ConstrComplete (A := RQ)).
  Proof.
    constructor.
    intros.
    exists (CReal_from_cauchy  xn (cauchy_neighboring_to_mod _ H0)).
    intros.
    contradict magic.
   Defined.

 Definition  seq_tuple {d} (p : (RQ * tuple d RQ))  (z : Z): Q * list Q.
 Proof.
   destruct p.
   destruct t.
   apply ((seq r z) , (map (fun x => (seq x z)) x)).
 Defined.
 Definition  seq_trajectory {d} (p : list (RQ * tuple d RQ))  (z : Z) :=  map (fun p => seq_tuple p z) p.
  Definition exp_example := exp_ivp (A := RQ).

  Check @analytic_poly.
  Definition p1  := analytic_poly (invSn := invSn) (normK := (@R_norm CRealConstructive)) exp_example.(pf) exp_example.(py0).


  Definition approx1 := approx (A := RQ) (invSn := invSn)  p1 (inject_Q (1 # 2)) 0 0.
  Set Printing Implicit.
Check @approx1.
Compute (seq approx1 3).

   Definition ap1 := ivp_solution_i_max (norm_abs := (norm_abs CRealConstructive)) p1 0%nat.

   Compute (seq (fst ap1) (-10)).

   Definition test_exp := pivp_solution_max  (norm_abs := (norm_abs CRealConstructive)) exp_example.(examples.f)  exp_example.(examples.y0).
   Compute (seq_tuple test_exp (-10)).
   Definition a0 := (nth 0 (snd (seq_tuple test_exp (-20))) 0).
   Compute a0.
   Definition y1 := (snd (test_exp )).
   Definition test_exp2 := pivp_solution_max  (norm_abs := (norm_abs CRealConstructive)) exp_example.(examples.f) t(inject_Q a0).
   Check test_exp2.
   Compute (seq_tuple (test_exp2) (-2)).
Definition Q_to_pair (q : Q) : Z * positive :=
  let n := Qnum q in
  let d := Qden q in
  (n, d).
Definition a1 := map Q_to_pair (snd (seq_tuple test_exp2 (-2))).
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require ExtrHaskellZInteger.
Extraction Language Haskell.
Unset Extraction SafeImplicits.
Extraction "exp2"  a1.






   
   Definition r := (algebra.mul combinatorics.inv2  (combinatorics.inv_Sn   (proj1_sig (analytic_solution_r (norm_abs := (norm_abs CRealConstructive)) p1)))).
   Compute (seq r 2).

   Definition r' := ivp_r_max (norm_abs := (norm_abs CRealConstructive)) p1.
Check CReal_from_cauchy.
   Definition test : RQ.
   Proof.
   
      destruct (has_limit (ConstrComplete := constrComplete) (fun n => inject_Q 1)).
      contradict magic.
      apply x.
   Defined.

   Eval vm_compute in (seq (test) 2).
   Compute (seq (fst ap1) (-10)).


  (** one dimensional examples **)
  Definition exp_example := exp_ivp (A := @mpoly RQ).
  Definition exp_approx := AIVP_nth_approx exp_example.
  kk
  (* radius for exp *)
  Compute (seq (y_radius exp_example) (-2)).
  (* 10th approximation of exp at 1/4 *)
  Compute (eval_Q (exp_approx 10) (1#4)).

  Definition tan_example := tan_ivp (A := @mpoly RQ).
  Definition tan_approx := AIVP_nth_approx tan_example.

  (* radius for tan *)
  Compute (seq (y_radius tan_example) -2).
  (* 3rd approximation of exp at 1/8 *)
  Compute (eval_Q (tan_approx 3) (1#8)).

  (** two dimensional examples **)

  Definition sin_cos_example := sin_cos_ivp (A := @mpoly RQ).
  Definition sin_cos_approx := AIVP_nth_approx sin_cos_example.
  (* radius  *)
  Compute (seq (y_radius sin_cos_example) -2).
  (* 6th approximation of sine/cosine at 1/16 *)
  Compute (eval_Q (sin_cos_approx 6) (1#16)).

  Definition vdp_example := vdp_ivp (inject_Q (1#10)) (A := @mpoly RQ).

  Definition vdp_approx := AIVP_nth_approx vdp_example.
  (* radius  *)
  Compute (seq (y_radius vdp_example) -2).
  
  
  (* 2nd approximation of vdp at 1/16 *)
  (* already takes a while, so commented out for now *)

  (* Compute (eval_Q (vdp_approx 2) (1#16)). *)
  

(* code extraction *)
  
Require Import Extraction.
Require ExtrHaskellBasic.
Require ExtrHaskellNatInteger.
Require ExtrHaskellZInteger.
Extraction Language Haskell.
Unset Extraction SafeImplicits.
Definition Q_to_pair (q : Q) : Z * positive :=
  let n := Qnum q in
  let d := Qden q in
  (n, d).
Definition vdp_val := Q_to_pair (nth 0 (eval_Q (vdp_approx 4) (1#16) 2) 0).
Extraction "vdp" vdp_val.
  (* Lemma un_cauchy_mod_exp : un_cauchy_mod . *)
  (* Definition w (n : nat) := inject_Q 2. *)
  (* Print Un_cauchy_mod. *)
  (* Check (Rcauchy_limit w). *)
Check ccDecimal.
  
  Definition minus1_poly : (@mpoly (CRcarrier CRealConstructive) 2).
  Proof.
    apply [[];[inject_Q (q (-1) 1)]].
  Defined.

  

  Definition sin_cos_taylor  := IVP_taylor (A := @mpoly RQ ) sin_cos_ivp.

  Definition vdp_taylor  := IVP_taylor (A := @mpoly RQ) (vdp_ivp (inject_Q (q 1  10))).

  Definition eval_tuple_poly {d} (p : (@poly (tuple d (@mpoly (CRcarrier CRealConstructive) 0)))) (t : CReal)  : list Q.
  Proof.
    pose proof (seq_to_tuple (fun n => t) d (def := t)).
    destruct X.
    pose proof (eval_poly p x).
    destruct X.
    apply (map (fun a => seq a 10) x0).
  Defined.

  Definition t0 := (t(inject_Q 3;inject_Q 1) : (tuple 2 RQ)).
  Definition t1 := (t(inject_Q 3;inject_Q 1;inject_Q 2) : (tuple 3 RQ)).
  Definition poly2 := const_to_mpoly 3 (inject_Q 3).
  Check poly2.
  Definition ppoly2 : (tuple 3 CReal {x^3}) := t(poly2;poly2;poly2).
  Lemma a : t0  \in_dom minus1_poly. 
  Proof.
    apply poly_total.
  Qed.

  Definition norm_poly := (poly_normt (vdp_ivp (inject_Q (q 1  10)) (A:=@mpoly RQ)).(f)).
  Eval vm_compute in (seq (norm_poly) 5).
  Search "limit".
  Check Rcauchy_limit.
  Print Un_cauchy_mod.
  Definition eval1 := (minus1_poly @ (t0;a)).
  Definition eval_s := (sin_cos_ivp (A:=@mpoly RQ)).(f) @ (sin_cos_ivp.(y0);sin_cos_ivp.(in_dom)).
  Eval vm_compute in  (eval_tuple_poly (vdp_taylor 1) (inject_Q (q 2 10))).

  Lemma ab : t1  \in_dom ppoly2.
  Proof.
    apply poly_total.
  Qed.
  Definition eval0 := poly2 @ (t1;ab).

  
  Definition eval_s := (sin_cos_ivp (A:=@mpoly RQ)).(f) @ (sin_cos_ivp.(y0);sin_cos_ivp.(in_dom)).
  Definition eval_t := (tan_ivp (A:=@mpoly RQ)).(f) @ (tan_ivp.(y0);tan_ivp.(in_dom)).
  Definition eval1 := (minus1_poly @ (t0;a)).
  Definition aa := (tuple_nth 0%nat eval_t (inject_Q 0)).
   
  





