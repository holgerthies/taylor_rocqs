Require Import Psatz.
Require Import Setoid.
Require Import Coq.Classes.SetoidClass.
Require Import algebra.
Require Import ZArith.
Require Import tuple.
Require Import List.

Open Scope algebra_scope.


(* We define a ring structure on nat to work with multi-indices *)

  #[global] Instance nat_setoid : Setoid nat.
  Proof.
    exists (fun x y => (x=y)).
    constructor; intros a; intros;try auto.
    rewrite H, H0;auto.
  Defined.

  #[global] Instance nat_rawring : RawRing (A := nat).
  Proof.
    constructor.
    apply 0%nat.
    apply 1%nat.
    intros a b.
    apply (a+b)%nat.
    intros a b.
    apply (a*b)%nat.
  Defined.

  #[global] Instance nat_semiring : SemiRing (A := nat).
  Proof.
    constructor;intros;simpl;try lia;intros a b eq c d eq';lia.
  Defined.

  Notation "# n" := (ntimes n 1) (at level 2).
(* Results about multiindices (tuples of nat) *)
Section Multiindex.

 Definition order {d} (n : nat^d) : nat.
 Proof.
   induction d.      
   apply 0%nat.
   destruct (destruct_tuple_cons n) as [hd [tl P]].
   apply (hd + (IHd tl))%nat.
 Defined.
 
    Lemma order_cons {d} hd tl : order (d:=S d) (tuple_cons hd tl) = (hd + order tl)%nat.
    Proof.
      simpl.
      destruct (destruct_tuple_cons (tuple_cons hd tl)) as [hd' [tl' P]].
      apply tuple_cons_ext in P.
      destruct P as [-> ->].
      lia.
    Qed.

    Lemma order_zero_split {d} hd tl : order (d:=S d) (tuple_cons hd tl) = 0%nat -> (hd = 0%nat /\ order tl = 0%nat).
    Proof.
      intros.
      rewrite order_cons in H.
      lia.
    Qed.

    Lemma order_zero1 {d} n : (order (d:=d) n) = 0%nat -> (forall i, i< d -> tuple_nth i n 0%nat = 0%nat).
    Proof.
      intros.
      generalize dependent i.
      induction d;intros; try lia.
      destruct (destruct_tuple_cons n) as [hd [tl ->]].
      apply order_zero_split in H.
      destruct i.
      rewrite tuple_nth_cons_hd.
      apply H.
      rewrite tuple_nth_cons_tl.
      apply IHd;try lia.
    Qed.

    Lemma order_zero {d} n : (order (d:=d) n) = 0%nat -> (forall i,  tuple_nth i n 0%nat = 0%nat).
    Proof.
      intros.
      destruct (Nat.lt_ge_cases i d).
      apply order_zero1;auto.
      destruct n.
      simpl.
      rewrite nth_overflow;auto;lia.
     Qed.

    Lemma zero_order {d} : (order (d:=d) 0) = 0%nat.
    Proof.
      induction d.
      simpl;reflexivity.
      rewrite vec0_cons.
      rewrite order_cons.
      rewrite IHd.
      simpl.
      reflexivity.
    Qed.
  #[global] Instance order_proper {d} : Proper (equiv ==> equiv) (order (d:=d)). 
  Proof.
    intros a b eq.
    induction d.
    simpl.
    reflexivity.
    Opaque equiv.
    simpl.
    destruct (destruct_tuple_cons a ) as [a0 [ta Pa]].
    destruct (destruct_tuple_cons b ) as [b0 [tb Pb]].
    Transparent equiv.
    rewrite Pa,Pb in eq.
    apply tuple_cons_equiv in eq;auto.
    destruct eq .
    rewrite H.
    rewrite (IHd ta tb);auto.
    reflexivity.
  Qed.
 End Multiindex.
 
(* factorial, inverse factorial and rising factorials *)
Section factorial.
  Context `{SemiRing}.
  Class Sn_invertible := {
      inv_Sn  (n : nat) : A; 
      inv_Sn_spec : forall n, (ntimes (S n) 1) * inv_Sn n == 1
  }.

  Definition inv_factorial `{Sn_invertible} (n : nat) : A.
  Proof.
    induction n.
    apply 1.
    apply  (inv_Sn n  * IHn).
  Defined.

  Definition factorial  (n : nat) : A.
  Proof.
    induction n.
    apply 1.
    apply  ((ntimes (S n) 1)  * IHn).
  Defined.

  Definition rising_factorial `{Sn_invertible} k n := factorial(k+n-1) * inv_factorial(k-1).

  Definition factorialt {d} (n : nat^d) : A.
  Proof.
    induction d.
    apply 1.
    destruct (destruct_tuple_cons n) as [n0 [nt P]].
    apply (factorial n0 * (IHd nt)).
  Defined.
  Definition inv_factorialt `{Sn_invertible}  {d} (n : nat^d) : A.
  Proof.
    induction d.
    apply 1.
    destruct (destruct_tuple_cons n) as [n0 [nt P]].
    apply (inv_factorial n0 * (IHd nt)).
  Defined.
  Definition rising_factorialt `{Sn_invertible}  {d} (k n : nat^d) : A.
  Proof.
    induction d.
    apply 1.
    destruct (destruct_tuple_cons k) as [k0 [kt Pk]].
    destruct (destruct_tuple_cons n) as [n0 [nt P]].
    apply ((rising_factorial k0 n0) * (IHd kt nt)).
  Defined.
End factorial.

Notation "[ k ! n ]" := (rising_factorial k n).
Notation "![ n ]" := (inv_factorial n).
Notation "[ n ]!" := (factorial n).

Notation "t[ k ! n ]" := (rising_factorialt k n).
Notation "t![ n ]" := (inv_factorialt n).
Notation "t[ n ]!" := (factorialt n).
Section factorialTheorems.
  Context `{SemiRing}.
  Context `{invSn : (Sn_invertible (A := A) (H:=_) (R_rawRing := _))}.
  Add Ring TRing: (ComSemiRingTheory (A := A)). 

  #[global] Instance rising_factorial_proper {d}: Proper (equiv ==> equiv ==> equiv) (rising_factorialt (d:=d)).
  Proof.
    intros a b eq e f eq'.
    induction d.
    simpl.
    reflexivity.
    simpl.
    destruct (destruct_tuple_cons a) as [k0 [kt Pk]].
    destruct (destruct_tuple_cons e) as [n0 [nt P]].
    destruct (destruct_tuple_cons b) as [k0' [kt' Pk']].
    destruct (destruct_tuple_cons f) as [n0' [nt' P']].
    enough (k0 = k0' /\ n0 = n0') as [-> ->].
    rewrite (IHd kt kt'  ).
  Admitted.
  Lemma fact_invfact n : [n]! * ![n] == 1. 
  Proof.
    induction n.
    simpl.
    ring.
    simpl.
    ring_simplify.
    rewrite mulC.
    rewrite (mulC (ntimes  _ _)).
    rewrite <-!(mulA ![n]).
    rewrite (mulC ![n]).
    rewrite IHn.
    ring_simplify.
    rewrite mulA.
    rewrite IHn.
    ring_simplify.
    setoid_replace (ntimes n 1 * inv_Sn n + inv_Sn n ) with (ntimes (S n) 1 * inv_Sn n).
    rewrite inv_Sn_spec;reflexivity.
    simpl;ring.
  Qed.

  Lemma ntimes_invfact n x : ntimes (S n) (inv_factorial (S n) * x) == (inv_factorial n * x).
  Proof.
    rewrite !ntimes_mult.
    setoid_replace x with (x*1) by ring.
    rewrite ntimes_mult.
    setoid_replace ( ![ S n] * (x * ntimes (S n) 1) ) with (![n] * ((ntimes (S n) 1) * (inv_Sn n)) * x) by (simpl;ring).
    rewrite inv_Sn_spec.
    ring.
  Qed.



 Lemma rising_factorial1 n : [1 ! n]  == [n]!.
 Proof.
   unfold rising_factorial.
   simpl.
   replace (n-0)%nat with n by lia.
   ring.
 Qed.

 Lemma rising_factorial0 n : [n ! 0]  == 1.
 Proof.
   unfold rising_factorial.
   replace (n+0-1)%nat with (n-1)%nat by lia.
   rewrite fact_invfact.
   reflexivity.
 Qed.

 Lemma rising_factorialn1 k : [k+1 ! 1]  == #(k+1).
 Proof.
   unfold rising_factorial.
   simpl.
   replace (k+1+1-1)%nat with (S k)%nat by lia.
   replace (k+1-1)%nat with k by lia.
   simpl.
   rewrite mulA.
   rewrite fact_invfact.
   replace (k+1)%nat with (S k) by lia.
   simpl;ring.
 Qed.
 Lemma rising_factorialt1 {d} (n : nat^d) : t[1 ! n]  == t[n]!.
 Proof.
   intros.
   induction d.
   simpl.
   reflexivity.
   simpl.
   destruct (destruct_tuple_cons n) as [n0 [nt P]].
   destruct (destruct_tuple_cons 1) as [h1 [t1 P1]].
   setoid_rewrite vec1_cons in P1.
   apply tuple_cons_ext in P1.
   destruct P1 as [<- <-].
   rewrite rising_factorial1.
   rewrite IHd.
   reflexivity.
Defined.

  Lemma rising_factorial_s n k : [k+1!n+1] == #(k+1) * [(k+2) ! n].
  Proof.
    simpl.
    unfold rising_factorial.
    replace (k + 1 + (n+1) - 1)%nat with (S(k + n))%nat by lia.
    replace (k + 1 - 1)%nat with k by lia.
    replace (k + 2 + n- 1)%nat with (S (k + n))%nat by lia.
    replace (k + 2 - 1)%nat with (S k)%nat by lia.
    replace (k +1 )%nat with (S k)%nat by lia.
    enough (![k] == ntimes (S k) 1 * ![S k]) as -> by ring.
    simpl inv_factorial.
    rewrite <-mulA.
    rewrite inv_Sn_spec.
    ring.
  Qed.

  Lemma rising_factorial_s' n k : [k+2!n] == (inv_Sn k) * [(k+1) ! (n+1)].
  Proof.
    simpl.
    unfold rising_factorial.
    replace (k + 1 + (n+1) - 1)%nat with (S(k + n))%nat by lia.
    replace (k + 1 - 1)%nat with k by lia.
    replace (k + 2 + n- 1)%nat with (S (k + n))%nat by lia.
    replace (k + 2 - 1)%nat with (S k)%nat by lia.
    simpl.
    ring.
  Qed.
  Lemma rising_factorial_ks n k : [k+2!n] ==   #(k+n+1) *  inv_Sn k * [(k+1) ! n].
  Proof.
    simpl.
    unfold rising_factorial.
    replace (k + 1 + n - 1)%nat with (k + n)%nat by lia.
    replace (k + 1 - 1)%nat with k by lia.
    replace (k + 2 + n- 1)%nat with (S (k + n))%nat by lia.
    replace (k + 2 - 1)%nat with (S k)%nat by lia.
    replace (k + n + 1)%nat with (S (k + n))%nat by lia.
    simpl.
    ring.
  Qed.
  Lemma rising_factorial_sk n k : [k+1!n] ==   #(k+1) *  inv_Sn (k+n) * [(k+2) ! n].
  Proof.
    simpl.
    unfold rising_factorial.
    replace (k + 1 + n - 1)%nat with (k + n)%nat by lia.
    replace (k + 1 - 1)%nat with k by lia.
    replace (k + 2 + n- 1)%nat with (S (k + n))%nat by lia.
    replace (k + 2 - 1)%nat with (S k)%nat by lia.
    replace (k + 1)%nat with (S k)%nat by lia.
    setoid_replace (#(S k) * inv_Sn (k + n) * ([S (k + n) ]! * ![ S k])) with ([k+n]!*![k] * (#(S (k+n))  * inv_Sn (k+n)) * (#(S k) * inv_Sn k)) by (simpl;ring).
    rewrite !inv_Sn_spec;ring.
  Qed.
  Lemma rising_factorial_sn n k : [S k! S n] ==   #(k+n+1) * [S k ! n].
  Proof.
    simpl.
    unfold rising_factorial.
    replace (S k + S n -1)%nat with (S (k + n))%nat by lia.
    replace (S k + n -1)%nat with (k + n )%nat by lia.
    replace (k+n+1)%nat with (S (k + n) )%nat by lia.
    simpl.
    ring.
  Qed.

  Lemma fact_invfactt {d} (n : nat^d) : t[n]! * t![n] == 1. 
  Proof.
   intros.
   induction d.
   simpl;ring.
   simpl.
   destruct (destruct_tuple_cons n) as [n0 [nt P]].
   setoid_replace (  [n0 ]! * t[ nt ]! * (![ n0] * t![ nt])) with (([n0]! * ![n0]) * (t[nt]! * t![nt])) by ring.
   rewrite fact_invfact.
   rewrite IHd.
   ring.
 Qed.
  Lemma invfact_factt {d} (n : nat^d) : t![n] * t[n]! == 1. 
  Proof.
    rewrite mulC.
    apply fact_invfactt.
  Qed.
  Lemma factt_cons {d} (n0 : nat) (nt : nat^d): factorialt (tuple_cons n0 nt) == (factorial n0 * factorialt nt).
  Proof.
   simpl.
   destruct (destruct_tuple_cons (tuple_cons n0 nt)) as [n0' [nt' P]].
   apply tuple_cons_ext in P.
   destruct P as [-> ->].
   reflexivity.
 Qed.

  Lemma inv_factt_cons {d} (n0 : nat) (nt : nat^d): inv_factorialt (tuple_cons n0 nt) == (inv_factorial n0 * inv_factorialt nt).
  Proof.
   simpl.
   destruct (destruct_tuple_cons (tuple_cons n0 nt)) as [n0' [nt' P]].
   apply tuple_cons_ext in P.
   destruct P as [-> ->].
   reflexivity.
 Qed.

  Lemma factt_S {d} (n0 : nat) (nt : nat^d): factorialt (tuple_cons (S n0) nt) == (#(n0+1) * factorialt (tuple_cons n0 nt)).
  Proof.
   simpl.
   destruct (destruct_tuple_cons (tuple_cons (S n0) nt)) as [n0' [nt' P]].
   destruct (destruct_tuple_cons (tuple_cons n0 nt)) as [n0'' [nt'' P']].
   apply tuple_cons_ext in P.
   apply tuple_cons_ext in P'.
   destruct P as [<- <-].
   destruct P' as [<- <-].
   replace (n0+1)%nat with (S n0) by lia.
   simpl.
   ring.
 Qed.
  Lemma inv_factt_S {d} (n0 : nat) (nt : nat^d): inv_factorialt (tuple_cons (S n0) nt) == (inv_Sn n0 * inv_factorialt (tuple_cons n0 nt)).
  Proof.
   simpl.
   destruct (destruct_tuple_cons (tuple_cons (S n0) nt)) as [n0' [nt' P]].
   destruct (destruct_tuple_cons (tuple_cons n0 nt)) as [n0'' [nt'' P']].
   apply tuple_cons_ext in P.
   apply tuple_cons_ext in P'.
   destruct P as [<- <-].
   destruct P' as [<- <-].
   simpl.
   ring.
 Qed.
  Lemma inv_factt_S_reverse {d} (n0 : nat) (nt : nat^d): #(n0+1) * inv_factorialt (tuple_cons (S n0) nt) ==  inv_factorialt (tuple_cons n0 nt).
  Proof.
  rewrite inv_factt_S.
  rewrite <-mulA.
  replace (n0+1)%nat with (S n0) by lia.
  rewrite inv_Sn_spec.
  ring.
Qed.
 End factorialTheorems.

Section FactorialOrderTheorems.
  Context `{TotallyOrderedField}.
 Context `{normK : (NormedSemiRing A A (H := _)  (H0 := _)  (R_rawRing0 := _) (R_rawRing := _) (R_TotalOrder := R_TotalOrder)) }.
  Context `{invSn : Sn_invertible (A := A) (H := _) (R_rawRing := _)}. (* Replace by proof *)

  Add Ring TRing: (ComSemiRingTheory (A := A)). 
  Lemma ntimes_nonneg x n: (0 <= x) -> 0 <= ntimes n x.
  Proof.
    intros.
    induction n.
    simpl;apply le_refl.
    simpl.
    setoid_replace 0 with (0 + 0) by ring.
    apply le_le_plus_le;auto.
 Qed.
  Lemma fact_pos n : 0 <= [n]!.
  Proof.
    induction n.
    simpl.
    apply le_0_1.
    simpl.
    apply mul_pos_pos;try apply IHn.
    setoid_replace (0 : A) with (0+0 ) by ring.
    apply le_le_plus_le; [apply le_0_1|].
    apply ntimes_nonneg;apply le_0_1.
  Qed.

    
  Lemma inv_Sn_pos n : 0 <= inv_Sn n.
  Proof.
  Admitted.    

  Lemma invfact_pos n : 0 <= ![n].
  Proof.
    induction n.
    simpl.
    apply le_0_1.
    simpl.
    apply mul_pos_pos;try apply IHn.
    apply inv_Sn_pos.
   Qed.
End FactorialOrderTheorems.

Section TupleFactorials.

End TupleFactorials.
