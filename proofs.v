
(** 
Projeto em Coq da disciplina de Tópicos Avançados em Engenharia de Software do CIn/UFPE 
Objetivo: provar corretude do Algoritmo RSA
Autores: Emmanuel Carreira Alves
         Lucas Geraldo Cilento
**)

Require Export definitions.

Require Import Notations Logic Datatypes.
Require Import Logic.
Require Import Coq.Init.Nat.
Local Open Scope nat_scope.
Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.
Require Import NZAxioms NZMulOrder Bool NAxioms NSub NParity NZPow.
Require Import Wf_nat.
Require Import Omega.
Require Import  NProperties OrdersFacts.

Module Nat
 <: NAxiomsSig
 <: UsualDecidableTypeFull
 <: OrderedTypeFull
 <: TotalOrder.

(*Lemma divide_simetria: forall x : nat, divide x x.

Lemma divide_antisimetria: forall x y : nat, divides x y -> divides y x -> x = y.

Lemma nao_primo_0 : ~ primo 0.

Lemma nao_primo_1 : ~ primo 1.*)

Axiom totientePrimo : forall x : nat, verificaPrimo x = true -> totiente x = x -1.

Axiom totienteMult : forall x y: nat, totiente (x*y) = (totiente x) * (totiente y).

Axiom mod0eqdiv: forall x y: nat, y mod x = 0-> divide x y.

Axiom dividePred: forall x y: nat, (y -1 ) mod x =0 -> 1 = y mod x.

Axiom dividePred2: forall x y: nat, 1 = y mod x -> (y -1 ) mod x =0.

Axiom swapMod: forall x y: nat, y > 1 ->1 =  y mod x  -> y = 1 mod x.

Axiom pot_pot: forall  m e n d : nat , (m ^ e mod n) ^ d mod n = (m ^(e * d)) mod n.

Axiom o_mod_n: forall n : nat,  0 mod n = 0.

Axiom mod_dist: forall a b c : nat, a*b mod c = (a mod c) * (b mod c).

Axiom mod__: forall a b  : nat, a < b -> a mod b = a.

Axiom pow_n_1: forall n: nat, n ^ 1 = n.

Axiom Euler_exp_totient: forall a n :nat , verificaCoPrimos a n = true -> a ^ totiente n  = 1 mod n.

Theorem euclides: forall a b c m : nat, divide c (m * a) -> divide c (m * b)-> divide c (m * gcd a b).
Proof.
intros.
  Admitted.

Theorem pow_1_l: forall n : nat, 1 ^ n = 1.
Proof.
  intros.
  induction n.
  - auto.
  - simpl. rewrite -> IHn. auto.
 Qed.
Theorem pow_n_0: forall n : nat, n ^ 0 = 1.
Proof.
  intros. intuition.
 Qed.

Theorem aXaton: forall n a: nat, a *(a ^ n) = a  ^ (n + 1).
Proof.
  intros.
  induction n.
  - auto.
  - simpl. rewrite -> IHn. auto.
 Qed.
Theorem nX0: forall n : nat, 0*n = 0.
Proof.
  intros. auto.
Qed.
Theorem oXn: forall n : nat, n*0 = 0.
Proof.
  intros. auto.
Qed.
Theorem nX1: forall n : nat, n *1 = n.
Proof.
  intros. intuition.
Qed.
Theorem add_commutative: forall n m : nat, n + m = m + n.
Proof.
  intros. intuition.
Qed.
Lemma mult_plus_distr_l : forall n m p, n * (m + p) = n * m + n * p.
Proof.
  induction n. trivial.
  intros. simpl in |- *. rewrite (IHn m p). apply sym_eq. apply plus_permute_2_in_4.
Qed.
Theorem n_plus_nXm: forall n m : nat, n + n*m = n*(m + 1).
Proof.
  intros. induction n.
  - intuition.
  - induction m.
    + intuition. 
    + rewrite -> mult_plus_distr_l. intuition. 
Qed. 
Lemma mult_assoc_reverse : forall n m p, n * m * p = n * (m * p).
Proof.
  intros; elim n; intros; simpl in |- *; auto with arith.
  rewrite mult_plus_distr_r.
  elim H; auto with arith.
Qed.
Lemma mult_comm : forall n m, n * m = m * n.
Proof.
intros; elim n; intros; simpl in |- *; auto with arith.
elim mult_n_Sm.
elim H; apply plus_comm.
Qed.

Theorem n_plus_mXn: forall n m : nat, n + m*n = n*(m + 1).
Proof.
  intros. induction n.
  - intuition.
  - induction m.
    + intuition. 
    + rewrite -> mult_plus_distr_l. rewrite -> nX1. rewrite -> add_commutative.
     rewrite <- mult_comm. auto.
Qed. 
Lemma pow_0_n: forall n :nat, n > 0 -> 0 ^ n = 0.
Proof.
intros n. induction n.
  - intuition.
  - intuition.
Qed.



Lemma potencia_mult: forall x n m : nat,  (x ^ n) * (x ^ m) =  x  ^ (n + m).
Proof.
  intros. auto. simpl. induction n as [O | n'].
  - auto. simpl. auto.
  - simpl. rewrite <- IHn'. intuition.
Qed.

Theorem divide_soma: forall x y z : nat, divide x y -> divide x z -> divide x (y + z) .
Proof.
  intros x y z.
  simpl. intros H. intros H2. simpl. induction y as [O |  n].
  - simpl. apply H2. 
  - simpl. induction z.
    + simpl. rewrite -> add_commutative. simpl. apply H.
    + simpl.  Admitted.
Lemma mod_1_l: forall a, 1<a -> 1 mod a = 1.
Proof.
intros. simpl. Admitted.


Lemma potencia_de_potencia: forall x n m : nat, (x ^ n) ^ m =  x ^ (n * m).
Proof.
  intros. simpl. induction n as [O | n'].
  - simpl. rewrite -> pow_1_l. reflexivity.
  - simpl. rewrite -> aXaton. rewrite -> n_plus_mXn. rewrite -> mult_comm.
    induction m.
    + rewrite -> mult_comm. rewrite -> pow_n_0. rewrite -> mult_plus_distr_l. simpl. reflexivity.
    +simpl. rewrite <- mult_comm. intuition. Admitted.


Theorem  totienteN: forall p q : nat, verificaPrimo p = true /\ verificaPrimo q = true-> totiente (p*q) =  (p - 1)*(q - 1).
Proof.
intros. rewrite -> totienteMult. inversion H. apply totientePrimo in H0.
  apply totientePrimo in H1. rewrite -> H0. rewrite -> H1. reflexivity.
Qed.

Theorem  aux: forall p : nat, p > 1-> p = (p -1) +1.

Proof.
intros. induction p.
  - simpl. intuition.
  - simpl. intuition.
Qed.

Theorem mult_gt_1: forall a b : nat, a > 1 -> b > 1 -> a*b > 1.
Proof.
intros.
induction a.
  -simpl. exfalso. intuition.
  - induction b.
    + simpl. rewrite -> oXn. exfalso. intuition.
    + unfold mult. intuition.
Qed.

Theorem  aux2: forall p q : nat, p > 1 -> q > 1-> p*q = (p*q -1) +1.
Proof.
intros.  rewrite <- aux.  reflexivity. induction p.
  - simpl. exfalso. intuition.
  - inversion H.  
    + intuition.
    + unfold mult. intuition.  

Qed.


  
Theorem mod_dist2: forall a b c : nat, a*b mod c = (a mod c) * (b mod c).
Proof.
intros.
  induction a.
  - simpl. rewrite -> o_mod_n. simpl. reflexivity.
  - simpl. induction b.
    + simpl. rewrite -> o_mod_n. rewrite -> oXn. rewrite -> o_mod_n. rewrite -> oXn. reflexivity.
    + unfold mult.  intuition. Admitted. 

Definition divide x y := exists z, y=z*x.
Notation "( x | y )" := (divide x y) (at level 0) : nat_scope.

Axiom exists_multiple: forall a b: nat, a mod b = 0 <> exists c, a = b*c.

Axiom exists_multiple2: forall a b: nat, a mod b = 0 -> divide b a.


Theorem cifraDecifra: forall m c e d p q n a b, e > 1 -> d > 1 -> a = e*d -> b = totiente n-> n = p*q -> 1 = e*d mod (totiente n) -> a >1-> c = encriptaNumero m n e -> m < n -> decriptaNumero c n d = m.
Proof.
intros. unfold decriptaNumero. rewrite -> H6. unfold encriptaNumero. rewrite -> pot_pot. rewrite -> aux2. rewrite <- H1. rewrite <- potencia_mult.  
  - rewrite -> mod_dist.  rewrite <- H1 in H4. rewrite -> pow_n_1.  rewrite -> mult_comm. rewrite -> mod__. apply dividePred2 in H4. rewrite <- H2 in H4.
  apply exists_multiple2 in H4. unfold divide in H4.
  destruct H4 as [z]. rewrite H4.
     