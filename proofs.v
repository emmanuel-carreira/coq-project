
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
Require Import ZArith_base.
Require Import ZArithRing.
Require Import Zcomplements.
Require Import Zdiv.
Require Import Wf_nat.
Require Import Omega.


(*Lemma divide_simetria: forall x : nat, divide x x.

Lemma divide_antisimetria: forall x y : nat, divides x y -> divides y x -> x = y.

Lemma nao_primo_0 : ~ primo 0.

Lemma nao_primo_1 : ~ primo 1.*)

Axiom totientePrimo : forall x : nat, verificaPrimo x = true -> totiente x = x -1.

Theorem divide_soma: forall x y z : nat, divide x y -> divide x z -> divide x (y + z) .
Proof.
  intros x y z.
  simpl. intros H. intros H2. simpl. induction y as [O |  n].
  - simpl. apply H2. 
  -  Admitted.
  
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

Lemma potencia_mult: forall x n m : nat,  (x ^ n) * (x ^ m) =  x  ^ (n + m).
Proof.
  intros. auto. simpl. induction n as [O | n'].
  - auto. simpl. auto.
  - simpl. rewrite <- IHn'. intuition.
Qed. 

Lemma pow_0_n: forall n :nat, n > 0 -> 0 ^ n = 0.
Proof.
intros n. induction n.
  - intuition.
  - intuition.
Qed.


Lemma potencia_de_potencia: forall x n m : nat, (x ^ n) ^ m =  x ^ (n * m).
Proof.
  intros. simpl. induction n as [O | n'].
  - simpl. rewrite -> pow_1_l. reflexivity.
  - simpl. rewrite -> aXaton. rewrite -> n_plus_mXn. rewrite -> mult_comm.
    induction m.
    + rewrite -> mult_comm. rewrite -> pow_n_0. rewrite -> mult_plus_distr_l. simpl. reflexivity.
    +simpl. rewrite <- mult_comm. intuition. rewrite <- mult_plus_distr_l.
Theorem  totienteNumeroPrimo: forall x : nat, verificaPrimo x = true-> totiente x = x - 1.
Proof.
intros. unfold totiente. destruct verificaCoPrimos.
  - auto.
  - auto.
  - Admitted.
Theorem  a_divide_b: forall a b : nat, b mod a = 0 -> divide a b = true.
Proof.
intros a b.  unfold divide. destruct divide.
  - auto.
  - induction b.  
    + simpl. Admitted.
    