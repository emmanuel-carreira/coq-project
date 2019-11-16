(** 
Projeto em Coq da disciplina de Tópicos Avançados em Engenharia de Software do CIn/UFPE 
Objetivo: provar corretude do Algoritmo RSA
Autores: Emmanuel Carreira Alves
         Lucas Geraldo Cilento
*)

Require Import Notations Logic Datatypes.
Require Import Logic.
Require Import Coq.Init.Nat.
Local Open Scope nat_scope.
Require Setoid.
Require Import PeanoNat Le Gt Minus Bool Lt.

Set Implicit Arguments.
Open Scope list_scope.
(** 
Projeto em Coq da disciplina de Tópicos Avançados em Engenharia de Software do CIn/UFPE 
Objetivo: provar corretude do Algoritmo RSA
Autores: Emmanuel Carreira Alves
         Lucas Geraldo Cilento
**)

(*Require Export definitions.]*)



(*Lemma divide_simetria: forall x : nat, divide x x.

Lemma divide_antisimetria: forall x y : nat, divides x y -> divides y x -> x = y.

Lemma nao_primo_0 : ~ primo 0.

Lemma nao_primo_1 : ~ primo 1.*)

Theorem divide_soma: forall x y z : nat, divide x y = true-> divide x z = true-> divide x (y + z) =true.
Proof.
  intros x y z.
  simpl. intros H. intros H2. simpl. induction y as [O |  n].
  - simpl. rewrite -> H2. reflexivity.
  - simpl. Admitted.
  
Theorem euclides: forall a b c m : nat, divide c (m * a)=true -> divide c (m * b)=true -> divide c (m * gcd a b)=true.
Proof.
  Admitted.
Require Import Coq.omega.Omega.
Lemma potencia_mult: forall x n m : nat,  (x ^ n) * (x ^ m) =  x  ^ (n + m).
Proof.
  intros. auto. simpl. induction n as [O | n'].
  - auto. simpl. auto.
  - simpl. rewrite <- IHn'. Admitted.

Lemma potencia_de_potencia: forall x n m : nat, (x ^n)^m =  x^ (n * m).
Proof.
  intros. simpl. induction n as [O | n'].
  - simpl. Admitted.
Theorem  totienteNumeroPrimo: forall x : nat, verificaPrimo x = true-> totiente x = x - 1.
Proof.
intros. unfold totiente. destruct verificaCoPrimos.
  - auto.
  - auto.
  - Admitted.
Theorem moduloPotencia: forall e m n: nat,e mod n = 1 -> m^(e) mod n = m.
Proof.
intros. Admitted.
(*Theorem divide_congruencia : forall x : nat, divide n x -> congruent 0 x.

Theorem existeInversoModular: forall e t: nat, gcd e t = 1 ->