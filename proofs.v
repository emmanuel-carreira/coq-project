(** 
Projeto em Coq da disciplina de Tópicos Avançados em Engenharia de Software do CIn/UFPE 
Objetivo: provar corretude do Algoritmo RSA
Autores: Emmanuel Carreira Alves
         Lucas Geraldo Cilento
*)

Require Exports definitions.

Check primo 2 1.
Check primo 13 12.
Check primo 4 3.

Lemma divide_simetria: forall x : nat, divide x x.

Lemma divide_antisimetria: forall x y : nat, divides x y -> divides y x -> x = y.

Lemma nao_primo_0 : ~ primo 0.

Lemma nao_primo_1 : ~ primo 1.

Theorem divide_soma: forall x y z : nat, divide x y -> divide x z -> divide x (y + z).

Theorem euclides: forall a b c m : nat, divide c (m * a) -> divide c (m * b) -> divide c (m * gcd a b).

Lemma potencia_mult: forall x n m : nat, power x n * power x m = power x (n + m).

Lemma potencia_de_potencia: forall x n m : nat, power (power x n) m = power x (n * m).

Theorem divide_congruencia : forall x : nat, divide n x -> congruent 0 x.

(*Theorem existeInversoModular: forall e t: nat, gcd e t = 1 ->