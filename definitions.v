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
Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End ListNotations.

Import ListNotations.
Import ZArith.

Fixpoint verificaCoPrimos (n1 n2: nat) : bool :=
   match gcd n1 n2 with
     | 1 => true
     | _ => false
     end.

Fixpoint criaListaNumericaSemZero (n: nat): list nat :=
  match n with
  | O => nil
  | S n' => S n' :: criaListaNumericaSemZero n' 
  end.

Fixpoint verificaListaCoPrimos (n : nat) (l : list nat) : list bool :=
  match l with
  | nil => nil
  | h :: t =>  verificaCoPrimos n h ::  verificaListaCoPrimos n t
  end.

Fixpoint fold_bool (l:list bool) : bool :=
  match l with
    | nil => true
    | h :: t => h && fold_bool t 
  end.

Fixpoint filter_bool (l:list bool) (b: bool) : list bool :=
  match l with
  | nil => nil
  | h :: t => match eqb h b with
              | true => h :: filter_bool t b
              | false => filter_bool t b
              end
  end.
  
Fixpoint verificaPrimo (n: nat) : bool :=
  match n with
  | O => false
  | 1 => false
  | _ => fold_bool  (verificaListaCoPrimos n (criaListaNumericaSemZero (sqrt n)))
  end.

Fixpoint totiente (n : nat)  : nat :=
  length ( filter_bool (verificaListaCoPrimos n (criaListaNumericaSemZero (n - 1))) true). 

Check (3,4).

Fixpoint determinaE (n index : nat) : nat := 
  match  index with
  | O => O
  | 1 => O
  | S n' => match verificaCoPrimos n (S n') with
            | true => S n'
            | false => determinaE n n'
            end
   end.


Fixpoint constroiChavePublica (n : nat) : nat*nat :=
  (n,determinaE (totiente n) (sqrt n)).

Inductive divide : nat -> nat -> Prop :=
  divide : forall x y q : nat, y = x * q -> divide x y.

Fixpoint fatorial (n : nat) : nat.

Fixpoint potencia (x n : nat) : nat.

(*
x é o número a ter sua primalidade verificada
y é o número da iteração corrente
Na chamada da função, y deve ser o antecessor de x
*)
Fixpoint primo (x y : nat) : bool :=
  match x, y with
  | 0, _ => false
  | 1, _ => false
  | S x', 0 => false
  | S x', 1 => true
  | S x', S y' => if divide y x
                  then false
                  else primo x y'
  end.

Definition divisao (n m q r : nat) : Prop := r < m /\ n = q * m + r.

Inductive congruente : nat -> nat -> Prop.