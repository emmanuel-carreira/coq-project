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

Fixpoint verificaCoPrimos (n1 n2: nat) : bool :=
  match n1 , n2 with
  | 0 , _ => false
  | 1 , _ => false
  | _ , 0 => false
  | _ , 1 => false
  | _ , _ => match gcd n1 n2 with
             | 1 => true
             | _ => false
             end
  end.

Fixpoint criaListaNumerica (n: nat): list nat :=
  match n with
  | O => nil
  | 1 => nil
  | S n' => S n' :: criaListaNumerica n' 
  end.

(*Fixpoint verificaListaCoPrimos (n : nat) (l : list nat) :  bool :=
  match l with
  | nil => true
  | h :: t => match verificaCoPrimos n h  with
              | false => false
              | true => verificaListaCoPrimos n t
              end
  end.
 
Fixpoint is_prime (n: nat) : bool :=
  match n with
  | O => false
  | 1 => false
  | _ => verificaListaCoPrimos n (criaListaNumerica (sqrt n))
  end.*)


Fixpoint verificaListaCoPrimos (n : nat) (l : list nat) : list bool :=
  match l with
  | nil => nil
  | h :: t =>  match n =? h with
               | true => true :: verificaListaCoPrimos n t
               | false => verificaCoPrimos n h ::  verificaListaCoPrimos n t
               end
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
  | _ => fold_bool  (verificaListaCoPrimos n (criaListaNumerica (sqrt n)))
  end.

Fixpoint totiente (n : nat)  : nat :=
  length ( filter_bool (verificaListaCoPrimos n (criaListaNumerica n)) true). 

