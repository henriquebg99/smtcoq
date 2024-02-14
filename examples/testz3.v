(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2022                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* [Require Import SMTCoq.SMTCoq.] loads the SMTCoq library.
   If you are using native-coq instead of Coq 8.11, replace it with:
     Require Import SMTCoq.
   *)
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Coq.Lists.List.

(* Goal match 0 with 0 => False | S n => True end.
Proof. print_type. *)

Goal forall A (l1: list A) l2, l1 ++ l2 = nil -> forall l3, l3 = l2 -> l3 = nil.
z3.
(*Goal forall A (l1: list A) l2, l1 ++ l2 = nil -> l1 = nil /\ l2 = nil.
Proof. z3.
Admitted.*)