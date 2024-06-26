(* Utils.v *)
(* Utilities *)
From Coq Require Import Strings.String.
From Coq Require Import FSets.FMapList.
From Coq Require Import FSets.FMapFacts.
From Coq Require Import Structures.OrderedTypeEx.
Import ListNotations.
Open Scope string_scope.

(* Finite maps from strings to types *)
Module Import StrMap := FMapList.Make(String_as_OT). 
Module StrMapFacts := FMapFacts.Facts(StrMap).

(* Synactic sugar for finite maps *)
Notation "[ x |-> y ]" := (StrMap.add x y (StrMap.empty _)) (at level 60).
Notation "m + [ x |-> y ]" := (StrMap.add x y m) (at level 50, right associativity).

