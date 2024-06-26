(* StrVList.v *)
(* This file defines a string-value list, which is a list of pairs of strings and values. *)
(* This is essentially an ordered map, where the keys are strings. *)
Require Import String List.
Export String List ListNotations.

(* A string-value list is a list of pairs of strings and values. *)
Definition svlist (B : Type) := list (string * B).

(* Check presence of a key in a string-value list. *)
Definition in_svlist {B : Type} (k : string) (l : svlist B) : Prop :=
  List.In k (map fst l).

(* Number of entries in a string-value list. *)
Definition svlist_length {B : Type} (l : svlist B) : nat :=
  List.length l.

(* Check if string-value list has no duplicate keys. *)
Definition distinct_keys {B : Type} (l : svlist B) : Prop :=
  List.NoDup (List.map fst l).

(* Find (first) value of a key in a string-value list. *)
Definition find_svlist {B : Type} (k : string) (l : svlist B) : option B :=
  match List.filter (fun p => if (String.eqb (fst p) k) then true else false) l with
  | [] => None
  | (x, y) :: _ => Some y
  end.

(* Add a key-value pair to a string-value list. *)
Definition add_svlist {B : Type} (k : string) (v : B) (l : svlist B) : svlist B :=
  (k, v) :: l.

(* Lemma: if a key is not in a string-value list, then adding it will to a string-value list
   with distinct keys will result in a string-value list with distinct keys. *)
Lemma add_distinct_keys {B : Type} (k : string) (v : B) (l : svlist B) :
  ~ in_svlist k l -> distinct_keys l -> distinct_keys (add_svlist k v l).
Proof.
  intros H1 H2.
  unfold distinct_keys in *.
  unfold in_svlist in H1.
  unfold add_svlist.
  rewrite List.map_cons.
  simpl.
  apply List.NoDup_cons; assumption.
Qed.
