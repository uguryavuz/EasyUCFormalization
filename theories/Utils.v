(* Utils.v *)
(* Utilities *)
Require Import String.
Require Import FMapList FMapFacts FSetList.
Require Import OrderedTypeEx.

(* Finite maps from strings to types *)
Module StrMap := FMapList.Make(String_as_OT). 
Module StrMapFacts := FMapFacts.Facts(StrMap).

(* Syntactic sugar for StrMap *)
Notation "[ x |-> y ]" := (StrMap.add x y (StrMap.empty _)) (at level 60).
Notation "m + [ x |-> y ]" := (StrMap.add x y m) (at level 50, right associativity).

(* Finite sets of strings *)
Module StrSet := FSetList.Make(String_as_OT).

(* Custom ordered type for string + string 
  - Heavily relies on the OrderedTypeEx.String_as_OT module
  - use t_left str and t_right str to create a 
    a key of type t from a string str *)
Module SumString_as_OT <: UsualOrderedType.

  Definition t := sum string string.
  Definition eq := @eq (sum string string).
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  (* Note that every left string is less than every right string *)
  Definition lt (ss1 ss2 : t) : Prop :=
    match ss1, ss2 with
    | inl s1, inl s2 => String_as_OT.lts s1 s2
    | inr s1, inr s2 => String_as_OT.lts s1 s2
    | inl _, inr _ => True
    | inr _, inl _ => False
    end.

  (* Transitivity of the lt relation *)
  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros x y z H1 H2.
    destruct x as [x1 | x2], y as [y1 | y2], z as [z1 | z2]; 
      try contradiction; unfold lt in *; trivial.
    - apply String_as_OT.lt_trans with (y := y1); assumption.
    - apply String_as_OT.lt_trans with (y := y2); assumption.
  Qed.

  (* lt implies not equal *)
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros x y H1 H2.
    destruct x as [x1 | x2], y as [y1 | y2]; try contradiction; 
      unfold lt in *; inversion H2; apply String_as_OT.lt_not_eq in H1; contradiction.
  Qed.

  (* Comparison function *)
  Definition cmp : t -> t -> comparison :=
    fun ss1 ss2 =>
      match ss1, ss2 with
      | inl s1, inl s2 => String_as_OT.cmp s1 s2
      | inr s1, inr s2 => String_as_OT.cmp s1 s2
      | inl _, inr _ => Lt
      | inr _, inl _ => Gt
      end.

  Lemma cmp_eq (a b : t):
    cmp a b = Eq  <->  a = b.
  Proof.
    destruct a as [a1 | a2], b as [b1 | b2]; cbn; try easy.
    - split; intro H; try discriminate.
      + apply String_as_OT.cmp_eq in H. now subst.
      + inversion H; subst. now rewrite String_as_OT.cmp_eq.
    - split; intro H; try discriminate.
      + apply String_as_OT.cmp_eq in H. now subst.
      + inversion H; subst. now rewrite String_as_OT.cmp_eq.
  Qed.

  (* Antisymmetry of the comparison function *)
  Lemma cmp_antisym (a b : t):
    cmp a b = CompOpp (cmp b a).
  Proof.
    destruct a as [a1 | a2], b as [b1 | b2]; cbn; try easy.
    - apply String_as_OT.cmp_antisym.
    - apply String_as_OT.cmp_antisym.
  Qed.

  Lemma cmp_lt (a b : t):
    cmp a b = Lt  <->  lt a b.
  Proof.
    destruct a as [a1 | a2], b as [b1 | b2]; cbn; try easy.
    - split; intro H; try discriminate.
      + apply String_as_OT.cmp_lt in H. now subst.
      + inversion H; subst; now rewrite String_as_OT.cmp_lt.
    - split; intro H; try discriminate.
      + apply String_as_OT.cmp_lt in H. now subst.
      + inversion H; subst; now rewrite String_as_OT.cmp_lt.
  Qed.

  Local Lemma compare_helper_lt {a b : t} (L : cmp a b = Lt):
    lt a b.
  Proof.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_gt {a b : t} (G : cmp a b = Gt):
    lt b a.
  Proof.
    rewrite cmp_antisym in G.
    rewrite CompOpp_iff in G.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_eq {a b : t} (E : cmp a b = Eq):
    a = b.
  Proof.
    now apply cmp_eq.
  Qed.

  Definition compare (a b : t) : Compare lt eq a b :=
    match cmp a b as z return _ = z -> _ with
    | Lt => fun E => LT (compare_helper_lt E)
    | Gt => fun E => GT (compare_helper_gt E)
    | Eq => fun E => EQ (compare_helper_eq E)
    end Logic.eq_refl.

  Definition eq_dec (x y : t): {x = y} + { ~ (x = y)}.
  Proof.
    destruct x as [x1 | x2], y as [y1 | y2].
    - destruct (String_as_OT.eq_dec x1 y1) as [E1 | NE1].
      + subst. left. reflexivity.
      + right. intro H. inversion H. contradiction.
    - right. congruence.
    - right. congruence.
    - destruct (String_as_OT.eq_dec x2 y2) as [E2 | NE2].
      + subst. left. reflexivity.
      + right. congruence.
  Defined.

End SumString_as_OT.

(* Finite maps from string + string to types *)
Module SumStrMap.
  Include FMapList.Make(SumString_as_OT).
  Definition str_to_left_key (s : string) : key := inl s.
  Definition str_to_right_key (s : string) : key := inr s.
End SumStrMap.

(* Syntactic sugar for SumStrMap *)
Notation "[ x |->l y ]" := (SumStrMap.add (SumStrMap.str_to_left_key x) y (SumStrMap.empty _)) (at level 60).
Notation "[ x |->r y ]" := (SumStrMap.add (SumStrMap.str_to_right_key x) y (SumStrMap.empty _)) (at level 60).
Notation "m + [ x |->l y ]" := (SumStrMap.add (SumStrMap.str_to_left_key x) y m) (at level 50, right associativity).
Notation "m + [ x |->r y ]" := (SumStrMap.add (SumStrMap.str_to_right_key x) y m) (at level 50, right associativity). 

(* Finite sets of string + string *)
Module SumStrSet := FSetList.Make(SumString_as_OT).
