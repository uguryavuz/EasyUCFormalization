(* NonProbTerms.v *)
(* Non-probabilistic terms *)
Require Import String ZArith.
From EasyUCFormalization Require Import Utils.

(* Ground types *)
Inductive ty : Type :=
  | Ty_Int : ty
  | Ty_Bool : ty
  | Ty_List : ty -> ty
  | Ty_Prod : list ty -> ty
  | Ty_Option : ty -> ty.

(* Operator type *)
Inductive opty : Type :=
  | Ty_Op : list ty -> ty -> opty.

(* Values: these are the terms that are not reducible *)
Inductive val : Type :=
  | Val_Int : Z -> val
  | Val_True : val
  | Val_False : val
  | Val_Prod : list val -> val
  | Val_Nil : ty -> val (* Note that empty list is also typed *)
  | Val_Cons : val -> val -> val
  | Val_None : ty -> val (* Note that None is also typed *)
  | Val_Some : val -> val.

(* Environments *)
(*  - opty_env  : maps operator names to their types *)
(*  - op_env    : maps operator names to their semantics,                *)
(*                i.e. the relation relating its list of argument values *)
(*                to its result                                          *)
(*  - varty_env : maps variable names to their types *)
(*  - var_env   : maps variable names to their values *)
Record env : Type :=
  { opty_env : StrMap.t opty;
    op_env : StrMap.t (list val -> val -> Prop); (* Note that this can be non-deterministic *)
    varty_env : StrMap.t ty;
    var_env : StrMap.t val }.

(* Typing on values *)
Inductive val_has_type : val -> ty -> Prop := 
  (* (Val_Int i) has type Ty_Int *)
  | ValHasTy_Int : forall (i : Z),
    val_has_type (Val_Int i) Ty_Int
  (* Val_True has type Ty_Bool *)
  | ValHasTy_True : val_has_type Val_True Ty_Bool
  (* Val_False has type Ty_Bool *)
  | ValHasTy_False : val_has_type Val_False Ty_Bool
  (* (Val_Prod nil) has type (Ty_Prod nil) *)
  | ValHasTy_Prod_Empty : val_has_type (Val_Prod nil) (Ty_Prod nil)
  (* (Val_Prod (v :: vl)) has type (Ty_Prod (hty :: ttl)) *) 
  (* if v has type hty *)
  (* and (Val_Prod vl) has type (Ty_Prod ttl) *)
  | ValHasTy_Prod_NonEmpty : forall (v : val) (hty : ty) (vl : list val) (ttl : list ty),
    val_has_type v hty ->
    val_has_type (Val_Prod vl) (Ty_Prod ttl) ->
    val_has_type (Val_Prod (v :: vl)) (Ty_Prod (hty :: ttl))
  (* (Val_Nil ty) has type (Ty_List ty) *)
  | ValHasTy_Nil : forall (ty : ty),
    val_has_type (Val_Nil ty) (Ty_List ty)
  (* (Val_Cons v1 v2) has type (Ty_List ty) *)
  (* if v1 has type ty *)
  (* and v2 has type (Ty_List ty) *)
  | ValHasTy_Cons : forall (v1 v2 : val) (ty : ty),
    val_has_type v1 ty ->
    val_has_type v2 (Ty_List ty) ->
    val_has_type (Val_Cons v1 v2) (Ty_List ty)
  (* (Val_None ty) has type (Ty_Option ty) *)
  | ValHasTy_None : forall (ty : ty),
    val_has_type (Val_None ty) (Ty_Option ty)
  (* (Val_Some v) has type (Ty_Option ty) *)
  | ValHasTy_Some : forall (v : val) (ty : ty),
    val_has_type v ty ->
    val_has_type (Val_Some v) (Ty_Option ty).

(* Terms *)
Inductive tm : Type :=
  | Tm_Int : Z -> tm
  | Tm_True : tm
  | Tm_False : tm
  | Tm_Prod : list tm -> tm
  | Tm_Nil : ty -> tm
  | Tm_Cons : tm -> tm -> tm 
  | Tm_None : ty -> tm
  | Tm_Some : tm -> tm
  (* Operator application - an operator name and a list of terms *)
  | Tm_Op : string -> list tm -> tm
  (* Variable *)
  | Tm_Var : string -> tm.

(* Typing relation *)                                                   
(* Takes a term and a type and returns a Prop.                 *)
(* This is the extrinsic approach.                             *)
(* For typing of operators, it performs a look-up in opty_env. *)    
Inductive tm_has_type (env : env) : tm -> ty -> Prop :=
  (* Integers *)
  | TmHasTy_Int : forall (i : Z), tm_has_type env (Tm_Int i) Ty_Int
  (* Booleans *)
  | TmHasTy_True : tm_has_type env Tm_True Ty_Bool
  | TmHasTy_False : tm_has_type env Tm_False Ty_Bool
  (* Products *)
  | TmHasTy_Prod_Empty : tm_has_type env (Tm_Prod nil) (Ty_Prod nil)
  | TmHasTy_Prod_NonEmpty : forall (htm : tm) (ttm : list tm) (hty : ty) (tty : list ty),
    tm_has_type env htm hty ->
    tm_has_type env (Tm_Prod ttm) (Ty_Prod tty) ->
    tm_has_type env (Tm_Prod (htm :: ttm)) (Ty_Prod (hty :: tty))
  (* Lists *)
  | TmHasTy_Nil : forall (ty : ty), tm_has_type env (Tm_Nil ty) (Ty_List ty)
  | TmHasTy_Cons : forall (htm : tm) (ttm : tm) (ty : ty),
    tm_has_type env htm ty ->
    tm_has_type env ttm (Ty_List ty) ->
    tm_has_type env (Tm_Cons htm ttm) (Ty_List ty)
  (* Options *)
  | TmHasTy_None : forall (ty : ty), tm_has_type env (Tm_None ty) (Ty_Option ty)
  | TmHasTy_Some : forall (stm : tm) (ty : ty),
    tm_has_type env stm ty ->
    tm_has_type env (Tm_Some stm) (Ty_Option ty)
  (* Operator *)
  | TmHasTy_Op : forall (op : string) (ltm : list tm) (lty : list ty) (ty : ty),
    StrMap.MapsTo op (Ty_Op lty ty) env.(opty_env) ->
    tm_has_type env (Tm_Prod ltm) (Ty_Prod lty) ->
    tm_has_type env (Tm_Op op ltm) ty
  (* Variables *)
  | TmHasTy_Var : forall (x : string) (ty : ty),
    StrMap.MapsTo x ty env.(varty_env) ->
    tm_has_type env (Tm_Var x) ty.

(* Theorem: any typed term has a unique type *)
Theorem tm_has_unique_type : forall (env : env) (t : tm) (ty1 ty2 : ty),
  tm_has_type env t ty1 -> tm_has_type env t ty2 -> ty1 = ty2.
Proof.
  intros env t ty1 ty2 H1.
  generalize dependent ty2.
  induction H1; intros ty2 H2; inversion H2; try trivial; auto.
  - subst.
    apply IHtm_has_type1 in H1.
    apply IHtm_has_type2 in H4.
    inversion H4.
    apply f_equal.
    rewrite H1.
    trivial.
  - subst.
    apply f_equal.
    apply IHtm_has_type.
    assumption.
  - subst.
    apply StrMap.find_1 in H, H4.
    rewrite H in H4.
    inversion H4.
    trivial.
  - subst. 
    apply StrMapFacts.MapsTo_fun 
      with (x:=x) (e:=ty2) (m:=env.(varty_env)) in H; auto.
Qed.

(* Evaluation relation - big step semantics *)
Inductive eval (env : env) : tm -> val -> Prop :=
  (* Integers *)
  | Eval_Int : forall (i : Z), 
    eval env (Tm_Int i) (Val_Int i)
  (* Booleans *)
  | Eval_True : eval env Tm_True Val_True
  | Eval_False : eval env Tm_False Val_False
  (* Products *)
  | Eval_Prod_Empty : eval env (Tm_Prod nil) (Val_Prod nil)
  | Eval_Prod_NonEmpty : forall (ht : tm) (tt : list tm) (hv : val) (tv : list val),
    eval env ht hv ->
    eval env (Tm_Prod tt) (Val_Prod tv) ->
    eval env (Tm_Prod (ht :: tt)) (Val_Prod (hv :: tv))
  (* Lists *)
  | Eval_Nil : forall (ty : ty), 
    eval env (Tm_Nil ty) (Val_Nil ty)
  | Eval_Cons : forall (ht tt : tm) (hv tv : val),
    eval env ht hv ->
    eval env tt tv ->
    eval env (Tm_Cons ht tt) (Val_Cons hv tv)
  (* Options *)
  | Eval_None : forall (ty : ty),
    eval env (Tm_None ty) (Val_None ty)
  | Eval_Some : forall (t : tm) (v : val),
    eval env t v ->
    eval env (Tm_Some t) (Val_Some v)
  (* Operator *)
  | Eval_Op : forall (op : string) (ltm : list tm) (lval : list val) 
                     (rval : val) (f : list val -> val -> Prop),
    StrMap.MapsTo op f env.(op_env) ->
    f lval rval ->
    eval env (Tm_Prod ltm) (Val_Prod lval) ->
    eval env (Tm_Op op ltm) rval
  | (* Variable *)
    Eval_Var : forall (x : string) (v : val),
    StrMap.MapsTo x v env.(var_env) ->
    eval env (Tm_Var x) v.

(* Type consistence for op_env and opty_env *)
(* If an operator is typed in opty_env, then its semantics in op_env *)
(* must be consistent with the types in opty_env.                    *)
Definition type_consistence_across_op_envs (env : env) : Prop :=
  forall (k : string) (lty : list ty) (rty : ty) (f : list val -> val -> Prop) (lval: list val),
  StrMap.MapsTo k (Ty_Op lty rty) env.(opty_env) ->
  StrMap.MapsTo k f env.(op_env) ->
  val_has_type (Val_Prod lval) (Ty_Prod lty) ->
  (forall (rval : val), f lval rval -> val_has_type rval rty).

(* Type consistence for var_env and varty_env *)
(* If a variable is typed in varty_env, then its value in var_env *)
(* must be consistent with the type in varty_env.                 *)
Definition type_consistence_across_var_envs (env : env) : Prop :=
  forall (x : string) (ty : ty) (v : val),
  StrMap.MapsTo x ty env.(varty_env) ->
  StrMap.MapsTo x v env.(var_env) ->
  val_has_type v ty.

(* Evaluability of operators *)
(* An operator in op_env must be evaluable, in that when given a list of values *)
(* that are typed according to the operator's type in opty_env,                 *)
(* there must be a value that the operator can evaluate to.                     *)
Definition evaluability_of_operators (env : env) : Prop :=
  forall (k : string) (lty : list ty) (rty : ty) (f : list val -> val -> Prop) (lval: list val),
  StrMap.MapsTo k (Ty_Op lty rty) env.(opty_env) ->
  StrMap.MapsTo k f env.(op_env) ->
  val_has_type (Val_Prod lval) (Ty_Prod lty) ->
  exists (rval : val), f lval rval.

(* Identifier agreement for op_env and opty_env *)
(* The set of identifiers in opty_env and op_env must be the same. *)
Definition id_agreement_across_op_envs (env : env) : Prop :=
  forall (k : string), StrMap.In k env.(opty_env) = StrMap.In k env.(op_env).

(* Identifier agreement for var_env and varty_env *)
(* The set of identifiers in varty_env and var_env must be the same. *)
Definition id_agreement_across_var_envs (env : env) : Prop :=
  forall (x : string), StrMap.In x env.(varty_env) = StrMap.In x env.(var_env).

(* Theorem: type preservation - if a term is typed and evaluates to a value, *)
(* then that value must have the same type as the term.                      *)
Theorem type_preservation : forall (env : env) (t : tm) (ty : ty) (v : val),
  type_consistence_across_op_envs env ->
  type_consistence_across_var_envs env ->
  tm_has_type env t ty -> 
  eval env t v -> 
  val_has_type v ty.
Proof.
  intros env t ty v Henv0 Henv1 H1 H2.
  generalize dependent v.
  induction H1; intros v H2; inversion H2.
  - apply ValHasTy_Int.
  - apply ValHasTy_True.
  - apply ValHasTy_False.
  - apply ValHasTy_Prod_Empty.
  - apply ValHasTy_Prod_NonEmpty with (v:=hv).
    + apply IHtm_has_type1 with (v:=hv); assumption.
    + apply IHtm_has_type2 with (v:=Val_Prod tv); assumption.
  - apply ValHasTy_Nil.
  - apply ValHasTy_Cons with (v1:=hv) (v2:=tv).
    + apply IHtm_has_type1 with (v:=hv); assumption.
    + apply IHtm_has_type2 with (v:=tv); assumption.
  - apply ValHasTy_None.
  - apply ValHasTy_Some; subst; auto.
  - (* In this case, we resort to the type consistence axiom for operators, i.e. Henv0 *)
    subst. rename op into opname. rename ty0 into rty.
    assert (H9 : val_has_type (Val_Prod lval) (Ty_Prod lty)) by auto.
    assert (H10 : forall (rval : val), f lval rval -> val_has_type rval rty) by
      (apply Henv0 with (k:=opname) (lty:=lty); auto).
    apply H10.
    assumption.
  - (* In this case, we resort to the type consistence axiom for variables, i.e. Henv1 *)
    subst.
    apply Henv1 with (ty:=ty0) (x:=x); assumption.
Qed.

(* Adapted from http://web4.ensiie.fr/~robillard/Graph_Library/MapFacts.html *)
Local Lemma mapsto_in : forall a v (m : StrMap.t a), StrMap.In v m <-> exists x, StrMap.MapsTo v x m.
Proof.
  intros. rewrite StrMapFacts.in_find_iff.
  case_eq (StrMap.find v m); intros.
  split; intros.
  exists a0. rewrite StrMapFacts.find_mapsto_iff. auto.
  congruence.
  split; intros.
  congruence.
  destruct H0. rewrite StrMapFacts.find_mapsto_iff in H0. congruence.
Qed.

(* Theorem: normalization - every typed term evaluates to a value *)
Theorem normalization : forall (env : env) (t : tm) (ty : ty),
  type_consistence_across_op_envs env ->
  type_consistence_across_var_envs env ->
  id_agreement_across_op_envs env ->
  id_agreement_across_var_envs env ->
  evaluability_of_operators env ->
  tm_has_type env t ty -> exists (v : val), eval env t v.
Proof.
  intros env tm ty Henv0 Henv1 Henv2 Henv3 Henv4 H1.
  induction H1;
    try rename IHtm_has_type into IH;
    try rename IHtm_has_type1 into IH1;
    try rename IHtm_has_type2 into IH2.
  - exists (Val_Int i); apply Eval_Int.
  - exists Val_True; apply Eval_True.
  - exists Val_False; apply Eval_False.
  - exists (Val_Prod nil); apply Eval_Prod_Empty.
  - destruct IH1 as [hv hVal_eval].
    destruct IH2 as [Val_lv Val_lVal_eval].
    assert (H2 : exists (lv : list val), Val_lv = Val_Prod lv). {
      inversion Val_lVal_eval; subst; eauto.
    }
    destruct H2 as [lv H2].
    exists (Val_Prod (hv :: lv)).
    apply Eval_Prod_NonEmpty with (hv:=hv) (tv:=lv); auto.
    subst; auto.
  - exists (Val_Nil ty0); apply Eval_Nil.
  - destruct IH1 as [hv hVal_eval]. destruct IH2 as [tv tVal_eval].
    exists (Val_Cons hv tv). apply Eval_Cons; trivial.
  - exists (Val_None ty0). apply Eval_None.
  - destruct IH as [v Val_eval].
    exists (Val_Some v). apply Eval_Some; trivial.
  - destruct IH as [Val_lval Val_lval_eval].
    assert (H2 : exists (lval : list val), Val_lval = Val_Prod lval). {
      inversion Val_lval_eval; subst; eauto.
    }
    destruct H2 as [lval lval_eval].
    subst.
    assert (H3 : exists f : list val -> val -> Prop, StrMap.MapsTo op f env.(op_env)). {
      assert (H3_1 : exists (x : opty), StrMap.MapsTo op x env.(opty_env)) by eauto.
      apply mapsto_in in H3_1.
      (* Here we resort to the identifier agreement axiom for operators *)
      rewrite Henv2 in H3_1.
      trivial.
    }
    destruct H3 as [f H2].
    assert (lval_type : val_has_type (Val_Prod lval) (Ty_Prod lty)). {
      (* Here we use the type preservation theorem we have proven *)
      apply type_preservation with (t:=Tm_Prod ltm) (v:=Val_Prod lval) (env:=env); auto.
    }
    assert (H4 : exists (rval : val), f lval rval). {
      (* Here we resort to the evaluability axiom for operators *)
      apply Henv4 with (lval:=lval) (k:=op) (lty:=lty) (rty:=ty0); auto.
    }
    destruct H4 as [rval H4].
    exists rval.
    apply Eval_Op with (f:=f) (lval:=lval); auto.
  - assert (H2 : exists (v : val), StrMap.MapsTo x v env.(var_env)). {
      assert (H2_1 : exists (ty : ty), StrMap.MapsTo x ty env.(varty_env)) by eauto.
      apply mapsto_in in H2_1.
      (* Here we resort to the identifier agreement axiom for variables *)
      rewrite Henv3 in H2_1.
      trivial.
    }
    destruct H2 as [v H2].
    exists v.
    apply Eval_Var; auto.
Qed.

(* Check whether a term contains a variable *)
Inductive tm_contains_var : tm -> string -> Prop :=
  (* | TmContainsVar_Prod : forall (ltm : list tm) (x : string), 
    (exists (t : tm), List.In t ltm /\ tm_contains_var t x) -> 
    tm_contains_var (Tm_Prod ltm) x *)
  | TmContainsVar_Prod : forall (htm : tm) (ltm : list tm) (x : string),
    (tm_contains_var htm x \/ tm_contains_var (Tm_Prod ltm) x) ->
    tm_contains_var (Tm_Prod (htm :: ltm)) x
  | TmContainsVar_Cons : forall (t1 t2 : tm) (x : string),
    (tm_contains_var t1 x \/ tm_contains_var t2 x) -> 
    tm_contains_var (Tm_Cons t1 t2) x
  | TmContainsVar_Some : forall (t : tm) (x : string),
    tm_contains_var t x -> 
    tm_contains_var (Tm_Some t) x
  | TmContainsVar_Op : forall (ltm : list tm) (opname x : string),
    (exists (t : tm), List.In t ltm /\ tm_contains_var t x) -> 
    tm_contains_var (Tm_Op opname ltm) x
  | TmContainsVar_Var : forall (t : tm) (x : string),
    t = Tm_Var x -> 
    tm_contains_var t x.
