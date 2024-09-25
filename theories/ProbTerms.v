(* ProbTerms.v *)
(* Probabilistic terms *)
From EasyUCFormalization Require Import NonProbTerms.
Require Import QArith String.

(* Distribution type *)
Inductive dty : Type :=
  | Ty_Dist : ty -> dty.

(* Distribution terms *)
Inductive dtm : Type :=
  (* dtm_uniform t1 t2 is the uniform distribution over the interval [t1, t2] *)
  | DTm_Uniform : tm -> tm -> dtm
  (* Cast normal terms to distribution terms *)
  | DTm_Cast : tm -> dtm
  (* Product terms *)
  | DTm_Prod : list dtm -> dtm.

(* Ground typing for distribution terms *)
Inductive dtm_has_ground_type (env : env) : dtm -> ty -> Prop :=
  | DtmUniformHasTy_Int : forall (t1 t2 : tm),
    tm_has_type env t1 Ty_Int ->
    tm_has_type env t2 Ty_Int ->
    dtm_has_ground_type env (DTm_Uniform t1 t2) Ty_Int
  | DtmCastHasTy : forall (t : tm) (ty : ty),
    tm_has_type env t ty ->
    dtm_has_ground_type env (DTm_Cast t) ty
  | DtmEmptyProdHasTy :
    dtm_has_ground_type env (DTm_Prod nil) (Ty_Prod nil)
  | DtmNEProdHasTy : forall (htm : dtm) (ltm : list dtm) (hty : ty) (lty : list ty),
    dtm_has_ground_type env htm hty ->
    dtm_has_ground_type env (DTm_Prod ltm) (Ty_Prod lty) ->
    dtm_has_ground_type env (DTm_Prod (htm :: ltm)) (Ty_Prod (hty :: lty)).

(* Semantics for distribution terms *)
(* Relation on distribution terms and pairs of values and probabilities *)
Inductive deval (env : env) : dtm -> (val * Q) -> Prop :=
  | DEval_Uniform : forall (t1 t2 : tm) (n1 n2 elt : Z),
    eval env t1 (Val_Int n1) -> 
    eval env t2 (Val_Int n2) -> 
    (n1 <= elt <= n2)%Z ->
    deval env (DTm_Uniform t1 t2) (Val_Int elt, 1 # (Z.to_pos (n2 - n1 + 1)))
  | DEval_Cast : forall (t : tm) (v : val),
    eval env t v ->
    deval env (DTm_Cast t) (v, 1)
  | DEval_Prod : forall (ht : dtm) (hv : val) 
      (lt : list dtm) (lv : list val) (hprob lprob : Q),
    deval env ht (hv, hprob) ->
    deval env (DTm_Prod lt) (Val_Prod lv, lprob) ->
    deval env (DTm_Prod (ht :: lt)) (Val_Prod (hv :: lv), hprob * lprob).

Theorem deterministic_eval_to_probabilistic_eval : forall (env : env) (t : tm) (v : val),
  eval env t v -> deval env (DTm_Cast t) (v, 1).
Proof.
  intros t v H.
  apply DEval_Cast.
Qed.

(* Check whether a distribution term contains a variable *)
Inductive dtm_contains_var : dtm -> string -> Prop :=
  | DtmContainsVar_Uniform : forall (t1 t2 : tm) (x : string),
    (tm_contains_var t1 x \/ tm_contains_var t2 x) -> 
    dtm_contains_var (DTm_Uniform t1 t2) x
  | DtmContainsVar_Cast : forall (t : tm) (x : string),
    tm_contains_var t x -> 
    dtm_contains_var (DTm_Cast t) x
  | DtmContainsVar_Prod : forall (htm : dtm) (ltm : list dtm) (x : string),
    (dtm_contains_var htm x \/ dtm_contains_var (DTm_Prod ltm) x) ->
    dtm_contains_var (DTm_Prod (htm :: ltm)) x.
