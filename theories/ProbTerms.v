(* ProbTerms.v *)
(* Probabilistic terms *)
From EasyUCFormalization Require Import NonProbTerms.
From Coq Require Import QArith.

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

(* Semantics for distribution terms *)
(* Relation on distribution terms and pairs of values and probabilities *)
Inductive deval : dtm -> (val * Q) -> Prop :=
  | DEval_Uniform : forall (t1 t2 : tm) (n1 n2 elt : Z),
    eval t1 (Val_Int n1) -> 
    eval t2 (Val_Int n2) -> 
    (n1 <= elt <= n2)%Z ->
    deval (DTm_Uniform t1 t2) (Val_Int elt, 1 # (Z.to_pos (n2 - n1 + 1)))
  | DEval_Cast : forall (t : tm) (v : val),
    eval t v ->
    deval (DTm_Cast t) (v, 1)
  | DEval_Prod : forall (ht : dtm) (hv : val) 
      (lt : list dtm) (lv : list val) (hprob lprob : Q),
    deval ht (hv, hprob) ->
    deval (DTm_Prod lt) (Val_Prod lv, lprob) ->
    deval (DTm_Prod (ht :: lt)) (Val_Prod (hv :: lv), hprob * lprob).
