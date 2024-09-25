(* Interfaces.v *)
(* Interfaces *)
From EasyUCFormalization Require Import Utils StrVList Msgs.

(* Interface kind: direct or adversarial *)
Inductive interface_kind : Type :=
  | DirectKind
  | AdvKind.

(* Basic interfaces *)
Inductive basic_inter : Type :=
  | BasicInter_Cons : StrMap.t msg -> basic_inter.

(* Composite interfaces *)
Inductive comp_inter : Type :=
  | CompInter_Cons : StrMap.t string -> comp_inter.  (* Note that StrMap.key = string *)

(* Interfaces *)
Inductive interface : Type :=
  | BasicInter : basic_inter -> interface
  | CompInter : comp_inter -> interface.

(* Checks ***************************************************************************)
(* 1. An interface cannot be empty.
      A basic interface has messages, and a composite interface has sub-interfaces.
      This check is in ucParser.mly. (inter - L576)

   2. Incoming messages of direct interfaces must have a (source) port.
      Outgoing messages of direct interfaces must have a (destination) port.
      This check is only performed at the level of basic interfaces.
      This check is in ucParser.mly. (check_parsing_direct_inter)
           
   3. Incoming messages of adversarial interfaces cannot have a (source) port.
      Outgoing messages of adversarial interfaces cannot have a (dest.) port.
      This check is only performed at the level of basic interfaces.
      This check is in ucParser.mly. (check_parsing_adversarial_inter)
      
   4. Composite interfaces are well-formed with respect to an interface env.
      Specifically, the keys of the sub-interfaces must map to basic interfaces
      in the interface environment.
      This check is in ucTypecheck.ml (check_comp_inter - L186) 
   **********************************************************************************)

(* Check well-formedness of a basic interface.
   Also parametrized by the interface kind. *)
Definition basic_inter_is_wf (bi : basic_inter) (kind : interface_kind) : Prop :=
  let (msg_map) := bi in
  match kind with
  | DirectKind =>
    ~ StrMap.Empty msg_map /\ forall k m, StrMap.MapsTo k m msg_map -> msg_has_port m /\ msg_is_wf m
  | AdvKind =>
    ~ StrMap.Empty msg_map /\ forall k m, StrMap.MapsTo k m msg_map -> ~ msg_has_port m /\ msg_is_wf m
  end.

(* Check well-formedness of a composite interface.
   Also parametrized by the interface kind and an interface environment. *)
Definition comp_inter_is_wf (ci : comp_inter) (kind : interface_kind) (env : StrMap.t interface) : Prop :=
  let (subinter_map) := ci in
  ~ StrMap.Empty subinter_map /\
  forall k i_name, 
    StrMap.MapsTo k i_name subinter_map -> 
    exists (bi : basic_inter), 
      StrMap.MapsTo i_name (BasicInter bi) env /\
      basic_inter_is_wf bi kind.

(* Interface environment well-formedness. 
   An interface environment is well-formed if all its interfaces are well-formed
   Since different kinds reside in different environments, we need to pass the kind *)
Definition interface_env_is_wf (env : StrMap.t interface) (kind : interface_kind) : Prop :=
  forall k i, StrMap.MapsTo k i env -> 
    match i with
    | BasicInter bi => basic_inter_is_wf bi kind
    | CompInter ci => comp_inter_is_wf ci kind env
    end.

(* Interface type-checking 
   ----------------------- 
   This is a five-tuple relation:
                      env |-(kind) (x, i) : env'
   where
     - env is the initial interface environment
     - kind is the interface kind
     - x is the identifier (name) of the interface
     - i is the interface
     - env' is the new interface environment after type-checking 

   For the relation to hold, the following must be true: 
     - x does not already exist in env
     - i is well-formed wrt. kind if it is basic,
       and wrt. kind and env if it is composite.
     - env' = env + [x |-> i] *)
Inductive interface_typecheck
    (env : StrMap.t interface) (kind : interface_kind) (x : string) : 
    interface -> StrMap.t interface -> Prop :=
  | BasicInter_TC : forall (bi : basic_inter) (env' : StrMap.t interface),
    ~ StrMap.In x env ->
    basic_inter_is_wf bi kind ->
    interface_typecheck env kind x (BasicInter bi) (env + [x |-> BasicInter bi])
  | CompInter_TC : forall (ci : comp_inter) (env' : StrMap.t interface),
    ~ StrMap.In x env ->
    comp_inter_is_wf ci kind env ->
    interface_typecheck env kind x (CompInter ci) (env + [x |-> CompInter ci]).

(* Interface list type-checking                                  
   ----------------------------                                  
   This is a four-tuple relation:                                
                     env |-(kind) l : env'                     
   where                                                         
     - env is the initial interface environment                  
     - kind is the interface kind                                
     - l is a list of interfaces                                 
          (with identifiers - so it is a string-value list)      
     - env' is the new interface environment after type-checking 
                                                               
   The relation is defined inductively by the following rules:   
     - env |-(kind) [] : env                                     
     - env |-(kind) (x, i) : env'                                
       env' |-(kind) l : env''                                   
       ---------------------------------                         
       env |-(kind) (x, i) :: l : env'' *)
Inductive interface_list_typecheck 
    (env : StrMap.t interface) (kind : interface_kind) :
    svlist interface -> StrMap.t interface -> Prop :=
  | EmptyInterList_TC :
    interface_list_typecheck env kind [] env
  | ConsInterList_TC : forall (x : string) (i : interface) (l : svlist interface) 
      (env' env'' : StrMap.t interface),
    interface_typecheck env kind x i env' ->
    interface_list_typecheck env' kind l env'' ->
    interface_list_typecheck env kind (add_svlist x i l) env''.
  
(* Lemma: if an interface is added to an environment, such that its identifier
    is not already in the environment, then any identifier already in the environment
    continues to map to the same interface *)
Local Lemma environment_mapping_invariance_with_new_identifier :
  forall (i new_i : interface) (i_name new_i_name : string) 
    (env : StrMap.t interface),
  ~ StrMap.In new_i_name env ->
  StrMap.MapsTo i_name i env ->
  StrMap.MapsTo i_name i (env + [new_i_name |-> new_i]).
Proof.
  intros i new_i i_name new_i_name env H1 H2.
  rewrite StrMapFacts.add_mapsto_iff.
  right. split.
  apply StrMap.find_1 in H2.
  assert (H3 : StrMap.find i_name env <> None) by (rewrite H2; discriminate).
  apply StrMapFacts.not_find_in_iff in H1.
  contradict H3.
  rewrite <- H1.
  rewrite H3; reflexivity.
  assumption.
Qed.

(* Theorem : if env |-(kind) (x, i) : env' and interface_env_is_wf env kind, 
             then interface_env_is_wf env' kind *)
Theorem environment_wf_preservation : 
  forall (env : StrMap.t interface) (kind : interface_kind) (x : string) 
    (i : interface) (env' : StrMap.t interface),
  interface_typecheck env kind x i env' ->
  interface_env_is_wf env kind ->
  interface_env_is_wf env' kind.
Proof.
  intros env kind x i env' H1 H2.
  induction H1 as [bi | ci]; 
    unfold interface_env_is_wf;
    intros k i' H3;
    rewrite StrMapFacts.add_mapsto_iff in H3.
  (* Basic interface case for the added interface *)
  + destruct H3 as [[H3 H4] | [H3 H4]].
    (* Proving well-formedness for the added interface *)
    * subst. assumption.
    (* Proving well-formedness for the existing interfaces *)
    * apply H2 in H4. 
      destruct i' as [bi' | ci'].
      (* Basic interface case for existing interface *)
      - assumption.
      (* Composite interface case for existing interface *)
      - destruct ci' as [subinter_map'].
        unfold comp_inter_is_wf.
        destruct H4 as [H4 H5].
        split; [assumption | intros k' i'_name H6].
        apply H5 in H6.
        destruct H6 as [bi'' [H6 H7]].
        exists bi''.
        split; [idtac | assumption].
        apply environment_mapping_invariance_with_new_identifier; assumption.
  (* Composite interface case for the added interface *)
  + destruct H3 as [[H3 H4] | [H3 H4]].
    (* Proving well-formedness for the added interface *)
    * subst.
      unfold comp_inter_is_wf.
      destruct ci as [subinter_map].
      split.
      (* Proving non-emptiness *)
      - unfold comp_inter_is_wf in H0.
        destruct H0 as [H0 H1].
        assumption.
      (* Proving well-formedness and basicity of sub-interfaces *)
      - intros k' i'_name H3.
        unfold comp_inter_is_wf in H0.
        destruct H0 as [H0 H1].
        remember (CompInter_Cons subinter_map) as ci.
        apply H1 in H3.
        destruct H3 as [bi [H3 H4]].
        exists bi.
        split; [idtac | assumption].
        apply environment_mapping_invariance_with_new_identifier; assumption.
    (* Proving well-formedness for the existing interfaces *)
    * apply H2 in H4.
      destruct i' as [bi' | ci'].
      (* Basic interface case for existing interface *)
      - assumption.
      (* Composite interface case for existing interface *)
      - destruct ci' as [subinter_map'].
        unfold comp_inter_is_wf.
        destruct H4 as [H4 H5].
        split; [assumption | intros k' i'_name H6].
        apply H5 in H6.
        destruct H6 as [bi'' [H6 H7]].
        exists bi''.
        split; [idtac | assumption].
        apply environment_mapping_invariance_with_new_identifier; assumption.
Qed.

(* Theorem: Similarly, the same well-formedness preservation holds in the case of 
            list type-checking *)
Theorem environment_list_wf_preservation : 
  forall (env env'': StrMap.t interface) (kind : interface_kind) (l : svlist interface),
  interface_list_typecheck env kind l env'' ->
  interface_env_is_wf env kind ->
  interface_env_is_wf env'' kind.
Proof.
  intros env env'' kind l H.
  induction H.
  - auto.
  - intros H1.
    apply IHinterface_list_typecheck.
    apply environment_wf_preservation in H; assumption.
Qed.