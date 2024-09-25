(* Msgs.v *)
(* Messages *)
From EasyUCFormalization Require Import NonProbTerms StrVList.

(* Message direction *)
Inductive msg_dir : Type :=
  | InDir
  | OutDir.

(* Message type *)
Record msg : Type :=
  { dir : msg_dir;
    params : svlist ty;
    port : option string }.

(* Checks ***************************************************************************)
(* 1. A message cannot have more than max_msg_params parameters.                    *)
(*    This check is in ucTypecheck.ml (check_basic_inter - L136)                    *)
(*    **********************************************************                    *)
(* 2. The port of a message cannot collide with a parameter name.                   *)
(*    This check (added recently) is in ucTypecheck.ml (check_basic_inter - L152)   *)
(*    ***************************************************************************   *)

Parameter max_msg_params : nat.

(* Check if a message has a port *)
Definition msg_has_port (m : msg) : Prop :=
  match m.(port) with
  | Some _ => True
  | None => False
  end.

(* Check if a message has a noncolliding port *)
(* Vacuously true if the message has no port *)
Definition msg_has_noncolliding_port (m : msg) : Prop :=
  match m.(port) with
  | Some p => ~ in_svlist p m.(params)
  | None => True
  end.

(* Check if a message has at most max_msg_params parameters *)
Definition msg_has_at_most_max_msg_params (m : msg) : Prop :=
  svlist_length m.(params) <= max_msg_params.

(* Check if a message has distinct parameter names *)
Definition msg_has_distinct_params (m : msg) : Prop :=
  distinct_keys m.(params).

(* Check if a message is well-formed *)
Definition msg_is_wf (m : msg) : Prop :=
  msg_has_at_most_max_msg_params m /\
  msg_has_distinct_params m /\
  (msg_has_port m -> msg_has_noncolliding_port m).
