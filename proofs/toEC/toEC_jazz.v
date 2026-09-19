Require Import compiler_util expr arch_decl arch_extra.
Require Import sem_type sem_params.
Require Import normalize_cond.
Require Import refresh_for.
Require Import init_local_arrays.
Require Import for_to_while.
Require Import flatten_while.
Require Import remove_baseop_casts.
Require Import make_coercions_explicit.
Require Import remove_nullary_opns.
Require Import toEC.

From xhl.pwhile Require Import inhabited pwhile.
From mathcomp.reals Require Import reals.

Section TOEC.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
.

Definition toEC_prog (p : _uprog) : cexec _uprog :=
  Let p1 := refresh_for_prog fresh_var_ident false (normalize_cond_prog p) in
  let p1' := init_local_arrays_prog p1 in
  Let p2 := for_to_while_prog fresh_var_ident p1' in
  let p3 := flatten_while_prog p2 in
  Let p4 := remove_baseop_casts_prog fresh_var_ident p3 in
  Let p6 := mce_prog p4 in
  remove_nullary_opns_prog p6

Section TO_PWHILE.

Context {R : realType} {wsw : WithSubWord} {wa : WithAssert}.

Definition toEC_pwhile (normal : bool) (p : _uprog) :=
  Let p' := toEC_prog normal p in
  toEC_ps (R:=R) p'.

End TO_PWHILE.

End TOEC.
