Require Import compiler_util expr arch_decl arch_extra.
Require Import normalize_cond.
Require Import refresh_for.
Require Import init_local_arrays.
Require Import for_to_while.
Require Import flatten_while.
Require Import remove_baseop_casts.
Require Import normalize_calls.
Require Import make_coercions_explicit.
Require Import remove_nullary_opns.
Require Import legalize_names.
Require Import toEC.
(* [toEC] fixes the code alphabet ([jcode = ctype]) and the identifier
   type ([jident = nat]); [pwhile_new] is needed here only to name
   [cmd_]/[cmem] in the signatures below. *)
From xhl.pwhile Require Import inhabited_new pwhile_new.

Section TOEC.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (rename : funname -> var -> Ident.ident)
.

Definition toEC_prog (normal : bool) (p : _uprog) : cexec _uprog :=
  Let p1 := refresh_for_prog fresh_var_ident false (normalize_cond_prog p) in
  let p1' := init_local_arrays_prog p1 in
  Let p2 := if normal then for_to_while_prog fresh_var_ident p1' else ok p1' in
  let p3 := flatten_while_prog p2 in
  Let p4 := remove_baseop_casts_prog fresh_var_ident p3 in
  Let p5 := normalize_calls_prog fresh_var_ident p4 in
  Let p6 := mce_prog p5 in
  let p7 := if normal then remove_nullary_opns_prog p6 else p6 in
  legalize_names_prog rename p7.

(* -------------------------------------------------------------------- *)
(* The pwhile back-end.  Kept in a nested section so that [toEC_prog]
   above does not acquire the two name-map parameters: its signature is
   the one [compiler/entry/jasmin2ec.ml] calls.

   [extraction.v] no longer names [toEC_jazz] at all, so none of this
   reaches the extracted OCaml -- note that also leaves
   [compiler/entry/jasmin2ec.ml:42], which calls [ToEC_jazz.toEC_prog],
   without an extracted module.  Pre-existing, and out of scope here. *)
Section TO_PWHILE.

Context
  (to_ident : var -> nat)
  (to_fname : funname -> nat)
.

(* return types left to inference: the section-local [pwcmd] notation of
   [toEC.v] is not in scope here, and spelling [cmd_ jcode jident ...] out
   would need the [nat -> eqType] coercion in an annotation position. *)
Definition toEC_pwhile (normal : bool) (p : _uprog) :=
  Let p' := toEC_prog normal p in
  toEC_ps to_ident to_fname p'.

(* The global constants of [p] as an initialisation command, to be run
   before the entry point: [toEC_ps] translates function bodies only. *)
Definition toEC_pwhile_globs (p : _uprog) :=
  toEC_globs to_ident p.(p_globs).

End TO_PWHILE.

End TOEC.
