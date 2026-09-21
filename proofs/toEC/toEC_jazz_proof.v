From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.
Require Import psem.
Require Import arch_decl arch_extra sem_params_of_arch_extra.
Require Export toEC_jazz.
Require Import normalize_cond_proof.
Require Import refresh_for_proof.
Require Import init_local_arrays_proof.
Require Import for_to_while_proof.
Require Import flatten_while_proof.
Require Import remove_baseop_casts_proof.
Require Import make_coercions_explicit_proof.
Require Import remove_nullary_opns_proof.
Import Utf8.

Section TOEC_PROOF.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {syscall_state : Type}
  {scs : syscall_sem syscall_state}
  {spp : SemPexprParams}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
  {rE0_trans : EventRels_trans rE0 rE0 rE0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.
#[local] Existing Instance sip_of_asm_e.
#[local] Existing Instance indirect_c.
(* [make_coercions_explicit_proof] (EJ-10) only holds under [nosubword]
   (its type-soundness argument needs a variable's runtime value to have
   exactly its declared [vtype]); pinning it here fixes the ambient
   [WithSubWord] instance for the WHOLE composed pipeline lemma below, the
   same way [indirect_c] is pinned for [dc] just above. Every other pass in
   this file remains generic in its own `{wsw}` Context and is specialized
   to [nosubword] only at its own call site below, mirroring how the other
   five passes are specialized to [indirect_c] for `dc`. *)
#[local] Existing Instance nosubword.
(* Likewise, [make_coercions_explicit_proof] pins its own [EstateParams]
   instance to [ep_of_asm_e] (needed so the [PointerData]/[MSFsize] pair
   [sopn_tin] resolves to at its call sites matches the one the pass itself
   uses, see the comment in [make_coercions_explicit_proof.v]). Mirroring
   [wsw]/[dc] above: [ep] is removed from this file's own [Context] and
   every earlier per-pass composition call is specialized to
   [ep := ep_of_asm_e] explicitly at its own call site. *)
#[local] Existing Instance ep_of_asm_e.

Context
  (fresh_var_ident : v_kind -> instr_info -> string -> atype -> Ident.ident)
  (rename : funname -> var -> Ident.ident)
  (normal : bool)
  (p p' : uprog)
  (ev : extra_val_t)
  (toEC_ok : toEC_prog fresh_var_ident p = ok p')
.

(* [sip_of_asm_e] fully applied: with the [asm_extra] context fixing the
   program's op type to [extended_op], relying on the ambient [sip_of_asm_e]
   instance (rather than passing it fully explicit) makes ssreflect's [have]
   generalize the still-implicit [reg]/.../[scs] arguments into the produced
   term instead of resolving them, so every per-pass lemma call below spells
   [sip] out fully applied. *)
Notation the_sip :=
  (@sip_of_asm_e reg regx xreg rflag cond asm_op extra_op asm_e
     syscall_state scs) (only parsing).

(* Same [have]-generalizes-typeclass-implicits gotcha as [the_sip] above,
   for [ep_of_asm_e] (pinned in place of the generic [{ep}] Context, see the
   comment on [#[local] Existing Instance ep_of_asm_e] above). *)
Notation the_ep :=
  (@ep_of_asm_e reg regx xreg rflag cond asm_op extra_op asm_e
     syscall_state scs) (only parsing).


End TOEC_PROOF.
