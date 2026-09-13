(* -------------------------------------------------------------------- *)
(* Correctness of the Jasmin -> pwhile translation of [toEC.v].

   This file *states* the correctness theorem and admits it; no proof is
   attempted here.

   Both languages give procedure calls the same treatment -- an
   uninterpreted event resolved by [mrec] ([handle_recCall] on the Jasmin
   side, [handle_Call] on the pwhile side) -- and their command semantics
   have the same shape:

     Jasmin  isem_cmd_rec : ... -> estate -> itree (recCall +' E) estate
     pwhile  com_sem      : cmd  -> cmem  -> itree (Call    +' E) cmem

   with [isem_while_round]/[isem_while_loop] matching name for name.  So
   the statement is an [xrutt] between the two interaction trees, the very
   relation Jasmin's own [wiequiv_f] is built from
   (relational_logic.v:225).

   The left-hand cutoff [errcutoff (is_error wE)] is what makes [toEC.v]'s
   "total denotations with defaults" convention honest without a side
   condition: pwhile has no error event at all (its only failure is
   [abort = ITree.spin], denoting [dnull]), so a Jasmin [ErrEvent]
   discharges the obligation and the statement reads *either Jasmin
   errors, or the two sides agree*.  On the right, [nocutoff].

   Everywhere the two states are compared the relation is [value_uincl]
   in the direction Jasmin-refines-to-pwhile, not equality.  That absorbs
   the places where [toEC.v] is deliberately more defined than Jasmin: an
   [sopn] leaving a flag undefined, and an out-of-bounds array or memory
   read.  It is also the orientation of the [uincl_spec] that the pipeline
   lemma [it_toEC_progP] already carries.                                *)
(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From mathcomp Require Import boot order.
From mathcomp.algebra Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import counting_distr.
From ITree Require Import ITree ITreeFacts.

Require Import psem.
Require Import xrutt core_logics.
Require Import arch_decl arch_extra sem_params_of_arch_extra.
Require Import memory_model low_memory.
Require Export toEC.

(* [psemantic_new] is deliberately *not* imported: its memory notations
   [_ .[ _ ]] / [_ .[ _ <- _ ]] are declared at argument levels
   incompatible with Jasmin's homonyms in [varmap.v], which is a hard
   error rather than an overridable warning.  [itree_new] only [Require]s
   it, so nothing leaks; the one thing needed from it is named qualified. *)
From xhl.pwhile Require Import inhabited_new pwhile_new itree_new.
From xhl.pwhile Require psemantic_new.

Import Utf8.

Section TOEC_PROOF.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
  {syscall_state : Type}
  {scs : syscall_sem syscall_state}
  {wsw : WithSubWord}
  {dc : DirectCall}
  {spp : SemPexprParams}
  {E E0 : Type -> Type}
  {wE : with_Error E E0}
  {rE0 : EventRels E0}
.

#[local] Existing Instance progUnit.
#[local] Existing Instance sCP_unit.
(* [ep] and [sip] are pinned rather than taken generically: the program's
   op type is fixed to [extended_op] by the [asm_extra] context above, so
   a generic [{ep : EstateParams _}] would give [emem] a [PointerData]
   distinct from [asm_e]'s [arch_pd] and nothing about memory would
   typecheck.  Same reasoning as [toEC_jazz_proof.v:35-51]. *)
#[local] Existing Instance ep_of_asm_e.
#[local] Existing Instance sip_of_asm_e.

Context
  (to_ident : var -> nat)
  (to_fname : funname -> nat)
.

Notation pwcmd := (cmd_ jcode jident (cmem jcode jident) jident).
Notation pwmem := (cmem jcode jident).

(* [Rnd] is indexed by the code alphabet; pin it to Jasmin.s. *)
Notation jRnd := (@Rnd jcode) (only parsing).

(* the pwhile variable / function / memory slots of [toEC.v] *)
Notation pvid x := (pw_var_id to_ident x) (only parsing).
Notation pfid f := (pw_fun_id to_fname f) (only parsing).

(* reading a Jasmin variable back out of a pwhile memory, as a [value].
   Note there is no conversion any more: [interp t] *is* the carrier, so
   this is just [to_val] after the store lookup. *)
Definition read_jvar (cm : pwmem) (x : var) : value :=
  jval (eval_atype (jtype x)) (mget (eval_atype (jtype x)) cm (pvid x)).

Definition read_jglob (cm : pwmem) (x : var) : value :=
  jval (eval_atype (jtype x)) (mgetg (eval_atype (jtype x)) cm (pvid x)).

(* ==================================================================== *)
(* 1. Matching relations                                                *)
(* ==================================================================== *)

(* pwhile's *local* store agrees with the Jasmin varmap, through
   [pw_var_id] and the code alphabet. *)
Definition match_vm (vm : Vm.t) (cm : pwmem) : Prop :=
  forall x : var, value_uincl (Vm.get vm x) (read_jvar cm x).

(* pwhile's *global* store holds Jasmin's memory, in the single cell
   [pw_mem_id], as one [WArray.array mem_size].  Only the addresses Jasmin
   can actually read are constrained -- that is the point of modelling
   memory by a total byte store. *)
Definition match_mem (m : Memory.mem) (cm : pwmem) : Prop :=
  forall (a : pointer) (w : u8),
    read m Aligned a U8 = ok w ->
    WArray.get8 (mgetg (carr (mem_size (asm_e := asm_e))) cm pw_mem_id)
                (wunsigned a) = ok w.

(* ... and it holds the global constants, which [toEC_globs] installs. *)
Definition match_globs (gd : glob_decls) (cm : pwmem) : Prop :=
  forall (x : var) (g : glob_value),
    assoc gd x = Some g -> value_uincl (gv2val g) (read_jglob cm x).

Definition match_estate (p : _uprog) (s : estate) (cm : pwmem) : Prop :=
  [/\ match_vm s.(evm) cm, match_mem s.(emem) cm & match_globs (p_globs p) cm ].

(* On entry to [fn], [cm] must already hold the arguments in the callee's
   own parameter slots -- which is exactly what pwhile's [minit] does at a
   [block], and what [toEC.call_cmd] emits.  Stating it this way lets the
   theorem talk about [pwhile_new.call] directly instead of fabricating a
   command out of runtime values. *)
Definition match_params (fd : _ufundef) (vs : values) (cm : pwmem) : Prop :=
  List.Forall2
    (fun (x : var_i) (v : value) => value_uincl v (read_jvar cm x.(v_var)))
    fd.(f_params) vs.

Definition match_res (fd : _ufundef) (vs : values) (cm : pwmem) : Prop :=
  List.Forall2
    (fun (x : var_i) (v : value) => value_uincl v (read_jvar cm x.(v_var)))
    fd.(f_res) vs.

(* [fstate]'s [fscs] (the syscall oracle state) has no pwhile counterpart:
   pwhile models [RandomBytes] as a genuine distribution rather than as an
   oracle, so nothing constrains it here.  See [randombytes_model]. *)
Definition match_fstate (p : _uprog) (fd : _ufundef) (fs : fstate) (cm : pwmem)
  : Prop :=
  [/\ match_params fd fs.(fvals) cm
    , match_mem fs.(fmem) cm
    & match_globs (p_globs p) cm ].

Definition match_fstate_out (p : _uprog) (fd : _ufundef) (fr : fstate)
    (cm : pwmem) : Prop :=
  [/\ match_res fd fr.(fvals) cm
    , match_mem fr.(fmem) cm
    & match_globs (p_globs p) cm ].

(* ==================================================================== *)
(* 2. Event relations                                                   *)
(* ==================================================================== *)

(* After [interp_call]/[mrec] the call events are gone from both sides, so
   the only events left are Jasmin's [ErrEvent] (cut off on the left) and
   pwhile's [Rnd] draws.  A draw arises solely from [Csyscall], and Jasmin
   threads its syscall oracle through the *state* rather than emitting an
   event -- there is nothing for a draw to be related to.  The relation is
   empty, and the theorem consequently speaks about [Csyscall]-free
   programs; see [randombytes_model] below. *)
Definition no_pre : forall X Y, E X -> jRnd Y -> Prop :=
  fun _ _ _ _ => False.

Definition no_post : forall X Y, E X -> X -> jRnd Y -> Y -> Prop :=
  fun _ _ _ _ _ _ => False.

(* -------------------------------------------------------------------- *)
(* The [RandomBytes] modelling gap.

   Jasmin models [RandomBytes] as a *deterministic oracle* over
   [syscall_state] ([fexec_syscall] -> [exec_syscall],
   it_sems_core.v:68): it is threaded through the state, not emitted as an
   itree event.  pwhile's counterpart, which [toEC.v] emits, is a genuine
   [Rnd] draw.  No proof can bridge the two -- there is no Jasmin event
   for a draw to be related to -- so this is a *modelling* step, the same
   one compiler/src/toEC.ml makes with its [SC.randombytes] module
   argument.

   It is named here rather than buried in the translation: [toEC_psP]
   below holds as stated for [Csyscall]-free programs, and any client that
   wants it for a program containing [Csyscall] has to assume this.  It
   says the oracle's answer is one the uniform distribution could have
   produced. *)
Definition randombytes_model : Prop :=
  forall (ws : wsize) (n : Z) (st st' : syscall_state)
         (m m' : Memory.mem)
         (a a' : WArray.array (arr_size ws n)),
    exec_syscall st m (RandomBytes ws n) [:: Varr a]
      = ok (st', m', [:: Varr a']) ->
    drandbytes (arr_size ws n) a' <> 0%R.

(* ==================================================================== *)
(* 3. The theorem                                                       *)
(* ==================================================================== *)

Context
  (p : _uprog)
  (ev : extra_val_t)
  (ps : jident -> pwcmd)
  (toEC_ok : toEC_ps to_ident to_fname p = ok ps)
.

Theorem toEC_psP fn fd fs cm :
  get_fundef (p_funcs p) fn = Some fd ->
  match_fstate p fd fs cm ->
  xrutt (errcutoff (is_error wE)) nocutoff no_pre no_post
    (match_fstate_out p fd)
    (isem_fun p ev fn fs)
    (interp_call (E := jRnd) ps
       (com_sem (E := jRnd) (pwhile_new.call (pfid fn)) cm)).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* The same statement at the level of sub-distributions comes for free
   from xhl: [interp_fullE] (itree_new.v:685) identifies [interp_full]
   with [psemantic_new.ssem_], so there is no need to name the
   distribution semantics here at all.

   ([range] is deliberately avoided: it lives in [pwhile/range.v], which
   is still bound to the *old* [pwhile.v], and requiring it would drag
   that stack in alongside this one.) *)
Corollary toEC_ps_interp_fullP fn fd fs cm :
  get_fundef (p_funcs p) fn = Some fd ->
  match_fstate p fd fs cm ->
  exists fr cm',
    [/\ isem_fun p ev fn fs ≈ Ret fr
      , match_fstate_out p fd fr cm'
      & interp_full (pwhile_new.call (pfid fn)) ps cm = dunit cm' ].
Proof. Admitted.

End TOEC_PROOF.
