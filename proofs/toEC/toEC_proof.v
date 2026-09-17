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

(* [psemantic] is deliberately *not* imported: its memory notations
   [_ .[ _ ]] / [_ .[ _ <- _ ]] are declared at argument levels
   incompatible with Jasmin's homonyms in [varmap.v], which is a hard
   error rather than an overridable warning.  [itree] only [Require]s
   it, so nothing leaks; the one thing needed from it is named qualified. *)
From xhl.pwhile Require Import inhabited mem pwhile itree.
From xhl.pwhile Require psemantic.

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

(* [R] is needed because [pwcmd] is a [cmd_ R ...]; [wa] because
   [toEC_ps] rejects [Cassert] under [noassert]. *)
Context {R : realType} {wa : WithAssert}.

Notation pwcmd := (cmd_ R jcode jgcode jident jidentg jmem funname).
(* the carrier, not the packed [jmem]: [mget] / [mgetg] find the memType
   on [jstate] by canonical structure resolution. *)
Notation pwmem := jstate.

(* [Rnd] is indexed by the real type and the *local* code alphabet
   ([random] assigns to a local variable); pin both. *)
Notation jRnd := (@Rnd R jcode) (only parsing).

(* No identifier maps any more: a Jasmin variable *is* a pwhile local
   identifier and a [funname] *is* a pwhile function name, so [pw_var_id]
   and [pw_fun_id] are gone.

   Reading a Jasmin variable back out of a pwhile memory, as a [value]:
   there is no conversion beyond [jval], since [interp t] is the carrier. *)
Definition read_jvar (cm : pwmem) (x : var) : value :=
  jval (eval_atype (jtype x)) (mget (eval_atype (jtype x)) cm x).

(* There is no [read_jglob]: the global store holds nothing but Jasmin's
   memory, and a program with global variables is rejected by [pwgvar]. *)

(* ==================================================================== *)
(* 1. Matching relations                                                *)
(* ==================================================================== *)

(* [toEC.v]'s [jstate] has fields named [emem] and [evm] too -- after
   [Require Export toEC] those shadow Jasmin's [estate] projections, so
   the Jasmin ones are qualified below. *)
Notation jsvm s := (psem_defs.evm s) (only parsing).
Notation jsmem s := (psem_defs.emem s) (only parsing).

(* pwhile's *local* store agrees with the Jasmin varmap, through the
   retyped key of [toEC.v] and the code alphabet. *)
Definition match_vm (vm : Vm.t) (cm : pwmem) : Prop :=
  forall x : var, value_uincl (Vm.get vm x) (read_jvar cm x).

(* pwhile's *global* store is Jasmin's memory and nothing else: the global
   alphabet has a single code whose interpretation *is* [mem], held at the
   single identifier [tt].  So this is an equality, not the byte-wise
   containment the old [WArray mem_size] encoding needed. *)
Definition match_mem (m : Memory.mem) (cm : pwmem) : Prop :=
  mgetg (@Gmem _) cm tt = m.

(* There is no [match_globs]: [toEC.v] has no [toEC_globs] and no global
   variables to install. *)
Definition match_estate (s : estate) (cm : pwmem) : Prop :=
  match_vm (jsvm s) cm /\ match_mem (jsmem s) cm.

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
Definition match_fstate (fd : _ufundef) (fs : fstate) (cm : pwmem) : Prop :=
  match_params fd fs.(fvals) cm /\ match_mem fs.(fmem) cm.

Definition match_fstate_out (fd : _ufundef) (fr : fstate) (cm : pwmem) : Prop :=
  match_res fd fr.(fvals) cm /\ match_mem fr.(fmem) cm.

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
    drandbytes (R:=R) (arr_size ws n) a' <> 0%R.

(* ==================================================================== *)
(* 3. The theorem                                                       *)
(* ==================================================================== *)

Context
  (p : _uprog)
  (ev : extra_val_t)
  (ps : funname -> pwcmd)
  (toEC_ok : toEC_ps (R:=R) p = ok ps)
.

Theorem toEC_psP fn fd fs cm :
  get_fundef (p_funcs p) fn = Some fd ->
  match_fstate fd fs cm ->
  xrutt (errcutoff (is_error wE)) nocutoff no_pre no_post
    (match_fstate_out fd)
    (isem_fun p ev fn fs)
    (interp_call (E := jRnd) ps
       (com_sem (E := jRnd) (pwhile.call fn) cm)).
Proof. Admitted.

(* -------------------------------------------------------------------- *)
(* The same statement at the level of sub-distributions comes for free
   from xhl: [interp_fullE] (itree.v:685) identifies [interp_full] with
   [psemantic.ssem_], so there is no need to name the distribution
   semantics here at all. *)
Corollary toEC_ps_interp_fullP fn fd fs cm :
  get_fundef (p_funcs p) fn = Some fd ->
  match_fstate fd fs cm ->
  exists fr cm',
    [/\ isem_fun p ev fn fs ≈ Ret fr
      , match_fstate_out fd fr cm'
      & interp_full (pwhile.call fn) ps cm = dunit cm' ].
Proof. Admitted.

End TOEC_PROOF.
