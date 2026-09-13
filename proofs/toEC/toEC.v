(* -------------------------------------------------------------------- *)
(* Translation of a Jasmin [_uprog] into an xhl/pwhile program.         *)
(* -------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import boot order.
From mathcomp.algebra Require Import algebra.
From mathcomp.classical Require Import boolp.
From mathcomp.reals Require Import reals.
From mathcomp.analysis Require Import counting_distr.
Require Import compiler_util expr arch_decl arch_extra.
Require Import utils type sem_type sem_op_typed values warray_ word wsize.
Require Import sopn syscall global psem_defs.
From xhl.pwhile Require Import inhabited pwhile.

Unset Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(* pwhile is imported last, so its [vtype], [vname] and [Var] shadow
   Jasmin's homonyms on [var]; its [cmd] shadows [seq instr] and its
   [cond] would collide with this file's [cond] type variable.  Jasmin's
   field is recovered here once, and every pwhile *command* constructor is
   written [pwhile_new.foo] below. *)
Notation jtype x := (var.vtype x) (only parsing).

Local Open Scope ring_scope.
Local Open Scope Z_scope.

(* -------------------------------------------------------------------- *)
Module Import E.

  Definition pass : string := "to pwhile".

  Definition arity_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "wrong number of arguments".

  Definition unknown_fun_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "call to an unknown function".

  Definition dest_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "destination is not a plain variable (normalize_calls should have run)".

  Definition syscall_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "unsupported syscall shape".

  Definition cfor_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "Cfor left over (for_to_while should have run)".

  Definition cwhile_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "while with a non-empty pre-block (flatten_while should have run)".

End E.

(* -------------------------------------------------------------------- *)
(* 1. Jasmin's types as a pwhile code alphabet                          *)
(* -------------------------------------------------------------------- *)

HB.instance Definition Z_eqType_  := gen_eqMixin Z.
HB.instance Definition Z_chType_  := gen_choiceMixin Z.
HB.instance Definition Z_inhab    := isInhab.Build Z 0%Z.

HB.instance Definition word_inhab (s : wsize) := isInhab.Build (word s) 0%R.

HB.instance Definition warr_eqType_ (n : Z) := gen_eqMixin (WArray.array n).
HB.instance Definition warr_chType_ (n : Z) := gen_choiceMixin (WArray.array n).
HB.instance Definition warr_inhab   (n : Z) :=
  isInhab.Build (WArray.array n) (WArray.empty n).

(* The alphabet: a Jasmin value type *is* a pwhile type code. *)
Definition jinterp (t : ctype) : inhabType :=
  match t with
  | cbool   => (bool : inhabType)
  | cint    => (Z : inhabType)
  | carr n  => (WArray.array n : inhabType)
  | cword s => (word s : inhabType)
  end.

HB.instance Definition ctype_typeCode := isTypeCode.Build ctype jinterp.

Notation jcode  := (ctype : codeType).
Notation jident := nat.

Lemma jinterpE (t : ctype) : interp t = sem_t t :> Type.
Proof. by case: t. Qed.

Definition of_interp (t : ctype) : interp t -> sem_t t :=
  match t return interp t -> sem_t t with
  | cbool   => id
  | cint    => id
  | carr _  => id
  | cword _ => id
  end.
Arguments of_interp : clear implicits.

Definition to_interp (t : ctype) : sem_t t -> interp t :=
  match t return sem_t t -> interp t with
  | cbool   => id
  | cint    => id
  | carr _  => id
  | cword _ => id
  end.
Arguments to_interp : clear implicits.

Definition dflt_t (t : ctype) : sem_t t := of_interp t (@witness (interp t)).
Arguments dflt_t : clear implicits.

Definition tot (t : ctype) (r : exec (sem_t t)) : interp t :=
  to_interp t (rdflt (dflt_t t) r).
Arguments tot : clear implicits.

Definition nth_out (t : ctype) (k : nat) (vs : values) : interp t :=
  tot t (of_val t (nth (Vbool false) vs k)).
Arguments nth_out : clear implicits.

Definition jval (t : ctype) (v : interp t) : value := to_val (of_interp t v).
Arguments jval : clear implicits.

(* -------------------------------------------------------------------- *)
(* 2. Randomness: the image of [Csyscall (RandomBytes ws n)]            *)
(* -------------------------------------------------------------------- *)

Definition all_bytes : seq u8 := [seq wrepr U8 k | k <- ziota 0 256].

Fixpoint drand_arr {R: realType} (len : Z) (idxs : seq Z) (a : WArray.array len)
  : { distr (WArray.array len) / R } :=
  match idxs with
  | [::] => dunit a
  | i :: idxs' =>
      \dlet_(b <- duni all_bytes) drand_arr len idxs' (rdflt a (WArray.set8 a i b))
  end.

Definition drandbytes {R: realType} (len : Z) : { distr (WArray.array len) / R } :=
  drand_arr len (ziota 0 len) (WArray.empty len).

(* -------------------------------------------------------------------- *)
(* Translation                                                          *)
(* -------------------------------------------------------------------- *)

Section TOEC.
Context {R: realType}.
Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
.

#[local] Existing Instance progUnit.

Context
  (* Keyed on the whole [var], not just its name: [eval_atype] is not
     injective ([aarr U8 4] and [aarr U32 1] both give [carr 4]), so two
     Jasmin variables differing only in [atype] would otherwise share a
     pwhile location.  Injectivity is needed only on the proof side. *)
  (to_ident : var -> nat)
  (to_fname : funname -> nat)
.

(* [cmd_ A ident (cmem A ident) ident] forces procedure names and variable
   names into the *same* type, and the memory cell needs a third slot;
   [xO]/[xI]-style tagging makes the three ranges disjoint by
   construction, so only injectivity of [to_ident]/[to_fname] is assumed. *)
Definition pw_var_id (x : var)     : jident := (to_ident x).*2.+2.
Definition pw_fun_id (f : funname) : jident := (to_fname f).*2.+3.
Definition pw_mem_id               : jident := 0.

Notation pexp T := (expr_ jcode jident (cmem jcode jident) T).
Notation pwcmd  := (@cmd_ R jcode jident (cmem jcode jident) jident).

Definition pwvar (x : var) : vars_ jident (eval_atype (jtype x)) :=
  pwhile.Var (eval_atype (jtype x)) (pw_var_id x).

(* Jasmin's memory is one global array cell, [wbase Uptr] bytes wide.
   Validity and alignment are replaced by [WArray]'s bounds -- the
   "total denotations with defaults" convention -- but word access reuses
   Jasmin's own [WArray.get]/[WArray.set] at [AAdirect] (scale 1). *)
Definition mem_size : Z := wbase Uptr.

Definition memv : vars_ jident (carr mem_size) :=
  pwhile.Var (carr mem_size) pw_mem_id.

(* a translated expression, together with its Jasmin type *)
Definition texp := { t : ctype & pexp (interp t) }.

Definition mk_texp (t : ctype) (e : pexp (interp t)) : texp := existT _ t e.
Arguments mk_texp : clear implicits.

Definition texp_ty (te : texp) : ctype := projT1 te.

(* -------------------------------------------------------------------- *)
(* Coercion.  Rather than transporting along a [ctype] equality (which
   would need an [eq_rect] at every operand), a coercion is *always*
   applied, exactly as Jasmin's own [truncate_val = of_val . to_val].
   When the types already agree this is semantically the identity
   ([of_val t (to_val x) = ok x]), so nothing is lost, and the definition
   is total -- no [cexec], no dependent pattern matching. *)
Definition coerce (tsrc tdst : ctype) (e : pexp (interp tsrc)) : pexp (interp tdst) :=
  app_ (cst_ (fun v => tot tdst (of_val tdst (jval tsrc v)))) e.
Arguments coerce : clear implicits.

Definition cast_e (tdst : ctype) (te : texp) : pexp (interp tdst) :=
  let: existT tsrc e := te in coerce tsrc tdst e.
Arguments cast_e : clear implicits.

(* -------------------------------------------------------------------- *)
(* Operator arguments, as one [expr_] over [values].

   [expr_] *can* now be instantiated at [value]/[values] (it could not
   under the old stack, which is why an auxiliary small sum type was
   needed); it still cannot be instantiated at [exec _] or [sem_prod _ _],
   so operators are applied through a value list with [app_sopn]/
   [app_sopn_v] inside a closure rather than by currying [sem_prod]. *)
Fixpoint pwargs_aux (ts : seq ctype) (tes : seq texp) : pexp values :=
  match ts, tes with
  | t :: ts', te :: tes' =>
      app_ (app_ (cst_ (@cons value)) (app_ (cst_ (jval t)) (cast_e t te)))
           (pwargs_aux ts' tes')
  | _, _ => cst_ [::]
  end.

Definition pwargs (ii : instr_info) (ts : seq ctype) (tes : seq texp) :
    cexec (pexp values) :=
  if size ts == size tes then ok (pwargs_aux ts tes)
  else Error (arity_error ii).

(* ==================================================================== *)
(* 3. Expressions                                                       *)
(* ==================================================================== *)

Definition pwgvar (x : gvar) : texp :=
  let xv := (gv x).(v_var) in
  mk_texp (eval_atype (jtype xv))
    (if x.(gs) is Slocal then var_ (pwvar xv) else gvar_ (pwvar xv)).

(* Array reads and writes need the array *length*, which lives in the
   code; a dependent match on the code exposes it.  The non-array branches
   are unreachable for a well-typed program. *)
Definition arr_get (al : aligned) (aa : arr_access) (ws : wsize)
    (te : texp) (ei : pexp (interp cint)) : pexp (interp (cword ws)) :=
  let: existT t e := te in
  (match t return pexp (interp t) -> pexp (interp (cword ws)) with
   | carr n  => fun e =>
       app_ (app_ (cst_ (fun (a : WArray.array n) (k : Z) =>
                           rdflt 0%R (WArray.get al aa ws a k))) e) ei
   | cbool   => fun _ => cst_ 0%R
   | cint    => fun _ => cst_ 0%R
   | cword _ => fun _ => cst_ 0%R
   end) e.

Definition arr_get_sub (aa : arr_access) (ws : wsize) (len : Z)
    (te : texp) (ei : pexp (interp cint))
  : pexp (interp (carr (arr_size ws len))) :=
  let: existT t e := te in
  (match t return pexp (interp t) -> pexp (interp (carr (arr_size ws len))) with
   | carr n  => fun e =>
       app_ (app_ (cst_ (fun (a : WArray.array n) (k : Z) =>
                           rdflt (WArray.empty (arr_size ws len))
                                 (WArray.get_sub aa ws len a k))) e) ei
   | cbool   => fun _ => cst_ (WArray.empty _)
   | cint    => fun _ => cst_ (WArray.empty _)
   | cword _ => fun _ => cst_ (WArray.empty _)
   end) e.

Fixpoint toEC_e (ii : instr_info) (e : pexpr) : cexec texp :=
  match e with
  | Pconst z => ok (mk_texp cint (cst_ z))

  | Pbool b => ok (mk_texp cbool (cst_ b))

  | Parr_init ws n =>
      ok (mk_texp (carr (arr_size ws n)) (cst_ (WArray.empty (arr_size ws n))))

  | Pvar x => ok (pwgvar x)

  | Pget al aa ws x i =>
      Let ti := toEC_e ii i in
      ok (mk_texp (cword ws) (arr_get al aa ws (pwgvar x) (cast_e cint ti)))

  | Psub aa ws len x i =>
      Let ti := toEC_e ii i in
      ok (mk_texp (carr (arr_size ws len))
            (arr_get_sub aa ws len (pwgvar x) (cast_e cint ti)))

  | Pload al ws a =>
      Let ta := toEC_e ii a in
      ok (mk_texp (cword ws)
            (app_ (app_ (cst_ (fun (m : WArray.array mem_size) (p : word Uptr) =>
                                 rdflt 0%R
                                   (WArray.get al AAdirect ws m (wunsigned p))))
                     (gvar_ memv))
                  (cast_e (cword Uptr) ta)))

  (* [of_interp] is applied *inside* the closure, so the closure's own type
     is [interp t1 -> interp t2] -- small enough to index [expr_]. *)
  | Papp1 o e1 =>
      Let t1 := toEC_e ii e1 in
      ok (mk_texp (eval_atype (type_of_op1 o).2)
            (app_ (cst_ (fun v =>
                     tot (eval_atype (type_of_op1 o).2)
                       (sem_sop1_typed o
                          (of_interp (eval_atype (type_of_op1 o).1) v))))
                  (cast_e (eval_atype (type_of_op1 o).1) t1)))

  | Papp2 o e1 e2 =>
      Let t1 := toEC_e ii e1 in
      Let t2 := toEC_e ii e2 in
      ok (mk_texp (eval_atype (type_of_op2 o).2)
            (app_ (app_ (cst_ (fun v1 v2 =>
                       tot (eval_atype (type_of_op2 o).2)
                         (sem_sop2_typed o
                            (of_interp (eval_atype (type_of_op2 o).1.1) v1)
                            (of_interp (eval_atype (type_of_op2 o).1.2) v2))))
                     (cast_e (eval_atype (type_of_op2 o).1.1) t1))
                  (cast_e (eval_atype (type_of_op2 o).1.2) t2)))

  | PappN o es =>
      Let tes := mapM (toEC_e ii) es in
      Let args := pwargs ii (map eval_atype (type_of_opN o).1) tes in
      ok (mk_texp (eval_atype (type_of_opN o).2)
            (app_ (cst_ (fun vs =>
                     tot (eval_atype (type_of_opN o).2)
                       (app_sopn (map eval_atype (type_of_opN o).1)
                          (sem_opN_typed o) vs)))
                  args))

  | Pif ty b e1 e2 =>
      Let tb := toEC_e ii b in
      Let t1 := toEC_e ii e1 in
      Let t2 := toEC_e ii e2 in
      ok (mk_texp (eval_atype ty)
            (app_ (app_ (app_
                     (cst_ (fun (c : bool) (v1 v2 : interp (eval_atype ty)) =>
                              if c then v1 else v2))
                     (cast_e cbool tb))
                     (cast_e (eval_atype ty) t1))
                  (cast_e (eval_atype ty) t2)))
  end.

Definition toEC_es (ii : instr_info) (es : pexprs) : cexec (seq texp) :=
  mapM (toEC_e ii) es.

(* -------------------------------------------------------------------- *)
(* Assertions.  [Cassert] becomes [If b then skip else abort]: [abort]
   denotes [dnull], so a failed assertion has no behaviour -- which is
   what Jasmin's [sem_assert] raising [ErrAssert] should map to.

   Two of the five [eassert] forms have no counterpart in this model and
   are over-approximated by [true]: every pwhile variable holds a value,
   and every address of the memory cell is readable.  That is sound in
   the direction the theorem is stated -- where Jasmin's check is false,
   [sem_assert] errors and the statement's left-hand [errcutoff]
   discharges the obligation.  [sem_assert]'s [assert_allowed] guard is
   dropped for the same reason.

   Note this makes the translation total on [Cassert], so it no longer
   depends on [remove_assert] (run inside [legalize_names]) having
   removed them: a program that still carries assertions translates. *)
Fixpoint toEC_assert (ii : instr_info) (a : eassert) : cexec (pexp bool) :=
  match a with
  | Pexpr e =>
      Let te := toEC_e ii e in
      ok (cast_e cbool te)

  | PappN_safety o es =>
      Let tes := toEC_es ii es in
      Let args := pwargs ii (map eval_atype (type_of_opN_safety o).1) tes in
      ok (app_ (cst_ (fun vs => rdflt false (sem_opN_safety o vs))) args)

  | Pis_var_init _ => ok (cst_ true)

  | Pis_mem_init _ _ => ok (cst_ true)

  | Pand a1 a2 =>
      Let b1 := toEC_assert ii a1 in
      Let b2 := toEC_assert ii a2 in
      ok (app_ (app_ (cst_ andb) b1) b2)
  end.

(* ==================================================================== *)
(* 4. Left-hand sides                                                   *)
(* ==================================================================== *)

(* Parallel assignment.  [block bs skip rs] evaluates [bs] in the *outer*
   memory into a frame that [minit]'s [mnew] has just wiped, then [mret]
   restores the outer locals and evaluates [rs] in that frame.  Reading
   each bound variable straight back therefore performs a simultaneous
   assignment -- with no auxiliary names to invent, and without
   re-evaluating right-hand sides that a destination may clobber
   ([normalize_calls] does not make destinations disjoint from the
   arguments' reads). *)
Definition pw_bind (x : var) (te : texp) : binding :=
  bind_of (pwvar x) (cast_e (eval_atype (jtype x)) te).

Definition passign (bs : seq binding) : pwcmd :=
  pwhile.block bs pwhile.skip
    (map (fun b => let: existT _ (x, _) := b in bind_of x (var_ x)) bs).

(* An array/memory write, with the length again exposed by a match. *)
Definition arr_set_cmd (al : aligned) (aa : arr_access) (ws : wsize)
    (x : var) (ei : pexp (interp cint)) (ev : pexp (interp (cword ws))) : pwcmd :=
  (match eval_atype (jtype x) as c
     return vars_ jident c -> pwcmd with
   | carr n  => fun v =>
       pwhile.assign v
         (app_ (app_ (app_
                  (cst_ (fun (a : WArray.array n) (k : Z) (w : word ws) =>
                           rdflt a (WArray.set a al aa k w))) (var_ v)) ei) ev)
   | cbool   => fun _ => pwhile.skip
   | cint    => fun _ => pwhile.skip
   | cword _ => fun _ => pwhile.skip
   end) (pwvar x).

Definition arr_setsub_cmd (aa : arr_access) (ws : wsize) (len : Z)
    (x : var) (ei : pexp (interp cint))
    (ev : pexp (interp (carr (arr_size ws len)))) : pwcmd :=
  (match eval_atype (jtype x) as c
     return vars_ jident c -> pwcmd with
   | carr n  => fun v =>
       pwhile.assign v
         (app_ (app_ (app_
                  (cst_ (fun (a : WArray.array n) (k : Z)
                             (b : WArray.array (arr_size ws len)) =>
                           rdflt a (WArray.set_sub aa a k b))) (var_ v)) ei) ev)
   | cbool   => fun _ => pwhile.skip
   | cint    => fun _ => pwhile.skip
   | cword _ => fun _ => pwhile.skip
   end) (pwvar x).

Definition toEC_lv (ii : instr_info) (lv : lval) (te : texp) : cexec pwcmd :=
  match lv with
  | Lnone _ _ => ok pwhile.skip

  | Lvar x =>
      ok (pwhile.assign (pwvar x.(v_var))
            (cast_e (eval_atype (jtype x.(v_var))) te))

  | Laset al aa ws x i =>
      Let ti := toEC_e ii i in
      ok (arr_set_cmd al aa ws x.(v_var) (cast_e cint ti) (cast_e (cword ws) te))

  | Lasub aa ws len x i =>
      Let ti := toEC_e ii i in
      ok (arr_setsub_cmd aa ws len x.(v_var) (cast_e cint ti)
            (cast_e (carr (arr_size ws len)) te))

  | Lmem al ws _ a =>
      Let ta := toEC_e ii a in
      ok (pwhile.gassign memv
            (app_ (app_ (app_
                     (cst_ (fun (m : WArray.array mem_size) (p : word Uptr)
                                (w : word ws) =>
                              rdflt m (WArray.set m al AAdirect (wunsigned p) w)))
                     (gvar_ memv))
                     (cast_e (cword Uptr) ta))
                  (cast_e (cword ws) te)))
  end.

(* Sequential writes, used when there is at most one destination. *)
Fixpoint toEC_lvs_seq (ii : instr_info) (lvs : lvals) (tes : seq texp) :
    cexec pwcmd :=
  match lvs, tes with
  | [::], [::] => ok pwhile.skip
  | lv :: lvs', te :: tes' =>
      Let c1 := toEC_lv ii lv te in
      Let c2 := toEC_lvs_seq ii lvs' tes' in
      ok (pwhile.seqc c1 c2)
  | _, _ => Error (arity_error ii)
  end.

(* Two or more destinations: they are pairwise-distinct [Lvar]s (by
   [normalize_calls]), so one parallel assignment is both correct and free
   of auxiliaries. *)
Fixpoint lvs_bindings (ii : instr_info) (lvs : lvals) (tes : seq texp) :
    cexec (seq binding) :=
  match lvs, tes with
  | [::], [::] => ok [::]
  | Lvar x :: lvs', te :: tes' =>
      Let bs := lvs_bindings ii lvs' tes' in
      ok (pw_bind x.(v_var) te :: bs)
  | _ :: _, _ :: _ => Error (dest_error ii)
  | _, _ => Error (arity_error ii)
  end.

Definition toEC_lvs (ii : instr_info) (lvs : lvals) (tes : seq texp) :
    cexec pwcmd :=
  if (size lvs <= 1)%nat then toEC_lvs_seq ii lvs tes
  else Let bs := lvs_bindings ii lvs tes in ok (passign bs).

(* [random] demands the sampled distribution be at the variable's own
   code, so the destination's array length has to be exposed before
   [drandbytes] fits.  [normalize_calls] guarantees it is an array. *)
Definition rand_assign (ii : instr_info) (x : var) : cexec pwcmd :=
  (match eval_atype (jtype x) as c
     return vars_ jident c -> cexec pwcmd with
   | carr n  => fun v => ok (pwhile.random v (cst_ (drandbytes n)))
   | cbool   => fun _ => Error (syscall_error ii)
   | cint    => fun _ => Error (syscall_error ii)
   | cword _ => fun _ => Error (syscall_error ii)
   end) (pwvar x).

(* ==================================================================== *)
(* 5. Instructions                                                      *)
(* ==================================================================== *)

(* A call frame: arguments are evaluated in the caller's memory by
   [minit], results are read out of the callee's final memory by [mret],
   which also restores the caller's locals while keeping the callee's
   globals -- so Jasmin's memory threading through calls is preserved. *)
Definition call_cmd (fd : _ufundef) (fn : funname) (ii : instr_info)
    (lvs : lvals) (tes : seq texp) : cexec pwcmd :=
  Let bs :=
    mapM2 (arity_error ii)
      (fun (x : var_i) (te : texp) => ok (pw_bind x.(v_var) te))
      fd.(f_params) tes
  in
  let res : seq texp :=
    map (fun (x : var_i) =>
           mk_texp (eval_atype (jtype x.(v_var))) (var_ (pwvar x.(v_var))))
        fd.(f_res)
  in
  Let rs := lvs_bindings ii lvs res in
  ok (pwhile.block bs (pwhile.call (pw_fun_id fn)) rs).

(* Same shape as the other passes (cf. [flatten_while.v:12-22]): the
   command-level fold takes the instruction-level translation as a
   parameter, so the recursion below is structural on [instr] alone.
   [cmd] is pwhile's notation here, so Jasmin commands are spelled
   [seq instr] throughout this file. *)
Section CMD.

Context (toEC_i : instr -> cexec pwcmd).

Fixpoint toEC_c_aux (c : seq instr) : cexec pwcmd :=
  match c with
  | [::] => ok pwhile.skip
  | i :: c' =>
      Let d1 := toEC_i i in
      Let d2 := toEC_c_aux c' in
      ok (pwhile.seqc d1 d2)
  end.

End CMD.

Fixpoint toEC_i (p : _uprog) (i : instr) : cexec pwcmd :=
  let: MkI ii ir := i in
  match ir with
  | Cassgn lv _ ty e =>
      Let te := toEC_e ii e in
      toEC_lv ii lv (mk_texp (eval_atype ty) (cast_e (eval_atype ty) te))

  (* One closure per output position.  [semi] is a pure function of the
     arguments, and all copies read the same [args] expression -- which
     [passign] evaluates once, in the caller's memory -- so the
     duplication is syntactic only. *)
  | Copn lvs _ o es =>
      Let tes := toEC_es ii es in
      let d := get_instr_desc o in
      Let args := pwargs ii (map eval_atype d.(tin)) tes in
      let outs :=
        mapi (fun k t =>
                mk_texp t
                  (app_ (cst_ (fun vs =>
                            nth_out t k (rdflt [::] (app_sopn_v d.(semi) vs))))
                        args))
             (map eval_atype d.(tout))
      in
      toEC_lvs ii lvs outs

  | Csyscall lvs o es =>
      match o, lvs with
      | RandomBytes _ _, [:: Lvar x] => rand_assign ii x.(v_var)
      | _, _ => Error (syscall_error ii)
      end

  | Cassert a =>
      Let b := toEC_assert ii a.2 in
      ok (pwhile.cond b pwhile.skip pwhile.abort)

  | Cif e c1 c2 =>
      Let te := toEC_e ii e in
      Let d1 := toEC_c_aux (toEC_i p) c1 in
      Let d2 := toEC_c_aux (toEC_i p) c2 in
      ok (pwhile.cond (cast_e cbool te) d1 d2)

  | Cfor _ _ _ => Error (cfor_error ii)

  | Cwhile _ c1 e _ c2 =>
      if c1 is [::] then
        Let te := toEC_e ii e in
        Let d2 := toEC_c_aux (toEC_i p) c2 in
        ok (pwhile.while (cast_e cbool te) d2)
      else Error (cwhile_error ii)

  | Ccall lvs fn es =>
      Let tes := toEC_es ii es in
      match get_fundef (p_funcs p) fn with
      | Some fd => call_cmd fd fn ii lvs tes
      | None => Error (unknown_fun_error ii)
      end
  end.

Definition toEC_c (p : _uprog) (c : seq instr) : cexec pwcmd :=
  toEC_c_aux (toEC_i p) c.

(* ==================================================================== *)
(* 6. Programs                                                          *)
(* ==================================================================== *)

(* Function bodies need no prologue: [minit]'s [mnew] wipes the frame to
   [witness], and [init_local_arrays] has already emitted an explicit
   [Parr_init] assignment for every local array. *)
Definition toEC_fd (p : _uprog) (fd : _ufundef) : cexec pwcmd :=
  toEC_c p fd.(f_body).

Definition toEC_fun_decl (p : _uprog) (fnd : funname * _ufundef) :
    cexec (jident * pwcmd) :=
  let: (fn, fd) := fnd in
  Let c := toEC_fd p fd in
  ok (pw_fun_id fn, c).

Definition toEC_funcs (p : _uprog) : cexec (seq (jident * pwcmd)) :=
  mapM (toEC_fun_decl p) (p_funcs p).

Fixpoint pw_assoc (l : seq (jident * pwcmd)) (f : jident) : pwcmd :=
  match l with
  | [::] => pwhile.abort
  | gc :: l' => if gc.1 == f then gc.2 else pw_assoc l' f
  end.

(* [abort] as the default for an unknown name is unreachable for accepted
   programs -- [normalize_calls] rejects calls to unknown functions, and so
   does [Ccall] above -- and it denotes [dnull], which is below everything
   in the refinement order anyway. *)
Definition toEC_ps (p : _uprog) : cexec (jident -> pwcmd) :=
  Let l := toEC_funcs p in ok (pw_assoc l).

(* Compile-time data: one [gassign] per global constant. *)
Definition toEC_glob (gd : glob_decl) : pwcmd :=
  let: (x, g) := gd in
  match g with
  | Gword ws w =>
      pwhile.gassign (pwvar x)
        (coerce (cword ws) (eval_atype (jtype x)) (cst_ w))
  | Garr len a =>
      pwhile.gassign (pwvar x)
        (coerce (carr len) (eval_atype (jtype x)) (cst_ a))
  end.

Definition toEC_globs (gd : glob_decls) : pwcmd :=
  foldr (fun g c => pwhile.seqc (toEC_glob g) c) pwhile.skip gd.

End TOEC.
