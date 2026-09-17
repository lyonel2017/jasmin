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
Require Import utils type sem_type sem_op_typed values varmap low_memory warray_ word wsize.
Require Import sopn syscall global psem_defs.

From xhl.pwhile Require Import inhabited mem pwhile.

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

  Definition typing_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii "wrong type".

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

  Definition global_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "global variable (remove_globals should have run)".

  Definition init_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "is_init on a variable is not representable".

  Definition assert_error (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "assert with assertions disabled always fails".

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

(* The alphabet: a Jasmin value type is a pwhile type code. *)
Definition jinterp (t : ctype) : inhabType :=
  match t with
  | cbool   => (bool : inhabType)
  | cint    => (Z : inhabType)
  | carr n  => (WArray.array n : inhabType)
  | cword s => (word s : inhabType)
  end.

HB.instance Definition ctype_typeCode := isTypeCode.Build ctype jinterp.

Notation jcode  := (ctype : codeType).

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

Definition jof_val (t : ctype) (v : value) : interp t := tot t (of_val t v).
Arguments jof_val : clear implicits.

Definition nth_out (t : ctype) (k : nat) (vs : values) : interp t :=
  jof_val t (nth (Vbool false) vs k).
Arguments nth_out : clear implicits.

Definition jval (t : ctype) (v : interp t) : value := to_val (of_interp t v).
Arguments jval : clear implicits.

(* [jof_val] undoes [jval].  This is the roundtrip that [mget_eq_] rests on. *)
Lemma to_of_interp (t : ctype) (v : interp t) : to_interp t (of_interp t v) = v.
Proof. by case: t v => [ | | n | s] v. Qed.

Lemma jof_val_jval (t : ctype) (v : interp t) : jof_val t (jval t v) = v.
Proof. by rewrite /jof_val /jval /tot of_val_to_val /=; apply: to_of_interp. Qed.

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
(* 3. A Jasmin state as a pwhile memory                                 *)
(* -------------------------------------------------------------------- *)

(* Jasmin's memory is the *only* thing in the global store: there are no
   global variables, so the global alphabet has a single code whose
   interpretation is [mem] itself, and a single identifier.  That is what
   makes [emem : mem] a genuine field rather than a slot in an encoding --
   the old [WArray (wbase Uptr)] cell existed only because the mixin used
   to have one alphabet, with no code for [mem]. *)

(* [mem] has no derivable inhabitant: it is [Parameter mem : PointerData ->
   Type] (memory_model.v) whose only constructor in [MemoryT] is
   [init : seq (pointer * Z) -> pointer -> exec mem], with no success spec.
   [isTypeCode] needs an inhabited interpretation, so one is assumed. *)
Axiom mem_witness : forall {pd : PointerData}, @mem pd.

(* [gcode] is parameterized by [pd] on purpose: [ginterp Gmem] is [@mem pd],
   so an instance on a bare [gcode] would discharge to [forall pd,
   isTypeCode gcode] with [pd] undetermined by the key, and [interp Gmem]
   would carry an unresolvable evar.  Same idiom as Jasmin's own
   [Arguments mem {_}]. *)
Variant gcode (pd : PointerData) := Gmem.
Arguments gcode {_}.
Arguments Gmem {_}.

Section GCode.
Context {pd : PointerData}.

Definition gcode_eqb (c1 c2 : gcode) : bool := true.

Lemma gcode_eqP : Equality.axiom gcode_eqb.
Proof. by case=> - []; constructor. Qed.

HB.instance Definition gcode_eqType := hasDecEq.Build gcode gcode_eqP.

Lemma mem_comparable : comparable (@mem pd).
Proof. by move=> m1 m2; apply/pselect. Qed.

HB.instance Definition mem_eqType :=
  hasDecEq.Build (@mem pd) (compareP mem_comparable).

HB.instance Definition mem_choiceType := gen_choiceMixin (@mem pd).

HB.instance Definition mem_inhab := isInhab.Build (@mem pd) mem_witness.

Definition ginterp (t : gcode) : inhabType :=
  match t with Gmem => (mem : inhabType) end.

HB.instance Definition gcode_typeCode := isTypeCode.Build gcode ginterp.

Lemma ginterpE : interp (@Gmem pd) = mem :> Type.
Proof. by []. Qed.

End GCode.

(* The two identifier types.  Locals are named by Jasmin variables; the
   global store holds only the memory, so one identifier suffices -- and
   that is what makes [mgetg_neq_] vacuous at [Gmem]/[Gmem].  These are
   notations, so [gcode]'s implicit [pd] resolves at the use site. *)
Notation jident  := var.
Notation jidentg := unit.
Notation jgcode  := (gcode : codeType).

(* -------------------------------------------------------------------- *)
Section Mem.
  Context {wsw : WithSubWord}.   (* for [Vm.t] *)
  Context {pd  : PointerData}.   (* for [mem]  *)

(* -------------------------------------------------------------------- *)
(* Keys.

   [Vm.set vm x v] stores [vm_truncate_val (eval_atype (Var.vtype x)) v]
   (varmap.v), so a slot may only be keyed by a variable whose type is the
   one being written -- otherwise the value read back is not the one that
   was written, and [mget_eq_] fails.  [atype_of_ctype] rebuilds that type
   from the pwhile type code, which makes the truncation the identity by
   construction, with no runtime check.

   It is a section of [eval_atype] -- which is itself *not* injective,
   since [aarr U16 4] and [aarr U8 8] share the [ctype] [carr 8] -- and is
   therefore injective. *)
Definition atype_of_ctype (t : ctype) : atype :=
  match t with
  | cbool   => abool
  | cint    => aint
  | carr n  => aarr U8 n
  | cword s => aword s
  end.

Lemma eval_atype_of_ctype : cancel atype_of_ctype eval_atype.
Proof. by case=> // n /=; congr carr; rewrite arr_sizeE; exact: Z.mul_1_l. Qed.

Lemma atype_of_ctype_inj : injective atype_of_ctype.
Proof. exact: (can_inj eval_atype_of_ctype). Qed.

Definition key (t : ctype) (x : Ident.ident) : var :=
  Var.Var (atype_of_ctype t) x.

Lemma eval_vtype_key (t : ctype) (x : Ident.ident) :
  eval_atype (Var.vtype (key t x)) = t.
Proof. exact: eval_atype_of_ctype. Qed.

Lemma key_neq (t u : ctype) (x y : Ident.ident) :
  (t <> u \/ x != y) -> key t x != key u y.
Proof.
move=> h; apply/eqP => -[] e1 e2; case: h => [ne | /eqP ne].
+ by apply: ne; apply: atype_of_ctype_inj.
by apply: ne.
Qed.

(* The point of the whole scheme: at a key built by [key], Jasmin's
   truncation on write is the identity, so nothing is lost. *)
Lemma vm_truncate_val_jval (t : ctype) (v : interp t) :
  vm_truncate_val t (jval t v) = jval t v.
Proof. by apply: vm_truncate_val_eq; exact: type_of_to_val. Qed.

(* -------------------------------------------------------------------- *)
(* The state.

   This is Jasmin's [estate] minus [escs]: [emem] is Jasmin's memory,
   verbatim.  [evm] is the local store -- a family of Jasmin varmaps
   indexed by the Jasmin type rather than a single one, because [key]
   pins the in-map variable's type to [atype_of_ctype T] (so that
   [Vm.set]'s truncation is the identity) and that leaves only the
   [ident] component free.  Making the Jasmin type the family index is
   what keeps two variables sharing a name but not a type -- which
   [eval_atype] would otherwise conflate -- in distinct slots. *)
Record jstate := Jstate {
  emem : mem;
  evm  : atype -> Vm.t
}.

Definition fupd (f : atype -> Vm.t) (a : atype) (vm : Vm.t) : atype -> Vm.t :=
  fun b => if a == b then vm else f b.

Lemma fupd_eq (f : atype -> Vm.t) (a : atype) (vm : Vm.t) :
  fupd f a vm a = vm.
Proof. by rewrite /fupd eqxx. Qed.

Lemma fupd_neq (f : atype -> Vm.t) (a b : atype) (vm : Vm.t) :
  a != b -> fupd f a vm b = f b.
Proof. by rewrite /fupd => /negbTE ->. Qed.

(* -------------------------------------------------------------------- *)
(* Local memory.

   [jget] is Jasmin's [get_var] with the definedness check replaced by a
   default -- [interp t] has no undefined inhabitant, so the check is
   vacuous -- and [jset] is [set_var] with the truncation check replaced
   by the retyped key, which makes it succeed by construction. *)
Definition jget (m : jstate) (t : ctype) (x : jident) : interp t :=
  jof_val t (evm m (Var.vtype x)).[key t (Var.vname x)]%vm.

Definition jset (m : jstate) (t : ctype) (x : jident) (v : interp t) : jstate :=
  Jstate (emem m)
    (fupd (evm m) (Var.vtype x)
       (evm m (Var.vtype x)).[key t (Var.vname x) <- jval t v]%vm).

(* -------------------------------------------------------------------- *)
(* Global memory: Jasmin's memory, and nothing else.  Both operations are
   a dependent match on the single code -- no [type_eq_dec], no [ecast]
   and no heterogeneous update. *)
Definition jgetg (m : jstate) (T : jgcode) (_ : jidentg) : interp T :=
  match T return interp T with Gmem => emem m end.

Definition jsetg (m : jstate) (T : jgcode) (_ : jidentg) (v : interp T) : jstate :=
  match T return interp T -> jstate with Gmem => fun v => Jstate v (evm m) end v.

(* Frame entry and exit.  No law forces [jnew] to clear the locals (there
   is no [mget_new_]), but leaving them would let a callee read the
   caller's frame through [minit]. *)
Definition jnew (m : jstate) : jstate := Jstate (emem m) (fun _ => Vm.init).

Definition jrestore (m0 m : jstate) : jstate := Jstate (emem m) (evm m0).

(* Jasmin's memory, as a pwhile global variable: [gvar_ memv] is an
   expression of type [interp Gmem = mem], so [Pload] / [Lmem] translate
   through Jasmin's own [read] / [write] rather than an array encoding. *)
Definition memv : vars_ jidentg (@Gmem pd) := pwhile.Var (@Gmem pd) tt.

(* -------------------------------------------------------------------- *)
(* The [isMemType] laws.  [mset_eq_] is no longer one of them, so [jset]
   needs no equality short-circuit and [interp t] need not be an eqType. *)

Lemma jget_jset (t : ctype) (m : jstate) (x : jident) (v : interp t) :
  jget (jset m t x v) t x = v.
Proof.
rewrite /jget /jset /= fupd_eq Vm.setP_eq eval_vtype_key vm_truncate_val_jval.
exact: jof_val_jval.
Qed.

Lemma jget_jset_neq (t u : ctype) (m : jstate) (x y : jident) (v : interp t) :
  (t <> u \/ x != y) -> jget (jset m t x v) u y = jget m u y.
Proof.
move=> h; rewrite /jget /jset /=.
case: (eqVneq (Var.vtype x) (Var.vtype y)) => [e | ne]; last by rewrite fupd_neq.
have hk : key t (Var.vname x) != key u (Var.vname y).
+ apply: key_neq; case: h => [ht | hxy]; first by left.
  right; apply: contra hxy => /eqP hn; apply/eqP.
  by move: e hn; case: x => [tx nx]; case: y => [ty ny] /= -> ->.
by rewrite -e fupd_eq Vm.setP_neq.
Qed.

Lemma jgetg_jsetg (T : jgcode) (m : jstate) (u : jidentg) (v : interp T) :
  jgetg (jsetg m T u v) T u = v.
Proof. by case: T v => v. Qed.

(* Vacuous: [jgcode] has one code and [jidentg] one identifier, so the
   premise is unsatisfiable.  This is exactly what having a dedicated
   alphabet for the global store buys -- the memory is a single slot. *)
Lemma jgetg_jsetg_neq (T U : jgcode) (m : jstate) (u u' : jidentg)
    (v : interp T) :
  (T <> U \/ u != u') -> jgetg (jsetg m T u v) U u' = jgetg m U u'.
Proof.
case: T U v => - [] v [h | h]; first by case: h.
by move: h; case: u; case: u'; rewrite eqxx.
Qed.

Lemma jget_jsetg (T : jgcode) (u : ctype) (m : jstate) (p : jidentg)
    (y : jident) (v : interp T) :
  jget (jsetg m T p v) u y = jget m u y.
Proof. by case: T v => v. Qed.

Lemma jgetg_jset (t : ctype) (U : jgcode) (m : jstate) (x : jident)
    (q : jidentg) (v : interp t) :
  jgetg (jset m t x v) U q = jgetg m U q.
Proof. by case: U. Qed.

Lemma jgetg_jnew (U : jgcode) (m : jstate) (q : jidentg) :
  jgetg (jnew m) U q = jgetg m U q.
Proof. by case: U. Qed.

Lemma jrestore_id (m : jstate) : jrestore m m = m.
Proof. by case: m. Qed.

Lemma jrestoreA (m0 m1 m : jstate) :
  jrestore m0 (jrestore m1 m) = jrestore m0 m.
Proof. by []. Qed.

Lemma jrestore_jnew (m0 m : jstate) : jrestore m0 (jnew m) = jrestore m0 m.
Proof. by []. Qed.

Lemma jrestore_jset (t : ctype) (m0 m : jstate) (x : jident) (v : interp t) :
  jrestore m0 (jset m t x v) = jrestore m0 m.
Proof. by []. Qed.

Lemma jrestore_jsetg (T : jgcode) (m0 m : jstate) (p : jidentg)
    (v : interp T) :
  jrestore m0 (jsetg m T p v) = jsetg (jrestore m0 m) T p v.
Proof. by case: T v => v. Qed.

Lemma jget_jrestore (u : ctype) (m0 m : jstate) (y : jident) :
  jget (jrestore m0 m) u y = jget m0 u y.
Proof. by []. Qed.

Lemma jgetg_jrestore (U : jgcode) (m0 m : jstate) (q : jidentg) :
  jgetg (jrestore m0 m) U q = jgetg m U q.
Proof. by case: U. Qed.

(* -------------------------------------------------------------------- *)
Lemma jstate_comparable : comparable jstate.
Proof. by move=> m1 m2; apply/pselect. Qed.

HB.instance Definition jstate_eqType :=
  hasDecEq.Build jstate (compareP jstate_comparable).

HB.instance Definition jstate_choiceType := gen_choiceMixin jstate.

HB.instance Definition jstate_memType :=
  isMemType.Build ctype jgcode jident jidentg jstate
    (@jget_jset) (@jget_jset_neq)
    (@jgetg_jsetg) (@jgetg_jsetg_neq)
    (@jget_jsetg) (@jgetg_jset) (@jgetg_jnew)
    jrestore_id jrestoreA jrestore_jnew (@jrestore_jset) (@jrestore_jsetg)
    (@jget_jrestore) (@jgetg_jrestore).

Definition jmem : memType jcode jgcode jident jidentg := jstate.

(* -------------------------------------------------------------------- *)
(* Sanity checks: the instance found by canonical structure resolution is
   the one defined above, and it separates the slots it is meant to. *)

Example mget_mset_j (t : ctype) (m : jstate) (x : jident) (v : interp t) :
  @mget jcode jgcode jident jidentg jstate t
    (@mset jcode jgcode jident jidentg jstate t m x v) x = v.
Proof. exact: mget_eq. Qed.

(* The memory round-trips through the instance, at [mem] itself. *)
Example mgetg_msetg_mem (m : jstate) (mm : mem) :
  @mgetg jcode jgcode jident jidentg jstate (@Gmem pd)
    (@msetg jcode jgcode jident jidentg jstate (@Gmem pd) m tt mm) tt = mm.
Proof. exact: mgetg_eq. Qed.

(* Two Jasmin variables sharing a name but not a type keep distinct slots,
   even when [eval_atype] conflates their types: [aarr U16 4] and
   [aarr U8 8] both evaluate to [carr 8].  This is what the [atype]-indexed
   family buys over keying the store by a bare [Ident.ident]. *)
Example slots_distinct (n : Ident.ident) (m : jstate) (a : interp (carr 8)) :
  @mget jcode jgcode jident jidentg jstate (carr 8)
    (@mset jcode jgcode jident jidentg jstate (carr 8) m
       (Var.Var (aarr U16 4) n) a)
    (Var.Var (aarr U8 8) n)
  = @mget jcode jgcode jident jidentg jstate (carr 8) m (Var.Var (aarr U8 8) n).
Proof. by apply: mget_neq; right. Qed.

End Mem.

(* -------------------------------------------------------------------- *)
(* 4. Translation                                                       *)
(* -------------------------------------------------------------------- *)

Section TOEC.
Context {R : realType}.
Context {wsw : WithSubWord}.   (* [Vm.t], hence [jstate] / [jmem] *)
Context {wa  : WithAssert}.    (* [assert_allowed] *)
Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
.

(* [PointerData] needs no [Context] of its own: [arch_pd] (arch_decl.v)
   derives it from [asm_e]. *)

#[local] Existing Instance progUnit.

Notation pexp T := (expr_ jcode jgcode jident jidentg jmem T).
Notation pwcmd  := (@cmd_ R jcode jgcode jident jidentg jmem funname).

(* A Jasmin variable *is* a pwhile local identifier, so no injection is
   needed.  [pwvar] is injective; [eval_atype] is not, so [x : u16[4]] and
   [x : u8[8]] get the same type code -- they still occupy distinct slots,
   which is what the [atype]-indexed [evm] family buys, and Jasmin's own
   [convertible] already identifies those two types. *)
Definition pwvar (x : var) : vars_ jident (eval_atype (jtype x)) :=
  pwhile.Var (eval_atype (jtype x)) x.

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
   ([jof_val_jval]), so nothing is lost, and the definition is total --
   no [cexec], no dependent pattern matching. *)
Definition coerce (tsrc tdst : ctype) (e : pexp (interp tsrc)) : pexp (interp tdst) :=
  app_ (cst_ (fun v => jof_val tdst (jval tsrc v))) e.
Arguments coerce : clear implicits.

Definition cast_e (tdst : ctype) (te : texp) : pexp (interp tdst) :=
  let: existT tsrc e := te in coerce tsrc tdst e.
Arguments cast_e : clear implicits.

(* -------------------------------------------------------------------- *)
(* Operator arguments, as one [expr_] over [values].

   [expr_] can be instantiated at [value]/[values], but still not at
   [exec _] or [sem_prod _ _], so operators are applied through a value
   list with [app_sopn] / [app_sopn_v] inside a closure rather than by
   currying [sem_prod]. *)
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

(* -------------------------------------------------------------------- *)
(* 5. Expressions                                                       *)
(* -------------------------------------------------------------------- *)

(* There are no global variables, so the [Sglob] case is rejected rather
   than translated -- [remove_globals] must have run. *)
Definition pwgvar (ii : instr_info) (x : gvar) : cexec texp :=
  if x.(gs) is Slocal then
    let xv := (gv x).(v_var) in
    ok (mk_texp (eval_atype (jtype xv)) (var_ (pwvar xv)))
  else Error (global_error ii).

Fixpoint toEC_e (ii : instr_info) (e : pexpr) : cexec texp :=
  match e with
  | Pconst z => ok (mk_texp cint (cst_ z))

  | Pbool b => ok (mk_texp cbool (cst_ b))

  | Parr_init ws n =>
      ok (mk_texp (carr (arr_size ws n)) (cst_ (WArray.empty (arr_size ws n))))

  | Pvar x => pwgvar ii x

  | Pget al aa ws x i =>
      Let ti := toEC_e ii i in
      Let tx := pwgvar ii x in
      let ei := (cast_e cint ti) in
      let: existT t e := tx in
      (match t return pexp (interp t) -> cexec texp with
       | carr n  => fun e =>
                     let e :=
                       app_ (app_ (cst_ (fun (a : WArray.array n) (k : Z) =>
                                           rdflt 0%R (WArray.get al aa ws a k))) e) ei
                     in
                     ok (mk_texp (cword ws) e)
       | _   => fun _ => Error (typing_error ii)
       end) e

  | Psub aa ws len x i =>
      Let ti := toEC_e ii i in
      Let tx := pwgvar ii x in
      let ei := (cast_e cint ti) in
      let: existT t e := tx in
      (match t return pexp (interp t) -> cexec texp with
       | carr n  => fun e =>
                     let e :=
                     app_ (app_ (cst_ (fun (a : WArray.array n) (k : Z) =>
                                         rdflt (WArray.empty (arr_size ws len))
                                           (WArray.get_sub aa ws len a k))) e) ei
                     in
                     ok (mk_texp (carr (arr_size ws len)) e)
       | _=> fun _ => Error (typing_error ii)
       end) e

  (* Jasmin's memory is a single global slot whose code interprets to [mem]
     itself, so loads are Jasmin's own [read]: validity and alignment are
     modelled, not replaced by array bounds.  A failing read yields the
     default word, per this file's total-denotation convention. *)
  | Pload al ws a =>
      Let ta := toEC_e ii a in
      ok (mk_texp (cword ws)
            (app_ (app_ (cst_ (fun (mm : mem) (p : word Uptr) =>
                                 rdflt 0%R (read mm al p ws)))
                     (gvar_ memv))
                  (cast_e (cword Uptr) ta)))

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
Fixpoint toEC_assert (ii : instr_info) (a : eassert) : cexec (pexp bool) :=
  match a with
  | Pexpr e =>
      Let te := toEC_e ii e in
      ok (cast_e cbool te)

  | PappN_safety o es =>
      Let tes := toEC_es ii es in
      Let args := pwargs ii (map eval_atype (type_of_opN_safety o).1) tes in
      ok (app_ (cst_ (fun vs => rdflt false (sem_opN_safety o vs))) args)

  (* [is_init x] reads [is_defined (evm s).[x]], and [interp t] has no
     undefined inhabitant, so the predicate is not representable.  It is
     rejected rather than approximated by [true]: [Cassert] compiles to
     [cond b skip abort], so [true] would let the pwhile program run on
     exactly where Jasmin aborts. *)
  | Pis_var_init _ => Error (init_error ii)

  (* Transcribed from [sem_eassert] (psem_defs.v), which the old array
     encoding of the memory could only stub as [cst_ true]. *)
  | Pis_mem_init e1 e2 =>
      Let t1 := toEC_e ii e1 in
      Let t2 := toEC_e ii e2 in
      ok (app_ (app_ (app_
               (cst_ (fun (mm : mem) (lo : word Uptr) (sz : Z) =>
                  all (fun i => is_ok (read mm Unaligned (lo + wrepr Uptr i)%w U8))
                      (ziota 0 sz)))
               (gvar_ memv))
               (cast_e (cword Uptr) t1))
            (cast_e cint t2))

  | Pand a1 a2 =>
      Let b1 := toEC_assert ii a1 in
      Let b2 := toEC_assert ii a2 in
      ok (app_ (app_ (cst_ andb) b1) b2)
  end.

(* -------------------------------------------------------------------- *)
(* 6. Left-hand sides                                                  *)
(* -------------------------------------------------------------------- *)

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

Definition toEC_lv (ii : instr_info) (lv : lval) (te : texp) : cexec pwcmd :=
  match lv with
  | Lnone _ _ => ok pwhile.skip

  | Lvar x =>
      ok (pwhile.assign (pwvar x.(v_var))
            (cast_e (eval_atype (jtype x.(v_var))) te))

  | Laset al aa ws x i =>
      Let ti := toEC_e ii i in
      let ei := (cast_e cint ti) in
      let ev := (cast_e (cword ws) te) in
      (match eval_atype (jtype x) as c
             return vars_ jident c -> cexec pwcmd  with
       | carr n  => fun v =>
                 ok (pwhile.assign v
                  (app_ (app_ (app_
                  (cst_ (fun (a : WArray.array n) (k : Z) (w : word ws) =>
                   rdflt a (WArray.set a al aa k w))) (var_ v)) ei) ev))
       | _ => fun _ => Error (typing_error ii)
       end) (pwvar x)

  | Lasub aa ws len x i =>
      Let ti := toEC_e ii i in
      let ei := (cast_e cint ti) in
      let ev := (cast_e (carr (arr_size ws len)) te) in
      (match eval_atype (jtype x) as c
             return vars_ jident c -> cexec pwcmd with
       | carr n  => fun v =>
                     ok (pwhile.assign v
                           (app_ (app_ (app_
                                   (cst_ (fun (a : WArray.array n) (k : Z)
                                   (b : WArray.array (arr_size ws len)) =>
                              rdflt a (WArray.set_sub aa a k b))) (var_ v)) ei) ev))
       | _ => fun _ => Error (typing_error ii)
       end) (pwvar x)

  (* Stores go through Jasmin's own [write]; a write that fails validity or
     alignment leaves the memory unchanged. *)
  | Lmem al ws _ a =>
      Let ta := toEC_e ii a in
      ok (pwhile.gassign memv
            (app_ (app_ (app_
                     (cst_ (fun (mm : mem) (p : word Uptr) (w : word ws) =>
                              rdflt mm (write mm al p w)))
                     (gvar_ memv))
                     (cast_e (cword Uptr) ta))
                  (cast_e (cword ws) te)))
  end.

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

Definition rand_assign (ii : instr_info) (x : var) : cexec pwcmd :=
  (match eval_atype (jtype x) as c
     return vars_ jident c -> cexec pwcmd with
   | carr n  => fun v => ok (pwhile.random v (cst_ (drandbytes n)))
   | _ => fun _ => Error (syscall_error ii)
   end) (pwvar x).

(* -------------------------------------------------------------------- *)
(* 7. Instructions                                                     *)
(* -------------------------------------------------------------------- *)

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
  ok (pwhile.block bs (pwhile.call fn) rs).

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

  (* Each output re-evaluates [args]; [app_sopn_v] is pure, so this is
     duplicated work and syntax, not a semantic difference.  Binding the
     result list once would need an auxiliary variable, and
     [Ident.ident] is abstract -- no fresh name can be fabricated. *)
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

  (* [sem_assert] begins with [assert assert_allowed ErrType], so under
     [noassert] a [Cassert] has no successful run at all.  Such a program
     is rejected rather than translated to [abort]. *)
  | Cassert a =>
      Let _ := assert assert_allowed (assert_error ii) in
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

(* -------------------------------------------------------------------- *)
(* 8. Programs                                                         *)
(* -------------------------------------------------------------------- *)

(* Jasmin function names are pwhile function names directly: [funname] is
   an eqType (var.v), so no injection into [nat] is needed.  There is no
   global-initialisation prelude either, since there are no globals. *)
Definition toEC_fd (p : _uprog) (fd : _ufundef) : cexec pwcmd :=
  toEC_c p fd.(f_body).

Definition toEC_fun_decl (p : _uprog) (fnd : funname * _ufundef) :
    cexec (funname * pwcmd) :=
  let: (fn, fd) := fnd in
  Let c := toEC_fd p fd in
  ok (fn, c).

Definition toEC_funcs (p : _uprog) : cexec (seq (funname * pwcmd)) :=
  mapM (toEC_fun_decl p) (p_funcs p).

Fixpoint pw_assoc (l : seq (funname * pwcmd)) (f : funname) : pwcmd :=
  match l with
  | [::] => pwhile.abort
  | gc :: l' => if gc.1 == f then gc.2 else pw_assoc l' f
  end.

Definition toEC_ps (p : _uprog) : cexec (funname -> pwcmd) :=
  Let l := toEC_funcs p in ok (pw_assoc l).

(* -------------------------------------------------------------------- *)
(* The three rejection cases are reachable, not dead branches.  Stated
   over abstract data, since Jasmin seals [Ident.ident] ([Cident :
   CORE_IDENT]) and no concrete variable can be built in Coq. *)

Lemma pwgvar_glob (ii : instr_info) (x : gvar) :
  x.(gs) = Sglob -> pwgvar ii x = Error (global_error ii).
Proof. by move=> h; rewrite /pwgvar h. Qed.

Lemma toEC_assert_var_init (ii : instr_info) (x : var_i) :
  toEC_assert ii (Pis_var_init x) = Error (init_error ii).
Proof. by []. Qed.

Lemma toEC_i_assert_disabled (p : _uprog) (ii : instr_info) (a : assertion) :
  assert_allowed = false ->
  toEC_i p (MkI ii (Cassert a)) = Error (assert_error ii).
Proof. by move=> h; rewrite /= /assert h. Qed.

End TOEC.
