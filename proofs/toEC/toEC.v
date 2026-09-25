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

 Definition unsafe_op (ii : instr_info) :=
    pp_internal_error_s_at pass ii
      "unsafe operator".

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

Axiom mem_witness : forall {pd : PointerData}, @mem pd.

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
   global store holds only the memory *)
Notation jident  := var.
Notation jidentg := unit.
Notation jgcode  := (gcode : codeType).

(* -------------------------------------------------------------------- *)
Section Mem.
  Context {wsw : WithSubWord}.   (* for [Vm.t] *)
  Context {pd  : PointerData}.   (* for [mem]  *)

(* -------------------------------------------------------------------- *)
(* Keys. *)
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

Lemma vm_truncate_val_jval (t : ctype) (v : interp t) :
  vm_truncate_val t (jval t v) = jval t v.
Proof. by apply: vm_truncate_val_eq; exact: type_of_to_val. Qed.

(* -------------------------------------------------------------------- *)
(* The state. *)
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
(* Local memory.*)
Definition jget (m : jstate) (t : ctype) (x : jident) : interp t :=
  jof_val t (evm m (Var.vtype x)).[key t (Var.vname x)]%vm.

Definition jset (m : jstate) (t : ctype) (x : jident) (v : interp t) : jstate :=
  Jstate (emem m)
    (fupd (evm m) (Var.vtype x)
       (evm m (Var.vtype x)).[key t (Var.vname x) <- jval t v]%vm).

(* -------------------------------------------------------------------- *)
(* Global memory.*)
Definition jgetg (m : jstate) (T : jgcode) (_ : jidentg) : interp T :=
  match T return interp T with Gmem => emem m end.

Definition jsetg (m : jstate) (T : jgcode) (_ : jidentg) (v : interp T) : jstate :=
  match T return interp T -> jstate with Gmem => fun v => Jstate v (evm m) end v.

Definition jnew (m : jstate) : jstate := Jstate (emem m) (fun _ => Vm.init).

Definition jrestore (m0 m : jstate) : jstate := Jstate (emem m) (evm m0).

Definition memv : vars_ jidentg (@Gmem pd) := pwhile.Var (@Gmem pd) tt.

(* -------------------------------------------------------------------- *)
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
(* Example mget_mset_j (t : ctype) (m : jstate) (x : jident) (v : interp t) : *)
(*   @mget jcode jgcode jident jidentg jstate t *)
(*     (@mset jcode jgcode jident jidentg jstate t m x v) x = v. *)
(* Proof. exact: mget_eq. Qed. *)

(* Example mgetg_msetg_mem (m : jstate) (mm : mem) : *)
(*   @mgetg jcode jgcode jident jidentg jstate (@Gmem pd) *)
(*     (@msetg jcode jgcode jident jidentg jstate (@Gmem pd) m tt mm) tt = mm. *)
(* Proof. exact: mgetg_eq. Qed. *)

(* Example slots_distinct (n : Ident.ident) (m : jstate) (a : interp (carr 8)) : *)
(*   @mget jcode jgcode jident jidentg jstate (carr 8) *)
(*     (@mset jcode jgcode jident jidentg jstate (carr 8) m *)
(*        (Var.Var (aarr U16 4) n) a) *)
(*     (Var.Var (aarr U8 8) n) *)
(*   = @mget jcode jgcode jident jidentg jstate (carr 8) m (Var.Var (aarr U8 8) n). *)
(* Proof. by apply: mget_neq; right. Qed. *)

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
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}.

#[local] Existing Instance progUnit.

Notation pexp T := (expr_ jcode jgcode jident jidentg jmem T).
Notation pwcmd  := (@cmd_ R jcode jgcode jident jidentg jmem funname).

Definition pwvar (x : var) : vars_ jident (eval_atype (jtype x)) :=
  pwhile.Var (eval_atype (jtype x)) x.

(* a translated expression, together with its Jasmin type *)
Definition texp := { t : ctype & pexp (interp t) }.

Definition mk_texp (t : ctype) (e : pexp (interp t)) : texp := existT _ t e.
Arguments mk_texp : clear implicits.

(* -------------------------------------------------------------------- *)
Definition cast_crash (ii : instr_info) (tdst : ctype) (te : texp) :
  cexec (pexp (interp tdst)) :=
  let: existT tsrc e := te in
  match ctype_eq_dec tsrc tdst with
   | left h  => ok (ecast t (pexp (interp t)) h e)
   | right _ => Error (typing_error ii)
   end.

(* -------------------------------------------------------------------- *)
Fixpoint pwargs (ii : instr_info) (ts : seq ctype) (tes : seq texp) :
  cexec (pexp values) :=
  match ts, tes with
  | t :: ts', te :: tes' =>
      Let te := cast_crash ii t te in
      Let tes' := pwargs ii ts' tes' in
      ok (app_ (app_ (cst_ (@cons value)) (app_ (cst_ (jval t)) te)) tes')
   | [::], [::] => ok (cst_ [::])
   | _, _ => Error (arity_error ii)
  end.

Definition pwgvar (ii : instr_info) (x : gvar) : cexec texp :=
  if x.(gs) is Slocal then
    let xv := (gv x).(v_var) in
    ok (mk_texp (eval_atype (jtype xv)) (var_ (pwvar xv)))
  else Error (global_error ii).

(* -------------------------------------------------------------------- *)
(* 5. Expressions                                                       *)
(* -------------------------------------------------------------------- *)

(* Expression should be normalized such that unsafe operator are part of a single
   assign, such that x = a / b goes to if b = 0 then abort else x = a / b; *)

Definition sem_sop1_typed (ii : instr_info) (o : sop1) :
  let t := type_of_op1 o in
  let t := (eval_atype t.1, eval_atype t.2) in
  cexec (sem_t t.1 -> (sem_t t.2)) :=
  match o with
  | Oword_of_int sz => ok (wrepr sz)
  | Oint_of_word sign sz => ok (@int_of_word sign sz)
  | Osignext szo szi => ok (@sign_extend szo szi)
  | Ozeroext szo szi => ok (@zero_extend szo szi)
  | Onot => ok negb
  | Olnot sz => ok (@wnot sz)
  | Oneg Op_int => ok Z.opp
  | Oneg (Op_w sz) => ok -%w
  (* | Owi1 sign o => sem_wiop1_typed sign o *)
  | _ => Error (unsafe_op ii)
  end.

Definition sem_sop2_typed (ii : instr_info) (o: sop2) :
  let t := type_of_op2 o in
  let t := (eval_atype t.1.1, eval_atype t.1.2, eval_atype t.2) in
  cexec (sem_t t.1.1 -> sem_t t.1.2 -> sem_t t.2) :=
  match o with
  | Obeq => ok (@eq_op bool)
  | Oand => ok andb
  | Oor  => ok orb

  | Oadd Op_int     => ok Z.add
  | Oadd (Op_w s)   => ok +%w
  | Omul Op_int     => ok Z.mul
  | Omul (Op_w s)   => ok *%w
  | Osub Op_int     => ok Z.sub
  | Osub (Op_w s)   => ok (fun x y =>  x - y)%w
  | Odiv u Op_int   => ok (signed Z.div Z.quot u)
  (* | Odiv u (Op_w s) => @mk_sem_divmod u s (signed wdiv wdivi u) *)
  | Omod u Op_int   => ok (signed Z.modulo Z.rem u)
  (* | Omod u (Op_w s) => @mk_sem_divmod u s (signed wmod wmodi u) *)

  | Oland s       => ok wand
  | Olor  s       => ok wor
  | Olxor s       => ok wxor
  | Olsr s        => ok sem_shr
  | Olsl Op_int   => ok zlsl
  | Olsl (Op_w s) => ok sem_shl
  | Oasr Op_int   => ok zasr
  | Oasr (Op_w s) => ok sem_sar
  | Oror s        => ok sem_ror
  | Orol s        => ok sem_rol

  | Oeq Op_int    => ok Z.eqb
  | Oeq (Op_w s)  => ok eq_op
  | Oneq Op_int   => ok (fun x y => negb (Z.eqb x y))
  | Oneq (Op_w s) => ok (fun x y => (x != y))

  (* Fixme use the "new" Z *)
  | Olt Cmp_int   => ok Z.ltb
  | Ole Cmp_int   => ok Z.leb
  | Ogt Cmp_int   => ok Z.gtb
  | Oge Cmp_int   => ok Z.geb

  | Olt (Cmp_w u s) => ok (wlt u)
  | Ole (Cmp_w u s) => ok (wle u)
  | Ogt (Cmp_w u s) => ok (fun x y => wlt u y x)
  | Oge (Cmp_w u s) => ok (fun x y => wle u y x)
  | Ovadd ve ws     => ok (sem_vadd ve)
  | Ovsub ve ws     => ok (sem_vsub ve)
  | Ovmul ve ws     => ok (sem_vmul ve)
  | Ovlsr ve ws     => ok (sem_vshr ve)
  | Ovlsl ve ws     => ok (sem_vshl ve)
  | Ovasr ve ws     => ok (sem_vsar ve)

  (* | Owi2 s sz o => sem_wiop2_typed s sz o *)
  | _ => Error (unsafe_op ii)
  end.


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
      Let ei := cast_crash ii cint ti in
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
      Let ei := (cast_crash ii cint ti) in
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

  | Pload al ws a =>
      Let ta := toEC_e ii a in
      Let ta := cast_crash ii (cword Uptr) ta in
      ok (mk_texp (cword ws)
            (app_ (app_ (cst_ (fun (mm : mem) (p : word Uptr) =>
                                 rdflt 0%R (read mm al p ws)))
                     (gvar_ memv)) ta))

  | Papp1 o e1 =>
      Let t1 := toEC_e ii e1 in
      Let t1 := cast_crash ii (eval_atype (type_of_op1 o).1) t1 in
      Let o' := sem_sop1_typed ii o in
      ok (mk_texp (eval_atype (type_of_op1 o).2)
            (app_ (cst_ (fun v =>
                     to_interp (eval_atype (type_of_op1 o).2)
                       (o'
                          (of_interp (eval_atype (type_of_op1 o).1) v))))
                   t1))

  | Papp2 o e1 e2 =>
      Let t1 := toEC_e ii e1 in
      Let t1 := cast_crash ii (eval_atype (type_of_op2 o).1.1) t1 in
      Let t2 := toEC_e ii e2 in
      Let t2 := cast_crash ii (eval_atype (type_of_op2 o).1.2) t2 in
      Let o' := sem_sop2_typed ii o in
      ok (mk_texp (eval_atype (type_of_op2 o).2)
            (app_ (app_ (cst_ (fun v1 v2 =>
                         to_interp (eval_atype (type_of_op2 o).2)
                            (o'
                            (of_interp (eval_atype (type_of_op2 o).1.1) v1)
                            (of_interp (eval_atype (type_of_op2 o).1.2) v2))))
                     t1) t2))

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
      Let tb := cast_crash ii cbool tb in
      Let t1 := toEC_e ii e1 in
      Let t1 := cast_crash ii (eval_atype ty) t1 in
      Let t2 := toEC_e ii e2 in
      Let t2 := cast_crash ii (eval_atype ty) t2 in
      ok (mk_texp (eval_atype ty)
            (app_ (app_ (app_
                     (cst_ (fun (c : bool) (v1 v2 : interp (eval_atype ty)) =>
                              if c then v1 else v2))
                     tb) t1) t2))
  end.

Definition toEC_es (ii : instr_info) (es : pexprs) : cexec (seq texp) :=
  mapM (toEC_e ii) es.

(* -------------------------------------------------------------------- *)
Fixpoint toEC_assert (ii : instr_info) (a : eassert) : cexec (pexp bool) :=
  match a with
  | Pexpr e =>
      Let te := toEC_e ii e in
      Let te := cast_crash ii cbool te in
      ok te

  | PappN_safety o es =>
      Let tes := toEC_es ii es in
      Let args := pwargs ii (map eval_atype (type_of_opN_safety o).1) tes in
      ok (app_ (cst_ (fun vs => rdflt false (sem_opN_safety o vs))) args)

  | Pis_var_init _ => Error (init_error ii)

  | Pis_mem_init e1 e2 =>
      Let t1 := toEC_e ii e1 in
      Let t1 := cast_crash ii (cword Uptr) t1 in
      Let t2 := toEC_e ii e2 in
      Let t2 := cast_crash ii cint t2 in
      ok (app_ (app_ (app_
               (cst_ (fun (mm : mem) (lo : word Uptr) (sz : Z) =>
                  all (fun i => is_ok (read mm Unaligned (lo + wrepr Uptr i)%w U8))
                      (ziota 0 sz)))
               (gvar_ memv))
               t1) t2)

  | Pand a1 a2 =>
      Let b1 := toEC_assert ii a1 in
      Let b2 := toEC_assert ii a2 in
      ok (app_ (app_ (cst_ andb) b1) b2)
  end.

(* -------------------------------------------------------------------- *)
(* 6. Left-hand sides                                                   *)
(* -------------------------------------------------------------------- *)

Definition toEC_lv (ii : instr_info) (lv : lval) (te : texp) : cexec pwcmd :=
  match lv with
  | Lnone _ _ => ok pwhile.skip

  | Lvar x =>
      Let te := cast_crash ii (eval_atype (jtype x.(v_var))) te in
      ok (pwhile.assign (pwvar x.(v_var)) te)

  | Laset al aa ws x i =>
      Let ti := toEC_e ii i in
      Let ei := cast_crash ii cint ti in
      Let ev := cast_crash ii (cword ws) te in
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
      Let ei := cast_crash ii cint ti in
      Let ev := cast_crash ii (carr (arr_size ws len)) te in
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

  | Lmem al ws _ a =>
      Let ta := toEC_e ii a in
      Let ta := cast_crash ii (cword Uptr) ta in
      Let te := cast_crash ii (cword ws) te in
      ok (pwhile.gassign memv
            (app_ (app_ (app_
                     (cst_ (fun (mm : mem) (p : word Uptr) (w : word ws) =>
                              rdflt mm (write mm al p w)))
                     (gvar_ memv))
                     ta) te))
  end.

Definition pw_bind (ii : instr_info) (x : var) (te : texp) : cexec binding :=
  Let te := cast_crash ii (eval_atype (jtype x)) te in
  ok (bind_of (pwvar x) te).

Definition passign (bs : seq binding) : pwcmd :=
  pwhile.block bs pwhile.skip
    (map (fun b => let: existT _ (x, _) := b in bind_of x (var_ x)) bs).

Fixpoint lvs_bindings (ii : instr_info) (lvs : lvals) (tes : seq texp) :
    cexec (seq binding) :=
  match lvs, tes with
  | [::], [::] => ok [::]
  | Lvar x :: lvs', te :: tes' =>
      Let bs := lvs_bindings ii lvs' tes' in
      Let te := pw_bind ii x.(v_var) te in
      ok ( te :: bs)
  | _, _ => Error (arity_error ii)
  end.

Fixpoint toEC_lvs (ii : instr_info) (lvs : lvals) (tes : seq texp) :
    cexec pwcmd :=
  match lvs, tes with
  | [::], [::] => ok pwhile.skip
  | lv :: [::], te :: [::] => toEC_lv ii lv te
  | _, _ =>
      Let bs := lvs_bindings ii lvs tes in
      ok (passign bs)
  end.

Definition rand_assign (ii : instr_info) (x : var) : cexec pwcmd :=
  (match eval_atype (jtype x) as c
     return vars_ jident c -> cexec pwcmd with
   | carr n  => fun v => ok (pwhile.random v (cst_ (drandbytes n)))
   | _ => fun _ => Error (syscall_error ii)
   end) (pwvar x).

(* -------------------------------------------------------------------- *)
(* 7. Instructions                                                      *)
(* -------------------------------------------------------------------- *)

Definition call_cmd (fd : _ufundef) (fn : funname) (ii : instr_info)
    (lvs : lvals) (tes : seq texp) : cexec pwcmd :=
  Let bs :=
    mapM2 (arity_error ii)
      (fun (x : var_i) (te : texp) => pw_bind ii x.(v_var) te)
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
      Let te := cast_crash ii (eval_atype ty) te in
      toEC_lv ii lv (mk_texp (eval_atype ty) te)

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
      Let _ := assert assert_allowed (assert_error ii) in
      Let b := toEC_assert ii a.2 in
      ok (pwhile.cond b pwhile.skip pwhile.abort)

  | Cif e c1 c2 =>
      Let te := toEC_e ii e in
      Let te := cast_crash ii cbool te in
      Let d1 := toEC_c_aux (toEC_i p) c1 in
      Let d2 := toEC_c_aux (toEC_i p) c2 in
      ok (pwhile.cond te d1 d2)

  | Cfor _ _ _ => Error (cfor_error ii)

  | Cwhile _ c1 e _ c2 =>
      if c1 is [::] then
        Let te := toEC_e ii e in
        Let te := cast_crash ii cbool te in
        Let d2 := toEC_c_aux (toEC_i p) c2 in
        ok (pwhile.while te d2)
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
