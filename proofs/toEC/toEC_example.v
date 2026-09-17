(* ==================================================================== *)
(* Worked examples for [toEC.v]: concrete Jasmin programs, run through   *)
(* the translation.                                                     *)
(*                                                                      *)
(* These are smoke tests, not proofs about the semantics.  They come in  *)
(* two kinds: the translation *succeeds* (reduces to [ok]) on programs   *)
(* of the shape the earlier passes leave behind, and it *rejects* -- with *)
(* the right message -- the constructs the current design cannot model.  *)
(* Two lemmas also pin down the syntactic image of a [Cassert] and of a  *)
(* [Ccall].                                                             *)
(*                                                                      *)
(* Three things have to stay abstract, because Jasmin seals them:        *)
(*   - [Ident.ident] ([Cident : CORE_IDENT], var.v/ident.v), so variable *)
(*     names cannot be built in Coq;                                     *)
(*   - [funname] ([FunName : TaggedCore], var.v);                        *)
(*   - the architecture, which is why no example uses [Copn] -- that     *)
(*     needs [get_instr_desc], hence a concrete [asm_extra].             *)
(* Consequently [get_fundef] does not compute on an abstract [funname]   *)
(* and the call lemmas go through [eqxx] rather than [by []].            *)
(*                                                                      *)
(* [R] must be given by name in every call: it occurs only in the result *)
(* type of [toEC_c] / [toEC_ps] ([pwcmd] is a [cmd_ R ...]), so it       *)
(* cannot be inferred from the arguments.  [wsw] and [wa] are classes,   *)
(* so instance resolution finds them. *)
(* ==================================================================== *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From mathcomp.reals Require Import reals.
Require Import compiler_util expr arch_decl arch_extra.
Require Import utils type sem_type sem_params values warray_ word wsize xseq.
Require Import low_memory.
Require Import toEC.
Import toEC.E.   (* [Module Import E] is not re-exported by [toEC.v] *)
From xhl.pwhile Require Import inhabited pwhile.

Section EXAMPLE.

Context {R : realType}.
Context {wsw : WithSubWord}.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}.

#[local] Existing Instance progUnit.

(* Assertions are enabled: [sem_assert] begins with
   [assert assert_allowed ErrType], so under [noassert] a [Cassert] has no
   successful run and the translation rejects it -- see
   [example_assert_rejected] at the end, which overrides this instance. *)
#[local] Existing Instance withassert.

Context (nn ss ii_ tt_ aa_ bb_ rr_ qq_ : Ident.ident).

Definition v_n : var := var.Var (aword U64)  nn.
Definition v_s : var := var.Var (aword U64)  ss.
Definition v_i : var := var.Var aint         ii_.
Definition v_t : var := var.Var (aarr U64 4) tt_.
Definition v_a : var := var.Var (aword U64)  aa_.
Definition v_b : var := var.Var (aword U64)  bb_.
Definition v_r : var := var.Var (aword U64)  rr_.
Definition v_q : var := var.Var (aword U64)  qq_.

Definition V (x : var) : var_i := mk_var_i x.
Definition E_ (x : var) : pexpr := Plvar (V x).

Definition w0 : pexpr := Papp1 (Oword_of_int U64) (Pconst 0).
Definition w1 : pexpr := Papp1 (Oword_of_int U64) (Pconst 1).

Definition II : instr_info := dummy_instr_info.

(* ==================================================================== *)
(* 1. A loop over a stack array                                          *)
(* ==================================================================== *)

(*  fn f(reg u64 n) -> reg u64 {
      stack u64[4] t;  reg u64 s;  inline int i;
      s = 0;
      i = 0;
      while (i < 4) { t[i] = n; s = s + t[i]; i = i + 1; }
      if (s == 0) { s = 1; }
      return s;
    }

    The [Cwhile] has an empty pre-block, which is the shape
    [flatten_while] leaves behind. *)
Definition body : seq instr :=
  [::
    MkI II (Cassgn (Lvar (V v_s)) AT_none (aword U64) w0);
    MkI II (Cassgn (Lvar (V v_i)) AT_none aint (Pconst 0));
    MkI II (Cwhile NoAlign [::]
              (Papp2 (Olt Cmp_int) (E_ v_i) (Pconst 4)) II
              [::
                 MkI II (Cassgn (Laset Aligned AAscale U64 (V v_t) (E_ v_i))
                           AT_none (aword U64) (E_ v_n));
                 MkI II (Cassgn (Lvar (V v_s)) AT_none (aword U64)
                           (Papp2 (Oadd (Op_w U64)) (E_ v_s)
                              (Pget Aligned AAscale U64 (mk_lvar (V v_t)) (E_ v_i))));
                 MkI II (Cassgn (Lvar (V v_i)) AT_none aint
                           (Papp2 (Oadd Op_int) (E_ v_i) (Pconst 1)))
              ]);
    MkI II (Cif (Papp2 (Oeq (Op_w U64)) (E_ v_s) w0)
              [:: MkI II (Cassgn (Lvar (V v_s)) AT_none (aword U64) w1) ]
              [::])
  ].

Definition fd_f : _ufundef :=
  {| f_info := FunInfo.witness;
     f_contract := None;
     f_tyin := [:: aword U64 ];
     f_params := [:: V v_n ];
     f_body := body;
     f_tyout := [:: aword U64 ];
     f_res := [:: V v_s ];
     f_extra := tt |}.

Context (fn_f : funname).

Definition prog : _uprog :=
  {| p_funcs := [:: (fn_f, fd_f) ]; p_globs := [::]; p_extra := tt |}.

Lemma example_body_ok : is_ok (toEC_c (R:=R) prog body).
Proof. by []. Qed.

Lemma example_prog_ok : is_ok (toEC_ps (R:=R) prog).
Proof. by []. Qed.

(* ==================================================================== *)
(* 2. Memory                                                             *)
(* ==================================================================== *)

(*  s = [u64 n];        becomes   s <<- read <mem> n U64
    [u64 n] = s;        becomes   G <mem> <<- write <mem> n s

    The global store holds exactly one slot, whose code interprets to
    Jasmin's [mem], so both sides are Jasmin's own [read] / [write] with
    validity and alignment intact -- not an array encoding.  A failing
    access falls back to a default, per the total-denotation convention. *)
Definition body_mem : seq instr :=
  [::
    MkI II (Cassgn (Lvar (V v_s)) AT_none (aword U64)
              (Pload Aligned U64 (E_ v_n)));
    MkI II (Cassgn (Lmem Aligned U64 dummy_var_info (E_ v_n))
              AT_none (aword U64) (E_ v_s))
  ].

Lemma example_mem_ok : is_ok (toEC_c (R:=R) prog body_mem).
Proof. by []. Qed.

(* The load reads the memory slot and the store writes it: the image is an
   [assign] to a local followed by a [gassign] to the one global. *)
Lemma example_mem_shape :
  match rdflt pwhile.abort (toEC_c (R:=R) prog body_mem) with
  | pwhile.seqc (pwhile.assign _ _ _)
                (pwhile.seqc (pwhile.gassign _ _ _) pwhile.skip) => True
  | _ => False
  end.
Proof. by []. Qed.

(* ==================================================================== *)
(* 3. Assertions                                                         *)
(* ==================================================================== *)

(*  assert (i < 4);   becomes   If <i < 4> then skip else abort. *)
Context (lbl : assertion_label).

Definition body_assert : seq instr :=
  [:: MkI II (Cassert (lbl, Pexpr (Papp2 (Olt Cmp_int) (E_ v_i) (Pconst 4)))) ].

Lemma example_assert_ok : is_ok (toEC_c (R:=R) prog body_assert).
Proof. by []. Qed.

(* the image really is a two-armed conditional ending in [abort] *)
Lemma example_assert_shape :
  match rdflt pwhile.abort (toEC_c (R:=R) prog body_assert) with
  | pwhile.seqc (pwhile.cond _ pwhile.skip pwhile.abort) pwhile.skip => True
  | _ => False
  end.
Proof. by []. Qed.

(*  assert (is_init [n : 8]);

    [Pis_mem_init] is now translated faithfully -- it is exactly
    [sem_eassert]'s [all (fun i => is_ok (read mm Unaligned (lo + i) U8))
    (ziota 0 sz)].  The old array encoding of the memory could only stub it
    as [cst_ true]. *)
Definition body_mem_init : seq instr :=
  [:: MkI II (Cassert (lbl, Pis_mem_init (E_ v_n) (Pconst 8))) ].

Lemma example_mem_init_ok : is_ok (toEC_c (R:=R) prog body_mem_init).
Proof. by []. Qed.

(* ==================================================================== *)
(* 4. A procedure call                                                   *)
(* ==================================================================== *)

(*  fn add(reg u64 a, reg u64 b) -> reg u64 { reg u64 r; r = a + b; return r; }
    fn g  (reg u64 n)            -> reg u64 { reg u64 q; q = add(n, n); return q; }

    The call's destinations are pairwise-distinct [Lvar]s whose types are
    exactly [f_tyout] -- the invariant [normalize_calls] establishes. *)
Definition body_add : seq instr :=
  [:: MkI II (Cassgn (Lvar (V v_r)) AT_none (aword U64)
                (Papp2 (Oadd (Op_w U64)) (E_ v_a) (E_ v_b))) ].

Definition fd_add : _ufundef :=
  {| f_info := FunInfo.witness;
     f_contract := None;
     f_tyin := [:: aword U64; aword U64 ];
     f_params := [:: V v_a; V v_b ];
     f_body := body_add;
     f_tyout := [:: aword U64 ];
     f_res := [:: V v_r ];
     f_extra := tt |}.

Context (fn_add fn_g : funname).

Definition body_g : seq instr :=
  [:: MkI II (Ccall [:: Lvar (V v_q) ] fn_add [:: E_ v_n; E_ v_n ]) ].

Definition fd_g : _ufundef :=
  {| f_info := FunInfo.witness;
     f_contract := None;
     f_tyin := [:: aword U64 ];
     f_params := [:: V v_n ];
     f_body := body_g;
     f_tyout := [:: aword U64 ];
     f_res := [:: V v_q ];
     f_extra := tt |}.

Definition prog_call : _uprog :=
  {| p_funcs := [:: (fn_add, fd_add) ]; p_globs := [::]; p_extra := tt |}.

Lemma example_call_ok : is_ok (toEC_c (R:=R) prog_call body_g).
Proof. by rewrite /toEC_c /body_g /= eqxx. Qed.

(* The image of [Ccall]: a [block] whose entry bindings are the callee's
   parameters (evaluated by [minit] in the *caller's* memory), whose body
   is the bare [call], and whose return bindings read the callee's
   [f_res] out of the callee's final memory ([mret], which also restores
   the caller's locals while keeping the callee's globals).

   The two binding lists have the callee's arities: 2 parameters in, 1
   result out.  The pwhile function name is the Jasmin [funname] itself --
   [funname] is an eqType, so no injection into [nat] is needed. *)
Lemma example_call_shape :
  match rdflt pwhile.abort (toEC_c (R:=R) prog_call body_g) with
  | pwhile.seqc (pwhile.block bs (pwhile.call f) rs) pwhile.skip =>
      [/\ f = fn_add, size bs = 2 & size rs = 1 ]
  | _ => False
  end.
Proof. by rewrite /toEC_c /body_g /= eqxx. Qed.

(* ==================================================================== *)
(* 5. What the translation rejects                                       *)
(* ==================================================================== *)

(* There are no global variables: the global store holds only the memory,
   so a [Sglob] read is refused rather than approximated.
   [remove_globals] must have run. *)
Lemma example_glob_rejected :
  toEC_c (R:=R) prog
    [:: MkI II (Cassgn (Lvar (V v_s)) AT_none (aword U64)
                  (Pvar (mk_gvar (V v_n)))) ]
  = Error (global_error II).
Proof. by []. Qed.

(* [is_init x] reads [is_defined (evm s).[x]], and [interp t] has no
   undefined inhabitant, so the predicate is not representable.  It is
   refused rather than approximated by [true], which would let the pwhile
   program run on exactly where Jasmin aborts. *)
Lemma example_var_init_rejected :
  toEC_c (R:=R) prog [:: MkI II (Cassert (lbl, Pis_var_init (V v_i))) ]
  = Error (init_error II).
Proof. by []. Qed.

(* [for_to_while] must have run. *)
Lemma example_cfor_rejected (x : var_i) (r : range) (c : seq instr) :
  toEC_c (R:=R) prog [:: MkI II (Cfor x r c) ] = Error (cfor_error II).
Proof. by []. Qed.

(* [flatten_while] must have run: a [Cwhile] with a non-empty pre-block is
   refused. *)
Lemma example_cwhile_rejected (e : pexpr) (c1 c2 : seq instr) :
  c1 <> [::] ->
  toEC_c (R:=R) prog [:: MkI II (Cwhile NoAlign c1 e II c2) ]
  = Error (cwhile_error II).
Proof. by case: c1 => // a l _. Qed.

(* Under [noassert] a [Cassert] instruction fails in Jasmin
   ([sem_assert]'s leading [assert assert_allowed ErrType]), so the
   translation refuses it instead of emitting [abort].  This is the one
   lemma that overrides the section's [withassert] instance. *)
Lemma example_assert_rejected :
  toEC_c (R:=R) (wa:=noassert) prog body_assert = Error (assert_error II).
Proof. by []. Qed.

End EXAMPLE.
