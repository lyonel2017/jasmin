(* ==================================================================== *)
(* Worked examples for [toEC.v]: concrete Jasmin programs, run through   *)
(* the translation.                                                     *)
(*                                                                      *)
(* These are smoke tests, not proofs about the semantics: each lemma     *)
(* says the translation *succeeds* (reduces to [ok]) on a program of the *)
(* shape [toEC_prog] produces, and the last one pins down the syntactic  *)
(* image of a [Ccall].                                                   *)
(*                                                                      *)
(* Two things have to stay abstract, because Jasmin seals them:          *)
(*   - [Ident.ident] ([Cident : CORE_IDENT], var.v/ident.v), so variable *)
(*     names cannot be built in Coq;                                     *)
(*   - [funname] ([FunName : TaggedCore], var.v:11).                     *)
(* Consequently [get_fundef] does not compute on an abstract [funname]   *)
(* and the call lemmas go through [eqxx] rather than [by []].            *)
(*                                                                      *)
(* The architecture is abstract too, which is why no example uses [Copn] *)
(* -- that needs [get_instr_desc], hence a concrete [asm_extra].         *)
(* ==================================================================== *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import compiler_util expr arch_decl arch_extra.
Require Import utils type sem_type values warray_ word wsize xseq.
Require Import toEC.
From xhl.pwhile Require Import inhabited_new pwhile_new.

Section EXAMPLE.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}.

#[local] Existing Instance progUnit.

Context (to_ident : var -> nat) (to_fname : funname -> nat).

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

Lemma example_body_ok : is_ok (toEC_c to_ident to_fname prog body).
Proof. by []. Qed.

Lemma example_prog_ok : is_ok (toEC_ps to_ident to_fname prog).
Proof. by []. Qed.

(* ==================================================================== *)
(* 2. An assertion                                                       *)
(* ==================================================================== *)

(*  assert (i < 4);   becomes   If <i < 4> then skip else abort.
    [legalize_names] removes assertions, but the translation no longer
    depends on that. *)
Context (lbl : assertion_label).

Definition body_assert : seq instr :=
  [:: MkI II (Cassert (lbl, Pexpr (Papp2 (Olt Cmp_int) (E_ v_i) (Pconst 4)))) ].

Lemma example_assert_ok : is_ok (toEC_c to_ident to_fname prog body_assert).
Proof. by []. Qed.

(* the image really is a two-armed conditional ending in [abort] *)
Lemma example_assert_shape :
  match rdflt pwhile_new.abort (toEC_c to_ident to_fname prog body_assert) with
  | pwhile_new.seqc (pwhile_new.cond _ pwhile_new.skip pwhile_new.abort)
                    pwhile_new.skip => True
  | _ => False
  end.
Proof. by []. Qed.

(* ==================================================================== *)
(* 3. A procedure call                                                   *)
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

Lemma example_call_ok : is_ok (toEC_c to_ident to_fname prog_call body_g).
Proof. by rewrite /toEC_c /body_g /= eqxx. Qed.

(* The image of [Ccall]: a [block] whose entry bindings are the callee's
   parameters (evaluated by [minit] in the *caller's* memory), whose body
   is the bare [call], and whose return bindings read the callee's
   [f_res] out of the callee's final memory ([mret], which also restores
   the caller's locals while keeping the callee's globals).

   The two binding lists have the callee's arities: 2 parameters in, 1
   result out. *)
Lemma example_call_shape :
  match rdflt pwhile_new.abort (toEC_c to_ident to_fname prog_call body_g) with
  | pwhile_new.seqc (pwhile_new.block bs (pwhile_new.call f) rs)
                    pwhile_new.skip =>
      [/\ f = pw_fun_id to_fname fn_add, size bs = 2 & size rs = 1 ]
  | _ => False
  end.
Proof. by rewrite /toEC_c /body_g /= eqxx. Qed.

End EXAMPLE.
