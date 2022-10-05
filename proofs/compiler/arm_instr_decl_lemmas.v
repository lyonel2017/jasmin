From mathcomp Require Import
  all_ssreflect
  all_algebra.
From mathcomp.word Require Import ssrZ.

Require Import
  psem
  shift_kind.
Require Import
  arm_decl
  arm_extra
  arm_instr_decl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma mn_desc_is_conditional mn sf ic hs ic' :
  let opts :=
    {| set_flags := sf; is_conditional := ic; has_shift := hs; |}
  in
  let opts' :=
    {| set_flags := sf; is_conditional := ic'; has_shift := hs; |}
  in
  mn_desc mn opts = mn_desc mn opts'.
Proof. by case: mn. Qed.

Lemma ignore_set_flags mn sf ic hs sf' :
  mn \notin set_flags_mnemonics
  -> let opts :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs; |}
     in
     let opts' :=
       {| set_flags := sf'; is_conditional := ic; has_shift := hs; |}
     in
     mn_desc mn opts = mn_desc mn opts'.
Proof. by case: mn. Qed.

Lemma ignore_has_shift mn sf ic hs hs' :
  mn \notin has_shift_mnemonics
  -> let opts :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs; |}
     in
     let opts' :=
       {| set_flags := sf; is_conditional := ic; has_shift := hs'; |}
     in
     mn_desc mn opts = mn_desc mn opts'.
Proof. by case: mn. Qed.

(* TODO_ARM: It seems like we need to characterize conditional execution,
   but the variable number of arguments makes it very cumbersome.
   This gets multiplied if they set flags or have shifts. *)

Section WITH_PARAMS.

Context
  {syscall_state : Type}
  {sc_sem : syscall_sem syscall_state}
  {eft : eqType}
  {pT : progT eft}
  {sCP : semCallParams}.

Definition truncate_args
  (op : sopn) (vargs : seq value) : exec (seq value) :=
  mapM2 ErrType truncate_val (sopn_tout op) vargs.

Lemma exec_sopn_conditional mn sf osk b vargs vprev vres0 vres1 :
  let opts :=
    {| set_flags := sf; is_conditional := false; has_shift := osk; |}
  in
  let op := Oarm (ARM_op mn opts) in
  truncate_args op vprev = ok vres1
  -> exec_sopn (spp := spp_of_asm_e) op vargs = ok vres0
  -> exec_sopn
       (spp := spp_of_asm_e)
       (Oarm (ARM_op mn (set_is_conditional opts)))
       (vargs ++ Vbool b :: vprev)
       = ok (if b then vres0 else vres1).
Proof.
  all: case: sf.
  all: case: osk => [sk|].
  all: case: mn.
  all: rewrite /truncate_args /truncate_val.

  all:
    repeat (
      case: vprev => [| ? vprev ] //=;
      t_xrbindP=> //;
      repeat
        match goal with
        | [ |- forall (_ : value), forall _, _ ] => move=> ? ? ? ? ?
        | [ |- ([::] = _) -> _ ] => move=> ?
        | [ |- (_ :: _ = _) -> _ ] => move=> ?
        end
    ).

  all: try move=> <-.
  all: subst.

  all: rewrite /exec_sopn /=.
  all: case: vargs => [| ? vargs ] //; t_xrbindP => // v.
  all:
    repeat (
      case: vargs => [| ? vargs ] //;
      t_xrbindP => //;
      match goal with
      | [ |- forall _, ((_ = ok _) -> _) ] => move=> ? ?
      end
    ).
  all: move=> hsemop ?; subst vres0.
  all: rewrite /=.
  all:
    repeat (
      match goal with
      | [ h : _ = ok _ |- _ ] => rewrite h {h} /=
      end
    ).

  all: move: hsemop.
  all: rewrite /sopn_sem /=.
  all: rewrite /drop_semi_nzcv /=.
  all: move=> [?]; subst v.
  all: by case: b.
Qed.

(* TODO_ARM: Is this the best way of expressing the [write_val] condition? *)
Lemma sem_i_conditional
  (p : prog)
  ev s0 s1 mn sf osk lvs tag args c prev vargs b vprev vprev' vres :
  let opts :=
    {| set_flags := sf; is_conditional := false; has_shift := osk; |}
  in
  let aop := Oarm (ARM_op mn opts) in
  sem_pexprs (p_globs p) s0 args = ok vargs
  -> sem_pexpr (p_globs p) s0 c = ok (Vbool b)
  -> sem_pexprs (p_globs p) s0 prev = ok vprev
  -> truncate_args aop vprev = ok vprev'
  -> exec_sopn aop vargs = ok vres
  -> (if b
      then write_lvals (p_globs p) s0 lvs vres = ok s1
      else write_lvals (p_globs p) s0 lvs vprev' = ok s1)
  -> let aop' := Oarm (ARM_op mn (set_is_conditional opts)) in
     let ir := Copn lvs tag aop' (args ++ c :: prev) in
     sem_i p ev s0 ir s1.
Proof.
  move=> opts aop hsemargs hsemc hsemprev htruncprev hexec hwrite.

  apply: Eopn.
  rewrite /sem_sopn /=.
  rewrite /sem_pexprs mapM_cat /= -2![mapM _ _]/(sem_pexprs _ _ _).
  rewrite hsemargs hsemc hsemprev {hsemargs hsemc hsemprev} /=.

  case: b hwrite => hwrite.
  all: rewrite (exec_sopn_conditional _ htruncprev hexec) {htruncprev hexec} /=.
  all: exact: hwrite.
Qed.

End WITH_PARAMS.