Require dmasm_Ssem.

Require Import Utf8.
Import Morphisms.
Import ssreflect.
Import ssrbool.
Import eqtype.
Import seq.
Import ZArith.
Local Open Scope Z_scope.

Import dmasm_utils.
Import dmasm_type.
Import dmasm_var.
Import dmasm_expr.
Import dmasm_sem.
Import dmasm_Ssem.
Import memory.
Import UnsafeMemory.

Lemma ssem_inv { prg s c s' } :
  ssem prg s c s' →
  match c with
  | [::] => s' = s
  | i :: c' => ∃ si, ssem_I prg s i si ∧ ssem prg si c' s'
end.
Proof. case; eauto. Qed.

Lemma ssem_I_inv { prg s i s' } :
  ssem_I prg s i s' →
  ∃ i' ii, i = MkI ii i' ∧ ssem_i prg s i' s'.
Proof. case; eauto. Qed.

Lemma ssem_i_inv { prg s i s' } :
  ssem_i prg s i s' →
  match i with
  | Cassgn x tg e => ∃ v, ssem_pexpr s e = ok v ∧ swrite_rval x v s = ok s'
  | _ => True
  end.
Proof.
  case; eauto.
  clear.
  move=> s s' x _ e H. case: (bindW H). eauto.
Qed.

Definition MkI_inj {ii i ii' i'} (H: MkI ii i = MkI ii' i') :
  ii = ii' ∧ i = i' :=
  let 'Logic.eq_refl := H in conj Logic.eq_refl Logic.eq_refl.

Definition hpred : Type :=
  sestate → Prop.

Notation "A ⊂ B" := (∀ x, A x → B x) (at level 80) : msem_scope.

Local Open Scope msem_scope.

Section HOARE_LOGIC.

Context (prg: prog).

Definition hoare (Pre: hpred) (c: cmd) (Post: hpred) : Prop :=
  ∀ s s' : sestate,
    ssem prg s c s' →
    Pre s → Post s'.

Lemma hoare_conseq (P1 Q1: hpred) (c: cmd) (P2 Q2: hpred) :
  P2 ⊂ P1 → Q1 ⊂ Q2 →
  hoare P1 c Q1 → hoare P2 c Q2.
Proof. firstorder. Qed.

Lemma hoare_skip_core P : hoare P [::] P.
Proof. by move => s s' H; case (ssem_inv H). Qed.

Lemma hoare_skip (Q P: hpred) : Q ⊂ P → hoare Q [::] P.
Proof. eauto using hoare_conseq, hoare_skip_core. Qed.

Lemma hoare_cons R P Q i c :
  hoare P [:: i] R →  hoare R c Q →  hoare P (i :: c) Q.
Proof.
  by
  move=> Hi Hc s s' /ssem_inv [ s1 [Hi' Hc']] H;
  eauto using SEseq, SEskip.
Qed.

Lemma hoare_assgn (P: hpred) ii x tag e :
  hoare
    (λ s, ∀ v s',
        ssem_pexpr s e = ok v →
        swrite_rval x v s = ok s' →
        P s')
    [:: MkI ii (Cassgn x tag e) ] P.
Proof.
  move=> s s1 / ssem_inv [ s' [Hi /ssem_inv]] ->.
  case: (ssem_I_inv Hi) => i' [ ii' [ /MkI_inj [? ?] Hi' ] ]; clear Hi; subst ii' i'.
  move: (ssem_i_inv Hi') => [ v [ Hv Hs' ] ].
  exact (λ H, H _ _ Hv Hs').
Qed.

End HOARE_LOGIC.

Section WEAKEST_PRECONDITION.

(* A formula is a predicate over an environment that maps logical variables to value. *)
(* This predicate should be extensional *)

Definition env : Type := Mv.t ssem_t.
Definition env_ext (m m': env) : Prop :=
  ∀ x, (m.[x] = m'.[x])%mv.

Definition env_ext_refl m : env_ext m m := λ x, Logic.eq_refl.

Definition env_ext_sym m m' (H: env_ext m m') : env_ext m' m :=
  λ x, Logic.eq_sym (H x).

Definition env_ext_trans m' m m'' (H: env_ext m m') (H': env_ext m' m'') :
  env_ext m m'' :=
  λ x, Logic.eq_trans (H x) (H' x).

Lemma env_ext_empty m m' :
  (∀ x, m x = m' x) →
  env_ext (Mv.empty m) (Mv.empty m').
Proof. by move=> E x; rewrite ! Mv.get0. Qed.

Lemma env_ext_set m m' x v :
  env_ext m m' →
  (env_ext (m.[x <- v]) (m'.[x <- v]))%mv.
Proof.
  move=> E y.
  case: (x =P y) => [ <- | H ].
  rewrite ! Mv.setP_eq //.
  assert (x != y) by (case: eqP => //).
  rewrite ! Mv.setP_neq //.
Qed.

Definition formula : Type :=
  sigT (Proper (@eq mem ==> env_ext ==> iff)).

Lemma formula_m (f: mem → env → Prop) :
  (∀ m s s', env_ext s s' → f m s → f m s') →
  Proper (@eq mem ==> env_ext ==> iff) f.
Proof.
  move=> E m ? <- s s' H.
  split; eauto using env_ext_sym.
Qed.

Instance constant_formula_m (P: Prop) : Proper (@eq mem ==> env_ext ==> iff) (λ _ _, P) :=
  formula_m _ (λ _ _ _ _ (p: P), p).

Example ftrue: formula := existT _ (λ _ _, True) _.
Example ffalse: formula := existT _ (λ _ _, False) _.

Definition formula_of_hpred (P: hpred) : formula.
Proof.
  refine (existT _ (λ (m: mem) (s: env), P {| semem := m ; sevm := Fv.empty (λ x, s.[x])%mv |}) _).
  apply formula_m.
  move=> m s s' E H.
  refine (eq_ind _ P H _ _).
  f_equal.
  apply Fv.map_ext. auto.
Defined.

Notation "⟨ P ⟩" := (formula_of_hpred P) : msem_scope.

Definition formula_denote (f: formula) : hpred :=
  λ s, projT1 f (semem s) (Mv.empty (λ x, (sevm s).[x])%vmap).

Notation "⟦ f ⟧" := (formula_denote f) : msem_scope.

Lemma formula_of_hpred_denote P :
  ∀ s, ⟦ ⟨P⟩ ⟧ s ↔ P s.
Proof.
  unfold formula_of_hpred, formula_denote. simpl.
  by
  move=> [ m vm ]; split; move=> H; refine (eq_ind _ P H _ _); f_equal; apply Fv.map_ext; move=> x;
  rewrite Fv.get0 Mv.get0.
Qed.

Remark ffalse_denote (P: Prop) s : ⟦ ffalse ⟧ s → P.
Proof. easy. Qed.

Variant stype' : Type := sint' | sbool'.

Definition stype_of_stype' (ty: stype') : stype :=
  match ty with
  | sint' => sint
  | sbool' => sbool
  end.

Local Coercion stype_of_stype' : stype' >-> stype.

Definition op2_type (op: sop2) : stype' * stype' :=
  match op with
  | (Oand | Oor ) => (sbool', sbool')
  | (Oadd | Omul | Osub) => (sint', sint')
  | (Oeq | Oneq | Olt | Ole | Ogt | Oge) => (sint', sbool')
  end.

Definition op2_type_i op := fst (op2_type op).
Definition op2_type_o op := snd (op2_type op).

Definition sem_texpr_sop2 op : ssem_t (op2_type_i op) → ssem_t (op2_type_i op) → ssem_t (op2_type_o op) :=
  match op with
  | Oand => andb
  | Oor => orb
  | Oadd => Z.add
  | Omul => Z.mul
  | Osub => Z.sub
  | Oeq => Z.eqb
  | Oneq => λ x y, negb (Z.eqb x y)
  | Olt => Z.ltb
  | Ole => Z.leb
  | Ogt => Z.gtb
  | Oge => Z.geb
  end.

Inductive texpr : stype → Type :=
| Tconst : Z → texpr sint
| Tbool : bool → texpr sbool
| Tcast : texpr sint → texpr sword
| Tvar x : texpr (vtype x)
| Tget : positive → Ident.ident → texpr sint → texpr sword
| Tload : Ident.ident → texpr sword → texpr sword
| Tnot : texpr sbool → texpr sbool
| Tapp2 op (_ _: texpr (op2_type_i op)) : texpr (op2_type_o op)
.

Section SEM_TEXPR.
  Context (m: mem) (s: env).
  Fixpoint sem_texpr ty (e: texpr ty) : ssem_t ty :=
    match e in texpr ty return ssem_t ty with
    | Tconst z => z
    | Tbool b => b
    | Tcast e => I64.repr (sem_texpr sint e)
    | Tvar x => s.[x]
    | Tget n x e =>
      let a := s.[{| vtype := sarr n; vname := x |}] in
      let i := sem_texpr sint e in
      FArray.get a i
    | Tload x e =>
      let w1 := s.[{| vtype := sword; vname := x |}] in
      let w2 := sem_texpr sword e in
      let w := read_mem m (I64.add w1 w2) in
      w
    | Tnot e => negb (sem_texpr sbool e)
    | Tapp2 op e1 e2 =>
      let v1 := sem_texpr (op2_type_i op) e1 in
      let v2 := sem_texpr (op2_type_i op) e2 in
      sem_texpr_sop2 op v1 v2
    end%mv.
End SEM_TEXPR.

Lemma sem_texpr_m (m: mem) (s s': env) :
  env_ext s s' →
  ∀ ty e, sem_texpr m s ty e = sem_texpr m s' ty e.
Proof.
  move=> E ty e.
  elim: e => //; simpl; congruence.
Qed.

Definition stype_eq_dec (ty ty': stype) : { ty = ty' } + { True } :=
  match ty, ty' with
  | sword, sword => left Logic.eq_refl
  | sbool, sbool => left Logic.eq_refl
  | sint, sint => left Logic.eq_refl
  | sarr n, sarr n' =>
    match Pos.eq_dec n n' with
    | left EQ => left (f_equal sarr EQ)
    | right _ => right I
    end
  | _, _ => right I
  end.

Fixpoint type_check_pexpr (e: pexpr) (ty: stype) : option (texpr ty) :=
  match e with
  | Pconst z => match ty with sint => Some (Tconst z) | _ => None end
  | Pbool b => match ty with sbool => Some (Tbool b) | _ => None end
  | Pcast p =>
    match type_check_pexpr p sint with
    | Some tp => match ty with sword => Some (Tcast tp) | _ => None end
    | None => None end
  | Pvar x =>
    match stype_eq_dec (vtype x) ty with
    | left EQ => Some (eq_rect _ _ (Tvar x) _ EQ)
    | right _ => None
    end
  | Pget x i =>
    match x with
    | {| v_var := Var (sarr n) t |} =>
    match type_check_pexpr i sint with
    | Some ti => match ty with sword => Some (Tget n t ti) | _ => None end
    | None => None end
    | _ => None end
  | Pload x i =>
    match x with
    | {| v_var := Var sword p |} =>
    match type_check_pexpr i sword with
    | Some ti => match ty with sword => Some (Tload p ti) | _ => None end
    | None => None end
    | _ => None end
  | Pnot p =>
    match type_check_pexpr p sbool with
    | Some tp => match ty with sbool => Some (Tnot tp) | _ => None end
    | None => None end
  | Papp2 op p q =>
    match type_check_pexpr p (op2_type_i op) with
    | Some tp =>
    match type_check_pexpr q (op2_type_i op) with
    | Some tq =>
      match stype_eq_dec (op2_type_o op) ty with
      | left EQ => Some (eq_rect _ _ (Tapp2 op tp tq) _ EQ)
      | _ => None end
    | None => None end
    | None => None end
  end.

End WEAKEST_PRECONDITION.
