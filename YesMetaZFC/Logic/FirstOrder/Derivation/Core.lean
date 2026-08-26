import YesMetaZFC.Logic.FirstOrder.Admissibility.OpenAt
/-!
# 计算合法的一阶自然演绎内核

自然演绎规则先组成不携带手写语法合法证明的 `ND_Raw` 树，再由纯函数
`ND_Raw.check` 检查整棵树。`ND_Checked` 只保存原始规则树与
`check = true`；公共命题 `Derives T Γ φ` 是 checked 证书的非空性。

检查器覆盖：

* 每个规则节点的结论公式；
* 量词实例项与等词规则中的项 sort/scope；
* 存在消去和等词替换中不会必然成为子结论的公式模板。

因此 checked 证书一旦形成，公式良构性完全由检查器 soundness 恢复。公开规则接口
只负责组合 checked 子证书；调用者不再向可信规则树写入 `Formula.Admissible`、
`TermWellSorted` 或 `Term.BoundClosed` 字段。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w

/-- 不含手写语法合法字段的自然演绎规则树。 -/
inductive ND_Raw {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] :
    Theory σ → Context σ → Formula σ → Type (max u v w) where
  | assumption {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
      (hMem : φ ∈ Γ) :
      ND_Raw T Γ φ
  | theoryAxiom {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
      (hMem : T φ) :
      ND_Raw T Γ φ
  | contextWeakening {T : Theory σ} {Γ Δ : Context σ} {φ : Formula σ}
      (hSubset : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ) (hDerives : ND_Raw T Γ φ) :
      ND_Raw T Δ φ
  | theoryWeakening {T U : Theory σ} {Γ : Context σ} {φ : Formula σ}
      (hSubset : ∀ ψ, T ψ → U ψ) (hDerives : ND_Raw T Γ φ) :
      ND_Raw U Γ φ
  | truthIntro {T : Theory σ} {Γ : Context σ} :
      ND_Raw T Γ Formula.truth
  | falsumElim {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
      (hFalse : ND_Raw T Γ Formula.falsum) :
      ND_Raw T Γ φ
  | conjIntro {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
      (hLeft : ND_Raw T Γ left) (hRight : ND_Raw T Γ right) :
      ND_Raw T Γ (Formula.conj left right)
  | conjElimLeft {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
      (hConj : ND_Raw T Γ (Formula.conj left right)) :
      ND_Raw T Γ left
  | conjElimRight {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
      (hConj : ND_Raw T Γ (Formula.conj left right)) :
      ND_Raw T Γ right
  | disjIntroLeft {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
      (hLeft : ND_Raw T Γ left) :
      ND_Raw T Γ (Formula.disj left right)
  | disjIntroRight {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
      (hRight : ND_Raw T Γ right) :
      ND_Raw T Γ (Formula.disj left right)
  | disjElim {T : Theory σ} {Γ : Context σ}
      {left right conclusion : Formula σ}
      (hDisj : ND_Raw T Γ (Formula.disj left right))
      (hLeft : ND_Raw T (left :: Γ) conclusion)
      (hRight : ND_Raw T (right :: Γ) conclusion) :
      ND_Raw T Γ conclusion
  | impIntro {T : Theory σ} {Γ : Context σ}
      {antecedent consequent : Formula σ}
      (hBody : ND_Raw T (antecedent :: Γ) consequent) :
      ND_Raw T Γ (Formula.imp antecedent consequent)
  | impElim {T : Theory σ} {Γ : Context σ}
      {antecedent consequent : Formula σ}
      (hImp : ND_Raw T Γ (Formula.imp antecedent consequent))
      (hAntecedent : ND_Raw T Γ antecedent) :
      ND_Raw T Γ consequent
  | iffIntro {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
      (hForward : ND_Raw T (left :: Γ) right)
      (hBackward : ND_Raw T (right :: Γ) left) :
      ND_Raw T Γ (Formula.iff left right)
  | iffElimLeft {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
      (hIff : ND_Raw T Γ (Formula.iff left right))
      (hRight : ND_Raw T Γ right) :
      ND_Raw T Γ left
  | iffElimRight {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
      (hIff : ND_Raw T Γ (Formula.iff left right))
      (hLeft : ND_Raw T Γ left) :
      ND_Raw T Γ right
  | negIntro {T : Theory σ} {Γ : Context σ} {body : Formula σ}
      (hFalse : ND_Raw T (body :: Γ) Formula.falsum) :
      ND_Raw T Γ (Formula.neg body)
  | negElim {T : Theory σ} {Γ : Context σ} {body : Formula σ}
      (hBody : ND_Raw T Γ body)
      (hNeg : ND_Raw T Γ (Formula.neg body)) :
      ND_Raw T Γ Formula.falsum
  | byContradiction {T : Theory σ} {Γ : Context σ} {formula : Formula σ}
      (hRefute : ND_Raw T (Formula.neg formula :: Γ) Formula.falsum) :
      ND_Raw T Γ formula
  | forallIntro {T : Theory σ} {Γ : Context σ}
      {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ}
      (hTheoryFresh :
        ∀ formula, T formula →
          (sort, eigen) ∉ Formula.freeSupport formula)
      (hContextFresh :
        ∀ formula, formula ∈ Γ →
          (sort, eigen) ∉ Formula.freeSupport formula)
      (hBody : ND_Raw T Γ body) :
      ND_Raw T Γ
        (Formula.forallE sort
          (Formula.closeFreeAt sort eigen 0 body))
  | forallElim {T : Theory σ} {Γ : Context σ}
      {sort : σ.SortSymbol} {body : Formula σ} {term : Term σ}
      (hForall : ND_Raw T Γ (Formula.forallE sort body)) :
      ND_Raw T Γ (Formula.openAt sort 0 term body)
  | existsIntro {T : Theory σ} {Γ : Context σ}
      {sort : σ.SortSymbol} {body : Formula σ} {term : Term σ}
      (hBody : ND_Raw T Γ (Formula.openAt sort 0 term body)) :
      ND_Raw T Γ (Formula.existsE sort body)
  | existsElim {T : Theory σ} {Γ : Context σ}
      {sort : σ.SortSymbol} {eigen : FreeVarId}
      {body conclusion : Formula σ}
      (hTheoryFresh :
        ∀ formula, T formula →
          (sort, eigen) ∉ Formula.freeSupport formula)
      (hContextFresh :
        ∀ formula, formula ∈ Γ →
          (sort, eigen) ∉ Formula.freeSupport formula)
      (hConclusionFresh :
        (sort, eigen) ∉ Formula.freeSupport conclusion)
      (hExists :
        ND_Raw T Γ
          (Formula.existsE sort
            (Formula.closeFreeAt sort eigen 0 body)))
      (hCase : ND_Raw T (body :: Γ) conclusion) :
      ND_Raw T Γ conclusion
  | equalityRefl {T : Theory σ} {Γ : Context σ}
      (sort : σ.SortSymbol) {term : Term σ} :
      ND_Raw T Γ (Formula.equal term term)
  | equalityElim {T : Theory σ} {Γ : Context σ}
      {sort : σ.SortSymbol} {eigen : FreeVarId}
      {left right : Term σ} {body : Formula σ}
      (hEquality : ND_Raw T Γ (Formula.equal left right))
      (hBody :
        ND_Raw T Γ
          (Formula.substituteFree sort eigen left body)) :
      ND_Raw T Γ
        (Formula.substituteFree sort eigen right body)

namespace ND_Raw

/-- 对整棵自然演绎规则树执行纯函数合法性检查。 -/
def check
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ} :
    ND_Raw T Γ φ → Bool
  | .assumption _ =>
      Formula.check_admissible φ && true
  | .theoryAxiom _ =>
      Formula.check_admissible φ && true
  | .contextWeakening _ hDerives =>
      Formula.check_admissible φ && check hDerives
  | .theoryWeakening _ hDerives =>
      Formula.check_admissible φ && check hDerives
  | .truthIntro =>
      Formula.check_admissible φ && true
  | .falsumElim hFalse =>
      Formula.check_admissible φ && check hFalse
  | .conjIntro hLeft hRight =>
      Formula.check_admissible φ &&
        check hLeft && check hRight
  | .conjElimLeft hConj =>
      Formula.check_admissible φ && check hConj
  | .conjElimRight hConj =>
      Formula.check_admissible φ && check hConj
  | .disjIntroLeft hLeft =>
      Formula.check_admissible φ && check hLeft
  | .disjIntroRight hRight =>
      Formula.check_admissible φ && check hRight
  | .disjElim hDisj hLeft hRight =>
      Formula.check_admissible φ &&
        check hDisj && check hLeft && check hRight
  | .impIntro hBody =>
      Formula.check_admissible φ && check hBody
  | .impElim hImp hAntecedent =>
      Formula.check_admissible φ &&
        check hImp && check hAntecedent
  | .iffIntro hForward hBackward =>
      Formula.check_admissible φ &&
        check hForward && check hBackward
  | .iffElimLeft hIff hRight =>
      Formula.check_admissible φ &&
        check hIff && check hRight
  | .iffElimRight hIff hLeft =>
      Formula.check_admissible φ &&
        check hIff && check hLeft
  | .negIntro hFalse =>
      Formula.check_admissible φ && check hFalse
  | .negElim hBody hNeg =>
      Formula.check_admissible φ &&
        check hBody && check hNeg
  | .byContradiction hRefute =>
      Formula.check_admissible φ && check hRefute
  | .forallIntro _ _ hBody =>
      Formula.check_admissible φ && check hBody
  | @ND_Raw.forallElim _ _ _ _ sort _ term hForall =>
      Formula.check_admissible φ &&
        Term.check_admissible sort term && check hForall
  | @ND_Raw.existsIntro _ _ _ _ sort _ term hBody =>
      Formula.check_admissible φ &&
        Term.check_admissible sort term && check hBody
  | @ND_Raw.existsElim _ _ _ _ _ _ body _ _ _ _ hExists hCase =>
      Formula.check_admissible φ &&
        Formula.check_admissible body &&
          check hExists && check hCase
  | @ND_Raw.equalityRefl _ _ _ _ sort term =>
      Formula.check_admissible φ &&
        Term.check_admissible sort term
  | @ND_Raw.equalityElim _ _ _ _ sort _ left right body hEquality hBody =>
      Formula.check_admissible φ &&
        Term.check_admissible sort left &&
          Term.check_admissible sort right &&
            Formula.check_admissible body &&
              check hEquality && check hBody

/-- 整树检查成功必然包含根公式的计算合法证书。 -/
theorem root_checked
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    {raw : ND_Raw T Γ φ}
    (hCheck : raw.check = true) :
    Formula.CheckCertificate φ := by
  cases raw <;>
    simp only [check, Bool.and_eq_true_iff] at hCheck <;>
    first
    | exact hCheck.1
    | exact hCheck.1.1
    | exact hCheck.1.1.1
    | exact hCheck.1.1.1.1
    | exact hCheck.1.1.1.1.1

end ND_Raw

/-- 由纯函数检查器验过的自然演绎证书。 -/
structure ND_Checked
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (T : Theory σ) (Γ : Context σ) (φ : Formula σ) where
  raw : ND_Raw T Γ φ
  checked : raw.check = true

namespace ND_Checked

/-- 运行纯函数检查器并在成功时产生 checked 证书。 -/
def mk?
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (raw : ND_Raw T Γ φ) :
    Option (ND_Checked T Γ φ) :=
  if h : raw.check = true then
    some { raw := raw, checked := h }
  else
    none

/-- checked 推导的根公式已经通过计算检查。 -/
theorem formula_checked
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (cert : ND_Checked T Γ φ) :
    Formula.CheckCertificate φ :=
  cert.raw.root_checked cert.checked

/-- checked 推导的根公式自动落在 proof-layer 良构性边界内。 -/
theorem admissible
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (cert : ND_Checked T Γ φ) :
    Formula.Admissible φ :=
  cert.formula_checked.admissible

/-- checked 推导的根公式自动具有 sort/arity 良构性。 -/
theorem wellFormed
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (cert : ND_Checked T Γ φ) :
    FormulaWellFormed φ :=
  cert.formula_checked.wellFormed

end ND_Checked

/-- 公共推导命题：存在一个通过纯函数检查的自然演绎证书。 -/
def Derives
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    (T : Theory σ) (Γ : Context σ) (φ : Formula σ) : Prop :=
  Nonempty (ND_Checked T Γ φ)

namespace Derives

/-- checked 证书进入公共推导命题。 -/
theorem of_checked
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (cert : ND_Checked T Γ φ) :
    Derives T Γ φ :=
  ⟨cert⟩

/-- 原始规则树连同检查等式进入公共推导命题。 -/
theorem of_check
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (raw : ND_Raw T Γ φ) (hCheck : raw.check = true) :
    Derives T Γ φ :=
  of_checked { raw := raw, checked := hCheck }

/-- 公共推导结论的计算合法证书。 -/
theorem formula_checked
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hDerives : Derives T Γ φ) :
    Formula.CheckCertificate φ := by
  rcases hDerives with ⟨cert⟩
  exact cert.formula_checked

/-- 公共推导结论自动满足 proof-layer 良构性。 -/
theorem admissible
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hDerives : Derives T Γ φ) :
    Formula.Admissible φ :=
  hDerives.formula_checked.admissible

/-- 公共推导结论自动满足 sort/arity 良构性。 -/
theorem wellFormed
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hDerives : Derives T Γ φ) :
    FormulaWellFormed φ :=
  hDerives.formula_checked.wellFormed

/-- 供规则接口自动恢复任意已证明公式的计算合法证书。 -/
macro "prove_nd_formula_check" : tactic =>
  `(tactic|
    solve
    | exact (Derives.formula_checked (by assumption))
    | exact Formula.check_admissible_complete (by assumption)
    | exact Formula.check_admissible_complete
        (Formula.Admissible.neg (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.conj
          (by assumption) (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.disj
          (by assumption) (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.imp
          (by assumption) (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.iff
          (by assumption) (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.neg_body (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.conj_left (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.conj_right (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.disj_left (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.disj_right (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.imp_left (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.imp_right (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.iff_left (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.iff_right (by assumption))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.neg_body
          (Derives.admissible (by assumption)))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.conj_left
          (Derives.admissible (by assumption)))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.conj_right
          (Derives.admissible (by assumption)))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.disj_left
          (Derives.admissible (by assumption)))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.disj_right
          (Derives.admissible (by assumption)))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.imp_left
          (Derives.admissible (by assumption)))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.imp_right
          (Derives.admissible (by assumption)))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.iff_left
          (Derives.admissible (by assumption)))
    | exact Formula.check_admissible_complete
        (Formula.Admissible.iff_right
          (Derives.admissible (by assumption)))
    | prove_formula_check)

/--
应用自然演绎规则后，自动消去由内核计算证书产生的 side goals。
逻辑前提仍按普通 `apply` 顺序保留，因此证明脚本不需要显式传递合法性参数。
-/
macro "nd_apply " rule:term : tactic =>
  `(tactic|
    apply $rule <;>
      all_goals
        try unfold autoParam
        try
          first
          | (change Formula.CheckCertificate _
             prove_nd_formula_check)
          | (change Term.CheckCertificate _ _
             prove_term_check))

/-- 假设规则。合法性由公式纯函数检查自动生成。 -/
theorem assumption
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hMem : φ ∈ Γ)
    (hCheck : Formula.CheckCertificate φ := by prove_nd_formula_check) :
    Derives T Γ φ :=
  of_check (.assumption hMem) <| by
    simp [ND_Raw.check, hCheck]

/-- 理论公理规则。合法性由公式纯函数检查自动生成。 -/
theorem theoryAxiom
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hMem : T φ)
    (hCheck : Formula.CheckCertificate φ := by prove_nd_formula_check) :
    Derives T Γ φ :=
  of_check (.theoryAxiom hMem) <| by
    simp [ND_Raw.check, hCheck]

theorem contextWeakening
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ Δ : Context σ} {φ : Formula σ}
    (hSubset : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ)
    (hDerives : Derives T Γ φ) :
    Derives T Δ φ := by
  rcases hDerives with ⟨cert⟩
  apply of_check (.contextWeakening hSubset cert.raw)
  simp [ND_Raw.check, cert.formula_checked, cert.checked]

theorem theoryWeakening
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T U : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hSubset : ∀ ψ, T ψ → U ψ)
    (hDerives : Derives T Γ φ) :
    Derives U Γ φ := by
  rcases hDerives with ⟨cert⟩
  apply of_check (.theoryWeakening hSubset cert.raw)
  simp [ND_Raw.check, cert.formula_checked, cert.checked]

theorem truthIntro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} :
    Derives T Γ Formula.truth :=
  of_check .truthIntro <| by
    simp [ND_Raw.check, Formula.check_admissible_complete
      (Formula.Admissible.truth : Formula.Admissible
        (Formula.truth : Formula σ))]

theorem falsumElim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hFalse : Derives T Γ Formula.falsum)
    (hCheck : Formula.CheckCertificate φ := by prove_nd_formula_check) :
    Derives T Γ φ := by
  rcases hFalse with ⟨cert⟩
  apply of_check (.falsumElim cert.raw)
  simp [ND_Raw.check, hCheck, cert.checked]

theorem conjIntro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hLeft : Derives T Γ left) (hRight : Derives T Γ right) :
    Derives T Γ (Formula.conj left right) := by
  rcases hLeft with ⟨leftCert⟩
  rcases hRight with ⟨rightCert⟩
  apply of_check (.conjIntro leftCert.raw rightCert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.conj leftCert.admissible rightCert.admissible),
    leftCert.checked, rightCert.checked]

theorem conjElimLeft
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hConj : Derives T Γ (Formula.conj left right)) :
    Derives T Γ left := by
  rcases hConj with ⟨cert⟩
  apply of_check (.conjElimLeft cert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.conj_left cert.admissible), cert.checked]

theorem conjElimRight
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hConj : Derives T Γ (Formula.conj left right)) :
    Derives T Γ right := by
  rcases hConj with ⟨cert⟩
  apply of_check (.conjElimRight cert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.conj_right cert.admissible), cert.checked]

theorem disjIntroLeft
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hLeft : Derives T Γ left)
    (hRightCheck : Formula.CheckCertificate right := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.disj left right) := by
  rcases hLeft with ⟨cert⟩
  apply of_check (.disjIntroLeft cert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.disj cert.admissible
      hRightCheck.admissible), cert.checked]

theorem disjIntroRight
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hRight : Derives T Γ right)
    (hLeftCheck : Formula.CheckCertificate left := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.disj left right) := by
  rcases hRight with ⟨cert⟩
  apply of_check (.disjIntroRight cert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.disj hLeftCheck.admissible
      cert.admissible), cert.checked]

theorem disjElim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {left right conclusion : Formula σ}
    (hDisj : Derives T Γ (Formula.disj left right))
    (hLeft : Derives T (left :: Γ) conclusion)
    (hRight : Derives T (right :: Γ) conclusion) :
    Derives T Γ conclusion := by
  rcases hDisj with ⟨disjCert⟩
  rcases hLeft with ⟨leftCert⟩
  rcases hRight with ⟨rightCert⟩
  apply of_check
    (.disjElim disjCert.raw leftCert.raw rightCert.raw)
  simp [ND_Raw.check, leftCert.formula_checked,
    disjCert.checked, leftCert.checked, rightCert.checked]

theorem impIntro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {antecedent consequent : Formula σ}
    (hBody : Derives T (antecedent :: Γ) consequent)
    (hAntecedentCheck : Formula.CheckCertificate antecedent := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.imp antecedent consequent) := by
  rcases hBody with ⟨cert⟩
  apply of_check (.impIntro cert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.imp hAntecedentCheck.admissible
      cert.admissible), cert.checked]

theorem impElim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {antecedent consequent : Formula σ}
    (hImp : Derives T Γ (Formula.imp antecedent consequent))
    (hAntecedent : Derives T Γ antecedent) :
    Derives T Γ consequent := by
  rcases hImp with ⟨impCert⟩
  rcases hAntecedent with ⟨antecedentCert⟩
  apply of_check (.impElim impCert.raw antecedentCert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.imp_right impCert.admissible),
    impCert.checked, antecedentCert.checked]

theorem iffIntro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hForward : Derives T (left :: Γ) right)
    (hBackward : Derives T (right :: Γ) left) :
    Derives T Γ (Formula.iff left right) := by
  rcases hForward with ⟨forwardCert⟩
  rcases hBackward with ⟨backwardCert⟩
  apply of_check (.iffIntro forwardCert.raw backwardCert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.iff backwardCert.admissible
      forwardCert.admissible),
    forwardCert.checked, backwardCert.checked]

theorem iffElimLeft
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hIff : Derives T Γ (Formula.iff left right))
    (hRight : Derives T Γ right) :
    Derives T Γ left := by
  rcases hIff with ⟨iffCert⟩
  rcases hRight with ⟨rightCert⟩
  apply of_check (.iffElimLeft iffCert.raw rightCert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.iff_left iffCert.admissible),
    iffCert.checked, rightCert.checked]

theorem iffElimRight
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hIff : Derives T Γ (Formula.iff left right))
    (hLeft : Derives T Γ left) :
    Derives T Γ right := by
  rcases hIff with ⟨iffCert⟩
  rcases hLeft with ⟨leftCert⟩
  apply of_check (.iffElimRight iffCert.raw leftCert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.iff_right iffCert.admissible),
    iffCert.checked, leftCert.checked]

theorem negIntro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {body : Formula σ}
    (hFalse : Derives T (body :: Γ) Formula.falsum)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.neg body) := by
  rcases hFalse with ⟨cert⟩
  apply of_check (.negIntro cert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.neg hBodyCheck.admissible), cert.checked]

theorem negElim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {body : Formula σ}
    (hBody : Derives T Γ body)
    (hNeg : Derives T Γ (Formula.neg body)) :
    Derives T Γ Formula.falsum := by
  rcases hBody with ⟨bodyCert⟩
  rcases hNeg with ⟨negCert⟩
  apply of_check (.negElim bodyCert.raw negCert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.falsum : Formula.Admissible
      (Formula.falsum : Formula σ)),
    bodyCert.checked, negCert.checked]

theorem byContradiction
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {formula : Formula σ}
    (hRefute :
      Derives T (Formula.neg formula :: Γ) Formula.falsum)
    (hFormulaCheck : Formula.CheckCertificate formula := by
      prove_nd_formula_check) :
    Derives T Γ formula := by
  rcases hRefute with ⟨cert⟩
  apply of_check (.byContradiction cert.raw)
  simp [ND_Raw.check, hFormulaCheck, cert.checked]

theorem forallIntro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ}
    (hTheoryFresh :
      ∀ formula, T formula →
        (sort, eigen) ∉ Formula.freeSupport formula)
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        (sort, eigen) ∉ Formula.freeSupport formula)
    (hBody : Derives T Γ body) :
    Derives T Γ
      (Formula.forallE sort
        (Formula.closeFreeAt sort eigen 0 body)) := by
  rcases hBody with ⟨cert⟩
  apply of_check
    (.forallIntro hTheoryFresh hContextFresh cert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.forall_closeFreeAt sort eigen
      cert.admissible), cert.checked]

theorem forallElim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {body : Formula σ} {term : Term σ}
    (hForall : Derives T Γ (Formula.forallE sort body))
    (hTermCheck : Term.CheckCertificate term sort := by
      prove_term_check) :
    Derives T Γ (Formula.openAt sort 0 term body) := by
  rcases hForall with ⟨cert⟩
  apply of_check (.forallElim cert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.forall_openAt sort cert.admissible
      hTermCheck.admissible), hTermCheck, cert.checked]

theorem existsIntro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {body : Formula σ} {term : Term σ}
    (hBody : Derives T Γ (Formula.openAt sort 0 term body))
    (hTermCheck : Term.CheckCertificate term sort := by
      prove_term_check) :
    Derives T Γ (Formula.existsE sort body) := by
  rcases hBody with ⟨cert⟩
  apply of_check (.existsIntro cert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.exists_of_openAt sort
      hTermCheck.admissible.1 cert.admissible),
    hTermCheck, cert.checked]

theorem existsElim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body conclusion : Formula σ}
    (hTheoryFresh :
      ∀ formula, T formula →
        (sort, eigen) ∉ Formula.freeSupport formula)
    (hContextFresh :
      ∀ formula, formula ∈ Γ →
        (sort, eigen) ∉ Formula.freeSupport formula)
    (hConclusionFresh :
      (sort, eigen) ∉ Formula.freeSupport conclusion)
    (hExists :
      Derives T Γ
        (Formula.existsE sort
          (Formula.closeFreeAt sort eigen 0 body)))
    (hCase : Derives T (body :: Γ) conclusion)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Derives T Γ conclusion := by
  rcases hExists with ⟨existsCert⟩
  rcases hCase with ⟨caseCert⟩
  apply of_check
    (.existsElim hTheoryFresh hContextFresh hConclusionFresh
      existsCert.raw caseCert.raw)
  simp [ND_Raw.check, caseCert.formula_checked, hBodyCheck,
    existsCert.checked, caseCert.checked]

theorem equalityRefl
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    (sort : σ.SortSymbol) {term : Term σ}
    (hTermCheck : Term.CheckCertificate term sort := by
      prove_term_check) :
    Derives T Γ (Formula.equal term term) :=
  of_check (.equalityRefl sort) <| by
    simp [ND_Raw.check, Formula.check_admissible_complete
      (Formula.Admissible.equal hTermCheck.admissible
        hTermCheck.admissible), hTermCheck]

theorem equalityElim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Term σ} {body : Formula σ}
    (hEquality : Derives T Γ (Formula.equal left right))
    (hBody :
      Derives T Γ
        (Formula.substituteFree sort eigen left body))
    (hLeftCheck : Term.CheckCertificate left sort := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right sort := by
      prove_term_check)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Derives T Γ
      (Formula.substituteFree sort eigen right body) := by
  rcases hEquality with ⟨equalityCert⟩
  rcases hBody with ⟨bodyCert⟩
  apply of_check (.equalityElim equalityCert.raw bodyCert.raw)
  simp [ND_Raw.check, Formula.check_admissible_complete
    (Formula.Admissible.substituteFree sort eigen
      hBodyCheck.admissible hRightCheck.admissible),
    hLeftCheck, hRightCheck, hBodyCheck,
    equalityCert.checked, bodyCert.checked]

/-- 沿公式等式运输推导结论。 -/
def formula_cast
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {source target : Formula σ}
    (hFormula : source = target) (hSource : Derives T Γ source) :
    Derives T Γ target :=
  hFormula ▸ hSource

/-! 下列 snake_case 名称构成稳定的公开证明脚本接口。 -/

theorem theory_axiom
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hTheory : T φ)
    (hCheck : Formula.CheckCertificate φ := by
      prove_nd_formula_check) :
    Derives T Γ φ :=
  theoryAxiom hTheory hCheck

theorem truth_intro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} :
    Derives T Γ Formula.truth :=
  truthIntro

theorem falsum_elim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (hFalse : Derives T Γ Formula.falsum)
    (hCheck : Formula.CheckCertificate φ := by
      prove_nd_formula_check) :
    Derives T Γ φ :=
  falsumElim hFalse hCheck

theorem conj_intro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hLeft : Derives T Γ left) (hRight : Derives T Γ right) :
    Derives T Γ (Formula.conj left right) :=
  conjIntro hLeft hRight

theorem conj_elim_left
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hConjunction : Derives T Γ (Formula.conj left right)) :
    Derives T Γ left :=
  conjElimLeft hConjunction

theorem conj_elim_right
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hConjunction : Derives T Γ (Formula.conj left right)) :
    Derives T Γ right :=
  conjElimRight hConjunction

theorem disj_intro_left
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hLeft : Derives T Γ left)
    (hRightCheck : Formula.CheckCertificate right := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.disj left right) :=
  disjIntroLeft hLeft hRightCheck

theorem disj_intro_right
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hRight : Derives T Γ right)
    (hLeftCheck : Formula.CheckCertificate left := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.disj left right) :=
  disjIntroRight hRight hLeftCheck

theorem disj_elim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {left right conclusion : Formula σ}
    (hDisjunction : Derives T Γ (Formula.disj left right))
    (hLeft : Derives T (left :: Γ) conclusion)
    (hRight : Derives T (right :: Γ) conclusion) :
    Derives T Γ conclusion :=
  disjElim hDisjunction hLeft hRight

theorem imp_intro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {antecedent consequent : Formula σ}
    (hBody : Derives T (antecedent :: Γ) consequent)
    (hAntecedentCheck : Formula.CheckCertificate antecedent := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.imp antecedent consequent) :=
  impIntro hBody hAntecedentCheck

theorem imp_elim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {antecedent consequent : Formula σ}
    (hImplication : Derives T Γ (Formula.imp antecedent consequent))
    (hAntecedent : Derives T Γ antecedent) :
    Derives T Γ consequent :=
  impElim hImplication hAntecedent

theorem iff_intro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hForward : Derives T (left :: Γ) right)
    (hBackward : Derives T (right :: Γ) left) :
    Derives T Γ (Formula.iff left right) :=
  iffIntro hForward hBackward

theorem iff_elim_left
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hIff : Derives T Γ (Formula.iff left right))
    (hRight : Derives T Γ right) :
    Derives T Γ left :=
  iffElimLeft hIff hRight

theorem iff_elim_right
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {left right : Formula σ}
    (hIff : Derives T Γ (Formula.iff left right))
    (hLeft : Derives T Γ left) :
    Derives T Γ right :=
  iffElimRight hIff hLeft

theorem neg_intro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {body : Formula σ}
    (hFalse : Derives T (body :: Γ) Formula.falsum)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.neg body) :=
  negIntro hFalse hBodyCheck

theorem neg_elim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {body : Formula σ}
    (hBody : Derives T Γ body)
    (hNegation : Derives T Γ (Formula.neg body)) :
    Derives T Γ Formula.falsum :=
  negElim hBody hNegation

theorem by_contradiction
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {formula : Formula σ}
    (hRefutation :
      Derives T (Formula.neg formula :: Γ) Formula.falsum)
    (hFormulaCheck : Formula.CheckCertificate formula := by
      prove_nd_formula_check) :
    Derives T Γ formula :=
  byContradiction hRefutation hFormulaCheck

end Derives
end FirstOrder
end Logic
end YesMetaZFC
