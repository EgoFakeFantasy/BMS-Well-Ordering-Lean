import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier
/-!
# 有限全称闭包
本模块把纸面证明中反复出现的“选择自由变量实例，再逐层应用全域化”整理为一个
列表驱动接口。调用方只需给出要关闭的具名自由变量；locally nameless 的深度移动
仍由 `Formula.closeFreeAt` 统一处理。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
universe u v w
namespace Formula
/-- 按给定顺序对有限自由变量列表作全称闭包。 -/
def forall_close {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (variables : List (σ.SortSymbol × FreeVarId)) (body : Formula σ) : Formula σ :=
  match variables with
  | [] => body
  | (sort, eigen) :: rest =>
      ∀ₘ[sort, eigen], forall_close rest body
@[simp]
theorem forall_close_nil {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (body : Formula σ) :
    forall_close [] body = body :=
  rfl
@[simp]
theorem forall_close_cons {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (eigen : FreeVarId) (variables : List (σ.SortSymbol × FreeVarId)) (body : Formula σ) :
    forall_close ((sort, eigen) :: variables) body = (∀ₘ[sort, eigen], forall_close variables body) :=
  rfl
/-- 有限全称闭包保持 proof-carrying 公式边界。 -/
theorem forall_close_admissible {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (variables : List (σ.SortSymbol × FreeVarId))
    {body : Formula σ} (hBody : FirstOrder.Formula.Admissible body) :
    FirstOrder.Formula.Admissible (forall_close variables body) := by
  induction variables with
  | nil =>
      simpa using hBody
  | cons head variables ih =>
      rcases head with ⟨sort, eigen⟩
      rw [forall_close_cons]
      exact FirstOrder.Formula.Admissible.forall_closeFreeAt
        sort eigen ih
/-- 全称闭包不会引入原公式之外的自由变量。 -/
theorem freeSupport_forall_close_subset {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (variables : List (σ.SortSymbol × FreeVarId)) (body : Formula σ) :
    ∀ freeVariable,
      freeVariable ∈
          FirstOrder.Formula.freeSupport (forall_close variables body) →
        freeVariable ∈ FirstOrder.Formula.freeSupport body := by
  induction variables with
  | nil =>
      intro freeVariable hFree
      simpa using hFree
  | cons head variables ih =>
      rcases head with ⟨sort, eigen⟩
      intro freeVariable hFree
      apply ih freeVariable
      by_cases hMember :
          freeVariable ∈
            FirstOrder.Formula.freeSupport (forall_close variables body)
      · exact hMember
      · apply False.elim
        apply (FirstOrder.Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            freeVariable sort eigen 0 (forall_close variables body) hMember)
        simpa [forall_close, FirstOrder.Formula.freeSupport] using hFree
/-- 列入关闭表的自由变量不会残留在闭包结果中。 -/
theorem not_mem_freeSupport_forall_close_of_mem
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {freeVariable : σ.SortSymbol × FreeVarId} (variables : List (σ.SortSymbol × FreeVarId)) (body : Formula σ) (hVariable : freeVariable ∈ variables) :
    freeVariable ∉
      FirstOrder.Formula.freeSupport (forall_close variables body) := by
  induction variables with
  | nil =>
      simp at hVariable
  | cons head variables ih =>
      rcases head with ⟨sort, eigen⟩
      rcases List.mem_cons.mp hVariable with hHead | hTail
      · subst freeVariable
        simpa [forall_close, FirstOrder.Formula.freeSupport] using
          FirstOrder.Formula.not_mem_freeSupport_closeFreeAt
            sort eigen 0 (forall_close variables body)
      · have hFresh :
            freeVariable ∉
              FirstOrder.Formula.freeSupport (forall_close variables body) :=
          ih hTail
        simpa [forall_close, FirstOrder.Formula.freeSupport] using
          FirstOrder.Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            freeVariable sort eigen 0 (forall_close variables body) hFresh
/--
只要关闭表覆盖公式的全部自由变量，全称闭包就得到一个闭的 admissible 句子。
-/
theorem forall_close_cover_sentence {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (variables : List (σ.SortSymbol × FreeVarId)) (body : Formula σ) (hBody : FirstOrder.Formula.Admissible body) (hCover :
      ∀ freeVariable,
        freeVariable ∈ FirstOrder.Formula.freeSupport body →
          freeVariable ∈ variables) :
    FirstOrder.Formula.Sentence (forall_close variables body) := by
  constructor
  · exact forall_close_admissible variables hBody
  · cases hSupport :
      FirstOrder.Formula.freeSupport (forall_close variables body) with
    | nil =>
        rfl
    | cons freeVariable rest =>
        have hClosedMember :
            freeVariable ∈
              FirstOrder.Formula.freeSupport (forall_close variables body) := by
          simp [hSupport]
        have hBodyMember :
            freeVariable ∈
              FirstOrder.Formula.freeSupport body :=
          freeSupport_forall_close_subset
            variables body freeVariable hClosedMember
        exact False.elim <| (not_mem_freeSupport_forall_close_of_mem
            variables body (hCover freeVariable hBodyMember)) hClosedMember
/--
按公式自身的自由变量支持作全称闭包，会得到一个闭的 admissible 句子。
支持列表允许重复；重复关闭同一变量只增加空量词，不影响闭性。
-/
theorem forall_close_freeSupport_sentence {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (body : Formula σ) (hBody : FirstOrder.Formula.Admissible body) :
    FirstOrder.Formula.Sentence (forall_close (FirstOrder.Formula.freeSupport body)
        body) :=
  forall_close_cover_sentence (FirstOrder.Formula.freeSupport body)
    body hBody (fun _ hVariable => hVariable)
/-- 去重自由变量支持后作全称闭包，得到更紧凑的闭句。 -/
theorem forall_close_eraseDups_freeSupport_sentence
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (body : Formula σ) (hBody : FirstOrder.Formula.Admissible body) :
    FirstOrder.Formula.Sentence (forall_close (FirstOrder.Formula.freeSupport body).eraseDups
        body) :=
  forall_close_cover_sentence (FirstOrder.Formula.freeSupport body).eraseDups
    body hBody (by
      intro freeVariable hVariable
      simpa using hVariable)
end Formula
namespace Derives
/--
在理论和局部上下文均满足 eigenvariable 条件时，可一次关闭有限个自由变量。
-/
theorem forall_close_of_derives {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {variables : List (σ.SortSymbol × FreeVarId)}
    {body : Formula σ} (hTheoryFresh :
      ∀ freeVar, freeVar ∈ variables →
        ∀ formula, T formula →
          freeVar freshForₘ formula) (hContextFresh :
      ∀ freeVar, freeVar ∈ variables →
        ∀ formula, formula ∈ Γ →
          freeVar freshForₘ formula) (hBody : Γ ⊢ₘ[T] body) :
    Γ ⊢ₘ[T] Formula.forall_close variables body := by
  induction variables with
  | nil =>
      simpa using hBody
  | cons freeVar variables ih =>
      rcases freeVar with ⟨sort, eigen⟩
      rw [Formula.forall_close_cons]
      apply FirstOrder.Derives.forall_intro
      · exact hTheoryFresh (sort, eigen) (by simp)
      · exact hContextFresh (sort, eigen) (by simp)
      · apply ih
        · intro freeVar hFreeVar
          exact hTheoryFresh freeVar (by simp [hFreeVar])
        · intro freeVar hFreeVar
          exact hContextFresh freeVar (by simp [hFreeVar])
/--
纯逻辑中的开放定理可以先作有限全称闭包，再弱化到任意理论与局部上下文。
-/
theorem forall_close_theorem {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {variables : List (σ.SortSymbol × FreeVarId)}
    {body : Formula σ} (hBody : ⊢ₘ body) :
    Γ ⊢ₘ[T] Formula.forall_close variables body := by
  apply FirstOrder.Derives.of_empty
  apply forall_close_of_derives
  · intro freeVar hFreeVar formula hFormula
    cases hFormula
  · intro freeVar hFreeVar formula hFormula
    cases hFormula
  · exact hBody
end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
