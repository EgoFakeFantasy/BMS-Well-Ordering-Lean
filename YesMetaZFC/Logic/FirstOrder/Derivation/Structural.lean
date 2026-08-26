import YesMetaZFC.Logic.FirstOrder.Derivation.Core
/-!
# Derives 的结构规则接口
这些定理把底层证书构造子包装成证明脚本更常用的结构性入口。它们不改变核心
判断，只提供上下文弱化、交换、收缩、cut 和假设/理论成员的可读形式。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Derives
theorem assumption_of_mem {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ} (hMem : φ ∈ Γ)
    (hFormulaCheck : Formula.CheckCertificate φ := by
      prove_nd_formula_check) :
    Derives T Γ φ :=
  .assumption hMem (hCheck := hFormulaCheck)
theorem theory_mem {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ} (hMem : T φ)
    (hFormulaCheck : Formula.CheckCertificate φ := by
      prove_nd_formula_check) :
    Derives T Γ φ :=
  .theoryAxiom hMem (hCheck := hFormulaCheck)
theorem context_weaken {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ Δ : Context σ} {φ : Formula σ} (hSubset : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ) (hDerives : Derives T Γ φ) :
    Derives T Δ φ :=
  .contextWeakening hSubset hDerives
theorem context_weaken_cons {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ : Context σ} {assumption φ : Formula σ} (hDerives : Derives T Γ φ) :
    Derives T (assumption :: Γ) φ :=
  context_weaken (fun ψ hMem => by simp [hMem]) hDerives
theorem context_weaken_append {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ Δ : Context σ} {φ : Formula σ} (hDerives : Derives T Γ φ) :
    Derives T (Γ ++ Δ) φ :=
  context_weaken (fun ψ hMem => by simp [hMem]) hDerives
theorem theory_weaken {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T U : Theory σ} {Γ : Context σ} {φ : Formula σ} (hSubset : ∀ ψ, T ψ → U ψ) (hDerives : Derives T Γ φ) :
    Derives U Γ φ :=
  .theoryWeakening hSubset hDerives
/-- 同时扩大理论和局部上下文。 -/
theorem monotone {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T U : Theory σ} {Γ Δ : Context σ} {φ : Formula σ} (hTheory : ∀ ψ, T ψ → U ψ) (hContext : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ) (hDerives : Derives T Γ φ) :
    Derives U Δ φ := (hDerives.theory_weaken hTheory).context_weaken hContext
/-- 空理论、空上下文中的逻辑定理可用于任意理论和局部上下文。 -/
theorem of_empty {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ : Context σ} {φ : Formula σ} (hDerives : Derives (Theory.empty : Theory σ) [] φ) :
    Derives T Γ φ :=
  context_weaken (by simp) <|
    theory_weaken (by simp [Theory.empty]) hDerives
/-- 在上下文左侧加入任意有限前缀。 -/
theorem context_weaken_prefix {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {initial Γ : Context σ} {φ : Formula σ} (hDerives : Derives T Γ φ) :
    Derives T (initial ++ Γ) φ :=
  context_weaken (fun _ hMem => List.mem_append.mpr (Or.inr hMem))
    hDerives
theorem exchange {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ : Context σ} {left right φ : Formula σ} (hDerives : Derives T (left :: right :: Γ) φ) :
    Derives T (right :: left :: Γ) φ :=
  context_weaken (by
    intro ψ hMem
    rcases List.mem_cons.mp hMem with rfl | hMem
    · simp
    · rcases List.mem_cons.mp hMem with rfl | hMem
      · simp
      · simp [hMem]) hDerives
theorem contraction {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ : Context σ} {assumption φ : Formula σ} (hDerives : Derives T (assumption :: assumption :: Γ) φ) :
    Derives T (assumption :: Γ) φ :=
  context_weaken (by
    intro ψ hMem
    rcases List.mem_cons.mp hMem with rfl | hMem
    · simp
    · rcases List.mem_cons.mp hMem with rfl | hMem
      · simp
      · simp [hMem]) hDerives
theorem cut {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ : Context σ} {cutFormula conclusion : Formula σ} (hCut : Derives T Γ cutFormula) (hConclusion : Derives T (cutFormula :: Γ) conclusion) :
    Derives T Γ conclusion :=
  .impElim (.impIntro hConclusion) hCut
theorem deduction {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ : Context σ} {antecedent consequent : Formula σ}
    (hBody : Derives T (antecedent :: Γ) consequent)
    (hAntecedentCheck :
      Formula.CheckCertificate antecedent := by
        prove_nd_formula_check) :
    Derives T Γ (Formula.imp antecedent consequent) :=
  .impIntro hBody (hAntecedentCheck := hAntecedentCheck)
/-- 已证明的蕴含可以在把前件加入上下文后直接应用。 -/
theorem imp_elim_assumption {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ : Context σ} {antecedent consequent : Formula σ} (hImp : Derives T Γ (Formula.imp antecedent consequent)) :
    Derives T (antecedent :: Γ) consequent :=
  .impElim (context_weaken_cons hImp) (.assumption (by simp))
/-- 自然演绎核中的演绎定理双向形式。 -/
theorem deduction_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ : Context σ} {antecedent consequent : Formula σ}
    (hAntecedentCheck :
      Formula.CheckCertificate antecedent := by
        prove_nd_formula_check) :
    Derives T (antecedent :: Γ) consequent ↔
      Derives T Γ (Formula.imp antecedent consequent) :=
  ⟨deduction (hAntecedentCheck := hAntecedentCheck),
    imp_elim_assumption⟩
/-- 有限多个已证明前提可一次性从结论证明中消去。 -/
theorem multi_cut {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ premises : Context σ}
    {conclusion : Formula σ} (hPremises :
      ∀ formula, formula ∈ premises →
        Derives T Γ formula) (hConclusion :
      Derives T (premises ++ Γ) conclusion) :
    Derives T Γ conclusion := by
  induction premises generalizing Γ with
  | nil =>
      simpa using hConclusion
  | cons head tail ih =>
      have hHead : Derives T Γ head :=
        hPremises head (by simp)
      have hHeadInTail :
          Derives T (tail ++ Γ) head :=
        hHead.context_weaken (by
          intro candidate hCandidate
          simp [hCandidate])
      have hAfterHead :
          Derives T (tail ++ Γ) conclusion := by
        apply hHeadInTail.cut
        simpa [List.cons_append] using hConclusion
      apply ih
      · intro formula hFormula
        exact hPremises formula (by simp [hFormula])
      · exact hAfterHead
/-- 把一组前提证明接到带独立右上下文的结论证明前。 -/
theorem multi_cut_append {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {left right premises : Context σ}
    {conclusion : Formula σ} (hPremises :
      ∀ formula, formula ∈ premises →
        Derives T left formula) (hConclusion :
      Derives T (premises ++ right) conclusion) :
    Derives T (left ++ right) conclusion := by
  apply multi_cut (Γ := left ++ right) (premises := premises)
  · intro formula hFormula
    exact (hPremises formula hFormula).context_weaken_append
  · apply hConclusion.context_weaken
    intro formula hFormula
    rcases List.mem_append.mp hFormula with hFormula | hFormula
    · exact List.mem_append.mpr (Or.inl hFormula)
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hFormula)))
/-- 单个中间公式的左右上下文拼接。 -/
theorem cut_append {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {left right : Context σ}
    {middle conclusion : Formula σ} (hMiddle : Derives T left middle) (hConclusion :
      Derives T (middle :: right) conclusion) :
    Derives T (left ++ right) conclusion := by
  apply Derives.cut (cutFormula := middle) (Γ := left ++ right)
  · exact hMiddle.context_weaken_append
  · apply hConclusion.context_weaken
    intro formula hFormula
    rcases List.mem_cons.mp hFormula with rfl | hFormula
    · simp
    · simp [hFormula]
/-- 左理论中的证明可嵌入理论并。 -/
theorem theory_union_left {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Theory σ} {Γ : Context σ} {φ : Formula σ} (hDerives : Derives left Γ φ) :
    Derives (Theory.union left right) Γ φ :=
  hDerives.theory_weaken (fun _ h => Or.inl h)
/-- 右理论中的证明可嵌入理论并。 -/
theorem theory_union_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {left right : Theory σ} {Γ : Context σ} {φ : Formula σ} (hDerives : Derives right Γ φ) :
    Derives (Theory.union left right) Γ φ :=
  hDerives.theory_weaken (fun _ h => Or.inr h)
end Derives
end FirstOrder
end Logic
end YesMetaZFC
