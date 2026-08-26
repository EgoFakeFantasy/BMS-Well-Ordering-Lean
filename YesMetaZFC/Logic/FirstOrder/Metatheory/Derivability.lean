import YesMetaZFC.Logic.FirstOrder.Derivation.Structural
/-!
# 可演绎关系与有限证明拼接
本模块在可信 `Derives` 核之上给出组合接口：理论和上下文的联合单调性、有限
multi-cut、带左右上下文的证明拼接，以及理论并的两侧嵌入。证明只组合已有证书，
不引入新的逻辑规则。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
universe u v w
namespace Derives
/-- 可演绎关系同时对理论包含和局部上下文包含单调。 -/
theorem mono_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T U : Theory σ}
    {Γ Δ : Context σ} {formula : Formula σ} (hTheory : ∀ ψ, T ψ → U ψ) (hContext : ∀ ψ, ψ ∈ Γ → ψ ∈ Δ) (hDerives : FirstOrder.Derives T Γ formula) :
    FirstOrder.Derives U Δ formula :=
  FirstOrder.Derives.context_weaken hContext <|
    FirstOrder.Derives.theory_weaken hTheory hDerives
/--
有限多个已证明前提可以一次性从结论证明中消去；这是单公式 cut 的有限列表版本。
-/
theorem cut_many_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ premises : Context σ} {conclusion : Formula σ} (hPremises :
      ∀ formula, formula ∈ premises →
        FirstOrder.Derives T Γ formula) (hConclusion :
      FirstOrder.Derives T (premises ++ Γ) conclusion) :
    FirstOrder.Derives T Γ conclusion := by
  induction premises generalizing Γ with
  | nil =>
      simpa using hConclusion
  | cons head tail ih =>
      have hHead : FirstOrder.Derives T Γ head :=
        hPremises head (by simp)
      have hHeadInTail :
          FirstOrder.Derives T (tail ++ Γ) head := by
        apply FirstOrder.Derives.context_weaken (Γ := Γ) (Δ := tail ++ Γ)
        · intro formula hFormula
          simp [hFormula]
        · exact hHead
      have hAfterHead :
          FirstOrder.Derives T (tail ++ Γ) conclusion := by
        apply FirstOrder.Derives.cut hHeadInTail
        simpa [List.cons_append] using hConclusion
      apply ih
      · intro formula hFormula
        exact hPremises formula (by simp [hFormula])
      · exact hAfterHead
/--
把 `Γ` 中的一组前提证明接到以 `premises ++ Δ` 为上下文的结论证明前，得到
`Γ ++ Δ` 中的结论证明。
-/
theorem cut_many_append_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ Δ premises : Context σ} {conclusion : Formula σ} (hPremises :
      ∀ formula, formula ∈ premises →
        FirstOrder.Derives T Γ formula) (hConclusion :
      FirstOrder.Derives T (premises ++ Δ) conclusion) :
    FirstOrder.Derives T (Γ ++ Δ) conclusion := by
  apply cut_many_m (Γ := Γ ++ Δ) (premises := premises)
  · intro formula hFormula
    exact FirstOrder.Derives.context_weaken_append (hPremises formula hFormula)
  · apply FirstOrder.Derives.context_weaken (Γ := premises ++ Δ) (Δ := premises ++ (Γ ++ Δ))
    · intro formula hFormula
      rcases List.mem_append.mp hFormula with hFormula | hFormula
      · exact List.mem_append.mpr (Or.inl hFormula)
      · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hFormula)))
    · exact hConclusion
/-- 单个中间公式的左右上下文证明拼接。 -/
theorem cut_append_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ Δ : Context σ} {middle conclusion : Formula σ} (hMiddle : FirstOrder.Derives T Γ middle) (hConclusion : FirstOrder.Derives T (middle :: Δ) conclusion) :
    FirstOrder.Derives T (Γ ++ Δ) conclusion := by
  apply FirstOrder.Derives.cut (cutFormula := middle) (Γ := Γ ++ Δ)
  · exact FirstOrder.Derives.context_weaken_append hMiddle
  · apply FirstOrder.Derives.context_weaken (Γ := middle :: Δ) (Δ := middle :: (Γ ++ Δ))
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · simp
      · simp [hFormula]
    · exact hConclusion
/-- 固定上下文中的可演绎关系由 cut 给出传递合成。 -/
theorem cut_trans_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {Γ : Context σ} {middle conclusion : Formula σ} (hMiddle : FirstOrder.Derives T Γ middle) (hConclusion : FirstOrder.Derives T (middle :: Γ) conclusion) :
    FirstOrder.Derives T Γ conclusion :=
  FirstOrder.Derives.cut hMiddle hConclusion
/-- 左理论中的证明可嵌入理论并。 -/
theorem union_left_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T U : Theory σ}
    {Γ : Context σ} {formula : Formula σ} (hDerives : FirstOrder.Derives T Γ formula) :
    FirstOrder.Derives (Theory.union T U) Γ formula :=
  FirstOrder.Derives.theory_weaken (fun _ h => Or.inl h) hDerives
/-- 右理论中的证明可嵌入理论并。 -/
theorem union_right_m {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T U : Theory σ}
    {Γ : Context σ} {formula : Formula σ} (hDerives : FirstOrder.Derives U Γ formula) :
    FirstOrder.Derives (Theory.union T U) Γ formula :=
  FirstOrder.Derives.theory_weaken (fun _ h => Or.inr h) hDerives
end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
