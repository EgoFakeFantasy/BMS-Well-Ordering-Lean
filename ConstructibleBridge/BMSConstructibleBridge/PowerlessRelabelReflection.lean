import BMSConstructibleBridge.PowerlessRelabelSource
import BMSConstructibleBridge.PowerlessReflectionLevel

/-!
# 同一实际重标号图的向下反射

先将上层共同函数图内化为原矩阵存在式，再反射整个存在式，最后解出下层的
一张实际函数图。顶端稳定条件随读取层由 β 变为 α；其余原关系和数码参数不变。
仍需由具体 BMS 表示提供上层见证及适当的外部层号重编号，不宣称良序终局。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelReflection

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure PowerlessRelabelMatrix

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

theorem transfer_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {α β A B S R F G : carrier_l ℳ}
    {hA₀ : ∃ x, member_l ℳ x A} {hB₀ : ∃ x, member_l ℳ x B}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : type_l A} (hω : omega_l ω.val)
    (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
    (hA : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α A S F)
    (hB : PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val β B R G)
    (k : Nat) (n : carrier_l ℳ) (hn : PowerlessNumeral.numeral_l e.val k n)
    (hs : PowerlessStageStability.stable_l ω.val e.val T.val t₁.val t₂.val t₃.val n α β)
    (h𝒜 : Theory.Models (structure_l A hA₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)))
    (hℬ : Theory.Models (structure_l B hB₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k)))
    {Δ : SortContext ℒ} (η : Env (structure_l A hA₀) [] Δ)
    (w z V s₁ s₂ s₃ c N q f D E : Term ℒ [] Δ .set)
    (Ψ : List (edge_m Δ)) (Θ : List (trace_m Δ))
    (hφ : PowerlessSourceStandardBudget.budget_m (formula_m w z V s₁ s₂ s₃ c N q f D E Ψ Θ) ≤ k)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val)
    (hV : (V.eval η).val = T.val) (hs₁ : (s₁.eval η).val = t₁.val)
    (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hN : member_l ℳ (N.eval η).val ω.val) (hq : member_l ℳ (q.eval η).val ω.val)
    (hΘ : ∀ p ∈ Θ, p.1 ≤ k ∧
      PowerlessNumeral.numeral_l e.val p.1 (p.2.1.eval η).val ∧
      subset_l (p.2.2.eval η).val (q.eval η).val) :
    (∃ g, map_l g (q.eval η).val B ∧
      PowerlessRelabelSource.conditions_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (c.eval η).val (N.eval η).val β (f.eval η).val g (D.eval η).val (E.eval η).val
        (Ψ.map (fun p => ((p.1.eval η).val, (p.2.1.eval η).val, (p.2.2.eval η).val)))
        (Θ.map (fun p => ((p.2.1.eval η).val, (p.2.2.eval η).val)))) ↔
    ∃ g, map_l g (q.eval η).val A ∧
      PowerlessRelabelSource.conditions_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (c.eval η).val (N.eval η).val α (f.eval η).val g (D.eval η).val (E.eval η).val
        (Ψ.map (fun p => ((p.1.eval η).val, (p.2.1.eval η).val, (p.2.2.eval η).val)))
        (Θ.map (fun p => ((p.2.1.eval η).val, (p.2.2.eval η).val))) := by
  obtain ⟨hωα, hαβ, hα, hβ⟩ := hs.2.1
  have hωβ := PowerlessOrdinal.transitive_l hβ.1 α ω.val hαβ hωα
  have hAB := PowerlessStageStructure.subset_l hℳ hω hA.1 hB.1 hαβ
  let ι : type_l A → type_l B := PowerlessSourceInclusion.inclusion_l hAB
  let ζ : Env (structure_l B hB₀) [] Δ := PowerlessSourceInclusion.env_l hAB η
  let φ : Formula ℒ [] Δ := formula_m w z V s₁ s₂ s₃ c N q f D E Ψ Θ
  obtain ⟨m, hm⟩ := PowerlessNumeral.exists_l hℳ e.val (PowerlessSourceStandardBudget.budget_m φ)
  have h₀ : PowerlessSourceFiniteReflection.reflects_l ω.val e.val T.val t₁.val t₂.val t₃.val m φ :=
    PowerlessSourceStandardBudget.reflect_budget_l hℳ hω ht hT φ m hm
  have h₁ : PowerlessSourceFiniteReflection.reflects_l ω.val e.val T.val t₁.val t₂.val t₃.val n φ :=
    PowerlessSourceFiniteReflection.monotone_l hℳ hω ht hT hs.1
      (PowerlessSourceStandardBudget.numeral_le_subset_l hℳ e.val hφ hm hn) h₀
  have h₂ := h₁ hA₀ hB₀ hB.2.2 hA.2.2 hB.2.1 hAB
    ((PowerlessStageStability.compare_l hℳ hω hA hB).mp hs).2.2 η
  have h₃ := PowerlessRelabelSource.realize_l hℳ hω ht hT hA hα hωα k h𝒜
    η w z V s₁ s₂ s₃ c N q f D E Ψ Θ hw hz hV hs₁ hs₂ hs₃ hN hq hΘ
  have h₄ := PowerlessRelabelSource.realize_l (ω := ι ω) (e := ι e) (T := ι T)
    (t₁ := ι t₁) (t₂ := ι t₂) (t₃ := ι t₃) hℳ hω ht hT hB hβ hωβ k hℬ
    ζ w z V s₁ s₂ s₃ c N q f D E Ψ Θ
    (by simpa only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] using hw)
    (by simpa only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] using hz)
    (by simpa only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] using hV)
    (by simpa only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] using hs₁)
    (by simpa only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] using hs₂)
    (by simpa only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] using hs₃)
    (by simpa only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] using hN)
    (by simpa only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] using hq)
    (by simpa only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] using hΘ)
  simp only [ζ, PowerlessSourceInclusion.term_l, ι, PowerlessSourceInclusion.inclusion_l] at h₄
  exact h₄.symm.trans (h₂.trans h₃)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelReflection
