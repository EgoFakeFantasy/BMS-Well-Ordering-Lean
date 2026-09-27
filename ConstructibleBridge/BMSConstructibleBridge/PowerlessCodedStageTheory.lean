import BMSConstructibleBridge.PowerlessFiniteTheoryCode
import BMSConstructibleBridge.PowerlessStageEvaluation

/-!
# 以数码参数表达实际层满足有限理论

公式正文不展开有限理论；变化的有限理论只改变自然数参数 c,N。
数码的跨域正确性由原闭句合取的统一编译证明，不预设一个真值谓词。
小层内部对本公式的绝对性仍须通过有限层系统的绝对性单独证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageTheory

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def holds_l (ω e T t₁ t₂ t₃ c N α : carrier_l ℳ) : Prop :=
  ∃ A S F, PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F ∧
    ∃ f, map_l f N A ∧ PowerlessEvaluationClause.query_l F c f

def holds_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c N α : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (t : Term ℒ Γ Δ .set) :=
    (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
      SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.existsE .set (.existsE .set (.conj
    (PowerlessStageEvaluation.system_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q α)
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.map_m (.bvar .here) (q N) (.bvar (.there (.there (.there .here)))))
      (PowerlessEvaluationClause.query_m (.bvar (.there .here)) (q c) (.bvar .here)))))))

theorem holds_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ c N α : Term ℒ Γ Δ .set) :
    (holds_m ω e T t₁ t₂ t₃ c N α).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (c.eval η) (N.eval η) (α.eval η) := by
  simp only [holds_m, holds_l, Formula.satisfies, PowerlessStageEvaluation.system_formula_l hℳ,
    map_formula_l, PowerlessEvaluationClause.query_formula_l, Term.eval_weakenBound]
  exact exists_congr (fun A => exists_congr (fun S => exists_congr (fun F =>
    ⟨fun ⟨f, h, hf⟩ => ⟨h, f, hf⟩, fun ⟨h, f, hf⟩ => ⟨f, h, hf⟩⟩)))

theorem code_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T) (Ξ : List (Sentence ℒ)) :
    ∃ c N, member_l ℳ c ω ∧ member_l ℳ N ω ∧
      ∀ {α A S F}, ∀ hA₀ : ∃ x, member_l ℳ x A,
        PowerlessStageEvaluation.system_l ω e T t₁ t₂ t₃ α A S F →
        (holds_l ω e T t₁ t₂ t₃ c N α ↔
          Theory.Models (PowerlessMemberStructure.structure_l A hA₀) (Theory.ofList Ξ)) := by
  obtain ⟨c, N, hc, hN, h⟩ := PowerlessFiniteTheoryCode.exists_l hℳ hω ht hT Ξ
  refine ⟨c, N, hc, hN, ?_⟩
  intro α A S F hA₀ hA
  constructor
  · rintro ⟨B, R, G, hB, hf⟩
    obtain ⟨rfl, rfl, rfl⟩ := PowerlessStageEvaluation.unique_l hℳ hω hB hA
    exact (h hA₀ hA.2.2 hA.2.1).mpr hf
  · intro hΞ
    exact ⟨A, S, F, hA, (h hA₀ hA.2.2 hA.2.1).mp hΞ⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageTheory
