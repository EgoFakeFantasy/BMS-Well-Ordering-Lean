import BMSConstructibleBridge.PowerlessOrdinalCut
import BMSConstructibleBridge.PowerlessStageStructure

/-!
# 实际 C 层的序数截面恰为其指标

以原纯公式沿模型内部序数归纳。上界使用每个输出子集来自更早层；
下界把更早层的序数截面作为其实际可定义子集。没有使用外部良基，
也没有预设 C 等于经典 L。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageOrdinal

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
  (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)

include hℳ hω ht hT

theorem cut_l {f α : carrier_l ℳ} (hα : PowerlessOrdinal.ordinal_l α)
    (hf : PowerlessEvaluationHierarchy.hierarchy_l ω e T t₁ t₂ t₃ f α) :
    ∀ a A, value_l f a A → PowerlessOrdinalCut.cut_l a A := by
  have hf₀ := hf
  obtain ⟨R, hF, _⟩ := hf₀
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => f, free := fun _ => α }
  let φ : Formula ℒ [] [.set, .set] :=
    .forallE .set (.imp
      (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
      (PowerlessOrdinalCut.cut_m (.fvar .here) (.bvar .here)))
  have h : ∀ a, φ.satisfies ((PowerlessComprehension.env_l η).pushFree a) ↔
      ∀ A, value_l f a A → PowerlessOrdinalCut.cut_l a A := by
    intro a
    simp only [φ, Formula.satisfies, value_formula_l, PowerlessOrdinalCut.cut_formula_l hℳ]
    rfl
  have h₀ := PowerlessOrdinalInduction.induction_l hℳ φ η hα (fun a ha h₁ => by
    apply (h a).mpr
    intro A hA x
    constructor
    · intro hx
      obtain ⟨B, hB, _⟩ := hF.2 x (PowerlessOrdinal.transitive_l hα a x ha hx)
      obtain ⟨D, hD⟩ := PowerlessEvaluationOperator.exists_l hℳ hω e T t₁ t₂ t₃ B
      have h₂ := PowerlessOrdinalCut.member_l hℳ hω ht hT hD
        (PowerlessHierarchyStructure.transitive_l hℳ hω ht hT hα hf x B hB.2)
        ((h x).mp (h₁ x hx) B hB.2)
      exact ⟨(PowerlessEvaluationHierarchy.equation_l hℳ hf hA x).mpr
        ⟨x, B, D, hx, hB.2, hD, h₂⟩,
        PowerlessOrdinal.mem_l (PowerlessOrdinal.mem_l hα ha) hx⟩
    · rintro ⟨hx, hO⟩
      obtain ⟨b, B, D, hb, hB, hD, hx⟩ :=
        (PowerlessEvaluationHierarchy.equation_l hℳ hf hA x).mp hx
      have hb₀ := PowerlessOrdinal.mem_l (PowerlessOrdinal.mem_l hα ha) hb
      have h₂ : subset_l x b := fun y hy =>
        ((h b).mp (h₁ b hb) B hB y).mpr
          ⟨PowerlessEvaluationOperator.subset_l hD hx y hy, PowerlessOrdinal.mem_l hO hy⟩
      rcases PowerlessOrdinalOrder.trichotomy_l hℳ hO hb₀ with h₃ | h₃ | h₃
      · exact PowerlessOrdinal.transitive_l (PowerlessOrdinal.mem_l hα ha) b x hb h₃
      · exact h₃.symm ▸ hb
      · exact (PowerlessNatural.asymmetry_l hℳ (h₂ b h₃) (h₂ b h₃)).elim)
  exact fun a A hA => (h a).mp (h₀ a (PowerlessFunction.value_mem_l hℳ hF hA).1) A hA

theorem stage_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A) :
    PowerlessOrdinalCut.cut_l α A := by
  obtain ⟨hα, β, f, hβ, hf, hA⟩ := hA
  exact cut_l hℳ hω ht hT (PowerlessOrdinalOrder.successor_l hℳ hα hβ) hf α A hA

theorem subset_l {α A : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A) :
    ThirdOrderSemantics.subset_l α A :=
  fun x hx => ((stage_l hℳ hω ht hT hA x).mp hx).1

theorem member_l {α A x : carrier_l ℳ} (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hx : PowerlessOrdinal.ordinal_l x) :
    ThirdOrderSemantics.member_l ℳ x A ↔ ThirdOrderSemantics.member_l ℳ x α :=
  ⟨fun h => (stage_l hℳ hω ht hT hA x).mpr ⟨h, hx⟩,
    fun h => ((stage_l hℳ hω ht hT hA x).mp h).1⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageOrdinal
