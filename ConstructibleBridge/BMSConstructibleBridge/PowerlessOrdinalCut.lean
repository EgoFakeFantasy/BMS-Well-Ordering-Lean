import BMSConstructibleBridge.PowerlessOrdinalBounded
import BMSConstructibleBridge.PowerlessSourceCoverage

/-!
# 域的序数截面及其在求值子集族中的实际成员性

截面是域中所有内部序数组成的指定集合。其定义使用原纯公式；
对传递域，原源有界序数判定及统一覆盖把该截面放进实际 D(A)。
空域单独使用已经证明的空域算子方程。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalCut

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def cut_l (α A : carrier_l ℳ) : Prop :=
  ∀ x, member_l ℳ x α ↔ member_l ℳ x A ∧ PowerlessOrdinal.ordinal_l x

def cut_m {Γ Δ : SortContext ℒ} (α A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff
    (SecondOrderObjectSyntax.member_m (.bvar .here) (α.weakenBound SetTheory.SetSort.set))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (A.weakenBound SetTheory.SetSort.set))
      (PowerlessOrdinal.ordinal_m (.bvar .here))))

theorem cut_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (α A : Term ℒ Γ Δ .set) :
    Formula.satisfies η (cut_m α A) ↔ cut_l (α.eval η) (A.eval η) := by
  simp only [cut_m, cut_l, Formula.satisfies, PowerlessOrdinal.ordinal_formula_l hℳ,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D)
    (hAT : PowerlessNaturalOrder.transitive_l A) (hα : cut_l α A) :
    ThirdOrderSemantics.member_l ℳ α D := by
  classical
  by_cases hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A
  · let φ : Formula ℒ [.set] [] := PowerlessOrdinalBounded.ordinal_m (.bvar .here)
    obtain ⟨B, hB, h⟩ := PowerlessSourceCoverage.operator_l hℳ hω ht hT hD (hA := hA) φ Env.empty
    have h₀ : B = α := by
      apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
      intro x
      constructor
      · intro hx
        obtain ⟨hx, h₁⟩ := (h x).mp hx
        exact (hα x).mpr ⟨hx, (PowerlessOrdinalBounded.member_l hℳ hAT
          (Env.empty.pushBound ⟨x, hx⟩) (.bvar .here)).mp h₁⟩
      · intro hx
        obtain ⟨hx, h₁⟩ := (hα x).mp hx
        exact (h x).mpr ⟨hx, (PowerlessOrdinalBounded.member_l hℳ hAT
          (Env.empty.pushBound ⟨x, hx⟩) (.bvar .here)).mpr h₁⟩
    exact h₀ ▸ hB
  · exact (PowerlessEvaluationOperator.empty_l hℳ hω hD
      (fun x hx => hA ⟨x, hx⟩) α).mpr (fun x hx => hA ⟨x, ((hα x).mp hx).1⟩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalCut
