import BMSConstructibleBridge.PowerlessHierarchyRestriction
import BMSConstructibleBridge.PowerlessHierarchyPresentation

/-!
# 不依赖所选图域的实际单级定义

在 α 的后继域上取唯一层次函数的 α 值。序数条件包含在纯定义内；
存在性由实际递归给出，跨域相容证明任意更长图读出的值都是同一级。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyStage

open Logic FirstOrder ThirdOrderSemantics PowerlessEvaluationHierarchy

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def stage_l (ω e T t₁ t₂ t₃ α A : carrier_l ℳ) : Prop :=
  PowerlessOrdinal.ordinal_l α ∧ ∃ β f, PowerlessNatural.successor_l α β ∧
    hierarchy_l ω e T t₁ t₂ t₃ f β ∧ value_l f α A

def stage_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ α A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (PowerlessOrdinal.ordinal_m α) (.existsE .set (.existsE .set (.conj
    (PowerlessNaturalStep.successor_m (w α) (.bvar (.there .here)))
    (.conj (PowerlessHierarchyPresentation.hierarchy_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃)
      (.bvar .here) (.bvar (.there .here)))
      (SecondOrderObjectSyntax.value_m (.bvar .here) (w α) (w A))))))

theorem stage_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ α A : Term ℒ Γ Δ .set) :
    (stage_m ω e T t₁ t₂ t₃ α A).satisfies η ↔
      stage_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (α.eval η) (A.eval η) := by
  simp only [stage_m, stage_l, Formula.satisfies, PowerlessOrdinal.ordinal_formula_l hℳ,
    PowerlessNaturalStep.successor_formula_l, PowerlessHierarchyPresentation.hierarchy_formula_l hℳ,
    value_formula_l, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω α : carrier_l ℳ} (hω : omega_l ω) (hα : PowerlessOrdinal.ordinal_l α)
    (e T t₁ t₂ t₃ : carrier_l ℳ) : ∃ A, stage_l ω e T t₁ t₂ t₃ α A := by
  obtain ⟨β, hβ⟩ := PowerlessNatural.successor_exists_l hℳ α
  obtain ⟨f, hf, _⟩ := PowerlessEvaluationHierarchy.exists_unique_l hℳ hω
    (PowerlessOrdinalOrder.successor_l hℳ hα hβ) e T t₁ t₂ t₃
  have hf₀ := hf
  obtain ⟨R, hF, _⟩ := hf₀
  obtain ⟨A, hA, _⟩ := hF.2 α ((hβ α).mpr (Or.inr rfl))
  exact ⟨A, hα, β, f, hβ, hf, hA.2⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A B : carrier_l ℳ} (hω : omega_l ω)
    (hA : stage_l ω e T t₁ t₂ t₃ α A) (hB : stage_l ω e T t₁ t₂ t₃ α B) : A = B := by
  obtain ⟨hα, β, f, hβ, hf, hA⟩ := hA
  obtain ⟨_, γ, g, hγ, hg, hB⟩ := hB
  have h := PowerlessNatural.successor_unique_l hℳ hβ hγ
  subst γ
  obtain ⟨q, _, h₀⟩ := PowerlessEvaluationHierarchy.exists_unique_l hℳ hω
    (PowerlessOrdinalOrder.successor_l hℳ hα hβ) e T t₁ t₂ t₃
  have h₁ := (h₀ f hf).trans (h₀ g hg).symm
  subst g
  obtain ⟨R, hF, _⟩ := hf
  exact PowerlessFunction.value_unique_l hℳ hF hA hB

theorem value_iff_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ f α a A : carrier_l ℳ} (hω : omega_l ω) (hα : PowerlessOrdinal.ordinal_l α)
    (hf : hierarchy_l ω e T t₁ t₂ t₃ f α) (ha : member_l ℳ a α) :
    value_l f a A ↔ stage_l ω e T t₁ t₂ t₃ a A := by
  have ha₀ := PowerlessOrdinal.mem_l hα ha
  constructor
  · intro hA
    obtain ⟨b, hb⟩ := PowerlessNatural.successor_exists_l hℳ a
    have hba : subset_l b α := by
      intro x hx
      rcases (hb x).mp hx with hx | hx
      · exact PowerlessOrdinal.transitive_l hα a x ha hx
      · exact hx.symm ▸ ha
    obtain ⟨g, hg, h⟩ := PowerlessHierarchyRestriction.exists_l hℳ hf
      (PowerlessOrdinalOrder.successor_l hℳ ha₀ hb) hba
    exact ⟨ha₀, b, g, hb, hg, (h a A).mpr ⟨(hb a).mpr (Or.inr rfl), hA⟩⟩
  · rintro ⟨_, b, g, hb, hg, hA⟩
    exact (PowerlessHierarchyRestriction.compatible_l hℳ hω hα
      (PowerlessOrdinalOrder.successor_l hℳ ha₀ hb) hf hg ha ((hb a).mpr (Or.inr rfl)) A).mpr hA

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyStage
