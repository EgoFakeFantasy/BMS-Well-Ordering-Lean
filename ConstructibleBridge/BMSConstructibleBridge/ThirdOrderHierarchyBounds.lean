import BMSConstructibleBridge.ThirdOrderHierarchyLimit
import BMSConstructibleBridge.ThirdOrderCountableBounds

/-!
# Cκ 的内部可数子集有统一早级界

以单级纯公式为每个元素选择一个早级指标，得到真实 B→κ 函数。
内部可数取界给共同严格上界，嵌套性将全部元素收进同一个可数早级。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderHierarchyBounds

open Logic FirstOrder ThirdOrderSemantics ThirdOrderOmegaOne PowerlessHierarchyStage

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def level_m {Γ Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ κ x a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.member_m a κ) (.existsE .set (.conj
    (stage_m (w ω) (w e) (w T) (w t₁) (w t₂) (w t₃) (w a) (.bvar .here))
    (SecondOrderObjectSyntax.member_m (w x) (.bvar .here))))

theorem level_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ κ x a : Term ℒ Γ Δ .set) :
    (level_m ω e T t₁ t₂ t₃ κ x a).satisfies η ↔
      member_l ℳ (a.eval η) (κ.eval η) ∧ ∃ A,
        stage_l (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (a.eval η) A ∧
        member_l ℳ (x.eval η) A := by
  simp only [level_m, Formula.satisfies, stage_formula_l hℳ, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ ThirdOrderTheory.theory_m)
    {ω e T t₁ t₂ t₃ κ U B : carrier_l ℳ} (hω : omega_l ω) (hκ : first_l ω κ)
    (hU : stage_l ω e T t₁ t₂ t₃ κ U) (hB : countable_l ω B) (hBU : subset_l B U) :
    ∃ a A, member_l ℳ a κ ∧ stage_l ω e T t₁ t₂ t₃ a A ∧ subset_l B A ∧ countable_l ω A := by
  have h₀ := ThirdOrderTheory.core_l hℳ
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 7 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases T (Fin.cases t₁ (Fin.cases t₂ (Fin.cases t₃ (fun _ => κ)))))),
      free := fun _ => U }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    level_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
      (.fvar (.there .here)) (.fvar .here)
  have h : ∀ x a, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree a) ↔
      member_l ℳ a κ ∧ ∃ A, stage_l ω e T t₁ t₂ t₃ a A ∧ member_l ℳ x A := by
    intro x a
    exact level_formula_l h₀ _ _ _ _ _ _ _ _ _ _
  obtain ⟨f, D, hf, hF⟩ := ThirdOrderSelection.exists_l hℳ φ η B (fun x hx => by
    obtain ⟨a, A, ha, hA, hx⟩ := (ThirdOrderHierarchyLimit.union_l h₀ hω hκ hU x).mp (hBU x hx)
    exact ⟨a, (h x a).mpr ⟨ha, A, hA, hx⟩⟩)
  have hf₀ : map_l f B κ := PowerlessFunction.range_l h₀ hf (fun x a ha => ((h x a).mp (hF x a ha)).1)
  obtain ⟨a, ha, h₁⟩ := ThirdOrderCountableBounds.strict_l hℳ hω hκ hB hf₀
  obtain ⟨A, hA⟩ := PowerlessHierarchyStage.exists_l h₀ hω (PowerlessOrdinal.mem_l hκ.1 ha) e T t₁ t₂ t₃
  refine ⟨a, A, ha, hA, ?_, ThirdOrderHierarchyStage.countable_l hℳ hω hA (hκ.2.2 a ha)⟩
  intro x hx
  obtain ⟨b, hb, _⟩ := hf.2 x hx
  obtain ⟨_, C, hC, hx⟩ := (h x b).mp (hF x b hb.2)
  exact PowerlessStageStructure.subset_l h₀ hω hC hA (h₁ x b hb.2) x hx

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderHierarchyBounds
