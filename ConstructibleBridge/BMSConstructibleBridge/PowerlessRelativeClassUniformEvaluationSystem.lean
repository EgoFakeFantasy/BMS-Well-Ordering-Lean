import BMSConstructibleBridge.PowerlessRelativeClassEvaluationSystem

/-! # 先固定原编码、再量化全部求值域的系统存在句

空集、标签和同一三角图先于 A 固定。只断言每个域存在集合求值图，
不抽取域到图的类函数，也不假定任意内部码已经识别为良构公式。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassUniformEvaluationSystem

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def existence_m {Γ Δ : SortContext ℒ} (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w := up (up (up (up (up (up (up (up ω)))))))
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    .forallE .set <| .existsE .set <| .existsE .set <|
      PowerlessRelativeClassEvaluationSystem.spec_m w (.bvar (.there (.there .here)))
        (.bvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.bvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.bvar (.there (.there (.there (.there (.there .here))))))
        (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)) (.bvar .here)

theorem existence_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω : Term ℒ Γ Δ .set) :
    (existence_m ω).satisfies η ↔ ∃ e t₁ t₂ t₃ T, ∀ A, ∃ S G,
      PowerlessRelativeClassEvaluationSystem.spec_l (ω.eval η) A e t₁ t₂ t₃ T S G := by
  simp only [existence_m, Formula.satisfies, PowerlessRelativeClassEvaluationSystem.spec_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

def sentence_m : Sentence ℒ :=
  .forallE .set <| .imp (SecondOrderOmegaSyntax.omega_m (.bvar .here)) (existence_m (.bvar .here))

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, omega_formula_l, existence_formula_l, Term.eval]
  exact fun _ hω => PowerlessRelativeClassEvaluationSystem.uniform_exists_l hω

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ hℳ B hBase => models_l hℳ B hBase)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassUniformEvaluationSystem
