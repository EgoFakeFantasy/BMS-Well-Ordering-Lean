import BMSConstructibleBridge.PowerlessRelativeLimitParameterBounds
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage

/-! # 极限阶段共尾条件下的严格先前共同界

共尾条件作为明确的纯公式守卫，不由普通极限性冒充。有限参数先取
严格较早的共同层，再用该守卫提升到非零极限层；这里只归纳外部上下文。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalLimitBounds

open Logic FirstOrder ThirdOrderSemantics SecondOrderObjectSyntax
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

def cofinal_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} (β : type_l hℳ) : Prop :=
  ∀ a, mem_l hℳ a β → ∃ γ, mem_l hℳ γ β ∧ mem_l hℳ a γ ∧ limit_l hℳ γ

def cofinal_m {Γ Δ : SortContext ℒ} (β : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (β.weakenBound SetTheory.SetSort.set)) <|
    .existsE .set <| .conj (member_m (.bvar .here) ((β.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)) <|
      .conj (member_m (.bvar (.there .here)) (.bvar .here))
        (PowerlessRelativeHierarchySyntax.limit_m (.bvar .here))

theorem cofinal_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (β : Term ℒ Γ Δ .set) :
    (cofinal_m β).satisfies η ↔ cofinal_l (β.eval η) := by
  simp only [cofinal_m, cofinal_l, Formula.satisfies, PowerlessRelativeHierarchySemantics.limit_formula_l,
    member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B β C X : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C) (hCofinal : cofinal_l β)
    {Δ : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (hX : mem_l hℳ X C) (hParams : ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) C) :
    ∃ γ D, mem_l hℳ γ β ∧ level_l hℳ B γ D ∧ limit_l hℳ γ ∧
      mem_l hℳ X D ∧ ∀ s (v : Variable Δ s), mem_l hℳ (η.freeVal v) D := by
  obtain ⟨a, c, ha, hc, hXc, hParamsC⟩ :=
    PowerlessRelativeLimitParameterBounds.exists_l hBase hLimit hC η hX hParams
  obtain ⟨γ, hγβ, haγ, hγLimit⟩ := hCofinal a ha
  have hγ : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) γ := by
    apply SetTheory.Structure.IsOrdinal.mem (PowerlessRelativeLevelClosure.ordinal_l hℳ hC)
    exact hγβ
  obtain ⟨D, hD⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hγ
  have hLift := PowerlessRelativeLevelClosure.subset_l hℳ hBase haγ hc hD
  exact ⟨γ, D, hγβ, hD, hγLimit, hLift X hXc, fun s v => hLift _ (hParamsC s v)⟩

#print axioms cofinal_formula_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCofinalLimitBounds
