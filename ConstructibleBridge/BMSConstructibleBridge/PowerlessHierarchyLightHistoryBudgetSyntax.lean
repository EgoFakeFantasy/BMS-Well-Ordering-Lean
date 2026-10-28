import BMSConstructibleBridge.PowerlessHierarchyLightHistoryBudgetInduction
import BMSConstructibleBridge.PowerlessMemberDefDerives

/-! # 原轻量前史预算的纯隶属对象规格

完整保存预算证书的五个实际字段，特别是先前预算层对象属于同一
非零极限母层的要求。公式只描述实际图和层关系，不编码宿主选择
函数，不把预算输出在 Class 中改写为输出严格低于某个截断。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryBudgetSyntax

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def layers_m {Γ Δ : SortContext ℒ} (B D W Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let a : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let δ : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let C : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (value_m (up₃ Q) a δ) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m (up₃ B) δ C) <|
        .existsE .set <| .existsE .set <| .existsE .set <|
          let ξ : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there .here))
          let C₀ : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there .here)
          let C₁ : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
          .conj (PowerlessRelativeHierarchySyntax.limit_m ξ) <|
            .conj (PowerlessRelativeHierarchySyntax.level_m (up₃ (up₃ B)) ξ C₀) <|
              .conj (PowerlessMemberDefSyntax.global_m C₀ C₁) <|
                .conj (PowerlessMemberDefSyntax.global_m C₁ (up₃ C)) <|
                  .conj (member_m (up₃ (up₃ B)) C₀) <|
                    .conj (member_m (up₃ (up₃ D)) C₀) <|
                      .conj (member_m (up₃ (up₃ W)) C₀) <|
                        .conj (member_m (up₃ a) C₀) <|
                          .forallE .set <| .imp (member_m (.bvar .here) (up (up₃ a))) <|
                            .forallE .set <| .forallE .set <|
                              .imp (value_m (up₃ (up₃ (up₃ Q)))
                                (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
                                .imp (PowerlessRelativeHierarchySyntax.level_m
                                  (up₃ (up₃ (up₃ B))) (.bvar (.there .here)) (.bvar .here))
                                  (member_m (.bvar .here) (up₃ C₀))

theorem layers_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B D W Q : Term ℒ Γ Δ .set) :
    (layers_m B D W Q).satisfies η ↔ ∀ a δ C,
      SecondOrderFunctionObjects.value_l hℳ (Q.eval η) a δ →
        PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) δ C →
          ∃ ξ C₀ C₁, PowerlessRelativeHierarchySemantics.limit_l hℳ ξ ∧
            PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) ξ C₀ ∧
              SecondOrderMemberDef.spec_l hℳ C₀ C₁ ∧ SecondOrderMemberDef.spec_l hℳ C₁ C ∧
                mem_l hℳ (B.eval η) C₀ ∧ mem_l hℳ (D.eval η) C₀ ∧
                  mem_l hℳ (W.eval η) C₀ ∧ mem_l hℳ a C₀ ∧
                    ∀ b, mem_l hℳ b a → ∀ θ E,
                      SecondOrderFunctionObjects.value_l hℳ (Q.eval η) b θ →
                        PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval η) θ E →
                          mem_l hℳ E C₀ := by
  simp only [layers_m, Formula.satisfies, SecondOrderObjectSyntax.value_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.limit_formula_l, PowerlessMemberDefDerives.formula_l K,
    member_m, Arguments.eval, up₃, up, Term.eval_weakenBound, Term.eval,
    SecondOrderQuotient.structure_l]
  rfl

def budget_m {Γ Δ : SortContext ℒ} (B D W A Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.ordinal_m A) <|
    .conj (.forallE .set <| .forallE .set <|
      .imp (value_m (up (up Q)) (.bvar (.there .here)) (.bvar .here))
        (member_m (.bvar (.there .here)) (up (up A)))) <|
      .conj (.forallE .set <| .imp (member_m (.bvar .here) (up A)) <|
        .existsE .set <| value_m (up (up Q)) (.bvar (.there .here)) (.bvar .here)) <|
        .conj (.forallE .set <| .forallE .set <|
          .imp (value_m (up (up Q)) (.bvar (.there .here)) (.bvar .here))
            (PowerlessRelativeHierarchySyntax.ordinal_m (.bvar .here))) (layers_m B D W Q)

theorem budget_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B D W A Q : Term ℒ Γ Δ .set) :
    (budget_m B D W A Q).satisfies η ↔
      PowerlessHierarchyLightHistoryBudgetInduction.budget_l hℳ
        (B.eval η) (D.eval η) (W.eval η) (A.eval η) (Q.eval η) := by
  simp only [budget_m, Formula.satisfies, PowerlessRelativeHierarchySemantics.ordinal_formula_l,
    SecondOrderObjectSyntax.value_l, layers_formula_l K,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval,
    SecondOrderQuotient.structure_l]
  constructor
  · rintro ⟨hA, hSource, hTotal, hOutput, hLayers⟩
    exact ⟨hA, hSource, hTotal, hOutput, hLayers⟩
  · intro h
    exact ⟨h.domain_ordinal, h.source, h.total, h.output_ordinal, h.layers⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHierarchyLightHistoryBudgetSyntax
