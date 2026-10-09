import BMSConstructibleBridge.PowerlessHereditaryOriginalParameterSeed
import BMSConstructibleBridge.PowerlessHereditaryProgramAlphabet
import BMSConstructibleBridge.PowerlessHereditaryProgramDomain

/-! # 原参数种子到同一原数码枚举图的遗传接线

纯隶属 ℒ，背景原 Z₂。只对指定的原参数 τ 要求遗传证书；
装配环境中的 C/G/Q/S/P/U 不回填进原参数列表。消费原种子包、
原字母表、原完整码域以及同一个 Class 枚举 U，得到整组实际
遗传资格。没有假设 U 遗传，没有更换任何原图。

公开出口为原推导核 Derives。这给后取分离包络提供真实输入，
不替代原算子读数、凝聚图资格或最终固定高度 BMS 良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOriginalProgram

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

def qualifications_m {Γ Ε : SortContext ℒ} (B C Q S P U : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .conj (PowerlessHereditaryClass.formula_m B C) <|
    .conj (PowerlessHereditaryClass.formula_m B Q) <|
      .conj (PowerlessHereditaryClass.formula_m B S) <|
        .conj (PowerlessHereditaryClass.formula_m B P) (PowerlessHereditaryClass.formula_m B U)

def schema_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω C G t₀ t₁ t₂ Q S P U : Term ℒ [] Ε .set)
    (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B B) <|
        .imp (PowerlessHereditaryParameterEnvelope.parameters_m Δ B τ) <|
          .imp (PowerlessHereditaryClass.formula_m B t₀) <|
            .imp (PowerlessHereditaryClass.formula_m B t₁) <|
              .imp (PowerlessHereditaryClass.formula_m B t₂) <|
                .imp (PowerlessRelativeClassParameterSeedLift.packet_m Δ B ω C G τ) <|
                  .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
                    .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                      .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                        .imp (PowerlessRelativeHierarchySyntax.class_m B U) <|
                          .imp (SecondOrderObjectSyntax.map_m U ω P) (qualifications_m B C Q S P U)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (B ω C G t₀ t₁ t₂ Q S P U : Term ℒ [] Ε .set)
    (τ : VariableSubstitution ℒ Δ [] Ε) :
    (Metatheory.Formula.forall_close (schema_m Δ B ω C G t₀ t₁ t₂ Q S P U τ)).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hω hB hParams h₀ h₁ h₂ hSeed hQ hAlphabet hDomain hU hMap
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩 η B).mp hBase
  have hω' := (SecondOrderOmegaSyntax.omega_l h𝒩 η ω).mp hω
  have hB' := (PowerlessHereditaryClass.formula_l K η B B).mp hB
  have hC := PowerlessHereditaryOriginalParameterSeed.member_l K Δ η B ω C G τ hBase' hω' hB'
    ((PowerlessHereditaryParameterEnvelope.parameters_formula_l K Δ η B τ).mp hParams) hSeed
  have hQ' := PowerlessHereditaryProgramAlphabet.member_l hBase' hω' hB' hC
    ((PowerlessHereditaryClass.formula_l K η B t₀).mp h₀)
    ((PowerlessHereditaryClass.formula_l K η B t₁).mp h₁)
    ((PowerlessHereditaryClass.formula_l K η B t₂).mp h₂)
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B Q).mp hQ)
    ((PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l η C ω t₀ t₁ t₂ Q).mp hAlphabet)
  obtain ⟨hS, hP⟩ := PowerlessHereditaryProgramDomain.member_l (hBase := hBase') hω' hQ'
    ((PowerlessRelativeFiniteProgramDomain.domain_formula_l K η B ω Q S P).mp hDomain)
  have hU' := PowerlessHereditaryProgramDomain.enumeration_l (hBase := hBase') hω' hP
    ((PowerlessRelativeHierarchySemantics.class_formula_l K η B U).mp hU)
    ((map_formula_l η U ω P).mp hMap)
  simp only [qualifications_m, Formula.satisfies, PowerlessHereditaryClass.formula_l K]
  exact ⟨hC, hQ', hS, hP, hU'⟩

theorem derives_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω C G t₀ t₁ t₂ Q S P U : Term ℒ [] Ε .set)
    (τ : VariableSubstitution ℒ Δ [] Ε) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (Metatheory.Formula.forall_close (schema_m Δ B ω C G t₀ t₁ t₂ Q S P U τ))) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 Δ B ω C G t₀ t₁ t₂ Q S P U τ)

#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOriginalProgram
