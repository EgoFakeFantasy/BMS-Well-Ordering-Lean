import BMSConstructibleBridge.PowerlessHereditaryParameterEnvelope

/-! # 同一原参数种子的遗传资格

原 C/G 不更换：消费已有参数种子包中实际 Class 资格和对任意
共同母界的包含规格。有限原参数先有实际可数传递包络，再用单点
扩张把这个原 C 纳入包络。不要求原 C 作为参数进入其自身母界。

纯隶属 ℒ，背景原 Z₂，出口是原核 Derives。原参数及基底的遗传性
仍须实际给出；原种子包只提供 Class 资格，不能独自替代遗传证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOriginalParameterSeed

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

theorem member_l (K : source_coding_l hℳ) {Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (η : Env 𝒱 [] Ε)
    (B ω C G : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε)
    (hBase : ∀ x, ε x (B.eval η) → ∀ y, ε y x → ε y (B.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η))
    (hB : PowerlessHereditaryClass.member_l hℳ (B.eval η) (B.eval η))
    (hParams : ∀ s (v : Variable Δ s),
      PowerlessHereditaryClass.member_l hℳ (B.eval η) ((τ v).eval η))
    (hSeed : (PowerlessRelativeClassParameterSeedLift.packet_m Δ B ω C G τ).satisfies η) :
    PowerlessHereditaryClass.member_l hℳ (B.eval η) (C.eval η) := by
  obtain ⟨hC, _hG, _hMap, _hOnto, _hωC, _hBC, _hMembers, hBound⟩ :=
    (PowerlessRelativeClassParameterSeedLift.packet_formula_l K Δ η B ω C G τ).mp hSeed
  obtain ⟨D, F, hEnvelope, hωD, hParamsD⟩ :=
    PowerlessHereditaryParameterEnvelope.exists_l hBase hω hB Δ η τ hParams
  obtain ⟨hD, hF, hBD, hTrans, _hω, hMap, hOnto⟩ := hEnvelope
  have hCD : ∀ x, ε x (C.eval η) → ε x D :=
    hBound D hD (fun x hx => hTrans (ω.eval η) hωD x hx) hBD hParamsD
  have hωClass := PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
    (SecondOrderOmegaOrdinal.ordinal_l hℳ hω)
  let O : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨ω.eval η, hωClass⟩
  let X : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨C.eval η, hC⟩
  let T : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨D, hD⟩
  let J : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨F, hF⟩
  exact (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) X).mpr
    (PowerlessHereditaryExtension.exists_l O X T J
      ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) O).mpr hω)
      ((PowerlessHereditaryClassInternals.transitive_l (hBase := hBase) T).mpr hTrans)
      (fun x hx => hCD x.val hx)
      ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) J O T).mpr hMap)
      ((PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) J O T).mpr hOnto))

def schema_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω C G : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Formula ℒ [] Ε :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <|
      .imp (PowerlessHereditaryClass.formula_m B B) <|
        .imp (PowerlessHereditaryParameterEnvelope.parameters_m Δ B τ) <|
          .imp (PowerlessRelativeClassParameterSeedLift.packet_m Δ B ω C G τ)
            (PowerlessHereditaryClass.formula_m B C)

def sentence_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω C G : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Δ B ω C G τ)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Ε : SortContext ℒ}
    (Δ : SortContext ℒ) (B ω C G : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) :
    (sentence_m Δ B ω C G τ).TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hω hB hParams hSeed
  exact (PowerlessHereditaryClass.formula_l K η B C).mpr <|
    member_l K Δ η B ω C G τ
      ((PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩 η B).mp hBase)
      ((SecondOrderOmegaSyntax.omega_l h𝒩 η ω).mp hω)
      ((PowerlessHereditaryClass.formula_l K η B B).mp hB)
      ((PowerlessHereditaryParameterEnvelope.parameters_formula_l K Δ η B τ).mp hParams) hSeed

theorem derives_m {Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (B ω C G : Term ℒ [] Ε .set) (τ : VariableSubstitution ℒ Δ [] Ε) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Δ B ω C G τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 Δ B ω C G τ)

#print axioms member_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryOriginalParameterSeed
