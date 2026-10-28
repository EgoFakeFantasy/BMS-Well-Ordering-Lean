import BMSConstructibleBridge.PowerlessRelativeClassCanonicalMemberDefStep

/-! # 同一全局编码包下的唯一规范后继

完整 Sat 在步骤关系中只作存在见证。通过其全环境读值唯一性消去见证
差异，获得真正唯一的完整后继序，而非预选 Sat 后的条件唯一性。
编码包先于所有母集固定；没有抽取 Type 层的域到 Sat 或后继函数。
该实际模型接口仍需对象 AST、正式步骤模式及内部历史构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalOrderUniform

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessFormulaValidityReading (code_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def step_l (ω A P e t₁ t₂ t₃ Pair Valid D E : type_l hℳ B) : Prop :=
  ∃ R : type_l hℳ B, PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ Pair Valid R ∧
    PowerlessRelativeClassCanonicalOrderStep.step_l (hBase := hBase) ω A P R D E

theorem unique_l (K : source_coding_l hℳ) {ω A P e t₁ t₂ t₃ Pair Valid D E E' : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃)
    (hPairMap : map_l (ℳ := 𝒱) Pair.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid.val c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (h : step_l (hBase := hBase) ω A P e t₁ t₂ t₃ Pair Valid D E)
    (h' : step_l (hBase := hBase) ω A P e t₁ t₂ t₃ Pair Valid D E') : E = E' := by
  obtain ⟨R, hR, hStep⟩ := h
  obtain ⟨R', hR', hStep'⟩ := h'
  have hValues := PowerlessRelativeClassSatisfactionUnique.values_l K hω he hTags hPairMap hPair hV hValid hR hR'
  exact PowerlessRelativeClassCanonicalOrderStep.unique_l
    ((PowerlessRelativeClassCanonicalOrderStep.step_congr_l hValues).mp hStep) hStep'

theorem exists_unique_l (K : source_coding_l hℳ) {ω A P e t₁ t₂ t₃ Pair Valid D : type_l hℳ B}
    (hΩ : omega_l (ℳ := 𝒞) ω) (hP : wellOrder_l (ℳ := 𝒱) A.val P.val)
    (hω : ω.val = K.omega) (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hTags : PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃)
    (hPairMap : map_l (ℳ := 𝒱) Pair.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair.val)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid.val c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hSat : ∃ R, PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ Pair Valid R)
    (hTrans : ∀ x y, SecondOrderQuotient.mem_l hℳ x A.val → SecondOrderQuotient.mem_l hℳ y x →
      SecondOrderQuotient.mem_l hℳ y A.val)
    (hD : SecondOrderMemberDef.spec_l hℳ A.val D.val) :
    ∃! E : type_l hℳ B, step_l (hBase := hBase) ω A P e t₁ t₂ t₃ Pair Valid D E ∧
      wellOrder_l (ℳ := 𝒱) D.val E.val ∧
      (∀ x y, SecondOrderQuotient.mem_l hℳ x A.val → SecondOrderQuotient.mem_l hℳ y A.val →
        (value_l (ℳ := 𝒱) E.val x y ↔ value_l (ℳ := 𝒱) P.val x y)) ∧
      (∀ x y, SecondOrderQuotient.mem_l hℳ x A.val → value_l (ℳ := 𝒱) E.val y x →
        SecondOrderQuotient.mem_l hℳ y A.val) := by
  obtain ⟨R, hR⟩ := hSat
  obtain ⟨L, hCandidate⟩ := PowerlessRelativeClassCanonicalMemberDefStep.of_spec_l
    K hΩ hP hω he hTags hPairMap hPair hV hValid hR hD
  have hAD := SecondOrderMemberDefProperties.contains_l hℳ hD hTrans
  obtain ⟨E, hStep, hOrder, hOld, hInitial⟩ :=
    PowerlessRelativeClassCanonicalOrderStep.exists_l
      (hBase := hBase) (ω := ω) (A := A) (P := P) (R := R) (D := D) hP hAD ⟨L, hCandidate⟩
  exact ⟨E, ⟨⟨R, hR, hStep⟩, hOrder, hOld, hInitial⟩,
    fun T hT => unique_l K hω he hTags hPairMap hPair hV hValid hT.1 ⟨R, hR, hStep⟩⟩

/-- 同一包先于所有域固定，完整 Sat 总性仍在 Prop 内逐域给出。 -/
theorem coding_exists_l {ω : type_l hℳ B} (hΩ : omega_l (ℳ := 𝒞) ω) :
    ∃ K : source_coding_l hℳ, ∃ V : SecondOrderModel.set_l ℳ,
      SecondOrderTriangularFormulaSyntax.spec_l V ∧ ∃ e t₁ t₂ t₃ Pair Valid : type_l hℳ B,
        ω.val = K.omega ∧ e.val = code_l K (SecondOrderModel.zero_l ℳ) ∧
        PowerlessEvaluationTags.tags_l (ℳ := 𝒞) e t₁ t₂ t₃ ∧
        map_l (ℳ := 𝒱) Pair.val K.omega K.omega ∧ PowerlessBMSQuotientPairingBounds.spec_l K Pair.val ∧
        (∀ c N, value_l (ℳ := 𝒱) Valid.val c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N) ∧
        ∀ A : type_l hℳ B, ∃ R, PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒞) ω A e t₁ t₂ t₃ Pair Valid R := by
  obtain ⟨K, V, hV, e, t₁, t₂, t₃, Pair, _, Valid, hω, he, hPairMap, hPair, _, hValid, hDomains⟩ :=
    PowerlessRelativeClassSatisfaction.exists_l hΩ
  obtain ⟨_, _, _, hSystemω, _, _⟩ := hDomains ω
  refine ⟨K, V, hV, e, t₁, t₂, t₃, Pair, Valid, hω, he, hSystemω.1, hPairMap, hPair, hValid, ?_⟩
  intro A
  obtain ⟨Seq, G, R, hSystem, hSeq, hRead⟩ := hDomains A
  exact ⟨R, PowerlessRelativeClassSatisfactionSpecification.instance_l
    hRead K hω hSeq hValid hSystem he hPairMap hPair hV⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalOrderUniform
