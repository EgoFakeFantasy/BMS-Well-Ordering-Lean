import BMSConstructibleBridge.SecondOrderCanonicalOrderStep
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalOrderUniform

/-! # 隐去 Sat 后的完整规范步骤

原对象公式只存在量化完整 Sat 图，不预选其 Type 数据。唯一性处理任意
环境 Sat 及后继见证。固定编码包先于全部类内域给出，候选和良序仍在
完整模型解释；以下总性是对象模式所用模型接口，不是最终 BMS 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderUniform

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessFormulaValidityReading (code_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def step_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A P e t₁ t₂ t₃ Pair Valid D E : carrier_l ℳ₀) : Prop :=
  ∃ R, PowerlessSatisfactionSpecification.spec_l ω A e t₁ t₂ t₃ Pair Valid R ∧
    SecondOrderCanonicalOrderSyntax.step_l ω A P R D E

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def step_m {Γ Δ : SortContext ℒ} (ω A P e t₁ t₂ t₃ Pair Valid D E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <|
    .conj (PowerlessSatisfactionSpecification.spec_m
      (up ω) (up A) (up e) (up t₁) (up t₂) (up t₃) (up Pair) (up Valid) (.bvar .here))
      (SecondOrderCanonicalOrderSyntax.step_m (up ω) (up A) (up P) (.bvar .here) (up D) (up E))

theorem step_formula_l {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env ℳ₀ Γ Δ) (ω A P e t₁ t₂ t₃ Pair Valid D E : Term ℒ Γ Δ .set) :
    (step_m ω A P e t₁ t₂ t₃ Pair Valid D E).satisfies η ↔
      step_l (ω.eval η) (A.eval η) (P.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (Pair.eval η) (Valid.eval η) (D.eval η) (E.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, PowerlessSatisfactionSpecification.spec_formula_l,
    SecondOrderCanonicalOrderSyntax.step_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem unique_l (K : source_coding_l hℳ)
    {ω A P e t₁ t₂ t₃ Pair Valid D E E' : SecondOrderQuotient.type_l hℳ}
    (hω : ω = K.omega) (he : e = code_l K (SecondOrderModel.zero_l ℳ))
    (ht₁ : t₁ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 1))
    (ht₂ : t₂ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 2))
    (ht₃ : t₃ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 3))
    (hPairMap : map_l (ℳ := 𝒱) Pair K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (h : step_l (ℳ₀ := 𝒱) ω A P e t₁ t₂ t₃ Pair Valid D E)
    (h' : step_l (ℳ₀ := 𝒱) ω A P e t₁ t₂ t₃ Pair Valid D E') : E = E' := by
  obtain ⟨R, hR, hStep⟩ := h
  obtain ⟨R', hR', hStep'⟩ := h'
  rw [hω, he, ht₁, ht₂, ht₃] at hR hR'
  have hRead := PowerlessSatisfactionUnique.values_l K hPairMap hPair hV hValid hR hR'
  exact SecondOrderCanonicalOrderStep.unique_l
    ((SecondOrderCanonicalOrderStep.step_congr_l hRead).mp hStep) hStep'

theorem step_ambient_l (K : source_coding_l hℳ)
    {ω A P e t₁ t₂ t₃ Pair Valid D E : type_l hℳ B}
    (hω : ω.val = K.omega) (he : e.val = code_l K (SecondOrderModel.zero_l ℳ))
    (hPairMap : map_l (ℳ := 𝒱) Pair.val K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair.val)
    (h : PowerlessRelativeClassCanonicalOrderUniform.step_l (hBase := hBase) ω A P e t₁ t₂ t₃ Pair Valid D E) :
    step_l (ℳ₀ := 𝒱) ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E.val := by
  obtain ⟨R, hR, hStep⟩ := h
  have hΩ : omega_l (ℳ := 𝒞) ω :=
    (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mpr (hω.symm ▸ K.omega_spec)
  exact ⟨R.val, PowerlessRelativeClassSatisfactionAbsolute.spec_l K hω he hPairMap hPair hR,
    SecondOrderCanonicalOrderSyntax.step_ambient_l hΩ hStep⟩

/-- 量词顺序固定：同一六对象包先于所有域，后继唯一性允许任意环境候选。 -/
theorem class_total_l {ω : type_l hℳ B} (hΩ : omega_l (ℳ := 𝒞) ω) :
    ∃ e t₁ t₂ t₃ Pair Valid : type_l hℳ B,
      ∀ A P D : type_l hℳ B, wellOrder_l (ℳ := 𝒱) A.val P.val →
        (∀ x y, SecondOrderQuotient.mem_l hℳ x A.val → SecondOrderQuotient.mem_l hℳ y x →
          SecondOrderQuotient.mem_l hℳ y A.val) → SecondOrderMemberDef.spec_l hℳ A.val D.val →
        ∃ E : type_l hℳ B,
          step_l (ℳ₀ := 𝒱) ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E.val ∧
          wellOrder_l (ℳ := 𝒱) D.val E.val ∧
          ∀ E' : SecondOrderQuotient.type_l hℳ,
            step_l (ℳ₀ := 𝒱) ω.val A.val P.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val D.val E' →
            E' = E.val := by
  obtain ⟨K, V, hV, e, t₁, t₂, t₃, Pair, Valid, hω, he, hTags, hPairMap, hPair, hValid, hDomains⟩ :=
    PowerlessRelativeClassCanonicalOrderUniform.coding_exists_l hΩ
  obtain ⟨ht₁, ht₂, ht₃⟩ := PowerlessRelativeClassSyntaxReading.tags_l (hBase := hBase) K he hTags
  refine ⟨e, t₁, t₂, t₃, Pair, Valid, ?_⟩
  intro A P D hP hTrans hDef
  obtain ⟨E, ⟨hStep, hOrder, _, _⟩, _⟩ :=
    PowerlessRelativeClassCanonicalOrderUniform.exists_unique_l
      K hΩ hP hω he hTags hPairMap hPair hV hValid (hDomains A) hTrans hDef
  have hRaw := step_ambient_l K hω he hPairMap hPair hStep
  exact ⟨E, hRaw, hOrder, fun E' hE' => unique_l K hω he ht₁ ht₂ ht₃ hPairMap hPair hV hValid hE' hRaw⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalOrderUniform
