import BMSConstructibleBridge.SecondOrderTriangularFormulaAgreement
import BMSConstructibleBridge.SecondOrderCanonicalLevel
import BMSConstructibleBridge.SecondOrderCanonicalIndexUnique

/-! # 同一内部编码下原规范层证书的跨图认同

配数图的干净映射规格给出对象相等；合法性图只认同完整读值，不能
忽略垃圾成员而声称图相等。原内部合法性强归纳确定读值，完整 Sat、
Uniform 后继与原规范历史保留同一组见证传输。没有增加编码唯一性公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalCodingAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem pair_unique_l (K : source_coding_l hℳ) {S T : type_l hℳ}
    (hSMap : map_l (ℳ := 𝒱) S K.omega K.omega)
    (hTMap : map_l (ℳ := 𝒱) T K.omega K.omega)
    (hS : PowerlessBMSQuotientPairingBounds.spec_l K S)
    (hT : PowerlessBMSQuotientPairingBounds.spec_l K T) : S = T := by
  have hTransfer {P Q : type_l hℳ} (hMap : map_l (ℳ := 𝒱) P K.omega K.omega)
      (hP : PowerlessBMSQuotientPairingBounds.spec_l K P)
      (hQ : PowerlessBMSQuotientPairingBounds.spec_l K Q) (a b : type_l hℳ)
      (hValue : value_l (ℳ := 𝒱) P a b) : value_l (ℳ := 𝒱) Q a b := by
    have hCoords := SecondOrderFunctionProperties.value_mem_l hℳ hMap hValue
    obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨a, hCoords.1⟩
    obtain ⟨j, hj⟩ := numberCode_surjective_l K ⟨b, hCoords.2⟩
    have ha : a = (numberCode_l K i).val := (congrArg Subtype.val hi).symm
    have hb : b = (numberCode_l K j).val := (congrArg Subtype.val hj).symm
    rw [ha, hb] at hValue ⊢
    exact (hQ i j).mpr ((hP i j).mp hValue)
  apply SecondOrderCanonicalIndexUnique.proper_unique_l (hℳ := hℳ)
  · intro p hp
    obtain ⟨a, b, _ha, _hb, hPair⟩ := hSMap.1 p hp
    exact ⟨a, b, hPair⟩
  · intro p hp
    obtain ⟨a, b, _ha, _hb, hPair⟩ := hTMap.1 p hp
    exact ⟨a, b, hPair⟩
  · exact fun a b => ⟨hTransfer hSMap hS hT a b, hTransfer hTMap hT hS a b⟩

theorem valid_values_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid s₁ s₂ s₃ Pair' Valid' : type_l hℳ}
    (h : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (h' : SecondOrderComparisonStageTotal.coding_l K s₁ s₂ s₃ Pair' Valid') :
    ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ value_l (ℳ := 𝒱) Valid' c N := by
  obtain ⟨V, hV, hRead⟩ := h.valid
  obtain ⟨W, hW, hRead'⟩ := h'.valid
  intro c N
  rw [hRead c N, hRead' c N]
  exact exists_congr fun n => exists_congr fun l =>
    and_congr Iff.rfl (and_congr Iff.rfl (SecondOrderTriangularFormulaAgreement.values_l hℳ hV hW n l))

theorem satisfaction_valid_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A e t₁ t₂ t₃ Pair Valid Valid' R : carrier_l 𝒩}
    (hValid : ∀ c N, value_l (ℳ := 𝒩) Valid c N ↔ value_l (ℳ := 𝒩) Valid' c N) :
    PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩) ω A e t₁ t₂ t₃ Pair Valid R ↔
      PowerlessSatisfactionSpecification.spec_l (𝒩 := 𝒩) ω A e t₁ t₂ t₃ Pair Valid' R := by
  simp only [PowerlessSatisfactionSpecification.spec_l, PowerlessSatisfactionSpecification.domain_l,
    PowerlessSatisfactionSpecification.equations_l, hValid]

theorem uniform_valid_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A P e t₁ t₂ t₃ Pair Valid Valid' D E : carrier_l 𝒩}
    (hValid : ∀ c N, value_l (ℳ := 𝒩) Valid c N ↔ value_l (ℳ := 𝒩) Valid' c N) :
    SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒩) ω A P e t₁ t₂ t₃ Pair Valid D E ↔
      SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒩) ω A P e t₁ t₂ t₃ Pair Valid' D E :=
  exists_congr fun _ => and_congr (satisfaction_valid_l hValid) Iff.rfl

theorem history_valid_l {ω e t₁ t₂ t₃ Pair Valid Valid' I J T G P₀ A : type_l hℳ}
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ value_l (ℳ := 𝒱) Valid' c N) :
    SecondOrderComparisonCanonicalSyntax.history_l ω e t₁ t₂ t₃ Pair Valid I J T G P₀ A ↔
      SecondOrderComparisonCanonicalSyntax.history_l ω e t₁ t₂ t₃ Pair Valid' I J T G P₀ A := by
  simp only [SecondOrderComparisonCanonicalSyntax.history_l, SecondOrderComparisonCanonicalSyntax.at_l,
    SecondOrderComparisonCanonicalSyntax.branch_l, SecondOrderComparisonCanonicalSyntax.successor_l,
    uniform_valid_l hValid]

theorem level_valid_l {ω e t₁ t₂ t₃ Pair Valid Valid' B P₀ a X P : type_l hℳ}
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ value_l (ℳ := 𝒱) Valid' c N) :
    SecondOrderCanonicalLevelSyntax.level_l ω e t₁ t₂ t₃ Pair Valid B P₀ a X P ↔
      SecondOrderCanonicalLevelSyntax.level_l ω e t₁ t₂ t₃ Pair Valid' B P₀ a X P := by
  have hTransfer {F F' : type_l hℳ}
      (hValues : ∀ c N, value_l (ℳ := 𝒱) F c N ↔ value_l (ℳ := 𝒱) F' c N)
      (hLevel : SecondOrderCanonicalLevelSyntax.level_l ω e t₁ t₂ t₃ Pair F B P₀ a X P) :
      SecondOrderCanonicalLevelSyntax.level_l ω e t₁ t₂ t₃ Pair F' B P₀ a X P := by
    obtain ⟨A, H, r, I, J, T, G, q, h, hRead⟩ := hLevel
    exact ⟨A, H, r, I, J, T, G, q,
      ⟨h.configuration, h.comparisonMap, (history_valid_l hValues).mp h.canonical, h.invariant⟩, hRead⟩
  exact ⟨hTransfer hValid, hTransfer (fun c N => (hValid c N).symm)⟩

theorem level_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid s₁ s₂ s₃ Pair' Valid' B P₀ a X P : type_l hℳ}
    (h : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (h' : SecondOrderComparisonStageTotal.coding_l K s₁ s₂ s₃ Pair' Valid') :
    SecondOrderCanonicalLevelSyntax.level_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid B P₀ a X P ↔
      SecondOrderCanonicalLevelSyntax.level_l K.omega (zero_l K) s₁ s₂ s₃ Pair' Valid' B P₀ a X P := by
  have h₁ : s₁ = t₁ := h'.one.trans h.one.symm
  have h₂ : s₂ = t₂ := h'.two.trans h.two.symm
  have h₃ : s₃ = t₃ := h'.three.trans h.three.symm
  have hPair : Pair' = Pair := pair_unique_l K h'.pairMap h.pairMap h'.pair h.pair
  subst s₁
  subst s₂
  subst s₃
  subst Pair'
  exact level_valid_l (valid_values_l K h h')

#print axioms pair_unique_l
#print axioms valid_values_l
#print axioms level_valid_l
#print axioms level_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalCodingAgreement
