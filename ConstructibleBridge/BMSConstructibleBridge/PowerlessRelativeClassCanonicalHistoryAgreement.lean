import BMSConstructibleBridge.PowerlessRelativeClassCanonicalHistoryAmbient
import BMSConstructibleBridge.PowerlessRelativeHierarchyAgreement
import BMSConstructibleBridge.PowerlessBMSQuotientRecursion

/-! # 类内规范历史与同一原历史的内部相容性

原 Z₂ 纯公式集合归纳逐阶段认同两图。原参考历史的母序证书通过
前驱值相等恢复到类内历史，随后才读回原后继；不预供待验证图的
全局 raw 良序，不用外部序数良基性或 ω 标准性。函数图保持干净、
定义域相同后取得图对象相等，raw 陪域无需属于 Class。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "M" => type_l hℳ B
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

private theorem step_unique_l (K : source_coding_l hℳ)
    {ω e t₁ t₂ t₃ Pair Valid B₀ P₀ F g g' a X P P' δ r : Raw}
    (hω : ω = K.omega) (he : e = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hF : map_l (ℳ := 𝒱) F δ r) (ha : Ordinal a)
    (hTotal : ∀ b, mem_l hℳ b a → ∃ Q, value_l (ℳ := 𝒱) g b Q)
    (hTotal' : ∀ b, mem_l hℳ b a → ∃ Q, value_l (ℳ := 𝒱) g' b Q)
    (hPast : ∀ b, mem_l hℳ b a → ∀ Q Q', value_l (ℳ := 𝒱) g b Q →
      value_l (ℳ := 𝒱) g' b Q' → Q = Q')
    (h : PowerlessCanonicalOrderEquations.step_l (𝒩 := 𝒱) ω e t₁ t₂ t₃ Pair Valid B₀ P₀ F g a X P)
    (h' : PowerlessCanonicalOrderEquations.step_l (𝒩 := 𝒱) ω e t₁ t₂ t₃ Pair Valid B₀ P₀ F g' a X P') :
    P = P' := by
  rcases h with ⟨hEmpty, _, hZero⟩ | ⟨b, Y, Q, hSucc, hY, hQ, hStep⟩ | ⟨hLimit, _, hUnion⟩
  · rcases h' with ⟨_, _, hZero'⟩ | ⟨b, _, _, hSucc', _⟩ | ⟨hLimit', _⟩
    · exact hZero.trans hZero'.symm
    · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc'))
    · obtain ⟨b, hb⟩ := hLimit'.1
      exact False.elim (hEmpty b hb)
  · rcases h' with ⟨hEmpty, _⟩ | ⟨c, Z, Q', hSucc', hZ, hQ', hStep'⟩ | ⟨hLimit', _⟩
    · exact False.elim (hEmpty b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc))
    · have hbc := PowerlessRelativeHierarchyStep.successor_unique_l hℳ ha hSucc hSucc'
      subst c
      have hYZ := SecondOrderFunctionProperties.value_unique_l hℳ hF hY hZ
      subst Z
      have hQQ' := hPast b (PowerlessRelativeHierarchyStep.successor_member_l hℳ hSucc) Q Q' hQ hQ'
      subst Q'
      obtain ⟨ht₁, ht₂, ht₃, hPairMap, hPair, V, hV, hValid⟩ := hCoding
      exact SecondOrderCanonicalOrderUniform.unique_l K hω he ht₁ ht₂ ht₃ hPairMap hPair hV hValid hStep hStep'
    · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ ha hSucc hLimit')
  · rcases h' with ⟨hEmpty, _⟩ | ⟨b, _, _, hSucc', _⟩ | ⟨_, _, hUnion'⟩
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
    · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ ha hSucc' hLimit)
    · apply SecondOrderQuotient.ext_l hℳ P P'
      intro p
      constructor
      · intro hp
        obtain ⟨b, Q, hb, hQ, hpQ⟩ := (hUnion p).mp hp
        obtain ⟨Q', hQ'⟩ := hTotal' b hb
        have hEq := hPast b hb Q Q' hQ hQ'
        exact (hUnion' p).mpr ⟨b, Q', hb, hQ', hEq ▸ hpQ⟩
      · intro hp
        obtain ⟨b, Q', hb, hQ', hpQ⟩ := (hUnion' p).mp hp
        obtain ⟨Q, hQ⟩ := hTotal b hb
        have hEq := hPast b hb Q Q' hQ hQ'
        exact (hUnion p).mpr ⟨b, Q, hb, hQ, hEq.symm ▸ hpQ⟩

theorem agreement_l (K : source_coding_l hℳ)
    (ω e t₁ t₂ t₃ Pair N Valid B₀ P₀ F g : M) {δ r q q₀ g₀ : Raw}
    (hω : ω.val = K.omega)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ Pair N Valid)
    (hδ : Ordinal δ) (hF : map_l (ℳ := 𝒱) F.val δ r)
    (hg : map_l (ℳ := 𝒱) g.val δ q) (hg₀ : map_l (ℳ := 𝒱) g₀ δ q₀)
    (hEq : PowerlessCanonicalOrderEquations.holds_l (𝒩 := 𝒩₀)
      ω e t₁ t₂ t₃ Pair Valid B₀ P₀ F g)
    (hEq₀ : PowerlessCanonicalOrderEquations.holds_l (𝒩 := 𝒱)
      ω.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val B₀.val P₀.val F.val g₀)
    (hOrder₀ : ∀ a X P, value_l (ℳ := 𝒱) F.val a X → value_l (ℳ := 𝒱) g₀ a P →
      wellOrder_l (ℳ := 𝒱) X P) :
    ∀ a, PowerlessRelativeHierarchyAgreement.point_l hℳ δ δ g.val g₀ a := by
  obtain ⟨he, ht₁, ht₂, ht₃, _hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hω hStatic
  obtain ⟨V, hV, _⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  have hCoding : SecondOrderComparisonStageTotal.coding_l K t₁.val t₂.val t₃.val Pair.val Valid.val :=
    ⟨ht₁, ht₂, ht₃, hPairMap, hPair, V, hV, hValid V hV⟩
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree g₀ |>.pushFree g.val |>.pushFree δ |>.pushFree δ
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ)
    PowerlessRelativeHierarchyAgreement.induction_m η (fun a ih =>
      (PowerlessRelativeHierarchyAgreement.induction_formula_l hℳ δ δ g.val g₀ a).mpr (by
        rintro ⟨haδ, _⟩ P P' ⟨hP, hP'⟩
        have ha : Ordinal a := SetTheory.Structure.IsOrdinal.mem hδ haδ
        have hTotal b (hb : mem_l hℳ b a) : ∃ Q, value_l (ℳ := 𝒱) g.val b Q := by
          obtain ⟨Q, hQ, _⟩ := hg.2 b (hδ.transitive a haδ b hb)
          exact ⟨Q, hQ.2⟩
        have hTotal₀ b (hb : mem_l hℳ b a) : ∃ Q, value_l (ℳ := 𝒱) g₀ b Q := by
          obtain ⟨Q, hQ, _⟩ := hg₀.2 b (hδ.transitive a haδ b hb)
          exact ⟨Q, hQ.2⟩
        have hPast b (hb : mem_l hℳ b a) Q Q'
            (hQ : value_l (ℳ := 𝒱) g.val b Q) (hQ' : value_l (ℳ := 𝒱) g₀ b Q') : Q = Q' :=
          (PowerlessRelativeHierarchyAgreement.induction_formula_l hℳ δ δ g.val g₀ b).mp
            (ih b hb) ⟨hδ.transitive a haδ b hb, hδ.transitive a haδ b hb⟩ Q Q' ⟨hQ, hQ'⟩
        obtain ⟨X, hX, _⟩ := hF.2 a haδ
        have hFX := hX.2
        have hCoordinates := PowerlessRelativeClassValueCoordinates.value_l hBase F hFX
        let a₀ : M := ⟨a, hCoordinates.1⟩
        let X₀ : M := ⟨X, hCoordinates.2⟩
        let P₁ : M := ⟨P, (PowerlessRelativeClassValueCoordinates.value_l hBase g hP).2⟩
        have hStep := PowerlessRelativeClassCanonicalHistoryAmbient.step_l
          K ω e t₁ t₂ t₃ Pair N Valid B₀ P₀ F g a₀ X₀ P₁ hω hStatic
          (fun b hb Y Q hY hQ => by
            obtain ⟨Q', hQ'⟩ := hTotal₀ b hb
            have hEqQ := hPast b hb Q Q' hQ hQ'
            exact hEqQ.symm ▸ hOrder₀ b Y Q' hY hQ')
          (hEq a₀ X₀ P₁
            ((PowerlessRelativeClassFunctionAbsolute.value_l F a₀ X₀).mpr hFX)
            ((PowerlessRelativeClassFunctionAbsolute.value_l g a₀ P₁).mpr hP))
        exact step_unique_l K hω he hCoding hF ha hTotal hTotal₀ hPast hStep (hEq₀ a X P' hFX hP')))
  intro a
  exact (PowerlessRelativeHierarchyAgreement.induction_formula_l hℳ δ δ g.val g₀ a).mp (hAll a)

theorem unique_l (K : source_coding_l hℳ)
    (ω e t₁ t₂ t₃ Pair N Valid B₀ P₀ F g : M) {δ r q q₀ g₀ : Raw}
    (hω : ω.val = K.omega)
    (hStatic : PowerlessSatisfactionExistenceSyntax.static_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ Pair N Valid)
    (hδ : Ordinal δ) (hF : map_l (ℳ := 𝒱) F.val δ r)
    (hg : map_l (ℳ := 𝒱) g.val δ q) (hg₀ : map_l (ℳ := 𝒱) g₀ δ q₀)
    (hEq : PowerlessCanonicalOrderEquations.holds_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ Pair Valid B₀ P₀ F g)
    (hEq₀ : PowerlessCanonicalOrderEquations.holds_l (𝒩 := 𝒱)
      ω.val e.val t₁.val t₂.val t₃.val Pair.val Valid.val B₀.val P₀.val F.val g₀)
    (hOrder₀ : ∀ a X P, value_l (ℳ := 𝒱) F.val a X → value_l (ℳ := 𝒱) g₀ a P →
      wellOrder_l (ℳ := 𝒱) X P) : g.val = g₀ := by
  have hAgree := agreement_l K ω e t₁ t₂ t₃ Pair N Valid B₀ P₀ F g hω hStatic hδ hF hg hg₀ hEq hEq₀ hOrder₀
  apply PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ) hg hg₀
  intro a P
  constructor
  · intro hP
    have ha := (SecondOrderFunctionProperties.value_mem_l hℳ hg hP).1
    obtain ⟨Q, hQ, _⟩ := hg₀.2 a ha
    have hSame := hAgree a ⟨ha, ha⟩ P Q ⟨hP, hQ.2⟩
    exact hSame.symm ▸ hQ.2
  · intro hP
    have ha := (SecondOrderFunctionProperties.value_mem_l hℳ hg₀ hP).1
    obtain ⟨Q, hQ, _⟩ := hg.2 a ha
    have hSame := hAgree a ⟨ha, ha⟩ Q P ⟨hQ.2, hP⟩
    exact hSame ▸ hQ.2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalHistoryAgreement
