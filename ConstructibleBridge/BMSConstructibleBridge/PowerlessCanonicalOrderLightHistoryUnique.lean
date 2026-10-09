import BMSConstructibleBridge.PowerlessCanonicalOrderLightHistory
import BMSConstructibleBridge.PowerlessCanonicalOrderCandidateUnique
import BMSConstructibleBridge.PowerlessRelativeHierarchyAgreement
import BMSConstructibleBridge.PowerlessBMSQuotientRecursion

/-! # 有界规范序前史的模型内部唯一性

在同一实际 F/G 上比较两张前史；其序数定义域和母界可不同。
归纳性质复用实际纯隶属 point_m，调用原弱集合归纳，不用外部良基性。
后继证书唯一性不需要父序良序性或 Sat 正确性；有限函数覆盖由实际
极限层构造在应用端提供，不能误计为最终 BMS 句的新增前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistoryUnique

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)
open PowerlessCanonicalOrderLightHistory (step_holds_l holds_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

private theorem step_unique_l {C C' W ω F G P₀ g g' a E E' α β δ : type_l hℳ}
    (hF : map_l (ℳ := 𝒱) F δ W) (hG : map_l (ℳ := 𝒱) G W W)
    (hCoverage : ∀ A, mem_l hℳ A W → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C)
    (hCoverage' : ∀ A, mem_l hℳ A W → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C')
    (ha : Ordinal a) (hg : map_l (ℳ := 𝒱) g α C) (hg' : map_l (ℳ := 𝒱) g' β C')
    (hTotal : ∀ b, mem_l hℳ b a → ∃ Q, value_l (ℳ := 𝒱) g b Q)
    (hTotal' : ∀ b, mem_l hℳ b a → ∃ Q, value_l (ℳ := 𝒱) g' b Q)
    (hPast : ∀ b, mem_l hℳ b a → ∀ Q Q',
      value_l (ℳ := 𝒱) g b Q → value_l (ℳ := 𝒱) g' b Q' → Q = Q')
    (h : step_holds_l (𝒩 := 𝒱) C W ω F G P₀ g a E)
    (h' : step_holds_l (𝒩 := 𝒱) C' W ω F G P₀ g' a E') : E = E' := by
  rcases h with ⟨hEmpty, hZero⟩ | hSuccessor | ⟨hLimit, hUnion⟩
  · rcases h' with ⟨_, hZero'⟩ | hSuccessor' | ⟨hLimit', _⟩
    · exact hZero.trans hZero'.symm
    · obtain ⟨b, hb, _⟩ := hSuccessor'
      exact False.elim (hEmpty b hb)
    · obtain ⟨b, hb⟩ := hLimit'.1
      exact False.elim (hEmpty b hb)
  · obtain ⟨b, hb, A, hA, D, _hD, Sat, _hSat, Q, _hQ,
      hSucc, hAValue, hDValue, hSatValue, hQValue, hCandidate⟩ := hSuccessor
    rcases h' with ⟨hEmpty, _⟩ | hSuccessor' | ⟨hLimit', _⟩
    · exact False.elim (hEmpty b hb)
    · obtain ⟨b', _hb', A', _hA', D', _hD', Sat', _hSat', Q', _hQ',
        hSucc', hAValue', hDValue', hSatValue', hQValue', hCandidate'⟩ := hSuccessor'
      have hbEq := PowerlessRelativeHierarchyStep.successor_unique_l hℳ ha hSucc hSucc'
      subst b'
      have hAEq := SecondOrderFunctionProperties.value_unique_l hℳ hF hAValue hAValue'
      subst A'
      have hDEq := SecondOrderFunctionProperties.value_unique_l hℳ hF hDValue hDValue'
      subst D'
      have hSatEq := SecondOrderFunctionProperties.value_unique_l hℳ hG hSatValue hSatValue'
      subst Sat'
      have hQEq := hPast b hb Q Q' hQValue hQValue'
      subst Q'
      exact PowerlessCanonicalOrderCandidateUnique.unique_l
        (hCoverage A hA) (hCoverage' A hA) hCandidate hCandidate'
    · exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ ha hSucc hLimit')
  · rcases h' with ⟨hEmpty, _⟩ | hSuccessor' | ⟨_, hUnion'⟩
    · obtain ⟨b, hb⟩ := hLimit.1
      exact False.elim (hEmpty b hb)
    · obtain ⟨b, _hb, A, _hA, D, _hD, Sat, _hSat, Q, _hQ,
        hSucc, _⟩ := hSuccessor'
      exact False.elim (PowerlessRelativeHierarchyStep.successor_not_limit_l hℳ ha hSucc hLimit)
    · have hUnionRaw := (PowerlessHierarchyLightHistory.union_reading_l hℳ hg).mp hUnion
      have hUnionRaw' := (PowerlessHierarchyLightHistory.union_reading_l hℳ hg').mp hUnion'
      apply SecondOrderQuotient.ext_l hℳ E E'
      intro p
      constructor
      · intro hp
        obtain ⟨b, Q, hb, hQ, hpQ⟩ := (hUnionRaw p).mp hp
        obtain ⟨Q', hQ'⟩ := hTotal' b hb
        have hEq := hPast b hb Q Q' hQ hQ'
        exact (hUnionRaw' p).mpr ⟨b, Q', hb, hQ', hEq ▸ hpQ⟩
      · intro hp
        obtain ⟨b, Q', hb, hQ', hpQ⟩ := (hUnionRaw' p).mp hp
        obtain ⟨Q, hQ⟩ := hTotal b hb
        have hEq := hPast b hb Q Q' hQ hQ'
        exact (hUnionRaw p).mpr ⟨b, Q, hb, hQ, hEq.symm ▸ hpQ⟩

/-- 实际原纯公式归纳覆盖全部内部序数坐标，不仅覆盖标准阶段。 -/
theorem agreement_l {C C' W ω F G P₀ α β δ g g' : type_l hℳ}
    (hF : map_l (ℳ := 𝒱) F δ W) (hG : map_l (ℳ := 𝒱) G W W)
    (hCoverage : ∀ A, mem_l hℳ A W → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C)
    (hCoverage' : ∀ A, mem_l hℳ A W → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C')
    (hα : Ordinal α) (hβ : Ordinal β)
    (hg : holds_l (𝒩 := 𝒱) C W ω F G P₀ α g)
    (hg' : holds_l (𝒩 := 𝒱) C' W ω F G P₀ β g') :
    ∀ a, PowerlessRelativeHierarchyAgreement.point_l hℳ α β g g' a := by
  have hSteps := (PowerlessCanonicalOrderLightHistory.full_reading_l hℳ).mp hg
  have hSteps' := (PowerlessCanonicalOrderLightHistory.full_reading_l hℳ).mp hg'
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree g' |>.pushFree g |>.pushFree β |>.pushFree α
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ)
    PowerlessRelativeHierarchyAgreement.induction_m η (fun a ih =>
      (PowerlessRelativeHierarchyAgreement.induction_formula_l hℳ α β g g' a).mpr (by
        rintro ⟨haα, haβ⟩ E E' ⟨hE, hE'⟩
        have ha : Ordinal a := SetTheory.Structure.IsOrdinal.mem hα haα
        have hTotal b (hb : mem_l hℳ b a) : ∃ Q, value_l (ℳ := 𝒱) g b Q := by
          obtain ⟨Q, hQ, _⟩ := hg.1.2 b (hα.transitive a haα b hb)
          exact ⟨Q, hQ.2⟩
        have hTotal' b (hb : mem_l hℳ b a) : ∃ Q, value_l (ℳ := 𝒱) g' b Q := by
          obtain ⟨Q, hQ, _⟩ := hg'.1.2 b (hβ.transitive a haβ b hb)
          exact ⟨Q, hQ.2⟩
        have hPast b (hb : mem_l hℳ b a) Q Q'
            (hQ : value_l (ℳ := 𝒱) g b Q) (hQ' : value_l (ℳ := 𝒱) g' b Q') : Q = Q' :=
          (PowerlessRelativeHierarchyAgreement.induction_formula_l hℳ α β g g' b).mp
            (ih b hb) ⟨hα.transitive a haα b hb, hβ.transitive a haβ b hb⟩ Q Q' ⟨hQ, hQ'⟩
        exact step_unique_l hℳ hF hG hCoverage hCoverage' ha hg.1 hg'.1
          hTotal hTotal' hPast (hSteps.2 a E hE) (hSteps'.2 a E' hE')))
  intro a
  exact (PowerlessRelativeHierarchyAgreement.induction_formula_l hℳ α β g g' a).mp (hAll a)

theorem unique_l {C C' W ω F G P₀ α δ g g' : type_l hℳ}
    (hF : map_l (ℳ := 𝒱) F δ W) (hG : map_l (ℳ := 𝒱) G W W)
    (hCoverage : ∀ A, mem_l hℳ A W → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C)
    (hCoverage' : ∀ A, mem_l hℳ A W → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C')
    (hα : Ordinal α)
    (hg : holds_l (𝒩 := 𝒱) C W ω F G P₀ α g)
    (hg' : holds_l (𝒩 := 𝒱) C' W ω F G P₀ α g') : g = g' := by
  have hAgree := agreement_l hℳ hF hG hCoverage hCoverage' hα hα hg hg'
  apply PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ) hg.1 hg'.1
  intro a E
  constructor
  · intro hE
    have ha := (SecondOrderFunctionProperties.value_mem_l hℳ hg.1 hE).1
    obtain ⟨E', hE', _⟩ := hg'.1.2 a ha
    have hEq := hAgree a ⟨ha, ha⟩ E E' ⟨hE, hE'.2⟩
    exact hEq.symm ▸ hE'.2
  · intro hE'
    have ha := (SecondOrderFunctionProperties.value_mem_l hℳ hg'.1 hE').1
    obtain ⟨Q, hQ, _⟩ := hg.1.2 a ha
    have hEq := hAgree a ⟨ha, ha⟩ Q E ⟨hQ.2, hE'⟩
    exact hEq ▸ hQ.2

#print axioms agreement_l
#print axioms unique_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderLightHistoryUnique
