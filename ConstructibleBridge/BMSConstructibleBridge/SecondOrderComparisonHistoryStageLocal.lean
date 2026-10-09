import BMSConstructibleBridge.SecondOrderComparisonHistoryStage
import BMSConstructibleBridge.SecondOrderStageIndexPredecessors

/-! # 原前驱实数行一致保持实际历史阶段输出

读取任意解码图的值，逐前驱传输实际切片与比较解码规格，再消费已验证的
三分支局部性。新旧历史和各自代表可不同，不比较未来行或选择规范历史图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryStageLocal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonHistoryStage (output_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

theorem decoded_read_l (K : source_coding_l hℳ)
    (E : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (H : SecondOrderModel.set_l ℳ)
    (hE : setRel_l K E H) {C f q G : type_l hℳ}
    (hG : SecondOrderComparisonHistoryDerives.history_l (𝒩 := 𝒱) K.omega (zero_l K) E.val f C q G)
    (i : SecondOrderModel.num_l ℳ) (P : type_l hℳ) :
    value_l (ℳ := 𝒱) G (numberCode_l K i).val P ↔ ∃ X,
      SecondOrderSections.spec_l H i X ∧ SecondOrderComparisonDecode.graph_l K C f X P := by
  have hRead : SecondOrderComparisonHistoryDerives.output_l (𝒩 := 𝒱)
      K.omega (zero_l K) E.val f C (numberCode_l K i).val P ↔ ∃ X,
        SecondOrderSections.spec_l H i X ∧ SecondOrderComparisonDecode.graph_l K C f X P :=
    SecondOrderComparisonHistoryDecode.formula_l K E H hE C f i P
  refine (hG.2.1 _ P).trans ⟨fun h => hRead.mp h.2, fun h => ?_⟩
  exact ⟨(numberCode_l K i).property, hRead.mpr h⟩

private theorem forward_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid I A J T P₀ f C W : type_l hℳ}
    (hJ : map_l (ℳ := 𝒱) J I A) (hI : subset_l (ℳ := 𝒱) I K.omega)
    (R H H' : SecondOrderModel.set_l ℳ)
    (hR : ∀ i j, SecondOrderPairing.relation_l R i j ↔ ∃ a b,
      value_l (ℳ := 𝒱) J (numberCode_l K i).val a ∧
      value_l (ℳ := 𝒱) J (numberCode_l K j).val b ∧ mem_l hℳ a b)
    (E E' : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega)
    (hE : setRel_l K E H) (hE' : setRel_l K E' H') (n : SecondOrderModel.num_l ℳ)
    (hPast : ∀ i, SecondOrderPairing.relation_l R i n → ∀ t,
      SecondOrderPairing.relation_l H i t ↔ SecondOrderPairing.relation_l H' i t)
    (h : output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T P₀ f C (numberCode_l K n).val E.val W) :
    output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T P₀ f C (numberCode_l K n).val E'.val W := by
  obtain ⟨_, q, G, hG, hW⟩ := h
  obtain ⟨q', G', hG'⟩ := SecondOrderComparisonHistoryDerives.exists_l K E' H' hE' C f
  refine ⟨E'.property, q', G', hG', (SecondOrderComparisonStageLocal.output_local_l ?_).mp hW⟩
  intro a hna j b hjb hb P
  have hjω := hI j (SecondOrderFunctionLaws.value_mem_l hℳ hJ hjb).1
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨j, hjω⟩
  have hij : (numberCode_l K i).val = j := congrArg Subtype.val hi
  rw [← hij] at hjb ⊢
  have hin := (hR i n).mpr ⟨b, a, hjb, hna, hb⟩
  have hSection (X : SecondOrderModel.set_l ℳ) :
      SecondOrderSections.spec_l H i X ↔ SecondOrderSections.spec_l H' i X :=
    forall_congr' (fun t => iff_congr Iff.rfl (hPast i hin t))
  exact (decoded_read_l K E H hE hG i P).trans
    ((exists_congr (fun X => and_congr (hSection X) Iff.rfl)).trans
      (decoded_read_l K E' H' hE' hG' i P).symm)

theorem output_local_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid I A J T P₀ f C W : type_l hℳ}
    (hJ : map_l (ℳ := 𝒱) J I A) (hI : subset_l (ℳ := 𝒱) I K.omega)
    (R H H' : SecondOrderModel.set_l ℳ)
    (hR : ∀ i j, SecondOrderPairing.relation_l R i j ↔ ∃ a b,
      value_l (ℳ := 𝒱) J (numberCode_l K i).val a ∧
      value_l (ℳ := 𝒱) J (numberCode_l K j).val b ∧ mem_l hℳ a b)
    (E E' : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega)
    (hE : setRel_l K E H) (hE' : setRel_l K E' H') (n : SecondOrderModel.num_l ℳ)
    (hPast : ∀ i, SecondOrderPairing.relation_l R i n → ∀ t,
      SecondOrderPairing.relation_l H i t ↔ SecondOrderPairing.relation_l H' i t) :
    output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T P₀ f C (numberCode_l K n).val E.val W ↔
      output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T P₀ f C (numberCode_l K n).val E'.val W :=
  ⟨forward_l K hJ hI R H H' hR E E' hE hE' n hPast,
    forward_l K hJ hI R H' H hR E' E hE' hE n (fun i hi t => (hPast i hi t).symm)⟩

#print axioms decoded_read_l
#print axioms output_local_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryStageLocal
