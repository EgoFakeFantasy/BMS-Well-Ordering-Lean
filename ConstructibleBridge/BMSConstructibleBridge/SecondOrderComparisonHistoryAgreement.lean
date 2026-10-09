import BMSConstructibleBridge.SecondOrderComparisonHistoryAgreementStep
import BMSConstructibleBridge.SecondOrderComparisonHistoryInvariant

/-! # 不同阶段界下的实际规范比较历史一致性

归纳性质是共同序数阶段的完整比较图相等。纯公式集合归纳只使用原
Z₂ 商中的弱集合论；两边的指标、共同载体和枚举可不同。基底序和
编码包固定，没有假设外部良基或预选全体阶段的历史函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryAgreement

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderObjectSyntax (member_m)
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonHistoryAgreementStep (read_m read_l read_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))

def point_m {Γ Δ : SortContext ℒ} (A A' J T G J' T' G' a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (.conj (member_m a A) (member_m a A')) <|
    .forallE .set <| .forallE .set <| .forallE .set <| .forallE .set <|
      let X : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
      let P := .bvar (.there (.there .here))
      let Y := .bvar (.there .here)
      let Q := .bvar .here
      .imp (.conj (read_m (up₄ J) (up₄ T) (up₄ G) (up₄ a) X P)
        (read_m (up₄ J') (up₄ T') (up₄ G') (up₄ a) Y Q)) (.equal P Q)

def point_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (A A' J T G J' T' G' a : carrier_l 𝒩) : Prop :=
  member_l 𝒩 a A ∧ member_l 𝒩 a A' → ∀ X P Y Q,
    read_l (𝒩 := 𝒩) J T G a X P ∧ read_l (𝒩 := 𝒩) J' T' G' a Y Q → P = Q

theorem point_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (A A' J T G J' T' G' a : Term ℒ Γ Δ .set) :
    (point_m A A' J T G J' T' G' a).satisfies η ↔
      point_l (A.eval η) (A'.eval η) (J.eval η) (T.eval η) (G.eval η)
        (J'.eval η) (T'.eval η) (G'.eval η) (a.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, member_m, read_formula_l,
    up₄, up, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set] :=
  point_m (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.fvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

set_option maxHeartbeats 1000000 in
theorem agree_l (K : source_coding_l hℳ)
    {A A' B F F' r r' I I' J J' T T' G G' q q' t₁ t₂ t₃ Pair Valid P₀ : type_l hℳ}
    (h : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A F r I J T)
    (h' : SecondOrderComparisonIndexedConfiguration.configuration_l K.omega B A' F' r' I' J' T')
    (hG : map_l (ℳ := 𝒱) G K.omega q) (hG' : map_l (ℳ := 𝒱) G' K.omega q')
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hCanonical : SecondOrderComparisonCanonicalSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid I J T G P₀ A)
    (hCanonical' : SecondOrderComparisonCanonicalSyntax.history_l K.omega (zero_l K)
      t₁ t₂ t₃ Pair Valid I' J' T' G' P₀ A') :
    ∀ a, point_l (𝒩 := 𝒱) A A' J T G J' T' G' a := by
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree G' |>.pushFree T' |>.pushFree J' |>.pushFree G
      |>.pushFree T |>.pushFree J |>.pushFree A' |>.pushFree A
  have hPoint a : formula_m.satisfies (η.pushFree a) ↔
      point_l (𝒩 := 𝒱) A A' J T G J' T' G' a :=
    point_formula_l _ _ _ _ _ _ _ _ _ _
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) formula_m η
    (fun a ih => (hPoint a).mpr (by
      rintro ⟨ha, ha'⟩ X P Y Q ⟨hRead, hRead'⟩
      have hPast b (hb : mem_l hℳ b a) X P Y Q
          (hRead : read_l (𝒩 := 𝒱) J T G b X P)
          (hRead' : read_l (𝒩 := 𝒱) J' T' G' b Y Q) : P = Q :=
        (hPoint b).mp (ih b hb) ⟨h.ordinal.transitive a ha b hb, h'.ordinal.transitive a ha' b hb⟩
          X P Y Q ⟨hRead, hRead'⟩
      obtain ⟨i, hia, hiX, hiP⟩ := hRead
      obtain ⟨j, hja, hjY, hjQ⟩ := hRead'
      have hi := (SecondOrderFunctionLaws.value_mem_l hℳ h.indexMap hia).1
      have hj := (SecondOrderFunctionLaws.value_mem_l hℳ h'.indexMap hja).1
      exact SecondOrderComparisonHistoryAgreementStep.step_l h h' hG hG' hCoding ha ha'
        ⟨i, hia, hiX, hiP⟩ ⟨j, hja, hjY, hjQ⟩ hPast
        (hCanonical a ha i X P ⟨⟨hi, hiX, hiP⟩, hia⟩)
        (hCanonical' a ha' j Y Q ⟨⟨hj, hjY, hjQ⟩, hja⟩)))
  exact fun a => (hPoint a).mp (hAll a)

#print axioms point_formula_l
#print axioms agree_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryAgreement
