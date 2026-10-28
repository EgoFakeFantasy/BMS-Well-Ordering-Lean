import BMSConstructibleBridge.SecondOrderComparisonStageTotal

/-! # 实际阶段比较行只读取前驱历史

局部性覆盖任意候选比较历史，且直接比较每个前驱上的全部值。极限的前驱
集合由实际 J 拉回；没有把域外或未来历史相同偷偷加入递归算子的假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStageLocal

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open SecondOrderComparisonStageSyntax (branch_l output_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def past_m {Γ Δ : SortContext ℒ} (J G H a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .imp
    (.conj (SecondOrderObjectSyntax.value_m (up (up J)) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up a)))) <|
        .forallE .set <| .iff
          (SecondOrderObjectSyntax.value_m (up (up (up G))) (.bvar (.there (.there .here))) (.bvar .here))
          (SecondOrderObjectSyntax.value_m (up (up (up H))) (.bvar (.there (.there .here))) (.bvar .here))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def past_l (J G H a : type_l hℳ) : Prop :=
  ∀ j b, value_l (ℳ := 𝒱) J j b → mem_l hℳ b a → ∀ P,
    value_l (ℳ := 𝒱) G j P ↔ value_l (ℳ := 𝒱) H j P

theorem past_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (J G H a : Term ℒ Γ Δ .set) :
    (past_m J G H a).satisfies η ↔ past_l (J.eval η) (G.eval η) (H.eval η) (a.eval η) := by
  simp only [past_m, past_l, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  simp only [and_imp]
  rfl

theorem branch_local_l {ω e t₁ t₂ t₃ Pair Valid J T G H P₀ f a C W : type_l hℳ}
    (hPast : past_l J G H a) :
    branch_l ω e t₁ t₂ t₃ Pair Valid J T G P₀ f a C W ↔
      branch_l ω e t₁ t₂ t₃ Pair Valid J T H P₀ f a C W := by
  apply or_congr Iff.rfl
  apply or_congr
  · unfold SecondOrderComparisonStageSyntax.successor_l
    apply exists_congr
    intro b
    apply exists_congr
    intro j
    apply exists_congr
    intro U
    constructor
    · rintro ⟨hb, hjb, hjU, hW⟩
      exact ⟨hb, hjb, hjU, (SecondOrderComparisonSuccessorSyntax.local_l
        (hPast j b hjb (PowerlessRelativeHierarchyStep.successor_member_l hℳ hb))).mp hW⟩
    · rintro ⟨hb, hjb, hjU, hW⟩
      exact ⟨hb, hjb, hjU, (SecondOrderComparisonSuccessorSyntax.local_l
        (hPast j b hjb (PowerlessRelativeHierarchyStep.successor_member_l hℳ hb))).mpr hW⟩
  · unfold SecondOrderComparisonStageSyntax.limit_l
    apply and_congr Iff.rfl
    apply exists_congr
    intro D
    constructor
    · rintro ⟨hD, hW⟩
      refine ⟨hD, (SecondOrderComparisonLimitSyntax.local_l (fun j hj P => ?_)).mp hW⟩
      obtain ⟨b, hjb, hb⟩ := (hD j).mp hj
      exact hPast j b hjb hb P
    · rintro ⟨hD, hW⟩
      refine ⟨hD, (SecondOrderComparisonLimitSyntax.local_l (fun j hj P => ?_)).mpr hW⟩
      obtain ⟨b, hjb, hb⟩ := (hD j).mp hj
      exact hPast j b hjb hb P

/-- 任一当前阶段候选对应的前驱一致，足够保持该指标的输出关系。 -/
theorem output_local_l {ω e t₁ t₂ t₃ Pair Valid I J T G H P₀ f i W : type_l hℳ}
    (hPast : ∀ a, value_l (ℳ := 𝒱) J i a → past_l J G H a) :
    output_l ω e t₁ t₂ t₃ Pair Valid I J T G P₀ f i W ↔
      output_l ω e t₁ t₂ t₃ Pair Valid I J T H P₀ f i W := by
  apply or_congr _ Iff.rfl
  apply and_congr Iff.rfl
  apply exists_congr
  intro a
  apply exists_congr
  intro C
  constructor
  · rintro ⟨hia, hiC, hW⟩
    exact ⟨hia, hiC, (branch_local_l (hPast a hia)).mp hW⟩
  · rintro ⟨hia, hiC, hW⟩
    exact ⟨hia, hiC, (branch_local_l (hPast a hia)).mpr hW⟩

/-- 原实数前驱行的逐位相同，经已有解码直接给出实际 J 前驱局部性。 -/
theorem history_past_l (K : source_coding_l hℳ)
    (D : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) {E H H' : SecondOrderModel.set_l ℳ}
    (hD : setRel_l K D E) {a J C f G G' : type_l hℳ}
    (hPred : SecondOrderStageLayerFunction.predecessor_l a J D.val)
    (hG : ∀ i P, value_l (ℳ := 𝒱) G (numberCode_l K i).val P ↔
      ∃ X, SecondOrderSections.spec_l H i X ∧ SecondOrderComparisonDecode.graph_l K C f X P)
    (hG' : ∀ i P, value_l (ℳ := 𝒱) G' (numberCode_l K i).val P ↔
      ∃ X, SecondOrderSections.spec_l H' i X ∧ SecondOrderComparisonDecode.graph_l K C f X P)
    (hPast : ∀ i, SecondOrderModel.mem_l i E → ∀ t,
      SecondOrderPairing.relation_l H i t ↔ SecondOrderPairing.relation_l H' i t) :
    past_l J G G' a := by
  intro j b hjb hb P
  exact SecondOrderComparisonHistoryDecode.value_congr_l K D hD hG hG' hPast j
    ((hPred j).mpr ⟨b, hjb, hb⟩) P

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStageLocal
