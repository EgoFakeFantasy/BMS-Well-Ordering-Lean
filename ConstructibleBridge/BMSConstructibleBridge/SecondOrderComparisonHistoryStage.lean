import BMSConstructibleBridge.SecondOrderComparisonStageLocal
import BMSConstructibleBridge.SecondOrderComparisonHistoryDerives

/-! # 原候选历史的解码与实际阶段行装配

解码的值域界和函数图由对象存在量词引入；所有候选历史均可解码。两份
解码见证只需在前驱指标上值相同，阶段输出即相同，不选择规范解码图。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryStage

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def output_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid I J T P₀ f C i H W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (ThirdOrderTheory.subset_m H ω) <| .existsE .set <| .existsE .set <|
    .conj (SecondOrderComparisonHistoryDerives.history_m (up (up ω)) (up (up e))
      (up (up H)) (up (up f)) (up (up C)) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderComparisonStageSyntax.output_m (up (up ω)) (up (up e)) (up (up t₁))
        (up (up t₂)) (up (up t₃)) (up (up Pair)) (up (up Valid)) (up (up I)) (up (up J))
        (up (up T)) (.bvar .here) (up (up P₀)) (up (up f)) (up (up i)) (up (up W)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
private abbrev zero_l (K : source_coding_l hℳ) := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val

def output_l (ω e t₁ t₂ t₃ Pair Valid I J T P₀ f C i H W : type_l hℳ) : Prop :=
  subset_l (ℳ := 𝒱) H ω ∧ ∃ q G,
    SecondOrderComparisonHistoryDerives.history_l (𝒩 := 𝒱) ω e H f C q G ∧
      SecondOrderComparisonStageSyntax.output_l ω e t₁ t₂ t₃ Pair Valid I J T G P₀ f i W

theorem output_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid I J T P₀ f C i H W : Term ℒ Γ Δ .set) :
    (output_m ω e t₁ t₂ t₃ Pair Valid I J T P₀ f C i H W).satisfies η ↔
      output_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (I.eval η) (J.eval η) (T.eval η) (P₀.eval η) (f.eval η) (C.eval η)
        (i.eval η) (H.eval η) (W.eval η) := by
  simp only [output_m, output_l, Formula.satisfies, subset_formula_l,
    SecondOrderComparisonHistoryDerives.history_formula_l, SecondOrderComparisonStageSyntax.output_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 解码图的全部值相同，允许直接替换解码见证；无需图的选择函数。 -/
theorem decoded_congr_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid I J T P₀ f C i H q q' G G' W : type_l hℳ}
    (hG : SecondOrderComparisonHistoryDerives.history_l (𝒩 := 𝒱) K.omega (zero_l K) H f C q G)
    (hG' : SecondOrderComparisonHistoryDerives.history_l (𝒩 := 𝒱) K.omega (zero_l K) H f C q' G') :
    SecondOrderComparisonStageSyntax.output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T G P₀ f i W ↔
      SecondOrderComparisonStageSyntax.output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T G' P₀ f i W := by
  apply SecondOrderComparisonStageLocal.output_local_l
  intro _ _ j _ _ _ P
  exact (hG.2.1 j P).trans (hG'.2.1 j P).symm

theorem exists_unique_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid I A J T B F r f P₀ C : type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hA : SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) A)
    (hJ : map_l (ℳ := 𝒱) J I A) (hInject : injective_l (ℳ := 𝒱) J)
    (hOnto : ∀ a, mem_l hℳ a A → ∃ i, mem_l hℳ i I ∧ value_l (ℳ := 𝒱) J i a)
    (hI : subset_l (ℳ := 𝒱) I K.omega) (hTMap : map_l (ℳ := 𝒱) T I r)
    (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B A F r)
    (hT : ∀ i X, value_l (ℳ := 𝒱) T i X ↔ ∃ a, value_l (ℳ := 𝒱) J i a ∧ value_l (ℳ := 𝒱) F a X)
    (H : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (R : SecondOrderModel.set_l ℳ) (hH : setRel_l K H R)
    (i : type_l hℳ) : ∃! W,
      output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T P₀ f C i H.val W := by
  obtain ⟨q, G, hG⟩ := SecondOrderComparisonHistoryDerives.exists_l K H R hH C f
  obtain ⟨W, hW, hOnly⟩ := SecondOrderComparisonStageTotal.exists_unique_l K hCoding hA hJ hInject
    hOnto hI hTMap hG.1 hF hT i
  refine ⟨W, ⟨H.property, q, G, hG, hW⟩, ?_⟩
  rintro X ⟨_, q', G', hG', hX⟩
  exact hOnly X ((decoded_congr_l K hG' hG).mp hX)

theorem guard_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid I J T P₀ f C i H W : type_l hℳ}
    (h : output_l K.omega (zero_l K) t₁ t₂ t₃ Pair Valid I J T P₀ f C i H W) :
    subset_l (ℳ := 𝒱) W K.omega := by
  obtain ⟨_, _, _, _, hW⟩ := h
  exact SecondOrderComparisonStageTotal.guard_l K hW

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryStage
