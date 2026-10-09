import BMSConstructibleBridge.SecondOrderCanonicalOrderComparisonTotalized
import BMSConstructibleBridge.SecondOrderComparisonHistoryDecode

/-! # 读取一条前驱历史的纯后继行

比较历史 G 是由原历史实数实际解码得到的函数。后继分支仅读取给定指标
i 的值；非法旧序也通过已经验证的缺省分支得到唯一行，不检查未来历史。
这里尚未装配零／后继／极限分类，也不宣称最终 BMS 推导已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonSuccessorSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open PowerlessFormulaValidityReading (code_l)
open SecondOrderQuotient (type_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def output_m {Γ Δ : SortContext ℒ}
    (ω A G i e t₁ t₂ t₃ Pair Valid D f W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.value_m (up G) (up i) (.bvar .here))
    (SecondOrderCanonicalOrderComparisonTotalized.output_m (up ω) (up A) (.bvar .here) (up e)
      (up t₁) (up t₂) (up t₃) (up Pair) (up Valid) (up D) (up f) (up W))

def output_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω A G i e t₁ t₂ t₃ Pair Valid D f W : carrier_l 𝒩) : Prop :=
  ∃ P, value_l (ℳ := 𝒩) G i P ∧
    SecondOrderCanonicalOrderComparisonTotalized.output_l ω A P e t₁ t₂ t₃ Pair Valid D f W

theorem output_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A G i e t₁ t₂ t₃ Pair Valid D f W : Term ℒ Γ Δ .set) :
    (output_m ω A G i e t₁ t₂ t₃ Pair Valid D f W).satisfies η ↔
      output_l (ω.eval η) (A.eval η) (G.eval η) (i.eval η) (e.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (Pair.eval η) (Valid.eval η) (D.eval η) (f.eval η) (W.eval η) := by
  simp only [output_m, output_l, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
    SecondOrderCanonicalOrderComparisonTotalized.output_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 单个前驱值的全部输出相同即可，域外历史没有任何限制。 -/
theorem local_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A G H i e t₁ t₂ t₃ Pair Valid D f W : carrier_l 𝒩}
    (h : ∀ P, value_l (ℳ := 𝒩) G i P ↔ value_l (ℳ := 𝒩) H i P) :
    output_l ω A G i e t₁ t₂ t₃ Pair Valid D f W ↔ output_l ω A H i e t₁ t₂ t₃ Pair Valid D f W :=
  exists_congr (fun P => and_congr (h P) Iff.rfl)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 原历史前驱行的逐位相同，直接保持后继分支的全部输出。 -/
theorem history_local_l (K : source_coding_l hℳ)
    (I : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) {E H H' : SecondOrderModel.set_l ℳ}
    (hI : setRel_l K I E) {C f G G' A t₁ t₂ t₃ Pair Valid D W : type_l hℳ}
    (hG : ∀ i P, value_l (ℳ := 𝒱) G (numberCode_l K i).val P ↔
      ∃ X, SecondOrderSections.spec_l H i X ∧ SecondOrderComparisonDecode.graph_l K C f X P)
    (hG' : ∀ i P, value_l (ℳ := 𝒱) G' (numberCode_l K i).val P ↔
      ∃ X, SecondOrderSections.spec_l H' i X ∧ SecondOrderComparisonDecode.graph_l K C f X P)
    (hPast : ∀ i, SecondOrderModel.mem_l i E → ∀ t,
      SecondOrderPairing.relation_l H i t ↔ SecondOrderPairing.relation_l H' i t)
    (n : SecondOrderModel.num_l ℳ) (hn : SecondOrderModel.mem_l n E) :
    output_l (𝒩 := 𝒱) K.omega A G (numberCode_l K n).val
      (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f W ↔
    output_l (𝒩 := 𝒱) K.omega A G' (numberCode_l K n).val
      (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f W :=
  local_l (SecondOrderComparisonHistoryDecode.value_congr_l K I hI hG hG' hPast
    (numberCode_l K n).val ((hI n).mpr hn))

theorem exists_unique_l (K : source_coding_l hℳ)
    {f A G i I r t₁ t₂ t₃ Pair Valid D : type_l hℳ}
    (ht₁ : t₁ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 1))
    (ht₂ : t₂ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 2))
    (ht₃ : t₃ = code_l K (SecondOrderEvaluationRule.numeral_l ℳ 3))
    (hPairMap : map_l (ℳ := 𝒱) Pair K.omega K.omega)
    (hPair : PowerlessBMSQuotientPairingBounds.spec_l K Pair)
    {V : SecondOrderModel.set_l ℳ} (hV : SecondOrderTriangularFormulaSyntax.spec_l V)
    (hValid : ∀ c N, value_l (ℳ := 𝒱) Valid c N ↔ PowerlessRelationalCodeValidity.valid_l K V c N)
    (hG : map_l (ℳ := 𝒱) G I r) (hi : SecondOrderQuotient.mem_l hℳ i I) :
    ∃! W : type_l hℳ, output_l (𝒩 := 𝒱) K.omega A G i
      (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f W := by
  obtain ⟨P, ⟨_, hiP⟩, _⟩ := hG.2 i hi
  obtain ⟨W, hW, hOnly⟩ := SecondOrderCanonicalOrderComparisonTotalized.exists_unique_l
    (A := A) (P := P) (D := D) (f := f) K ht₁ ht₂ ht₃ hPairMap hPair hV hValid
  refine ⟨W, ⟨P, hiP, hW⟩, ?_⟩
  rintro X ⟨Q, hiQ, hX⟩
  have hQP := SecondOrderFunctionLaws.value_unique_l hℳ hG hiQ hiP
  subst Q
  exact hOnly X hX

theorem guard_l (K : source_coding_l hℳ)
    {A G i t₁ t₂ t₃ Pair Valid D f W : type_l hℳ}
    (h : output_l (𝒩 := 𝒱) K.omega A G i
      (code_l K (SecondOrderModel.zero_l ℳ)) t₁ t₂ t₃ Pair Valid D f W) :
    subset_l (ℳ := 𝒱) W K.omega := by
  obtain ⟨_, _, hW⟩ := h
  exact SecondOrderCanonicalOrderComparisonTotalized.guard_l K hW

#print axioms output_formula_l
#print axioms local_l
#print axioms history_local_l
#print axioms exists_unique_l
#print axioms guard_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonSuccessorSyntax
