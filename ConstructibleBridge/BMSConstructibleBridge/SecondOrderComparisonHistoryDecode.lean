import BMSConstructibleBridge.PowerlessSecondOrderSections
import BMSConstructibleBridge.SecondOrderComparisonDecodeReading
import BMSConstructibleBridge.SecondOrderBoundedRelationHistory

/-! # 原二阶历史实数解码为实际比较图函数

同一个原历史实数的每行，先以纯切片公式读取，再解码为固定载体上的
唯一完整关系图。以 C×C 为统一子集界组装实际函数图；没有可数选择、
Collection 或对模型 ω 的外部归纳。这里不证明输入历史满足良序递归。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryDecode

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 首自由槽为输出图，次槽为阶段数；其余五槽是固定参数。 -/
def formula_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  let P : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let i : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let ω : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let e : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let H : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let f : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let C : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  .existsE .set <| .conj (PowerlessSecondOrderSections.formula_m ω e H i (.bvar .here))
    (SecondOrderComparisonDecodeSyntax.graph_m ω e (.bvar .here) f C P)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def parameters_l (K : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (C f : type_l hℳ) :
    Env 𝒱 [] [.set, .set, .set, .set, .set] :=
  (((((Env.empty.pushFree C).pushFree f).pushFree A.val).pushFree
    (numberCode_l K (SecondOrderModel.zero_l ℳ)).val).pushFree K.omega)

theorem formula_l (K : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (H : SecondOrderModel.set_l ℳ)
    (hA : setRel_l K A H) (C f : type_l hℳ) (i : SecondOrderModel.num_l ℳ) (P : type_l hℳ) :
    formula_m.satisfies (((parameters_l K A C f).pushFree (numberCode_l K i).val).pushFree P) ↔
      ∃ X : SecondOrderModel.set_l ℳ, SecondOrderSections.spec_l H i X ∧
        SecondOrderComparisonDecode.graph_l K C f X P := by
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set, .set] :=
    ((parameters_l K A C f).pushFree (numberCode_l K i).val).pushFree P
  let w : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let z : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let Q : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let n : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let F : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let D : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let T : Term ℒ [.set] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  have hSection (B : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega)
      (X : SecondOrderModel.set_l ℳ) (hB : setRel_l K B X) :
      (PowerlessSecondOrderSections.formula_m w z Q n (.bvar .here)).satisfies (η.pushBound B.val) ↔
        SecondOrderSections.spec_l H i X :=
    PowerlessSecondOrderSections.formula_l K _ w z Q n (.bvar .here) B A X H i
      rfl rfl rfl rfl rfl hB hA
  have hGraph (B : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega)
      (X : SecondOrderModel.set_l ℳ) (hB : setRel_l K B X) :
      (SecondOrderComparisonDecodeSyntax.graph_m w z (.bvar .here) F D T).satisfies (η.pushBound B.val) ↔
        SecondOrderComparisonDecode.graph_l K C f X P :=
    (SecondOrderComparisonDecodeSyntax.graph_formula_l _ w z (.bvar .here) F D T).trans
      (SecondOrderComparisonDecodeReading.graph_l K B X hB C f P)
  change (∃ r, (PowerlessSecondOrderSections.formula_m w z Q n (.bvar .here)).satisfies (η.pushBound r) ∧
    (SecondOrderComparisonDecodeSyntax.graph_m w z (.bvar .here) F D T).satisfies (η.pushBound r)) ↔ _
  constructor
  · rintro ⟨r, hs, hg⟩
    have hSubset := (subset_formula_l (η.pushBound r) (.bvar .here) w).mp hs.1
    have hSubset' : ∀ x, mem_l hℳ x r → mem_l hℳ x K.omega := hSubset
    let B : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega := ⟨r, hSubset'⟩
    obtain ⟨X, hB⟩ := PowerlessBMSQuotientReals.trace_exists_l K B
    exact ⟨X, (hSection B X hB).mp hs, (hGraph B X hB).mp hg⟩
  · rintro ⟨X, hs, hg⟩
    obtain ⟨B, hB⟩ := representative_exists_l K X
    exact ⟨B.val, (hSection B X hB).mpr hs, (hGraph B X hB).mpr hg⟩

theorem total_l (K : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (H : SecondOrderModel.set_l ℳ)
    (hA : setRel_l K A H) (C f : type_l hℳ) (i : SecondOrderModel.num_l ℳ) :
    ∃ P, formula_m.satisfies (((parameters_l K A C f).pushFree (numberCode_l K i).val).pushFree P) := by
  obtain ⟨X, hX⟩ := SecondOrderSections.exists_l hℳ H i
  obtain ⟨P, hP⟩ := SecondOrderComparisonDecode.exists_l K C f X
  exact ⟨P, (formula_l K A H hA C f i P).mpr ⟨X, hX, hP⟩⟩

theorem unique_l (K : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (H : SecondOrderModel.set_l ℳ)
    (hA : setRel_l K A H) (C f : type_l hℳ) (i : SecondOrderModel.num_l ℳ)
    (P Q : type_l hℳ)
    (hP : formula_m.satisfies (((parameters_l K A C f).pushFree (numberCode_l K i).val).pushFree P))
    (hQ : formula_m.satisfies (((parameters_l K A C f).pushFree (numberCode_l K i).val).pushFree Q)) : P = Q := by
  obtain ⟨X, hX, hXP⟩ := (formula_l K A H hA C f i P).mp hP
  obtain ⟨Y, hY, hYQ⟩ := (formula_l K A H hA C f i Q).mp hQ
  have hXY := SecondOrderSections.unique_l hℳ hX hY
  subst Y
  exact SecondOrderComparisonDecode.unique_l K hXP hYQ

theorem exists_l (K : source_coding_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) (H : SecondOrderModel.set_l ℳ)
    (hA : setRel_l K A H) (C f : type_l hℳ) :
    ∃ b g : type_l hℳ, map_l (ℳ := 𝒱) g K.omega b ∧
      (∀ P, mem_l hℳ P b ↔ ∃ i X, SecondOrderSections.spec_l H i X ∧
        SecondOrderComparisonDecode.graph_l K C f X P) ∧
      ∀ i P, value_l (ℳ := 𝒱) g (numberCode_l K i).val P ↔
        ∃ X, SecondOrderSections.spec_l H i X ∧ SecondOrderComparisonDecode.graph_l K C f X P := by
  obtain ⟨b, g, hb, hg, hRead⟩ := SecondOrderBoundedRelationHistory.exists_l K
    formula_m (parameters_l K A C f) C (total_l K A H hA C f) (unique_l K A H hA C f) (by
      intro i P hP p hp
      obtain ⟨X, _, hXP⟩ := (formula_l K A H hA C f i P).mp hP
      obtain ⟨x, y, ⟨hx, hy, _⟩, hxy⟩ := (hXP p).mp hp
      exact ⟨x, y, hx, hy, hxy⟩)
  refine ⟨b, g, hg, ?_, ?_⟩
  · intro P
    exact (hb P).trans (exists_congr (fun i => formula_l K A H hA C f i P))
  · intro i P
    exact (hRead (numberCode_l K i).val P).trans
      ⟨fun h => (formula_l K A H hA C f i P).mp h.2,
        fun h => ⟨(numberCode_l K i).property, (formula_l K A H hA C f i P).mpr h⟩⟩

/-- 只要求指定行域内逐位一致，不要求两份完整历史相同或相容。 -/
theorem value_congr_l (K : source_coding_l hℳ)
    (I : PowerlessArithmetic.set_l (ℳ := 𝒱) K.omega) {E H H' : SecondOrderModel.set_l ℳ}
    (hI : setRel_l K I E) {C f G G' : type_l hℳ}
    (hG : ∀ i P, value_l (ℳ := 𝒱) G (numberCode_l K i).val P ↔
      ∃ X, SecondOrderSections.spec_l H i X ∧ SecondOrderComparisonDecode.graph_l K C f X P)
    (hG' : ∀ i P, value_l (ℳ := 𝒱) G' (numberCode_l K i).val P ↔
      ∃ X, SecondOrderSections.spec_l H' i X ∧ SecondOrderComparisonDecode.graph_l K C f X P)
    (hPast : ∀ i, SecondOrderModel.mem_l i E → ∀ t,
      SecondOrderPairing.relation_l H i t ↔ SecondOrderPairing.relation_l H' i t) :
    ∀ i, mem_l hℳ i I.val → ∀ P, value_l (ℳ := 𝒱) G i P ↔ value_l (ℳ := 𝒱) G' i P := by
  intro i hi P
  obtain ⟨n, hn⟩ := numberCode_surjective_l K ⟨i, I.property i hi⟩
  have hnEq : (numberCode_l K n).val = i := congrArg Subtype.val hn
  have hnE : SecondOrderModel.mem_l n E := (hI n).mp (hnEq.symm ▸ hi)
  have hSection (X : SecondOrderModel.set_l ℳ) :
      SecondOrderSections.spec_l H n X ↔ SecondOrderSections.spec_l H' n X :=
    forall_congr' (fun t => iff_congr Iff.rfl (hPast n hnE t))
  have hValue : value_l (ℳ := 𝒱) G (numberCode_l K n).val P ↔
      value_l (ℳ := 𝒱) G' (numberCode_l K n).val P :=
    (hG n P).trans ((exists_congr (fun X => and_congr (hSection X) Iff.rfl)).trans (hG' n P).symm)
  simpa only [hnEq] using hValue

#print axioms value_congr_l
#print axioms total_l
#print axioms unique_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonHistoryDecode
