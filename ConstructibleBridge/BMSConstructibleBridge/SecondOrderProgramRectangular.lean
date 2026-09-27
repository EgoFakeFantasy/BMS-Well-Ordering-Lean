import BMSConstructibleBridge.SecondOrderProgramListAll

/-!
# 内部数组的矩形性公式

数组码具有实际宽度n，每个有效列码具有同一实际长度h。这里保留真实长度图，
不把外部列表或标准高度假设加到定义中。等长列的集合由原理解公理实际取得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangular

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramListAll (all_l)
open SecondOrderProgramListShift (output_m output_syntax_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 真实宽度与每个有效列的共同长度；空宽度时列条件为空。 -/
def rectangular_l (L E : set_l ℳ) (x n h : num_l ℳ) : Prop :=
  relation_l L x n ∧ ∀ j, SecondOrderOrder.lt_l j n →
    ∀ s, relation_l E (value_l x j) s → relation_l L s h

/-- 同一性质的纯公式模板，可用于非标准数域上的原内部归纳。 -/
def rectangular_m {Γ Δ : SortContext signature_m} (L E : Term signature_m Γ Δ .set)
    (x n h : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .conj (GraphSyntax.edge_m L x n)
    (.forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (n.weakenBound sort_m.num))
      (.forallE .num (.imp
        (output_m ((E.weakenBound sort_m.num).weakenBound sort_m.num)
          ((x.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here)) (.bvar .here))
        (GraphSyntax.edge_m ((L.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here)
          ((h.weakenBound sort_m.num).weakenBound sort_m.num))))))

/-- 公式使用原读取图、原长度图与同一宽高值，语义不丢失有效下标限制。 -/
theorem rectangular_syntax_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (L E : Term signature_m Γ Δ .set) (x n h : Term signature_m Γ Δ .num) :
    Formula.satisfies η (rectangular_m L E x n h) ↔
      rectangular_l (L.eval η) (E.eval η) (x.eval η) (n.eval η) (h.eval η) := by
  simp only [rectangular_m, rectangular_l, Formula.satisfies, SecondOrderPairing.edge_l,
    SecondOrderOrder.formula_l, output_syntax_l, Term.eval_weakenBound]
  rfl

/-- 给定内部高度，真实长度图的该高度纤维是模型中的集合，而非外部谓词。 -/
theorem length_set_l (hℳ : Theory.Models ℳ theory_m) (L : set_l ℳ) (h : num_l ℳ) :
    ∃ S : set_l ℳ, ∀ s, mem_l s S ↔ relation_l L s h := by
  let φ : Formula signature_m [] [.num, .num, .set] :=
    GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  obtain ⟨S, hS⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((Env.empty (M := ℳ)).pushFree L).pushFree h)
  refine ⟨S, fun s => (hS s).trans ?_⟩
  exact SecondOrderPairing.edge_l _ _ _ _

/-- 同一长度纤维集合把矩形性精确改写为真实宽度与全部有效列的集合性质。 -/
theorem rectangular_iff_all_l {L E S : set_l ℳ} {x n h : num_l ℳ}
    (hS : ∀ s, mem_l s S ↔ relation_l L s h) :
    rectangular_l L E x n h ↔ relation_l L x n ∧ all_l E S x n := by
  simp only [rectangular_l, all_l, hS]

#print axioms rectangular_l
#print axioms rectangular_m
#print axioms rectangular_syntax_l
#print axioms length_set_l
#print axioms rectangular_iff_all_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramRectangular
