import BMSConstructibleBridge.SecondOrderInternalFormulaCompilation
import BMSConstructibleBridge.SecondOrderDefinableFamily

/-!
# 合法公式及有效参数赋值的内部索引选择

索引同时编码公式、参数长度和参数赋值码。检查的是模型内全部索引，合法性
及赋值有效性均用已有的实际公式；不以外部公式枚举代替这个选择谓词。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegalFormulaIndex

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (V E : set_l ℳ) (i : num_l ℳ) : Prop :=
  ∃ p l c, SecondOrderDefinableFamily.index_l p l c = i ∧
    SecondOrderAssignmentSyntax.valid_l E c l ∧ relation_l V p (succ_l l)

def formula_m : Formula signature_m [] [.num, .set, .set] :=
  .existsE .num (.existsE .num (.existsE .num (.existsE .num (.conj
    (PrimitiveFormulas.pair_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
    (.conj (PrimitiveFormulas.pair_m (.bvar (.there (.there (.there .here)))) (.bvar .here) (.fvar .here))
      (.conj (SecondOrderAssignmentSyntax.formula_m (.fvar (.there (.there .here)))
        (.bvar (.there .here)) (.bvar (.there (.there .here))))
        (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar (.there (.there (.there .here))))
          (Term.app (σ := signature_m) .succ (.cons (.bvar (.there (.there .here))) .nil)))))))))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (η : Env ℳ [] [.num, .set, .set]) : formula_m.satisfies η ↔
    spec_l (η.freeVal (.there .here)) (η.freeVal (.there (.there .here))) (η.freeVal .here) := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l,
    SecondOrderAssignmentSyntax.raw_l, SecondOrderPairing.edge_l, Term.eval]
  change (∃ p l c a, value_l l c = a ∧ value_l p a = η.freeVal .here ∧
    SecondOrderAssignmentSyntax.valid_l (η.freeVal (.there (.there .here))) c l ∧
      relation_l (η.freeVal (.there .here)) p (succ_l l)) ↔ _
  constructor
  · rintro ⟨p, l, c, _, rfl, hi, hc, hV⟩
    exact ⟨p, l, c, hi, hc, hV⟩
  · rintro ⟨p, l, c, hi, hc, hV⟩
    exact ⟨p, l, c, _, rfl, hi, hc, hV⟩

theorem index_l (hℳ : Theory.Models ℳ theory_m) (V E : set_l ℳ) (p l c : num_l ℳ) :
    spec_l V E (SecondOrderDefinableFamily.index_l p l c) ↔
      SecondOrderAssignmentSyntax.valid_l E c l ∧ relation_l V p (succ_l l) := by
  constructor
  · rintro ⟨q, m, d, h, hc, hV⟩
    obtain ⟨rfl, rfl, rfl⟩ := SecondOrderDefinableFamily.index_injective_l hℳ q m d p l c h
    exact ⟨hc, hV⟩
  · rintro ⟨hc, hV⟩
    exact ⟨p, l, c, rfl, hc, hV⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegalFormulaIndex
