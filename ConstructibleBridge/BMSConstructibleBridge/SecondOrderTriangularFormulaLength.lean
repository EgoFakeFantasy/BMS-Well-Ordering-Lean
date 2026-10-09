import BMSConstructibleBridge.SecondOrderTriangularFormulaSyntax
import BMSConstructibleBridge.SecondOrderListInduction

/-! # 内部合法码对赋值长度的单调性

强归纳用于一个实际原算术公式，参数是合法性关系 V；没有假设模型自然数
的外部良基性。延长赋值不会破坏合法性，结论另有原 Z₂ 对象闭句推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularFormulaLength

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderTriangularFormulaSyntax (spec_l spec_m spec_formula_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m} (t : Term signature_m Γ Δ s) :=
  t.weakenBound sort_m.num

def monotone_m {Γ Δ : SortContext signature_m} (V : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .num <| .imp
    (.disj (.equal (.bvar (.there .here)) (.bvar .here))
      (PrimitiveFormulas.lt_m (.bvar (.there .here)) (.bvar .here))) <| .imp
    (GraphSyntax.edge_m (up (up V)) (up (up n)) (.bvar (.there .here)))
    (GraphSyntax.edge_m (up (up V)) (up (up n)) (.bvar .here))

theorem monotone_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (V : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    (monotone_m V n).satisfies η ↔ ∀ l m, (l = m ∨ SecondOrderOrder.lt_l l m) →
      relation_l (V.eval η) (n.eval η) l → relation_l (V.eval η) (n.eval η) m := by
  simp only [monotone_m, Formula.satisfies, SecondOrderOrder.formula_l, SecondOrderPairing.edge_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem monotone_l (hℳ : Theory.Models ℳ theory_m) {V : set_l ℳ} (hV : spec_l V) :
    ∀ n l m, (l = m ∨ SecondOrderOrder.lt_l l m) → relation_l V n l → relation_l V n m := by
  let φ : Formula signature_m [] [.num, .set] := monotone_m (.fvar (.there .here)) (.fvar .here)
  have hφ : language_m φ = true := pure_language_m _ rfl
  apply SecondOrderListInduction.strong_induct_l hℳ φ hφ (Env.empty.pushFree V)
    (fun n => ∀ l m, (l = m ∨ SecondOrderOrder.lt_l l m) → relation_l V n l → relation_l V n m)
    (fun n => monotone_formula_l _ _ _) ?_
  intro n ih l m hlm hn
  have hLift {a : num_l ℳ} (ha : SecondOrderOrder.lt_l a l) : SecondOrderOrder.lt_l a m :=
    hlm.elim (fun hEq => hEq ▸ ha) (fun hLt => SecondOrderOrder.trans_l hℳ ha hLt)
  apply (hV n m).mpr
  rcases (hV n l).mp hn with hZero | ⟨a, b, hCases⟩
  · exact Or.inl hZero
  · refine Or.inr ⟨a, b, ?_⟩
    rcases hCases with ⟨hAtomic, ha, hb⟩ | ⟨hNand, ha, hb⟩ | ⟨hExists, ha, hb⟩
    · exact Or.inl ⟨hAtomic, hLift ha, hLift hb⟩
    · obtain ⟨han, hbn⟩ := SecondOrderTriangularConstructor.bounds_l hℳ hNand
      exact Or.inr (Or.inl ⟨hNand, ih a han l m hlm ha, ih b hbn l m hlm hb⟩)
    · exact Or.inr (Or.inr ⟨hExists, hLift ha,
        ih b (SecondOrderTriangularConstructor.bounds_l hℳ hExists).2 l m hlm hb⟩)

def sentence_m : Sentence signature_m := .forallE .set <|
  .imp (spec_m (.bvar .here)) <| .forallE .num <| monotone_m (.bvar (.there .here)) (.bvar .here)

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, spec_formula_l, monotone_formula_l, Term.eval]
  exact fun V hV => monotone_l hℳ hV

#print axioms monotone_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularFormulaLength
