import BMSConstructibleBridge.SecondOrderTriangularFormulaSyntax
import BMSConstructibleBridge.SecondOrderEvaluationEquations

/-! # 三角合法码的精确分支

由构造子单射性排除其他标签与载荷，不用外部有限枚举代替模型内部的码。
NAND 要求两个子码合法；存在量词保持赋值长度并要求指定变量槽在界内。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularFormulaBranches

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderEvaluationRule (numeral_l)
open SecondOrderTriangularConstructor (constructor_l)
open SecondOrderTriangularFormulaSyntax (spec_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem zero_l {V : set_l ℳ} (hV : spec_l V) (l : num_l ℳ) : relation_l V (SecondOrderModel.zero_l ℳ) l :=
  (hV _ l).mpr (Or.inl rfl)

theorem constructor_case_l (hℳ : Theory.Models ℳ theory_m) {V : set_l ℳ} (hV : spec_l V)
    {t a b n : num_l ℳ} (hn : constructor_l t a b n) (l : num_l ℳ) :
    relation_l V n l ↔
      ((t = numeral_l ℳ 0 ∨ t = numeral_l ℳ 1) ∧ SecondOrderOrder.lt_l a l ∧ SecondOrderOrder.lt_l b l) ∨
      (t = numeral_l ℳ 2 ∧ relation_l V a l ∧ relation_l V b l) ∨
      (t = numeral_l ℳ 3 ∧ SecondOrderOrder.lt_l a l ∧ relation_l V b l) := by
  rw [hV]
  simp only [SecondOrderTriangularFormulaSyntax.rule_l, SecondOrderTriangularConstructor.nonzero_l hℳ hn, false_or]
  constructor
  · rintro ⟨x, y, h⟩
    rcases h with ⟨hAtomic, hx, hy⟩ | ⟨hNand, hx, hy⟩ | ⟨hExists, hx, hy⟩
    · rcases hAtomic with hEqual | hMember
      · obtain ⟨ht, rfl, rfl⟩ := SecondOrderTriangularConstructor.injective_l hℳ hEqual hn
        exact Or.inl ⟨Or.inl ht.symm, hx, hy⟩
      · obtain ⟨ht, rfl, rfl⟩ := SecondOrderTriangularConstructor.injective_l hℳ hMember hn
        exact Or.inl ⟨Or.inr ht.symm, hx, hy⟩
    · obtain ⟨ht, rfl, rfl⟩ := SecondOrderTriangularConstructor.injective_l hℳ hNand hn
      exact Or.inr (Or.inl ⟨ht.symm, hx, hy⟩)
    · obtain ⟨ht, rfl, rfl⟩ := SecondOrderTriangularConstructor.injective_l hℳ hExists hn
      exact Or.inr (Or.inr ⟨ht.symm, hx, hy⟩)
  · intro h
    refine ⟨a, b, ?_⟩
    rcases h with ⟨hAtomic, ha, hb⟩ | ⟨ht, ha, hb⟩ | ⟨ht, ha, hb⟩
    · exact Or.inl ⟨hAtomic.elim (fun ht => Or.inl (ht ▸ hn)) (fun ht => Or.inr (ht ▸ hn)), ha, hb⟩
    · exact Or.inr (Or.inl ⟨ht ▸ hn, ha, hb⟩)
    · exact Or.inr (Or.inr ⟨ht ▸ hn, ha, hb⟩)

theorem membership_l (hℳ : Theory.Models ℳ theory_m) {V : set_l ℳ} (hV : spec_l V)
    {a b n : num_l ℳ} (hn : constructor_l (numeral_l ℳ 0) a b n) (l : num_l ℳ) :
    relation_l V n l ↔ SecondOrderOrder.lt_l a l ∧ SecondOrderOrder.lt_l b l := by
  simpa [SecondOrderEvaluationEquations.numeral_eq_l hℳ] using constructor_case_l hℳ hV hn l

theorem equality_l (hℳ : Theory.Models ℳ theory_m) {V : set_l ℳ} (hV : spec_l V)
    {a b n : num_l ℳ} (hn : constructor_l (numeral_l ℳ 1) a b n) (l : num_l ℳ) :
    relation_l V n l ↔ SecondOrderOrder.lt_l a l ∧ SecondOrderOrder.lt_l b l := by
  simpa [SecondOrderEvaluationEquations.numeral_eq_l hℳ] using constructor_case_l hℳ hV hn l

theorem nand_l (hℳ : Theory.Models ℳ theory_m) {V : set_l ℳ} (hV : spec_l V)
    {a b n : num_l ℳ} (hn : constructor_l (numeral_l ℳ 2) a b n) (l : num_l ℳ) :
    relation_l V n l ↔ relation_l V a l ∧ relation_l V b l := by
  simpa [SecondOrderEvaluationEquations.numeral_eq_l hℳ] using constructor_case_l hℳ hV hn l

theorem existential_l (hℳ : Theory.Models ℳ theory_m) {V : set_l ℳ} (hV : spec_l V)
    {a b n : num_l ℳ} (hn : constructor_l (numeral_l ℳ 3) a b n) (l : num_l ℳ) :
    relation_l V n l ↔ SecondOrderOrder.lt_l a l ∧ relation_l V b l := by
  simpa [SecondOrderEvaluationEquations.numeral_eq_l hℳ] using constructor_case_l hℳ hV hn l

#print axioms constructor_case_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularFormulaBranches
