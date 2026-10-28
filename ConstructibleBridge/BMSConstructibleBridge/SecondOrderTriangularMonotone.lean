import BMSConstructibleBridge.SecondOrderTriangularBounds
import YesMetaZFC.Automation.ModelClosure

/-! # 全部内部数上的三角数严格单调性

对实际算术公式作归纳，将后继增长扩展到任意内部正差。
只使用关系及显式差值见证，不把非标准数域当成宿主良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularMonotone

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers
open SecondOrderTriangularArithmetic (relation_l relation_m)
open SecondOrderOrder (lt_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem zero_bound_l (hℳ : Theory.Models ℳ theory_m) (n : num_l ℳ) : ¬lt_l n (zero_l ℳ) := by
  rintro ⟨k, h⟩
  rw [add_succ_l hℳ] at h
  exact nonzero_l hℳ (add_l n k) h

theorem successor_bound_l (hℳ : Theory.Models ℳ theory_m) {n r : num_l ℳ}
    (h : lt_l n (succ_l r)) : lt_l n r ∨ n = r := by
  obtain ⟨k, h⟩ := h
  rw [add_succ_l hℳ, (injective_l hℳ).eq_iff] at h
  rcases predecessor_l hℳ k with rfl | ⟨k, rfl⟩
  · exact Or.inr ((add_zero_l hℳ n).symm.trans h)
  · exact Or.inl ⟨k, h⟩

theorem successor_lower_l (hℳ : Theory.Models ℳ theory_m) {n r : num_l ℳ}
    (h : lt_l n r) : succ_l n = r ∨ lt_l (succ_l n) r := by
  obtain ⟨k, h⟩ := h
  have hStep : add_l (succ_l n) k = r :=
    (succ_add_l hℳ n k).trans ((add_succ_l hℳ n k).symm.trans h)
  rcases predecessor_l hℳ k with rfl | ⟨k, rfl⟩
  · exact Or.inl ((add_zero_l hℳ (succ_l n)).symm.trans hStep)
  · exact Or.inr ⟨k, hStep⟩

def formula_m : Formula signature_m [] [.num] := .forallE .num <| .forallE .num <| .forallE .num <|
  let n : Term signature_m [.num, .num, .num] [.num] .num := .bvar (.there (.there .here))
  let t : Term signature_m [.num, .num, .num] [.num] .num := .bvar (.there .here)
  let v : Term signature_m [.num, .num, .num] [.num] .num := .bvar .here
  let r : Term signature_m [.num, .num, .num] [.num] .num := .fvar .here
  .imp (relation_m n t) <| .imp (relation_m r v) <|
    .imp (PrimitiveFormulas.lt_m n r) (PrimitiveFormulas.lt_m t v)

theorem formula_l (η : Env ℳ [] [.num]) : formula_m.satisfies η ↔
    ∀ n t v : num_l ℳ, relation_l n t → relation_l (η.freeVal .here) v →
      lt_l n (η.freeVal .here) → lt_l t v := by
  simp only [formula_m, Formula.satisfies, SecondOrderTriangularArithmetic.relation_formula_l,
    SecondOrderOrder.formula_l, Term.eval]
  rfl

theorem monotone_l (hℳ : Theory.Models ℳ theory_m) {n r t v : num_l ℳ}
    (ht : relation_l n t) (hv : relation_l r v) (hnr : lt_l n r) : lt_l t v := by
  have h := induct_l hℳ formula_m (pure_language_m _ rfl) (Env.empty (M := ℳ))
    (fun r => ∀ n t v : num_l ℳ, relation_l n t → relation_l r v → lt_l n r → lt_l t v)
    (fun r => formula_l (Env.empty.pushFree r)) ?_ ?_ r
  · exact h n t v ht hv hnr
  · intro n _ _ _ _ hn
    exact (zero_bound_l hℳ n hn).elim
  · intro r h n t v ht hv hn
    obtain ⟨q, hq⟩ := SecondOrderTriangularArithmetic.exists_l hℳ r
    rcases successor_bound_l hℳ hn with hn | rfl
    · exact SecondOrderOrder.trans_l hℳ (h n t q ht hq hn) (SecondOrderTriangularBounds.growth_l hℳ hq hv)
    · exact (SecondOrderTriangularArithmetic.unique_l hℳ ht hq).symm ▸
        SecondOrderTriangularBounds.growth_l hℳ hq hv

def sentence_m : Sentence signature_m := Metatheory.Formula.forall_close formula_m

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact (formula_l η).mpr (fun _ _ _ ht hv hn => monotone_l hℳ ht hv hn)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularMonotone
