import BMSConstructibleBridge.SecondOrderOmega

/-!
# 内部数集合及数关系值域的自然数对象像

选点实数或关系实数经实际理解和拼接变为商内的 ω 子集。其成员规格涵盖
全部模型数，没有使用集合论替换或外部函数图收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalSubsets

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b) (P : set_l ℳ) :
    ∃ d : SecondOrderQuotient.type_l hℳ, ∀ x, SecondOrderQuotient.mem_l hℳ x d ↔
      ∃ n, mem_l n P ∧ x = SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n) := by
  obtain ⟨D, hD⟩ := SecondOrderGraftSemantics.exists_l hℳ R P
    (fun n _ => SecondOrderNaturalGraph.wf_l hℳ R hR n)
  refine ⟨SecondOrderQuotient.mk_l hℳ D, fun x => ?_⟩
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  refine (hD X).trans (exists_congr (fun n => and_congr Iff.rfl ?_))
  exact (SecondOrderQuotient.eq_iff_l hℳ X (SecondOrderNaturalGraph.code_l hℳ R hR n)).symm

theorem range_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b) (X : set_l ℳ) :
    ∃ d : SecondOrderQuotient.type_l hℳ, ∀ x, SecondOrderQuotient.mem_l hℳ x d ↔
      ∃ i n, relation_l X i n ∧
        x = SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n) := by
  let φ : Formula signature_m [] [.num, .set] :=
    .existsE .num (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar .here) (.fvar .here))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl) ((Env.empty (M := ℳ)).pushFree X)
  have h₀ : ∀ n, mem_l n P ↔ ∃ i, relation_l X i n := by
    intro n
    refine (hP n).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    rfl
  obtain ⟨d, hd⟩ := exists_l hℳ R hR P
  refine ⟨d, fun x => (hd x).trans ?_⟩
  constructor
  · rintro ⟨n, hn, h⟩
    obtain ⟨i, hi⟩ := (h₀ n).mp hn
    exact ⟨i, n, hi, h⟩
  · rintro ⟨i, n, hi, h⟩
    exact ⟨n, (h₀ n).mpr ⟨i, hi⟩, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalSubsets
