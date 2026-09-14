import BMSConstructibleBridge.SecondOrderMinimum

/-!
# 内部对象成员的最小根编号

用一个最大内部双模拟关系实数比较所有根，再取每个成员等价类中最小的母根
子节点编号。选择规格可内部理解，且换码不改变输出、不同对象不共用编号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEnumeration

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (R : set_l ℳ) (r a n : num_l ℳ) : Prop :=
  relation_l R a r ∧ relation_l R n r ∧ SecondOrderBisimulation.eq_l R R a n ∧
    ∀ m, SecondOrderOrder.lt_l m n → relation_l R m r → ¬SecondOrderBisimulation.eq_l R R a m

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (r : num_l ℳ) :
    ∃ S : set_l ℳ, ∀ a n, relation_l S a n ↔ spec_l R r a n := by
  obtain ⟨E, hE⟩ := SecondOrderBisimulation.maximum_l hℳ R R
  let φ : Formula signature_m [] [.num, .num, .num, .set, .set] :=
    .conj (GraphSyntax.edge_m (.fvar (.there (.there (.there .here))))
      (.fvar .here) (.fvar (.there (.there .here))))
      (.conj (GraphSyntax.edge_m (.fvar (.there (.there (.there .here))))
        (.fvar (.there .here)) (.fvar (.there (.there .here))))
        (.conj (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here)))))
          (.fvar .here) (.fvar (.there .here)))
          (.forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar (.there .here)))
            (.imp (GraphSyntax.edge_m (.fvar (.there (.there (.there .here))))
              (.bvar .here) (.fvar (.there (.there .here))))
              (.neg (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here)))))
                (.fvar .here) (.bvar .here))))))))
  obtain ⟨S, hS⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree E).pushFree R).pushFree r)
  refine ⟨S, fun a n => (hS a n).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
  change (relation_l R a r ∧ relation_l R n r ∧ relation_l E a n ∧
    ∀ m, SecondOrderOrder.lt_l m n → relation_l R m r → ¬relation_l E a m) ↔ _
  simp only [hE, spec_l]

theorem total_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (r a : num_l ℳ)
    (ha : relation_l R a r) : ∃ n, spec_l R r a n := by
  obtain ⟨E, hE⟩ := SecondOrderBisimulation.maximum_l hℳ R R
  let φ : Formula signature_m [] [.num, .num, .num, .set, .set] :=
    .conj (GraphSyntax.edge_m (.fvar (.there (.there (.there .here))))
      (.fvar .here) (.fvar (.there (.there .here))))
      (GraphSyntax.edge_m (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there .here)) (.fvar .here))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
    (((((Env.empty (M := ℳ)).pushFree E).pushFree R).pushFree r).pushFree a)
  have h₀ : ∀ n, mem_l n P ↔ relation_l R n r ∧ SecondOrderBisimulation.eq_l R R a n := by
    intro n
    refine (hP n).trans ?_
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
    change (relation_l R n r ∧ relation_l E a n) ↔ _
    rw [hE]
  obtain ⟨n, hn, h⟩ := SecondOrderMinimum.exists_l hℳ P
    ⟨a, (h₀ a).mpr ⟨ha, SecondOrderBisimulation.refl_l hℳ R a⟩⟩
  exact ⟨n, ha, ((h₀ n).mp hn).1, ((h₀ n).mp hn).2,
    fun m hm hr he => h m hm ((h₀ m).mpr ⟨hr, he⟩)⟩

/-- 相同成员的任意两个原根都选到同一最小编号。 -/
theorem congr_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (r a b n m : num_l ℳ)
    (h : SecondOrderBisimulation.eq_l R R a b) (ha : spec_l R r a n) (hb : spec_l R r b m) : n = m := by
  rcases SecondOrderOrder.trichotomy_l hℳ n m with h₁ | h₁ | h₁
  · exact False.elim (hb.2.2.2 n h₁ ha.2.1
      (SecondOrderBisimulation.trans_l hℳ R R R b a n
        (SecondOrderBisimulation.symm_l hℳ R R a b h) ha.2.2.1))
  · exact h₁
  · exact False.elim (ha.2.2.2 m h₁ hb.2.1
      (SecondOrderBisimulation.trans_l hℳ R R R a b m h hb.2.2.1))

theorem eq_iff_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (r a b n m : num_l ℳ)
    (ha : spec_l R r a n) (hb : spec_l R r b m) :
    SecondOrderBisimulation.eq_l R R a b ↔ n = m := by
  refine ⟨fun h => congr_l hℳ R r a b n m h ha hb, ?_⟩
  rintro rfl
  exact SecondOrderBisimulation.trans_l hℳ R R R a n b ha.2.2.1
    (SecondOrderBisimulation.symm_l hℳ R R b n hb.2.2.1)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEnumeration
