import BMSConstructibleBridge.SecondOrderSubsetCollection

/-!
# 非空集合的全数域成员代表

已是母根子节点的数保持不变，其余数映到一个指定子节点。选择图由实际
理解产生；指定子节点是显式非空见证，不作额外可数选择。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberNormalizer

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

noncomputable def value_l (R : set_l ℳ) (r a n : num_l ℳ) : num_l ℳ :=
  @ite _ (relation_l R n r) (Classical.propDecidable _) n a

theorem fixed_l (R : set_l ℳ) (r a n : num_l ℳ) (h : relation_l R n r) : value_l R r a n = n := if_pos h

theorem member_l (R : set_l ℳ) (r a : num_l ℳ) (ha : relation_l R a r) (n : num_l ℳ) :
    relation_l R (value_l R r a n) r := by
  classical
  by_cases h : relation_l R n r
  · exact (fixed_l R r a n h).symm ▸ h
  · simpa only [value_l, if_neg h] using ha

def formula_m : Formula signature_m [] [.num, .num, .set, .num, .num] :=
  .disj
    (.conj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there (.there (.there .here)))))
      (.equal (.fvar (.there .here)) (.fvar .here)))
    (.conj (.neg (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there (.there (.there .here))))))
      (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there (.there .here)))))))

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (r a : num_l ℳ) :
    ∃ N : set_l ℳ, ∀ n b, relation_l N n b ↔ b = value_l R r a n := by
  classical
  obtain ⟨N, hN⟩ := SecondOrderRelations.comprehension_l hℳ formula_m (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree a).pushFree r).pushFree R)
  refine ⟨N, fun n b => (hN n b).trans ?_⟩
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l]
  change ((relation_l R n r ∧ b = n) ∨ (¬ relation_l R n r ∧ b = a)) ↔ _
  by_cases h : relation_l R n r <;> simp [value_l, h]

noncomputable def code_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) (n : num_l ℳ) : SecondOrderGraph.code_l ℳ :=
  SecondOrderGraph.child_l hℳ A (value_l A.real A.root a n) (member_l A.real A.root a ha n)

theorem code_mem_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) (n : num_l ℳ) :
    SecondOrderGraph.mem_l (code_l hℳ A a ha n) A :=
  SecondOrderGraph.child_mem_l hℳ A _ (member_l A.real A.root a ha n)

theorem code_fixed_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (a : num_l ℳ) (ha : relation_l A.real a A.root) (n : num_l ℳ) (hn : relation_l A.real n A.root) :
    code_l hℳ A a ha n = SecondOrderGraph.child_l hℳ A n hn := by
  unfold code_l
  simp only [fixed_l A.real A.root a n hn]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberNormalizer
