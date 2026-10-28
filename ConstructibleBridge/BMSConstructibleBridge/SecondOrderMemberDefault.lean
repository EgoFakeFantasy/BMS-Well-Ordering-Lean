import BMSConstructibleBridge.SecondOrderMinimum

/-! # 原图根的唯一默认成员编号

非空纤维取模型内部最小编号；空纤维取零。结果只作为 Prop 中的唯一存在
证书，不选择模型实数族，也不假定非标准数序在宿主意义下良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefault

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def spec_l (R : set_l ℳ) (r a : num_l ℳ) : Prop :=
  (relation_l R a r ∧ ∀ b, SecondOrderOrder.lt_l b a → ¬relation_l R b r) ∨
    ((∀ b, ¬relation_l R b r) ∧ a = zero_l ℳ)

def formula_m : Formula signature_m [] [.num, .num, .set] :=
  .disj (.conj (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here)))
    (.forallE .num (.imp (PrimitiveFormulas.lt_m (.bvar .here) (.fvar .here))
      (.neg (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar (.there .here)))))))
    (.conj (.forallE .num (.neg
      (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar (.there .here)))))
      (.equal (.fvar .here) (numeral_m 0)))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

theorem formula_l (R : set_l ℳ) (r a : num_l ℳ) : formula_m.satisfies
    ((((Env.empty (M := ℳ)).pushFree R).pushFree r).pushFree a) ↔ spec_l R r a := by
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderOrder.formula_l]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ) (r : num_l ℳ) :
    ∃ a, spec_l R r a := by
  classical
  by_cases h : ∃ a, relation_l R a r
  · let φ : Formula signature_m [] [.num, .num, .set] :=
      GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
    obtain ⟨X, hX⟩ := comprehension_l hℳ φ (pure_language_m _ rfl)
      (((Env.empty (M := ℳ)).pushFree R).pushFree r)
    have hRead a : mem_l a X ↔ relation_l R a r := (hX a).trans (SecondOrderPairing.edge_l _ _ _ _)
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb, hMin⟩ := SecondOrderMinimum.exists_l hℳ X ⟨a, (hRead a).mpr ha⟩
    exact ⟨b, Or.inl ⟨(hRead b).mp hb, fun c hc hd => hMin c hc ((hRead c).mpr hd)⟩⟩
  · exact ⟨zero_l ℳ, Or.inr ⟨fun b hb => h ⟨b, hb⟩, rfl⟩⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {R : set_l ℳ} {r a b : num_l ℳ}
    (ha : spec_l R r a) (hb : spec_l R r b) : a = b := by
  rcases ha with ⟨ha, hMinA⟩ | ⟨hEmpty, rfl⟩
  · rcases hb with ⟨hb, hMinB⟩ | ⟨hEmpty, _⟩
    · rcases SecondOrderOrder.trichotomy_l hℳ a b with h | h | h
      · exact False.elim (hMinB a h ha)
      · exact h
      · exact False.elim (hMinA b h hb)
    · exact False.elim (hEmpty a ha)
  · rcases hb with ⟨hb, _⟩ | ⟨_, rfl⟩
    · exact False.elim (hEmpty b hb)
    · rfl

theorem member_l {R : set_l ℳ} {r a : num_l ℳ} (ha : spec_l R r a)
    (h : ∃ b, relation_l R b r) : relation_l R a r := by
  rcases ha with ⟨ha, _⟩ | ⟨hEmpty, _⟩
  · exact ha
  · obtain ⟨b, hb⟩ := h
    exact False.elim (hEmpty b hb)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberDefault
