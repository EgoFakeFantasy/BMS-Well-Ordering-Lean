import BMSConstructibleBridge.SecondOrderTriangularBounds

/-! # 原三角配数的内部坐标界

保留 c=T(a+b)+a，使用关系式三角数，不选取 Type 层函数。
全部数可以是非标准内部数；存在唯一性与坐标界一起回到原 Z₂ 闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularPairing

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel SecondOrderNumbers

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def code_l (a b c : num_l ℳ) : Prop :=
  ∃ t, SecondOrderTriangularArithmetic.relation_l (add_l a b) t ∧ c = add_l t a

def code_m {Γ Δ : SortContext signature_m} (a b c : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .existsE .num <| .conj
    (SecondOrderTriangularArithmetic.relation_m
      (Term.app (σ := signature_m) .add
        (.cons (a.weakenBound sort_m.num) (.cons (b.weakenBound sort_m.num) .nil))) (.bvar .here))
    (.equal (c.weakenBound sort_m.num)
      (Term.app (σ := signature_m) .add (.cons (.bvar .here) (.cons (a.weakenBound sort_m.num) .nil))))

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (a b c : Term signature_m Γ Δ .num) :
    (code_m a b c).satisfies η ↔ code_l (a.eval η) (b.eval η) (c.eval η) := by
  simp only [code_m, code_l, Formula.satisfies,
    SecondOrderTriangularArithmetic.relation_formula_l, Term.eval, Arguments.eval,
    Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (a b : num_l ℳ) : ∃ c, code_l a b c := by
  obtain ⟨t, ht⟩ := SecondOrderTriangularArithmetic.exists_l hℳ (add_l a b)
  exact ⟨add_l t a, t, ht, rfl⟩

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {a b c d : num_l ℳ}
    (hc : code_l a b c) (hd : code_l a b d) : c = d := by
  obtain ⟨t, ht, rfl⟩ := hc
  obtain ⟨v, hv, rfl⟩ := hd
  exact congrArg (fun x => add_l x a) (SecondOrderTriangularArithmetic.unique_l hℳ ht hv)

theorem addition_lower_l (hℳ : Theory.Models ℳ theory_m) (a b : num_l ℳ) :
    a = add_l a b ∨ SecondOrderOrder.lt_l a (add_l a b) := by
  rcases predecessor_l hℳ b with rfl | ⟨b, rfl⟩
  · exact Or.inl (add_zero_l hℳ a).symm
  · exact Or.inr ⟨b, rfl⟩

theorem trans_l (hℳ : Theory.Models ℳ theory_m) {a b c : num_l ℳ}
    (hab : a = b ∨ SecondOrderOrder.lt_l a b) (hbc : b = c ∨ SecondOrderOrder.lt_l b c) :
    a = c ∨ SecondOrderOrder.lt_l a c := by
  rcases hab with rfl | hab
  · exact hbc
  · rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (SecondOrderOrder.trans_l hℳ hab hbc)

theorem coordinates_l (hℳ : Theory.Models ℳ theory_m) {a b c : num_l ℳ} (hc : code_l a b c) :
    (a = c ∨ SecondOrderOrder.lt_l a c) ∧ (b = c ∨ SecondOrderOrder.lt_l b c) := by
  obtain ⟨t, ht, rfl⟩ := hc
  have hSum := trans_l hℳ (SecondOrderTriangularBounds.lower_l hℳ ht) (addition_lower_l hℳ t a)
  refine ⟨trans_l hℳ (addition_lower_l hℳ a b) hSum, trans_l hℳ ?_ hSum⟩
  simpa only [add_comm_l hℳ b a] using addition_lower_l hℳ b a

def sentence_m : Sentence signature_m := .forallE .num <| .forallE .num <| .existsE .num <|
  let a : Term signature_m [.num, .num, .num] [] .num := .bvar (.there (.there .here))
  let b : Term signature_m [.num, .num, .num] [] .num := .bvar (.there .here)
  let c : Term signature_m [.num, .num, .num] [] .num := .bvar .here
  .conj (code_m a b c) <| .conj
    (.conj (.disj (.equal a c) (PrimitiveFormulas.lt_m a c))
      (.disj (.equal b c) (PrimitiveFormulas.lt_m b c)))
    (.forallE .num <| .imp
      (code_m (a.weakenBound sort_m.num) (b.weakenBound sort_m.num) (.bvar .here))
      (.equal (.bvar .here) (c.weakenBound sort_m.num)))

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies, formula_l,
    SecondOrderOrder.formula_l, Term.eval]
  intro a b
  obtain ⟨c, hc⟩ := exists_l hℳ a b
  exact ⟨c, hc, coordinates_l hℳ hc, fun d hd => unique_l hℳ hd hc⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularPairing
