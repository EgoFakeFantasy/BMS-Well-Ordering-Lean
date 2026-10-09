import BMSConstructibleBridge.PowerlessBMSTransitiveImage

/-!
# 部分可定义类函数的传递值域

非空像时，在 Prop 内固定一个已有输出作为未定义输入的默认值，再使用总
函数版本。空像直接取空集；这不是选择逐输入见证，也不假定类值域为集合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSPartialTransitiveImage

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def insert_m {Γ Δ : SortContext ℒ}
    (x y : Term ℒ Γ (.set :: .set :: .set :: Δ) .set) :
    VariableSubstitution ℒ (.set :: .set :: Δ) Γ (.set :: .set :: .set :: Δ)
  | _, .here => y
  | _, .there .here => x
  | _, .there (.there v) => .fvar (.there (.there (.there v)))

private def at_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (x y : Term ℒ Γ (.set :: .set :: .set :: Δ) .set) :
    Formula ℒ Γ (.set :: .set :: .set :: Δ) :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) Γ (.set :: .set :: .set :: Δ) from
    .map (fun v => nomatch v) (insert_m x y))

/-- 自由槽为输出、输入、默认输出及原参数；只有未定义输入才使用默认输出。 -/
def extend_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  .disj (at_m φ (.fvar (.there .here)) (.fvar .here))
    (.conj (.neg (.existsE .set (at_m φ (.fvar (.there .here)) (.bvar .here))))
      (.equal (.fvar .here) (.fvar (.there (.there .here)))))

theorem extend_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒩 [] Δ) (d n y : 𝒩.Carrier .set) :
    (extend_m φ).satisfies (((η.pushFree d).pushFree n).pushFree y) ↔
      φ.satisfies ((η.pushFree n).pushFree y) ∨
        (¬∃ z, φ.satisfies ((η.pushFree n).pushFree z)) ∧ y = d := by
  simp only [extend_m, Formula.satisfies, Term.eval]
  refine or_congr ?_ (and_congr (not_congr ?_) Iff.rfl)
  · refine (Formula.satisfies_substitute _ _ φ).trans ?_
    apply Iff.of_eq
    apply congrArg (fun η => φ.satisfies η)
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v <;> rfl
  · apply exists_congr
    intro z
    refine (Formula.satisfies_substitute _ _ φ).trans ?_
    apply Iff.of_eq
    apply congrArg (fun η => φ.satisfies η)
    apply Env.ext
    · intro s v
      nomatch v
    · intro s v
      cases v with
      | here => rfl
      | there v => cases v <;> rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem exists_l (C : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env quotient_l [] Δ)
    (hUnique : ∀ n y z,
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree z) → y = z)
    (hTrans : ∀ n y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      ∀ z, SecondOrderQuotient.mem_l hℳ z y →
        ∃ m, φ.satisfies ((η.pushFree (numberCode_l C m).val).pushFree z)) :
    ∃ b : SecondOrderQuotient.type_l hℳ, ∀ y, SecondOrderQuotient.mem_l hℳ y b ↔
      ∃ n, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) := by
  classical
  by_cases hNonempty : ∃ n y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y)
  · obtain ⟨n₀, y₀, hy₀⟩ := hNonempty
    let ψ := extend_m φ
    let ξ : Env quotient_l [] (.set :: Δ) := η.pushFree y₀
    have hEval n y := extend_formula_l φ η y₀ (numberCode_l C n).val y
    have hTotal n : ∃ y, ψ.satisfies ((ξ.pushFree (numberCode_l C n).val).pushFree y) := by
      by_cases h : ∃ y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y)
      · obtain ⟨y, hy⟩ := h
        exact ⟨y, (hEval n y).mpr (Or.inl hy)⟩
      · exact ⟨y₀, (hEval n y₀).mpr (Or.inr ⟨h, rfl⟩)⟩
    have hUnique' n y z
        (hy : ψ.satisfies ((ξ.pushFree (numberCode_l C n).val).pushFree y))
        (hz : ψ.satisfies ((ξ.pushFree (numberCode_l C n).val).pushFree z)) : y = z := by
      rcases (hEval n y).mp hy with hy | ⟨hNone, rfl⟩
      · rcases (hEval n z).mp hz with hz | ⟨hz, _⟩
        · exact hUnique n y z hy hz
        · exact (hz ⟨y, hy⟩).elim
      · rcases (hEval n z).mp hz with hz | ⟨_, rfl⟩
        · exact (hNone ⟨z, hz⟩).elim
        · rfl
    have hOriginal n y (hy : ψ.satisfies ((ξ.pushFree (numberCode_l C n).val).pushFree y)) :
        ∃ m, φ.satisfies ((η.pushFree (numberCode_l C m).val).pushFree y) := by
      rcases (hEval n y).mp hy with hy | ⟨_, rfl⟩
      · exact ⟨n, hy⟩
      · exact ⟨n₀, hy₀⟩
    have hTrans' n y (hy : ψ.satisfies ((ξ.pushFree (numberCode_l C n).val).pushFree y))
        z (hz : SecondOrderQuotient.mem_l hℳ z y) :
        ∃ m, ψ.satisfies ((ξ.pushFree (numberCode_l C m).val).pushFree z) := by
      obtain ⟨k, hk⟩ := hOriginal n y hy
      obtain ⟨m, hm⟩ := hTrans k y hk z hz
      exact ⟨m, (hEval m z).mpr (Or.inl hm)⟩
    obtain ⟨b, hb⟩ := PowerlessBMSTransitiveImage.exists_l C ψ ξ hTotal hUnique' hTrans'
    refine ⟨b, fun y => (hb y).trans ?_⟩
    exact ⟨fun ⟨n, hn⟩ => hOriginal n y hn,
      fun ⟨n, hn⟩ => ⟨n, (hEval n y).mpr (Or.inl hn)⟩⟩
  · obtain ⟨e, he⟩ := SecondOrderQuotient.empty_l hℳ
    refine ⟨e, fun y => ⟨fun hy => (he y hy).elim, ?_⟩⟩
    rintro ⟨n, hn⟩
    exact (hNonempty ⟨n, y, hn⟩).elim

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSPartialTransitiveImage
