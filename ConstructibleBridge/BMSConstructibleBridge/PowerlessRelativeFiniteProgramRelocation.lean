import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAlphabet
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 实际指令的父坐标重编号

常量不变，调用的一个父坐标及配对的两个父坐标沿给定 ω 自映射移动。
三标签互异保证原指令解析唯一；新坐标来自同一实际映射图的读数。
这里不抽取 Type 层重编号函数；给出原关系 AST、合法输出存在性及唯一性，
供有限词重编号的对象推导和后续执行读数保持消费。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRelocation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)
private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up₃ (up₃ t)

def formula_m {Γ Δ : SortContext ℒ} (C ω A t₀ t₁ t₂ q r : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up C)) <|
      .conj (SecondOrderObjectSyntax.ordered_m (up t₀) (.bvar .here) (up q)) (.equal (up r) (up q))) <|
    .disj (.existsE .set <| .existsE .set <|
      .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up₂ ω)) <|
        .conj (SecondOrderObjectSyntax.value_m (up₂ A) (.bvar (.there .here)) (.bvar .here)) <|
          .conj (SecondOrderObjectSyntax.ordered_m (up₂ t₁) (.bvar (.there .here)) (up₂ q))
            (SecondOrderObjectSyntax.ordered_m (up₂ t₁) (.bvar .here) (up₂ r))) <|
      .existsE .set <| .existsE .set <| .existsE .set <|
        .existsE .set <| .existsE .set <| .existsE .set <|
          let k : Term ℒ (.set :: .set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there (.there (.there .here)))))
          let l := .bvar (.there (.there (.there (.there .here))))
          let p := .bvar (.there (.there (.there .here)))
          let i := .bvar (.there (.there .here))
          let j := .bvar (.there .here)
          let s := .bvar .here
          .conj (SecondOrderObjectSyntax.member_m k (up₆ ω)) <|
            .conj (SecondOrderObjectSyntax.member_m l (up₆ ω)) <|
              .conj (SecondOrderObjectSyntax.ordered_m k l p) <|
                .conj (SecondOrderObjectSyntax.ordered_m (up₆ t₂) p (up₆ q)) <|
                  .conj (SecondOrderObjectSyntax.value_m (up₆ A) k i) <|
                    .conj (SecondOrderObjectSyntax.value_m (up₆ A) l j) <|
                      .conj (SecondOrderObjectSyntax.ordered_m i j s)
                        (SecondOrderObjectSyntax.ordered_m (up₆ t₂) s (up₆ r))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def relation_l (C ω A t₀ t₁ t₂ q r : type_l hℳ) : Prop :=
  (∃ a, mem_l hℳ a C ∧ ordered_l (ℳ := 𝒱) t₀ a q ∧ r = q) ∨
    (∃ k i, mem_l hℳ k ω ∧ value_l (ℳ := 𝒱) A k i ∧
      ordered_l (ℳ := 𝒱) t₁ k q ∧ ordered_l (ℳ := 𝒱) t₁ i r) ∨
      ∃ k l p i j s, mem_l hℳ k ω ∧ mem_l hℳ l ω ∧ ordered_l (ℳ := 𝒱) k l p ∧
        ordered_l (ℳ := 𝒱) t₂ p q ∧ value_l (ℳ := 𝒱) A k i ∧ value_l (ℳ := 𝒱) A l j ∧
          ordered_l (ℳ := 𝒱) i j s ∧ ordered_l (ℳ := 𝒱) t₂ s r

theorem formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (C ω A t₀ t₁ t₂ q r : Term ℒ Γ Δ .set) :
    (formula_m C ω A t₀ t₁ t₂ q r).satisfies η ↔ relation_l
      (C.eval η) (ω.eval η) (A.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) (r.eval η) := by
  simp only [formula_m, relation_l, Formula.satisfies, ordered_formula_l, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₆, up₃, up₂, up,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem constant_l {C ω A t₀ t₁ t₂ a q r : type_l hℳ}
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂) (ha : mem_l hℳ a C)
    (hq : ordered_l (ℳ := 𝒱) t₀ a q) : relation_l C ω A t₀ t₁ t₂ q r ↔ r = q := by
  constructor
  · rintro (⟨_, _, _, hr⟩ | ⟨_, _, _, _, hq', _⟩ | ⟨_, _, _, _, _, _, _, _, _, hq', _⟩)
    · exact hr
    · exact (hTags.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1).elim
    · exact (hTags.2.1 ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1).elim
  · intro hr
    exact Or.inl ⟨a, ha, hq, hr⟩

theorem call_l {C ω A t₀ t₁ t₂ k q r : type_l hℳ}
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂) (hk : mem_l hℳ k ω)
    (hq : ordered_l (ℳ := 𝒱) t₁ k q) : relation_l C ω A t₀ t₁ t₂ q r ↔
      ∃ i, value_l (ℳ := 𝒱) A k i ∧ ordered_l (ℳ := 𝒱) t₁ i r := by
  constructor
  · rintro (⟨_, _, hq', _⟩ | ⟨k', i, _, hi, hq', hr⟩ |
      ⟨_, _, _, _, _, _, _, _, _, hq', _⟩)
    · exact (hTags.1 (((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1.symm)).elim
    · have hEq := ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).2
      subst k'
      exact ⟨i, hi, hr⟩
    · exact (hTags.2.2 ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1).elim
  · rintro ⟨i, hi, hr⟩
    exact Or.inr (Or.inl ⟨k, i, hk, hi, hq, hr⟩)

theorem pair_l {C ω A t₀ t₁ t₂ k l p q r : type_l hℳ}
    (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂) (hk : mem_l hℳ k ω) (hl : mem_l hℳ l ω)
    (hp : ordered_l (ℳ := 𝒱) k l p) (hq : ordered_l (ℳ := 𝒱) t₂ p q) :
    relation_l C ω A t₀ t₁ t₂ q r ↔ ∃ i j s,
      value_l (ℳ := 𝒱) A k i ∧ value_l (ℳ := 𝒱) A l j ∧
        ordered_l (ℳ := 𝒱) i j s ∧ ordered_l (ℳ := 𝒱) t₂ s r := by
  constructor
  · rintro (⟨_, _, hq', _⟩ | ⟨_, _, _, _, hq', _⟩ |
      ⟨k', l', p', i, j, s, _, _, hp', hq', hi, hj, hs, hr⟩)
    · exact (hTags.2.1 (((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1.symm)).elim
    · exact (hTags.2.2 (((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).1.symm)).elim
    · have hpp := ((SecondOrderPairObjects.ordered_eq_l hℳ hq hq').mp rfl).2
      subst p'
      obtain ⟨hkk, hll⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hp hp').mp rfl
      subst k'
      subst l'
      exact ⟨i, j, s, hi, hj, hs, hr⟩
  · rintro ⟨i, j, s, hi, hj, hs, hr⟩
    exact Or.inr (Or.inr ⟨k, l, p, i, j, s, hk, hl, hp, hq, hi, hj, hs, hr⟩)

theorem unique_l {C ω A t₀ t₁ t₂ q r s : type_l hℳ}
    (hMap : map_l (ℳ := 𝒱) A ω ω) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hr : relation_l C ω A t₀ t₁ t₂ q r) (hs : relation_l C ω A t₀ t₁ t₂ q s) : r = s := by
  rcases hr with ⟨a, ha, hq, hr⟩ | ⟨k, i, hk, hi, hq, hr⟩ |
    ⟨k, l, p, i, j, v, hk, hl, hp, hq, hi, hj, hv, hr⟩
  · exact hr.trans ((constant_l hTags ha hq).mp hs).symm
  · obtain ⟨i', hi', hs⟩ := (call_l hTags hk hq).mp hs
    have hEq := SecondOrderFunctionProperties.value_unique_l hℳ hMap hi hi'
    subst i'
    exact SecondOrderPairObjects.ordered_unique_l hℳ hr hs
  · obtain ⟨i', j', v', hi', hj', hv', hs⟩ := (pair_l hTags hk hl hp hq).mp hs
    have hiEq := SecondOrderFunctionProperties.value_unique_l hℳ hMap hi hi'
    have hjEq := SecondOrderFunctionProperties.value_unique_l hℳ hMap hj hj'
    subst i'
    subst j'
    have hvEq := SecondOrderPairObjects.ordered_unique_l hℳ hv hv'
    subst v'
    exact SecondOrderPairObjects.ordered_unique_l hℳ hr hs

theorem exists_l {C ω A t₀ t₁ t₂ q : type_l hℳ}
    (hMap : map_l (ℳ := 𝒱) A ω ω)
    (hq : PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ q) :
    ∃ r, PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ r ∧
      relation_l C ω A t₀ t₁ t₂ q r := by
  rcases hq with ⟨a, ha, hq⟩ | ⟨k, hk, hq⟩ | ⟨k, l, p, hk, hl, hp, hq⟩
  · exact ⟨q, Or.inl ⟨a, ha, hq⟩, Or.inl ⟨a, ha, hq, rfl⟩⟩
  · obtain ⟨i, hi, _⟩ := hMap.2 k hk
    obtain ⟨r, hr⟩ := SecondOrderPairObjects.ordered_exists_l hℳ t₁ i
    exact ⟨r, Or.inr (Or.inl ⟨i, hi.1, hr⟩), Or.inr (Or.inl ⟨k, i, hk, hi.2, hq, hr⟩)⟩
  · obtain ⟨i, hi, _⟩ := hMap.2 k hk
    obtain ⟨j, hj, _⟩ := hMap.2 l hl
    obtain ⟨s, hs⟩ := SecondOrderPairObjects.ordered_exists_l hℳ i j
    obtain ⟨r, hr⟩ := SecondOrderPairObjects.ordered_exists_l hℳ t₂ s
    exact ⟨r, Or.inr (Or.inr ⟨i, j, s, hi.1, hj.1, hs, hr⟩),
      Or.inr (Or.inr ⟨k, l, p, i, j, s, hk, hl, hp, hq, hi.2, hj.2, hs, hr⟩)⟩

/-- 任意实际重编号见证都给出合法输出，不只限于存在性定理所构造的输出。 -/
theorem range_l {C ω A t₀ t₁ t₂ q r : type_l hℳ}
    (hMap : map_l (ℳ := 𝒱) A ω ω) (hr : relation_l C ω A t₀ t₁ t₂ q r) :
    PowerlessRelativeFiniteProgramAlphabet.instruction_l C ω t₀ t₁ t₂ r := by
  rcases hr with ⟨a, ha, hq, rfl⟩ | ⟨k, i, _, hi, _, hr⟩ |
    ⟨k, l, _, i, j, s, _, _, _, _, hi, hj, hs, hr⟩
  · exact Or.inl ⟨a, ha, hq⟩
  · exact Or.inr (Or.inl ⟨i, (SecondOrderFunctionProperties.value_mem_l hℳ hMap hi).2, hr⟩)
  · exact Or.inr (Or.inr ⟨i, j, s,
      (SecondOrderFunctionProperties.value_mem_l hℳ hMap hi).2,
      (SecondOrderFunctionProperties.value_mem_l hℳ hMap hj).2, hs, hr⟩)

#print axioms formula_l
#print axioms unique_l
#print axioms exists_l
#print axioms range_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramRelocation
