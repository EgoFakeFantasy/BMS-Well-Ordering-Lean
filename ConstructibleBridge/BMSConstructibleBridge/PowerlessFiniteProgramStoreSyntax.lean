import BMSConstructibleBridge.PowerlessFiniteProgramInstructionSyntax
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramStore

/-! # 同一指令输出的类内精确存储矩阵

纯隶属语言 ℒ，保持原添入方程、函数图和全部取值读数。类内载体已承担
对象资格，不重复 raw Class 原子。这里给出 AST 与读数，原商中的同值
对应另证；不能以此代替完整程序执行或最终良序的对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramStoreSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m map_m)
open SecondOrderFunctionAppendDerives (adjoin_m reading_m)
open PowerlessFiniteProgramInstructionSyntax (computed_m computed_l computed_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def store_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C A D f c t₀ t₁ t₂ q S E g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <|
    .conj (computed_m φ (up B) (up C) (up f) (up t₀) (up t₁) (up t₂) (up q) (.bvar .here)) <|
      .conj (adjoin_m (up A) (up c) (up S)) <|
        .conj (adjoin_m (up D) (.bvar .here) (up E)) <|
          .conj (map_m (up g) (up S) (up E))
            (reading_m (up f) (up c) (.bvar .here) (up g))

def store_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (B C A D f c t₀ t₁ t₂ q S E g : carrier_l 𝒩) : Prop :=
  ∃ y, computed_l φ η B C f t₀ t₁ t₂ q y ∧
    (∀ x, member_l 𝒩 x S ↔ member_l 𝒩 x A ∨ x = c) ∧
      (∀ z, member_l 𝒩 z E ↔ member_l 𝒩 z D ∨ z = y) ∧
        map_l (ℳ := 𝒩) g S E ∧
          ∀ x z, value_l (ℳ := 𝒩) g x z ↔
            value_l (ℳ := 𝒩) f x z ∨ x = c ∧ z = y

theorem store_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C A D f c t₀ t₁ t₂ q S E g : Term ℒ Γ Δ .set) :
    (store_m φ B C A D f c t₀ t₁ t₂ q S E g).satisfies η ↔
      store_l φ (parameters_l η) (B.eval η) (C.eval η) (A.eval η) (D.eval η)
        (f.eval η) (c.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η)
          (S.eval η) (E.eval η) (g.eval η) := by
  simp only [store_m, store_l, Formula.satisfies, computed_formula_l,
    adjoin_m, reading_m, map_formula_l, value_formula_l, parameters_pushBound_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms store_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramStoreSyntax
