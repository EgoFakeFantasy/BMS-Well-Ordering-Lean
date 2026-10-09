import BMSConstructibleBridge.PowerlessRelativeFiniteProgramInstruction

/-! # 类内同一三种有限程序指令的纯矩阵

纯隶属 ℒ 的通用矩阵，保留原常量、算子调用、配对三种标签，
旧存储坐标及无有效输出时返回 B 的分支。域内资格由实际载体承担，
不在 Class 结构中重新解释 raw Class 定义。只有 AST 与语义读数；
与原 raw 指令的对应和完整执行资格必须另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramInstructionSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (ordered_m member_m value_m)
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₅ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ (up₂ t))

def good_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (C f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.existsE .set <| .conj (ordered_m (up t₀) (.bvar .here) (up q)) <|
      .conj (member_m (.bvar .here) (up C)) (.equal (up y) (.bvar .here))) <|
    .disj (.existsE .set <| .existsE .set <|
      .conj (ordered_m (up₂ t₁) (.bvar (.there .here)) (up₂ q)) <|
        .conj (value_m (up₂ f) (.bvar (.there .here)) (.bvar .here))
          (at_m φ (.bvar .here) (up₂ y))) <|
      .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
        let p : Term ℒ (.set :: .set :: .set :: .set :: .set :: Γ) Δ .set :=
          .bvar (.there (.there (.there (.there .here))))
        let k := .bvar (.there (.there (.there .here)))
        let l := .bvar (.there (.there .here))
        let x := .bvar (.there .here)
        let z := .bvar .here
        .conj (ordered_m (up₅ t₂) p (up₅ q)) <|
          .conj (ordered_m k l p) <| .conj (value_m (up₅ f) k x) <|
            .conj (value_m (up₅ f) l z) (ordered_m x z (up₅ y))

def computed_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (good_m φ C f t₀ t₁ t₂ q y) <|
    .conj (.neg (.existsE .set (good_m φ (up C) (up f) (up t₀)
      (up t₁) (up t₂) (up q) (.bvar .here)))) (.equal y B)

def good_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (C f t₀ t₁ t₂ q y : carrier_l 𝒩) : Prop :=
  (∃ a, ordered_l t₀ a q ∧ member_l 𝒩 a C ∧ y = a) ∨
    (∃ k x, ordered_l t₁ k q ∧ value_l f k x ∧ φ.satisfies ((η.pushFree x).pushFree y)) ∨
      ∃ p k l x z, ordered_l t₂ p q ∧ ordered_l k l p ∧
        value_l f k x ∧ value_l f l z ∧ ordered_l x z y

def computed_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (B C f t₀ t₁ t₂ q y : carrier_l 𝒩) : Prop :=
  good_l φ η C f t₀ t₁ t₂ q y ∨ (¬∃ z, good_l φ η C f t₀ t₁ t₂ q z) ∧ y = B

theorem good_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (C f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) :
    (good_m φ C f t₀ t₁ t₂ q y).satisfies η ↔
      good_l φ (parameters_l η) (C.eval η) (f.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) (y.eval η) := by
  simp only [good_m, good_l, Formula.satisfies, ordered_formula_l, value_formula_l,
    at_formula_l, parameters_pushBound_l, member_m, Arguments.eval, up₅, up₂, up,
    Term.eval_weakenBound, Term.eval]
  rfl

theorem computed_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C f t₀ t₁ t₂ q y : Term ℒ Γ Δ .set) :
    (computed_m φ B C f t₀ t₁ t₂ q y).satisfies η ↔
      computed_l φ (parameters_l η) (B.eval η) (C.eval η) (f.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) (y.eval η) := by
  simp only [computed_m, computed_l, Formula.satisfies, good_formula_l,
    parameters_pushBound_l, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms good_formula_l
#print axioms computed_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteProgramInstructionSyntax
