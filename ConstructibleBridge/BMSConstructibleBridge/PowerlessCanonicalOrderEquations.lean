import BMSConstructibleBridge.PowerlessCanonicalOrderOrdinalRestriction

/-! # 同一规范比较历史的无枚举递归公式

对象语言为纯隶属 ℒ；公式保留原 Uniform 后继、零值与完整极限成员并。
阶段域和陪域的函数规格由调用端另给，不把 raw 层次中含枚举的 Def
公式直接复制为类内层次。这里是通用 AST 及其逐参数读数，非存在公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderEquations

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m value_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def limit_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (a : carrier_l 𝒩) : Prop :=
  (∃ x, member_l 𝒩 x a) ∧ ∀ x, member_l 𝒩 x a → ∃ y, member_l 𝒩 y a ∧ member_l 𝒩 x y

def union_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (f a X : carrier_l 𝒩) : Prop :=
  ∀ x, member_l 𝒩 x X ↔ ∃ b Y, member_l 𝒩 b a ∧ value_l (ℳ := 𝒩) f b Y ∧ member_l 𝒩 x Y

theorem empty_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (a : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.empty_m a).satisfies η ↔ ∀ x, ¬member_l 𝒩 x (a.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.empty_m, PowerlessRelativeHierarchySyntax.up,
    Formula.satisfies, member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

theorem successor_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (a b : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.successor_m a b).satisfies η ↔
      ∀ x, member_l 𝒩 x (b.eval η) ↔ member_l 𝒩 x (a.eval η) ∨ x = a.eval η := by
  simp only [PowerlessRelativeHierarchySyntax.successor_m, PowerlessRelativeHierarchySyntax.up,
    Formula.satisfies, member_m, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

theorem limit_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (a : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.limit_m a).satisfies η ↔ limit_l (a.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.limit_m, PowerlessRelativeHierarchySyntax.up,
    Formula.satisfies, member_m, Arguments.eval, Term.eval_weakenBound, Term.eval, limit_l]
  rfl

theorem union_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (f a X : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.union_m f a X).satisfies η ↔
      union_l (f.eval η) (a.eval η) (X.eval η) := by
  simp only [PowerlessRelativeHierarchySyntax.union_m, PowerlessRelativeHierarchySyntax.up,
    Formula.satisfies, value_formula_l, member_m, Arguments.eval, Term.eval_weakenBound, Term.eval, union_l]
  rfl

def step_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ f g a X P : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (PowerlessRelativeHierarchySyntax.empty_m a) (.conj (.equal X B) (.equal P P₀))) <|
    .disj (.existsE .set <| .existsE .set <| .existsE .set <|
      .conj (PowerlessRelativeHierarchySyntax.successor_m (.bvar (.there (.there .here))) (up₃ a)) <|
        .conj (value_m (up₃ f) (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
          .conj (value_m (up₃ g) (.bvar (.there (.there .here))) (.bvar .here)) <|
            SecondOrderCanonicalOrderUniform.step_m (up₃ ω) (.bvar (.there .here)) (.bvar .here)
              (up₃ e) (up₃ t₁) (up₃ t₂) (up₃ t₃) (up₃ Pair) (up₃ Valid) (up₃ X) (up₃ P))
      (.conj (PowerlessRelativeHierarchySyntax.limit_m a) <|
        .conj (PowerlessRelativeHierarchySyntax.union_m f a X) (PowerlessRelativeHierarchySyntax.union_m g a P))

def step_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ f g a X P : carrier_l 𝒩) : Prop :=
  ((∀ x, ¬member_l 𝒩 x a) ∧ X = B ∧ P = P₀) ∨
    (∃ b Y Q, (∀ x, member_l 𝒩 x a ↔ member_l 𝒩 x b ∨ x = b) ∧
      value_l (ℳ := 𝒩) f b Y ∧ value_l (ℳ := 𝒩) g b Q ∧
      SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒩) ω Y Q e t₁ t₂ t₃ Pair Valid X P) ∨
    (limit_l a ∧ union_l f a X ∧ union_l g a P)

theorem step_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ f g a X P : Term ℒ Γ Δ .set) :
    (step_m ω e t₁ t₂ t₃ Pair Valid B P₀ f g a X P).satisfies η ↔
      step_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) (f.eval η)
        (g.eval η) (a.eval η) (X.eval η) (P.eval η) := by
  simp only [step_m, step_l, Formula.satisfies, empty_formula_l, successor_formula_l,
    value_formula_l, SecondOrderCanonicalOrderUniform.step_formula_l, limit_formula_l,
    union_formula_l, up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ f g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <| .imp
    (value_m (up₃ f) (.bvar (.there (.there .here))) (.bvar (.there .here))) <| .imp
    (value_m (up₃ g) (.bvar (.there (.there .here))) (.bvar .here)) <|
      step_m (up₃ ω) (up₃ e) (up₃ t₁) (up₃ t₂) (up₃ t₃) (up₃ Pair) (up₃ Valid)
        (up₃ B) (up₃ P₀) (up₃ f) (up₃ g)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e t₁ t₂ t₃ Pair Valid B P₀ f g : carrier_l 𝒩) : Prop :=
  ∀ a X P, value_l (ℳ := 𝒩) f a X → value_l (ℳ := 𝒩) g a P →
    step_l ω e t₁ t₂ t₃ Pair Valid B P₀ f g a X P

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid B P₀ f g : Term ℒ Γ Δ .set) :
    (formula_m ω e t₁ t₂ t₃ Pair Valid B P₀ f g).satisfies η ↔
      holds_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (Pair.eval η) (Valid.eval η) (B.eval η) (P₀.eval η) (f.eval η) (g.eval η) := by
  simp only [formula_m, holds_l, Formula.satisfies, value_formula_l, step_formula_l,
    up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 原 raw 方程与此无枚举公式的读数严格相同。 -/
theorem raw_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    (t₁ t₂ t₃ Pair Valid B P₀ f g : SecondOrderQuotient.type_l hℳ) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) K.omega
      (PowerlessBMSQuotientCoding.numberCode_l K (SecondOrderModel.zero_l ℳ)).val
      t₁ t₂ t₃ Pair Valid B P₀ f g ↔
    PowerlessCanonicalOrderOrdinalRestriction.equations_l K t₁ t₂ t₃ Pair Valid B P₀ f g := Iff.rfl

#print axioms formula_l
#print axioms raw_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderEquations
