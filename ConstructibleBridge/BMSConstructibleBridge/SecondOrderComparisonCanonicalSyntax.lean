import BMSConstructibleBridge.SecondOrderComparisonStagePreservation

/-! # 解码比较历史的规范方程

零阶段固定完整基底序，后继满足同一规范步骤，极限是全部前驱比较的
完整并图。方程不含用于传输实数的枚举 f 或共同载体 C，供跨编码一致性
和原对象理论推导使用。下面分别给出纯公式及其原商语义。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonCanonicalSyntax

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (value_m member_m)
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
private abbrev up₄ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up (up t))

def successor_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid J T G a X Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    let b : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there (.there .here)))
    let j := .bvar (.there (.there .here))
    let Y := .bvar (.there .here)
    let P := .bvar .here
    .conj (PowerlessRelativeHierarchySyntax.successor_m b (up₄ a)) <|
      .conj (value_m (up₄ J) j b) <| .conj (value_m (up₄ T) j Y) <|
        .conj (value_m (up₄ G) j P) <|
          SecondOrderCanonicalOrderUniform.step_m (up₄ ω) Y P (up₄ e)
            (up₄ t₁) (up₄ t₂) (up₄ t₃) (up₄ Pair) (up₄ Valid) (up₄ X) (up₄ Q)

def limit_m {Γ Δ : SortContext ℒ} (J T G a Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.limit_m a) <|
    .existsE .set <| .conj (SecondOrderStageLayerFunction.predecessor_m (up a) (up J) (.bvar .here))
      (SecondOrderWellOrderCoherentUnionDerives.graph_m (.bvar .here) (up T) (up G) (up Q))

def branch_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid J T G P₀ a X Q : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (PowerlessRelativeHierarchySyntax.empty_m a) (.equal Q P₀)) <|
    .disj (successor_m ω e t₁ t₂ t₃ Pair Valid J T G a X Q) (limit_m J T G a Q)

def at_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid I J T G P₀ a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let i : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let X := .bvar (.there .here)
    let Q := .bvar .here
    .imp (.conj (SecondOrderWellOrderCoherentUnion.stage_m (up₃ I) (up₃ T) (up₃ G) i X Q)
      (value_m (up₃ J) i (up₃ a))) <|
        branch_m (up₃ ω) (up₃ e) (up₃ t₁) (up₃ t₂) (up₃ t₃) (up₃ Pair)
          (up₃ Valid) (up₃ J) (up₃ T) (up₃ G) (up₃ P₀) (up₃ a) X Q

def history_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid I J T G P₀ A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .imp (member_m (.bvar .here) (up A)) <|
    at_m (up ω) (up e) (up t₁) (up t₂) (up t₃) (up Pair) (up Valid)
      (up I) (up J) (up T) (up G) (up P₀) (.bvar .here)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def successor_l (ω e t₁ t₂ t₃ Pair Valid J T G a X Q : type_l hℳ) : Prop :=
  ∃ b j Y P, PowerlessRelativeHierarchySemantics.successor_l hℳ b a ∧
    value_l (ℳ := 𝒱) J j b ∧ value_l (ℳ := 𝒱) T j Y ∧ value_l (ℳ := 𝒱) G j P ∧
      SecondOrderCanonicalOrderUniform.step_l (ℳ₀ := 𝒱) ω Y P e t₁ t₂ t₃ Pair Valid X Q

def limit_l (J T G a Q : type_l hℳ) : Prop :=
  PowerlessRelativeHierarchySemantics.limit_l hℳ a ∧ ∃ D,
    SecondOrderStageLayerFunction.predecessor_l a J D ∧
      SecondOrderWellOrderCoherentUnion.graph_l (ℳ₀ := 𝒱) D T G Q

def branch_l (ω e t₁ t₂ t₃ Pair Valid J T G P₀ a X Q : type_l hℳ) : Prop :=
  (PowerlessRelativeHierarchySemantics.empty_l hℳ a ∧ Q = P₀) ∨
    successor_l ω e t₁ t₂ t₃ Pair Valid J T G a X Q ∨ limit_l J T G a Q

def at_l (ω e t₁ t₂ t₃ Pair Valid I J T G P₀ a : type_l hℳ) : Prop :=
  ∀ i X Q, SecondOrderWellOrderCoherentUnion.stage_l (ℳ₀ := 𝒱) I T G i X Q ∧
    value_l (ℳ := 𝒱) J i a → branch_l ω e t₁ t₂ t₃ Pair Valid J T G P₀ a X Q

def history_l (ω e t₁ t₂ t₃ Pair Valid I J T G P₀ A : type_l hℳ) : Prop :=
  ∀ a, mem_l hℳ a A → at_l ω e t₁ t₂ t₃ Pair Valid I J T G P₀ a

theorem successor_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid J T G a X Q : Term ℒ Γ Δ .set) :
    (successor_m ω e t₁ t₂ t₃ Pair Valid J T G a X Q).satisfies η ↔
      successor_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (Pair.eval η) (Valid.eval η) (J.eval η) (T.eval η) (G.eval η) (a.eval η) (X.eval η) (Q.eval η) := by
  simp only [successor_m, successor_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.successor_formula_l, value_formula_l,
    SecondOrderCanonicalOrderUniform.step_formula_l, up₄, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem limit_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (J T G a Q : Term ℒ Γ Δ .set) :
    (limit_m J T G a Q).satisfies η ↔ limit_l (J.eval η) (T.eval η) (G.eval η) (a.eval η) (Q.eval η) := by
  simp only [limit_m, limit_l, Formula.satisfies, PowerlessRelativeHierarchySemantics.limit_formula_l,
    SecondOrderStageLayerFunction.predecessor_formula_l, SecondOrderWellOrderCoherentUnionDerives.graph_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem branch_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid J T G P₀ a X Q : Term ℒ Γ Δ .set) :
    (branch_m ω e t₁ t₂ t₃ Pair Valid J T G P₀ a X Q).satisfies η ↔
      branch_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (Pair.eval η) (Valid.eval η) (J.eval η) (T.eval η) (G.eval η) (P₀.eval η)
        (a.eval η) (X.eval η) (Q.eval η) := by
  simp only [branch_m, branch_l, Formula.satisfies, PowerlessRelativeHierarchySemantics.empty_formula_l,
    successor_formula_l, limit_formula_l]

theorem at_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid I J T G P₀ a : Term ℒ Γ Δ .set) :
    (at_m ω e t₁ t₂ t₃ Pair Valid I J T G P₀ a).satisfies η ↔
      at_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (I.eval η) (J.eval η) (T.eval η) (G.eval η) (P₀.eval η) (a.eval η) := by
  simp only [at_m, at_l, Formula.satisfies, SecondOrderWellOrderCoherentUnion.stage_formula_l,
    value_formula_l, branch_formula_l, up₃, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem history_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid I J T G P₀ A : Term ℒ Γ Δ .set) :
    (history_m ω e t₁ t₂ t₃ Pair Valid I J T G P₀ A).satisfies η ↔
      history_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (I.eval η) (J.eval η) (T.eval η) (G.eval η) (P₀.eval η) (A.eval η) := by
  simp only [history_m, history_l, Formula.satisfies, member_m, at_formula_l,
    up, Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms branch_formula_l
#print axioms history_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonCanonicalSyntax
