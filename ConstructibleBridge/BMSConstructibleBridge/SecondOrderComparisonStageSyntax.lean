import BMSConstructibleBridge.SecondOrderComparisonSuccessorSyntax
import BMSConstructibleBridge.SecondOrderComparisonLimitSyntax
import BMSConstructibleBridge.SecondOrderStageLayerFunction
import BMSConstructibleBridge.PowerlessRelativeHierarchyStep

/-! # 实际层次上的零、后继与极限比较行

J 将指标接到阶段，T 读取该阶段的实际层。后继仅读取唯一前驱的比较行，
极限只读取 J 拉回的前驱域；域外指标输出空集。所有分支均为纯隶属公式，
没有额外的历史良序守卫，后续可以用于原二阶递归的任意候选历史。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStageSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (empty_l successor_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def successor_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid J T G f a X W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .existsE .set <| .existsE .set <|
    .conj (PowerlessRelativeHierarchySyntax.successor_m (.bvar (.there (.there .here))) (up (up (up a)))) <|
      .conj (SecondOrderObjectSyntax.value_m (up (up (up J))) (.bvar (.there .here)) (.bvar (.there (.there .here)))) <|
        .conj (SecondOrderObjectSyntax.value_m (up (up (up T))) (.bvar (.there .here)) (.bvar .here))
          (SecondOrderComparisonSuccessorSyntax.output_m (up (up (up ω))) (.bvar .here)
            (up (up (up G))) (.bvar (.there .here)) (up (up (up e))) (up (up (up t₁)))
            (up (up (up t₂))) (up (up (up t₃))) (up (up (up Pair))) (up (up (up Valid)))
            (up (up (up X))) (up (up (up f))) (up (up (up W))))

def limit_m {Γ Δ : SortContext ℒ}
    (ω e J T G f a W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelativeHierarchySyntax.limit_m a) <|
    .existsE .set <| .conj (SecondOrderStageLayerFunction.predecessor_m (up a) (up J) (.bvar .here))
      (SecondOrderComparisonLimitSyntax.output_m (up ω) (up e) (.bvar .here) (up T) (up G) (up f) (up W))

def branch_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid J T G P₀ f a X W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (PowerlessRelativeHierarchySyntax.empty_m a)
    (SecondOrderComparisonEncodeSyntax.formula_m ω e W f P₀)) <|
      .disj (successor_m ω e t₁ t₂ t₃ Pair Valid J T G f a X W)
        (limit_m ω e J T G f a W)

def output_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ Pair Valid I J T G P₀ f i W : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (SecondOrderObjectSyntax.member_m i I) <|
    .existsE .set <| .existsE .set <|
      .conj (SecondOrderObjectSyntax.value_m (up (up J)) (up (up i)) (.bvar (.there .here))) <|
        .conj (SecondOrderObjectSyntax.value_m (up (up T)) (up (up i)) (.bvar .here))
          (branch_m (up (up ω)) (up (up e)) (up (up t₁)) (up (up t₂)) (up (up t₃))
            (up (up Pair)) (up (up Valid)) (up (up J)) (up (up T)) (up (up G))
            (up (up P₀)) (up (up f)) (.bvar (.there .here)) (.bvar .here) (up (up W))))
    (.conj (.neg (SecondOrderObjectSyntax.member_m i I)) (.equal W e))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def successor_l (ω e t₁ t₂ t₃ Pair Valid J T G f a X W : type_l hℳ) : Prop :=
  ∃ b j Y, PowerlessRelativeHierarchySemantics.successor_l hℳ b a ∧
    value_l (ℳ := 𝒱) J j b ∧ value_l (ℳ := 𝒱) T j Y ∧
      SecondOrderComparisonSuccessorSyntax.output_l (𝒩 := 𝒱) ω Y G j e t₁ t₂ t₃ Pair Valid X f W

def limit_l (ω e J T G f a W : type_l hℳ) : Prop :=
  PowerlessRelativeHierarchySemantics.limit_l hℳ a ∧ ∃ D,
    SecondOrderStageLayerFunction.predecessor_l a J D ∧
      SecondOrderComparisonLimitSyntax.output_l (𝒩 := 𝒱) ω e D T G f W

def branch_l (ω e t₁ t₂ t₃ Pair Valid J T G P₀ f a X W : type_l hℳ) : Prop :=
  (empty_l hℳ a ∧ SecondOrderComparisonEncodeSyntax.encoded_l (𝒩 := 𝒱) ω e W f P₀) ∨
    successor_l ω e t₁ t₂ t₃ Pair Valid J T G f a X W ∨ limit_l ω e J T G f a W

def output_l (ω e t₁ t₂ t₃ Pair Valid I J T G P₀ f i W : type_l hℳ) : Prop :=
  (mem_l hℳ i I ∧ ∃ a X, value_l (ℳ := 𝒱) J i a ∧ value_l (ℳ := 𝒱) T i X ∧
    branch_l ω e t₁ t₂ t₃ Pair Valid J T G P₀ f a X W) ∨ (¬mem_l hℳ i I ∧ W = e)

theorem successor_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid J T G f a X W : Term ℒ Γ Δ .set) :
    (successor_m ω e t₁ t₂ t₃ Pair Valid J T G f a X W).satisfies η ↔
      successor_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (J.eval η) (T.eval η) (G.eval η) (f.eval η) (a.eval η) (X.eval η) (W.eval η) := by
  simp only [successor_m, successor_l, Formula.satisfies, PowerlessRelativeHierarchySemantics.successor_formula_l,
    ThirdOrderSemantics.value_formula_l, SecondOrderComparisonSuccessorSyntax.output_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem limit_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e J T G f a W : Term ℒ Γ Δ .set) :
    (limit_m ω e J T G f a W).satisfies η ↔
      limit_l (ω.eval η) (e.eval η) (J.eval η) (T.eval η) (G.eval η) (f.eval η) (a.eval η) (W.eval η) := by
  simp only [limit_m, limit_l, Formula.satisfies, PowerlessRelativeHierarchySemantics.limit_formula_l,
    SecondOrderStageLayerFunction.predecessor_formula_l, SecondOrderComparisonLimitSyntax.output_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem branch_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid J T G P₀ f a X W : Term ℒ Γ Δ .set) :
    (branch_m ω e t₁ t₂ t₃ Pair Valid J T G P₀ f a X W).satisfies η ↔
      branch_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (J.eval η) (T.eval η) (G.eval η) (P₀.eval η) (f.eval η) (a.eval η) (X.eval η) (W.eval η) := by
  simp only [branch_m, branch_l, Formula.satisfies, PowerlessRelativeHierarchySemantics.empty_formula_l,
    SecondOrderComparisonEncodeSyntax.formula_l, successor_formula_l, limit_formula_l]

theorem output_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω e t₁ t₂ t₃ Pair Valid I J T G P₀ f i W : Term ℒ Γ Δ .set) :
    (output_m ω e t₁ t₂ t₃ Pair Valid I J T G P₀ f i W).satisfies η ↔
      output_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η) (Pair.eval η)
        (Valid.eval η) (I.eval η) (J.eval η) (T.eval η) (G.eval η) (P₀.eval η) (f.eval η) (i.eval η) (W.eval η) := by
  simp only [output_m, output_l, Formula.satisfies, ThirdOrderSemantics.value_formula_l,
    branch_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms output_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderComparisonStageSyntax
