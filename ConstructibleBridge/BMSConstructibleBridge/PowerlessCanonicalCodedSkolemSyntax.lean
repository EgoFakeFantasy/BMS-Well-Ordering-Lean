import BMSConstructibleBridge.PowerlessCanonicalCodedEdgeSyntax
import BMSConstructibleBridge.PowerlessSourceOpening

/-! # 完整覆盖比较下的关系式最小见证算子

纯隶属 ℒ 的通用矩阵，在实际 Class 结构中使用全部域内候选。
请求正文、原参数和槽序保持不变；无候选分支返回 B，但不冒充请求见证。
本模块只有 AST 和精确读数，不能据此声称原程序算子已替换或总性已证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalCodedSkolemSyntax

open Logic FirstOrder ThirdOrderSemantics
open PowerlessBMSQuotientSubsetImageDerives
  (at_m at_formula_l parameters_l parameters_pushBound_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def relation_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω P₀ x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (at_m φ x y) <| .forallE .set <|
    .imp (at_m φ (up x) (.bvar .here)) <|
      .neg (PowerlessCanonicalCodedEdgeSyntax.edge_m (up B) (up ω) (up P₀) (.bvar .here) (up y)))
    (.conj (.neg (.existsE .set (at_m φ (up x) (.bvar .here)))) (.equal y B))

def relation_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 [] Δ)
    (B ω P₀ x y : carrier_l 𝒩) : Prop :=
  (φ.satisfies ((η.pushFree x).pushFree y) ∧ ∀ z,
    φ.satisfies ((η.pushFree x).pushFree z) →
      ¬PowerlessCanonicalCodedEdgeSyntax.edge_l B ω P₀ z y) ∨
  (¬∃ z, φ.satisfies ((η.pushFree x).pushFree z)) ∧ y = B

theorem relation_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B ω P₀ x y : Term ℒ Γ Δ .set) :
    (relation_m φ B ω P₀ x y).satisfies η ↔
      relation_l φ (parameters_l η) (B.eval η) (ω.eval η) (P₀.eval η) (x.eval η) (y.eval η) := by
  simp only [relation_m, relation_l, Formula.satisfies, at_formula_l,
    PowerlessCanonicalCodedEdgeSyntax.edge_formula_l hExt, parameters_pushBound_l,
    up, Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here]

/-- 与原有限程序相同的输出／输入首两槽及原参数尾部，不选择输出数据。 -/
def operator_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω P₀ : Term ℒ Γ Δ .set) :
    Formula ℒ [] (.set :: .set :: (List.replicate Γ.length .set ++ Δ)) :=
  PowerlessSourceOpening.form_m <| relation_m φ (up₂ B) (up₂ ω) (up₂ P₀)
    (.bvar (.there .here)) (.bvar .here)

theorem operator_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B ω P₀ : Term ℒ Γ Δ .set) (x y : carrier_l 𝒩) :
    (operator_m φ B ω P₀).satisfies
      (((PowerlessSourceOpening.env_l η).pushFree x).pushFree y) ↔
      relation_l φ (parameters_l η) (B.eval η) (ω.eval η) (P₀.eval η) x y := by
  have h := PowerlessSourceOpening.formula_l
    (relation_m φ (up₂ B) (up₂ ω) (up₂ P₀) (.bvar (.there .here)) (.bvar .here))
    ((η.pushBound x).pushBound y)
  simpa only [operator_m, PowerlessSourceOpening.push_l, relation_formula_l hExt,
    parameters_pushBound_l, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there] using h

/-- 全部类内输入的关系式总唯一性；不返回 Type 层选择函数。 -/
def conclusion_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω P₀ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .existsE .set <| .conj
    (relation_m φ (up₂ B) (up₂ ω) (up₂ P₀) (.bvar (.there .here)) (.bvar .here)) <|
    .forallE .set <| .imp
      (relation_m φ (up (up₂ B)) (up (up₂ ω)) (up (up₂ P₀))
        (.bvar (.there (.there .here))) (.bvar .here))
      (.equal (.bvar .here) (.bvar (.there .here)))

theorem conclusion_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩))
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B ω P₀ : Term ℒ Γ Δ .set) :
    (conclusion_m φ B ω P₀).satisfies η ↔ ∀ x, ∃ y,
      relation_l φ (parameters_l η) (B.eval η) (ω.eval η) (P₀.eval η) x y ∧
      ∀ z, relation_l φ (parameters_l η) (B.eval η) (ω.eval η) (P₀.eval η) x z → z = y := by
  simp only [conclusion_m, Formula.satisfies, relation_formula_l hExt,
    parameters_pushBound_l, up₂, up, Term.eval_weakenBound, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]

#print axioms relation_formula_l
#print axioms operator_formula_l
#print axioms conclusion_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalCodedSkolemSyntax
