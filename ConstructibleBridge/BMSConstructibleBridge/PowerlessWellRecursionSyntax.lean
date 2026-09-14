import BMSConstructibleBridge.PowerlessHistory

/-!
# 依赖前驱图的内部递归公式

原算子 φ 的自由槽为新值、前驱图、当前点及原参数。
解方程和含端点初段的局部解均在同一个纯语言中表示。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionSyntax

open Logic FirstOrder ThirdOrderSemantics PowerlessInitialSegment

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def rule_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (x H y : carrier_l ℳ) : Prop :=
  φ.satisfies ((((PowerlessComprehension.env_l η).pushFree x).pushFree H).pushFree y)

def solution_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f R : carrier_l ℳ) : Prop :=
  ∀ x y, value_l f x y → ∃ H, PowerlessHistory.history_l H f R x ∧ rule_l φ η x H y

def solution_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: Γ) :=
  let σ : Substitution ℒ [] (.set :: .set :: .set :: Γ) [.set, .set, .set] (.set :: .set :: Γ) :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .bvar (.there .here)
      | .set, .there .here => .bvar .here
      | .set, .there (.there .here) => .bvar (.there (.there .here))
      | .set, .there (.there (.there v)) => .fvar (.there (.there v)))
  .forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.value_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
    (.existsE .set (.conj
      (PowerlessHistory.history_m (.bvar .here) (.fvar .here) (.fvar (.there .here)) (.bvar (.there (.there .here))))
      (φ.substitute σ)))))

theorem solution_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f R : carrier_l ℳ) :
    (solution_m φ).satisfies (((PowerlessComprehension.env_l η).pushFree R).pushFree f) ↔ solution_l φ η f R := by
  simp only [solution_m, solution_l, rule_l, Formula.satisfies, value_formula_l,
    PowerlessHistory.history_formula_l, Formula.satisfies_substitute]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro y
  apply imp_congr_right
  intro _
  apply exists_congr
  intro H
  apply and_congr Iff.rfl
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there .here) => rfl
    | .set, .there (.there (.there v)) => rfl

def stage_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f x R A : carrier_l ℳ) : Prop :=
  ∃ D B, segment_l D A R x ∧ map_l f D B ∧ solution_l φ η f R

def stage_m {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ)) :
    Formula ℒ [] (.set :: .set :: .set :: .set :: Γ) :=
  let σ : Substitution ℒ [] (.set :: .set :: Γ) [.set, .set] (.set :: .set :: .set :: .set :: Γ) :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .fvar .here
      | .set, .there .here => .fvar (.there (.there .here))
      | .set, .there (.there v) => .fvar (.there (.there (.there (.there v)))))
  .existsE .set (.existsE .set (.conj
    (segment_m (.bvar (.there .here)) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there .here))) (.fvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.map_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
      ((solution_m φ).substitute σ))))

theorem stage_formula_l {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length)
    (f x R A : carrier_l ℳ) :
    (stage_m φ).satisfies (((((PowerlessComprehension.env_l η).pushFree A).pushFree R).pushFree x).pushFree f) ↔
      stage_l φ η f x R A := by
  simp only [stage_m, stage_l, Formula.satisfies, segment_formula_l, map_formula_l, Formula.satisfies_substitute]
  apply exists_congr
  intro D
  apply exists_congr
  intro B
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  rw [← solution_formula_l φ η f R]
  apply Iff.of_eq
  apply congrArg (fun η => (solution_m φ).satisfies η)
  apply Env.ext
  · intro s v
    nomatch v
  · intro s v
    match s, v with
    | .set, .here => rfl
    | .set, .there .here => rfl
    | .set, .there (.there v) => rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWellRecursionSyntax
