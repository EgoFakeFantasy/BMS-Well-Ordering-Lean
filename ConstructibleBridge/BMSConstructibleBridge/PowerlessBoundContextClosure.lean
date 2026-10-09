import BMSConstructibleBridge.PowerlessBMSQuotientSubsetImageDerives

/-! # 固定绑定参数内关闭外部有限自由上下文

保留已有绑定上下文 Γ，只对自由上下文做全称闭包；用于确保存在编码包
先于所有源矩阵参数。语义覆盖模型中全部赋值，不要求外部 ω 标准性。
这是 AST 与读数工具，不是新背景公理或统一真值断言。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundContextClosure

open Logic FirstOrder
set_option autoImplicit false

universe u

private def insert_m {Γ Δ : SortContext ℒ} :
    Substitution ℒ Γ (.set :: Δ) (.set :: Γ) Δ :=
  .map (fun v => .bvar (.there v)) (fun {_} v => match v with
    | .here => .bvar .here
    | .there v => .fvar v)

def abstract_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ (.set :: Δ)) : Formula ℒ Γ Δ :=
  .forallE .set (φ.substitute insert_m)

theorem abstract_formula_l {𝒱 : Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ Γ (.set :: Δ)) (η : Env 𝒱 Γ Δ) :
    (abstract_m φ).satisfies η ↔ ∀ x : 𝒱.Carrier .set, φ.satisfies (η.pushFree x) := by
  simp only [abstract_m, Formula.satisfies]
  apply forall_congr'
  intro x
  refine (Formula.satisfies_substitute (η.pushBound x) insert_m φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro s v
    rfl
  · intro s v
    cases v <;> rfl

def formula_m {Γ : SortContext ℒ} : {Δ : SortContext ℒ} → Formula ℒ Γ Δ → Formula ℒ Γ []
  | List.nil, φ => φ
  | List.cons .set _, φ => formula_m (abstract_m φ)

theorem formula_l {𝒱 : Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ Γ Δ) (η : Env 𝒱 Γ []) :
    (formula_m φ).satisfies η ↔
      ∀ ρ : Assignment 𝒱 Δ, φ.satisfies ⟨η.boundVal, ρ⟩ := by
  induction Δ with
  | nil =>
    constructor
    · intro h ρ
      have hEnv : (⟨η.boundVal, ρ⟩ : Env 𝒱 Γ []) = η := by
        apply Env.ext
        · intro s v; rfl
        · intro s v; nomatch v
      simpa only [formula_m, hEnv] using h
    · intro h
      simpa only [formula_m] using h η.freeVal
  | cons s Δ ih =>
    cases s
    rw [formula_m, ih]
    constructor
    · intro h ρ
      let tail : Assignment 𝒱 Δ := fun v => ρ (.there v)
      have hφ := (abstract_formula_l φ (⟨η.boundVal, tail⟩ : Env 𝒱 Γ Δ)).mp (h tail) (ρ .here)
      have hEnv : (⟨η.boundVal, tail⟩ : Env 𝒱 Γ Δ).pushFree (ρ .here) = ⟨η.boundVal, ρ⟩ := by
        apply Env.ext
        · intro s v; rfl
        · intro s v; cases v <;> rfl
      exact hEnv ▸ hφ
    · intro h ρ
      apply (abstract_formula_l φ (⟨η.boundVal, ρ⟩ : Env 𝒱 Γ Δ)).mpr
      intro x
      exact h (Assignment.push x ρ)

#print axioms abstract_formula_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundContextClosure
