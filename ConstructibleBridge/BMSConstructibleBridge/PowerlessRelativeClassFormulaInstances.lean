import BMSConstructibleBridge.PowerlessRelativeClassRelativization
import BMSConstructibleBridge.PowerlessRelativeParameters

/-! # 原类相对公式在任意环境中的精确参数代入

只代入给定项和已有 Class 取值证据，保留原公式及原上下文顺序。
构造的是环境值的子类型包装，不从存在性抽取 Type 层选择数据。
类参数 B 是环境外部元数据，不要求 B 属于自身或任意指定子域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFormulaInstances

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

def instance_m {Δ Γ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    (B : Term ℒ Γ Θ .set) (ν : Variable Δ .set → Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  (PowerlessRelativeClassRelativization.formula_m φ).substitute
    (PowerlessRelativeParameters.binding_m B ν)

def members_m {Γ Θ : SortContext ℒ} (Δ : SortContext ℒ)
    (B : Term ℒ Γ Θ .set) (ν : Variable Δ .set → Term ℒ Γ Θ .set) : Formula ℒ Γ Θ :=
  match Δ with
  | [] => .truth
  | .set :: Δ => .conj (PowerlessRelativeHierarchySyntax.class_m B (ν .here))
      (members_m Δ B (fun v => ν (.there v)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem members_l (K : source_coding_l hℳ) {Γ Θ : SortContext ℒ}
    (Δ : SortContext ℒ) (η : Env 𝒱 Γ Θ) (B : Term ℒ Γ Θ .set)
    (ν : Variable Δ .set → Term ℒ Γ Θ .set) :
    (members_m Δ B ν).satisfies η ↔ ∀ v,
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) ((ν v).eval η) := by
  induction Δ with
  | nil =>
      constructor
      · intro _ v; nomatch v
      · intro _; trivial
  | cons s Δ ih =>
      cases s
      change (_ ∧ (members_m Δ B (fun v => ν (.there v))).satisfies η) ↔ _
      rw [PowerlessRelativeHierarchySemantics.class_formula_l K, ih]
      constructor
      · rintro ⟨h₀, h₁⟩ v
        cases v with
        | here => exact h₀
        | there v => exact h₁ v
      · intro h
        exact ⟨h .here, fun v => h (.there v)⟩

theorem instance_l (K : source_coding_l hℳ) {Δ Γ Θ : SortContext ℒ}
    {B₀ : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B₀ → ∀ y, mem_l hℳ y x → mem_l hℳ y B₀}
    (φ : Formula ℒ [] Δ) (η : Env 𝒱 Γ Θ) (B : Term ℒ Γ Θ .set)
    (ν : Variable Δ .set → Term ℒ Γ Θ .set)
    (ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ B₀ hBase) [] Δ)
    (hB : B.eval η = B₀) (hν : ∀ v, (ν v).eval η = (ξ.freeVal v).val) :
    (instance_m φ B ν).satisfies η ↔ φ.satisfies ξ := by
  rw [instance_m, Formula.satisfies_substitute]
  have hEnv : η.pullback (PowerlessRelativeParameters.binding_m B ν) =
      (PowerlessRelativeClassRelativization.env_l ξ).pushFree B₀ := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => exact hB
      | there v => exact hν v
  rw [hEnv]
  exact PowerlessRelativeClassRelativization.formula_l K φ ξ

#print axioms members_l
#print axioms instance_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFormulaInstances
