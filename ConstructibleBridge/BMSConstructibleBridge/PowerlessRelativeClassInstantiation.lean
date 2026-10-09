import BMSConstructibleBridge.PowerlessRelativeClassRelativization

/-! # 环境层谓词与类内正文的混合实例化

只相对化指定正文，再把基集及自由参数代入任意环境。不改变外层的层级
谓词、序数守卫或成员前提，避免把原商层关系误译成类内层关系。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInstantiation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private def insert_m {Ξ Γ Δ : SortContext ℒ} (B : Term ℒ Γ Δ .set)
    (σ : VariableSubstitution ℒ Ξ Γ Δ) : VariableSubstitution ℒ (.set :: Ξ) Γ Δ
  | _, .here => B
  | _, .there v => σ v

def formula_m {Ξ Γ Δ : SortContext ℒ} (B : Term ℒ Γ Δ .set)
    (φ : Formula ℒ [] Ξ) (σ : VariableSubstitution ℒ Ξ Γ Δ) : Formula ℒ Γ Δ :=
  (PowerlessRelativeClassRelativization.formula_m φ).substitute
    (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v) (insert_m B σ))

theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    (K : source_coding_l hℳ) {Ξ Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] Ξ) (η : Env (structure_l hℳ B hBase) [] Ξ)
    (ρ : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ)
    (b : Term ℒ Γ Δ .set) (σ : VariableSubstitution ℒ Ξ Γ Δ)
    (hb : b.eval ρ = B)
    (hσ : ∀ (v : Variable Ξ .set), (σ v).eval ρ = (η.freeVal v).val) :
    (formula_m b φ σ).satisfies ρ ↔ φ.satisfies η := by
  unfold formula_m
  rw [Formula.satisfies_substitute]
  have hEnv : ρ.pullback (.map
      (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v) (insert_m b σ)) =
      (PowerlessRelativeClassRelativization.env_l η).pushFree B := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v
      cases s
      cases v with
      | here => exact hb
      | there v => exact hσ v
  rw [hEnv]
  exact PowerlessRelativeClassRelativization.formula_l K φ η

#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInstantiation
