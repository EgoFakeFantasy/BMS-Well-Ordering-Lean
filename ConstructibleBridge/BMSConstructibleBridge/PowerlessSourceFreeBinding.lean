import BMSConstructibleBridge.PowerlessSourceOpening

/-! # 原自由参数全部绑定而不更换公式正文

将原自由上下文原样作为绑定上下文；这是原 Substitution，不是新的
公式编码或真值谓词。对应环境只转接已经给定的值，不抽取 Type 见证。
有限类程序的空自由上下文接口由此能捕获任意原参数公式的请求。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceFreeBinding

open Logic FirstOrder

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

def formula_m {Δ : SortContext ℒ} (φ : Formula ℒ [] Δ) : Formula ℒ Δ [] :=
  φ.substitute (show Substitution ℒ [] Δ Δ [] from
    .map (fun v => nomatch v) (fun v => .bvar v))

def env_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env 𝒱 [] Δ) : Env 𝒱 Δ [] where
  boundVal v := η.freeVal v
  freeVal v := nomatch v

theorem formula_l {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (φ : Formula ℒ [] Δ) (η : Env 𝒱 [] Δ) :
    (formula_m φ).satisfies (env_l η) ↔ φ.satisfies η := by
  rw [formula_m, Formula.satisfies_substitute]
  apply Iff.of_eq
  apply congrArg (fun ξ => φ.satisfies ξ)
  apply Env.ext
  · intro _ v; nomatch v
  · intro _ _; rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceFreeBinding
