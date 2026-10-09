import YesMetaZFC.Logic.Semantics

/-! # 相等结构上环境与公式的显式传输

环境携带整个结构索引，即使实际载体相同也不能直接更换索引。
本接口以结构相等及全部赋值的异质相等为证书；不构造选择函数，
不要求理论模型公理，不限制公式复杂度。
-/

namespace YesMetaZFC.Automation.StructureCongruence

open Logic FirstOrder

set_option autoImplicit false

universe u v w x

theorem satisfies_l {σ : Signature.{u, v, w}} {ℳ 𝒩 : Structure.{u, v, w, x} σ}
    (hStructures : ℳ = 𝒩) {Γ Δ : SortContext σ} (η : Env ℳ Γ Δ) (ξ : Env 𝒩 Γ Δ)
    (hBound : ∀ s (a : Variable Γ s), HEq (η.boundVal a) (ξ.boundVal a))
    (hFree : ∀ s (a : Variable Δ s), HEq (η.freeVal a) (ξ.freeVal a)) (φ : Formula σ Γ Δ) :
    φ.satisfies η ↔ φ.satisfies ξ := by
  subst 𝒩
  have hEnv : η = ξ := Env.ext (fun {s} a => eq_of_heq (hBound s a))
    (fun {s} a => eq_of_heq (hFree s a))
  exact Iff.of_eq (congrArg (fun θ => φ.satisfies θ) hEnv)

#print axioms satisfies_l

end YesMetaZFC.Automation.StructureCongruence
