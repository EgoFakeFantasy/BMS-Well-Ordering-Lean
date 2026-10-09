import BMSConstructibleBridge.PowerlessSourceNaturalAbsolute
import BMSConstructibleBridge.PowerlessSourceInclusion
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity

/-! # 同一有限元素性域中的实际 ω

ω 的最小归纳集定义不是 Δ₀，不对非传递 I 使用绝对性。先在传递 W
中读取原实际 ω，再由该原公式的有限元素性送入同一个 MemberI。
不要求 W 满足完整源理论，也不把内部自然数当成外部标准自然数。
本模块提供源装配的语义中间接口，不代替最终固定高度的 Z₂ 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullOmega

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

def matrix_m (Δ : SortContext ℒ) : Formula ℒ [.set] Δ :=
  SecondOrderOmegaSyntax.omega_m (.bvar .here)

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk [.set] (matrix_m Δ)]

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 原实际 ω 在任意包含它的非空传递成员域中仍是最小归纳集。 -/
theorem omega_member_l {W : carrier_l 𝒩} (hW : ∃ x, member_l 𝒩 x W)
    (hWT : PowerlessNaturalOrder.transitive_l W)
    (ω : PowerlessMemberStructure.type_l (ℳ := 𝒩) W)
    (hω : omega_l (ℳ := 𝒩) ω.val) :
    omega_l (ℳ := PowerlessMemberStructure.structure_l W hW) ω := by
  refine ⟨(PowerlessSourceNaturalAbsolute.inductive_l hWT).mpr hω.1, ?_⟩
  intro A hA
  exact (PowerlessSourceNaturalAbsolute.subset_l hWT).mpr
    (hω.2 A.val ((PowerlessSourceNaturalAbsolute.inductive_l hWT).mp hA))

/-- 消费同一 I 的 ω 公式元素性，读取 MemberI 中的原最小归纳集定义。 -/
theorem model_l {Δ Ε : SortContext ℒ} {I₀ W₀ : carrier_l 𝒩}
    (hI : ∃ x, member_l 𝒩 x I₀) (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (ω : PowerlessMemberStructure.type_l (ℳ := 𝒩) I₀)
    (hω : omega_l (ℳ := 𝒩) ω.val) :
    omega_l (ℳ := PowerlessMemberStructure.structure_l I₀ hI) ω := by
  have hNonempty : ∃ x, member_l 𝒩 x W₀ := by
    obtain ⟨x, hx⟩ := hI
    exact ⟨x, hIW x hx⟩
  let η : Env (PowerlessMemberStructure.structure_l I₀ hI) [.set] Δ := ν.pushBound ω
  let ξ := PowerlessSourceInclusion.env_l (hU := hNonempty) hIW η
  have hEnv : PowerlessRelativization.env_l ξ = PowerlessRelativization.env_l η := by
    apply Env.ext <;> intro _ _ <;> rfl
  have hWT : PowerlessNaturalOrder.transitive_l W₀ := fun x y hx hy => hW x hx y hy
  have hωW := omega_member_l hNonempty hWT
    (PowerlessSourceInclusion.inclusion_l hIW ω) hω
  have hMatrix : (matrix_m Δ).satisfies ξ := by
    rw [matrix_m, omega_formula_l]
    exact hωW
  have hRelative := (PowerlessRelativization.formula_l (matrix_m Δ) ξ).mpr hMatrix
  rw [hEnv] at hRelative
  change (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧ True at h
  have hReflect := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (matrix_m Δ) ζ I W τ (PowerlessRelativization.env_l ν) hτ).mp h.1
      (PowerlessRelativization.env_l η) (fun _ _ => rfl)
      (fun v => hI₀.symm ▸ (η.boundVal v).property)
  rw [hI₀, hW₀] at hReflect
  have hMember := (PowerlessRelativization.formula_l (matrix_m Δ) η).mp
    (hReflect.mp hRelative)
  exact (omega_formula_l η (.bvar .here)).mp hMember

#print axioms omega_member_l
#print axioms model_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullOmega
