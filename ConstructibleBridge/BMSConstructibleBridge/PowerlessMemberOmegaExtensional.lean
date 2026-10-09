import BMSConstructibleBridge.PowerlessSourceNaturalAbsolute

/-! # 仅用外延性识别传递成员域中的 ω

背景是任意纯集合结构及显式外延性证书，不假定完整源理论。
成员域传递且含实际 ω 时，内部最小归纳集与同一 ω 相等。
弱前提接口独立于原源模型模块，保留旧文件内容和全部旧签名。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberOmegaExtensional

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

variable {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem omega_l
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱))
    {A ω : carrier_l 𝒱} {hA : ∃ a, member_l 𝒱 a A}
    (hAT : PowerlessNaturalOrder.transitive_l A) (hω : ThirdOrderSemantics.omega_l ω)
    (hωA : member_l 𝒱 ω A) (a : type_l A) :
    ThirdOrderSemantics.omega_l (ℳ := structure_l A hA) a ↔ a.val = ω := by
  constructor
  · intro h
    have h₀ := h.2 ⟨ω, hωA⟩ ((PowerlessSourceNaturalAbsolute.inductive_l hAT).mpr hω.1)
    have h₁ := (PowerlessSourceNaturalAbsolute.subset_l hAT).mp h₀
    have h₂ := hω.2 a.val ((PowerlessSourceNaturalAbsolute.inductive_l hAT).mp h.1)
    exact hExt.eq_of_same_members a.val ω (fun x => ⟨h₁ x, h₂ x⟩)
  · intro ha
    have h₀ : ThirdOrderSemantics.inductive_l a.val := ha.symm ▸ hω.1
    refine ⟨(PowerlessSourceNaturalAbsolute.inductive_l hAT).mpr h₀, ?_⟩
    intro b hb
    apply (PowerlessSourceNaturalAbsolute.subset_l hAT).mpr
    intro x hx
    exact hω.2 b.val ((PowerlessSourceNaturalAbsolute.inductive_l hAT).mp hb) x (ha ▸ hx)

theorem formula_l
    (hExt : SetTheory.Extensional (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱))
    {A ω : carrier_l 𝒱} {hA : ∃ a, member_l 𝒱 a A}
    (hAT : PowerlessNaturalOrder.transitive_l A) (hω : ThirdOrderSemantics.omega_l ω)
    (hωA : member_l 𝒱 ω A) {Γ Δ : SortContext ℒ}
    (η : Env (structure_l A hA) Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (SecondOrderOmegaSyntax.omega_m a) ↔ (a.eval η).val = ω :=
  (ThirdOrderSemantics.omega_formula_l η a).trans (omega_l hExt hAT hω hωA (a.eval η))

#print axioms omega_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberOmegaExtensional
