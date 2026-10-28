import BMSConstructibleBridge.SecondOrderOmegaSyntax
import BMSConstructibleBridge.SecondOrderWeakSetTheory
import BMSConstructibleBridge.ThirdOrderSemantics

/-!
# 任意二阶算术模型的图商 ω 可作无幂集算术源的 ω

将图商中已证明的最小归纳对象转换为 Powerless 算术结构使用的 ω 谓词。
该转换只用目标模型的算术公理和图商定义，不要求图商满足 Collection；它
不构造完整 `PowerlessTheory` 模型，也不单独给出七字段纯算术对应。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientOmega

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic

set_option autoImplicit false

universe u

private def set_variable_identity :
    Substitution ℒ [] [.set] [] [.set] :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => Term.fvar .here)

/-- 图商结构中的归纳集谓词与目标 Z₂ 模型的图商谓词等价。 -/
private theorem inductive_iff_l
    {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hM : Theory.Models M SecondOrderArithmetic.theory_m)
    (A : SecondOrderQuotient.type_l hM) :
    ThirdOrderSemantics.inductive_l (ℳ := SecondOrderQuotient.structure_l hM) A ↔
      SecondOrderOmega.inductive_l hM A := by
  let η : Env (SecondOrderQuotient.structure_l hM) [] [.set] :=
    (Env.empty (M := SecondOrderQuotient.structure_l hM)).pushFree
      (sort := _root_.YesMetaZFC.SetTheory.SetSort.set) A
  have h := SecondOrderOmegaSyntax.inductive_l hM η (Term.fvar .here)
  change Formula.satisfies η
      (SecondOrderOmegaSyntax.inductive_template_m.substitute set_variable_identity) ↔
    SecondOrderOmega.inductive_l hM A at h
  rw [Formula.satisfies_substitute] at h
  have hEnv : η.pullback set_variable_identity = η := by
    apply Env.ext
    · intro s v
      cases v
    · intro s v
      cases v with
      | here => rfl
      | there rest => cases rest
  rw [hEnv] at h
  simpa [ThirdOrderSemantics.inductive_l, η] using h

/-- Z₂ 模型的图商最小归纳对象满足 Powerless 算术模型所需的 ω 规格。 -/
theorem omega_l
    {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hM : Theory.Models M SecondOrderArithmetic.theory_m)
    {A : SecondOrderQuotient.type_l hM}
    (hA : SecondOrderOmega.omega_l hM A) :
    ThirdOrderSemantics.omega_l (ℳ := SecondOrderQuotient.structure_l hM) A := by
  change ThirdOrderSemantics.inductive_l (ℳ := SecondOrderQuotient.structure_l hM) A ∧
    ∀ B, ThirdOrderSemantics.inductive_l (ℳ := SecondOrderQuotient.structure_l hM) B →
      ThirdOrderSemantics.subset_l A B
  constructor
  · exact (inductive_iff_l hM A).mpr hA.1
  · intro B hB x hx
    exact hA.2 B ((inductive_iff_l hM B).mp hB) x hx

/-! The generic quotient construction supplies this ω for every target model. -/
theorem exists_l
    {M : FirstOrder.Structure.{0, 0, 0, u} signature_m}
    (hM : Theory.Models M SecondOrderArithmetic.theory_m) :
    ∃ A : ThirdOrderSemantics.carrier_l (SecondOrderQuotient.structure_l hM),
      ThirdOrderSemantics.omega_l
        (ℳ := SecondOrderQuotient.structure_l hM) A := by
  obtain ⟨A, hA⟩ := SecondOrderOmega.exists_l hM
  exact ⟨A, omega_l hM hA⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientOmega
