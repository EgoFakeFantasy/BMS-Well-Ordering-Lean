import BMSConstructibleBridge.PowerlessRelationalParameterSchema
import BMSConstructibleBridge.PowerlessRelationalValidParameterCompilation

/-! # 带参数跨域编译模式的原 Z₂ 推导

先固定编码系统、互异槽和公式数码；随后对每个域构造一张实际求值图，
并覆盖所有域内参数与足够长内部赋值。对象推导保留基集传递及实际 ω
的条件；本模式不是最终 BMS 良序句，也不假定弱相对类满足完整源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterDerives

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelationalParameterSchema

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

theorem exists_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
    {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
    {Δ : SortContext ℒ} (φ : Formula ℒ [] Δ)
    {ω : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ e t₁ t₂ t₃ T c : type_l hℳ B, mem_l hℳ c.val ω.val ∧ ∃ N : type_l hℳ B,
      mem_l hℳ N.val ω.val ∧ ∃ ξ : Env (structure_l hℳ B hBase) [] Δ,
        PowerlessSourceEnvironment.bounded_l ξ N ∧ ∀ A,
          PowerlessRelationalParameterDomain.domain_l φ ξ ω e T t₁ t₂ t₃ c N A := by
  obtain ⟨_, _, _, e, t₁, t₂, t₃, T, _, _, _, _, c, N, hc, hN, _, ξ, hξ, h⟩ :=
    PowerlessRelationalValidParameterCompilation.exists_l φ hω
  exact ⟨e, t₁, t₂, t₃, T, c, hc, N, hN, ξ, hξ, h⟩

theorem models_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ) (ω : Term ℒ [] Θ .set) :
    (sentence_m φ ω).TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ρ
  simp only [schema_m, Formula.satisfies, omega_formula_l, existence_formula_l]
  exact fun hω => exists_l φ hω

theorem derives_m {Δ Θ : SortContext ℒ} (φ : Formula ℒ [] Δ) (ω : Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m (sentence_m φ ω))) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ hℳ B hBase => models_l hℳ B hBase φ ω)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalParameterDerives
