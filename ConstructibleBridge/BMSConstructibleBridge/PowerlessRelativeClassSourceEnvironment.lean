import BMSConstructibleBridge.PowerlessRelativeClassAssignmentUpdate
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
import BMSConstructibleBridge.PowerlessSourceEnvironment
import BMSConstructibleBridge.SecondOrderNaturalCases

/-! # 无完整源模型假设的变量槽与原子语义

自然数界由原商 ω 传递性给出，新槽由正则性排除旧槽；原子语义只用
实际函数取值唯一性。源环境的 push/update 仍复用原有纯逻辑接口。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSourceEnvironment

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessSourceEnvironment (bounded_l represents_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}
  {Γ Δ : SortContext ℒ}

theorem natural_l {ω k : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hk : mem_l hℳ k.val ω.val) {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    (hξ : bounded_l ξ k) (t : Term ℒ Γ Δ .set) : mem_l hℳ (t.eval ξ).val ω.val :=
  SecondOrderOmegaTransitive.member_l hℳ ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω)
    hk (hξ t)

theorem fresh_l {k : type_l hℳ B} {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    (hξ : bounded_l ξ k) (t : Term ℒ Γ Δ .set) : t.eval ξ ≠ k := by
  intro h
  have hk : mem_l hℳ k.val k.val := by
    have hx : mem_l hℳ (t.eval ξ).val k.val := hξ t
    simpa only [h] using hx
  exact SecondOrderNaturalCases.asymmetry_l hℳ hk hk

theorem equal_l {A m f : type_l hℳ B} {hA : ∃ a, member_l (structure_l hℳ B hBase) a A}
    {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    {η : Env (PowerlessMemberStructure.structure_l A hA) Γ Δ}
    (hf : map_l (ℳ := structure_l hℳ B hBase) f m A) (hη : represents_l ξ η f)
    (s t : Term ℒ Γ Δ .set) :
    PowerlessEvaluationClause.equal_l f (s.eval ξ) (t.eval ξ) ↔ s.eval η = t.eval η := by
  constructor
  · rintro ⟨c, hc, hd⟩
    apply Subtype.ext
    exact (PowerlessRelativeClassFunctionProperties.value_unique_l hf (hη s) hc).trans
      (PowerlessRelativeClassFunctionProperties.value_unique_l hf (hη t) hd).symm
  · intro h
    exact ⟨(s.eval η).val, hη s, h.symm ▸ hη t⟩

theorem member_l {A m f : type_l hℳ B} {hA : ∃ a, ThirdOrderSemantics.member_l (structure_l hℳ B hBase) a A}
    {ξ : Env (structure_l hℳ B hBase) Γ Δ}
    {η : Env (PowerlessMemberStructure.structure_l A hA) Γ Δ}
    (hf : map_l (ℳ := structure_l hℳ B hBase) f m A) (hη : represents_l ξ η f)
    (s t : Term ℒ Γ Δ .set) :
    PowerlessEvaluationClause.member_l f (s.eval ξ) (t.eval ξ) ↔
      Formula.satisfies η (.rel .membership (.cons s (.cons t .nil))) := by
  change (∃ c d, value_l f (s.eval ξ) c ∧ value_l f (t.eval ξ) d ∧
    ThirdOrderSemantics.member_l (structure_l hℳ B hBase) c d) ↔
      ThirdOrderSemantics.member_l (structure_l hℳ B hBase) (s.eval η).val (t.eval η).val
  constructor
  · rintro ⟨c, d, hc, hd, hcd⟩
    have hcEq := PowerlessRelativeClassFunctionProperties.value_unique_l hf hc (hη s)
    have hdEq := PowerlessRelativeClassFunctionProperties.value_unique_l hf hd (hη t)
    exact hcEq ▸ hdEq ▸ hcd
  · exact fun h => ⟨(s.eval η).val, (t.eval η).val, hη s, hη t, h⟩

#print axioms natural_l
#print axioms equal_l
#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSourceEnvironment
