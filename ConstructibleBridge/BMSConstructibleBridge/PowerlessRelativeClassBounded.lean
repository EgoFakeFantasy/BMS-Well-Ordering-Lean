import BMSConstructibleBridge.PowerlessRelativeClassRelativization
import BMSConstructibleBridge.PowerlessSourceAmbient

/-! # 实际相对类子模型的 Δ₀ 绝对性

传递类中的有界原像由成员闭包构造。复用原 Formula 的 LevyEmbedding 接口，
不假设完整源理论、不要求类域对所有公式初等，也不添加满足关系公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBounded

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

def embedding_l : Formula.LevyEmbedding membershipLevyBound (structure_l hℳ B hBase)
    (SecondOrderQuotient.structure_l hℳ) where
  map _ x := x.val
  map_injective _ _ _ h := Subtype.ext h
  function_eq f _ := nomatch f
  relation_iff
    | .membership, .cons _ (.cons _ .nil) => Iff.rfl
  bounded_preimage x y h :=
    ⟨⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase x.property h⟩, rfl⟩

theorem formula_l {Γ Δ : SortContext ℒ} {φ : Formula ℒ Γ Δ}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) Γ Δ) :
    φ.satisfies η ↔ φ.satisfies (PowerlessRelativeClassRelativization.env_l η) :=
  Formula.delta0_absolute embedding_l hφ η

#print axioms embedding_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassBounded
