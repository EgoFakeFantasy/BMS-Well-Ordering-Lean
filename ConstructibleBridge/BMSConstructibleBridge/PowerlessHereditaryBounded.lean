import BMSConstructibleBridge.PowerlessHereditaryRelativization
import BMSConstructibleBridge.PowerlessSourceAmbient

/-! # 遗传子模型的有界绝对性

成员原像直接来自遗传传递性，不假定完整分离或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryBounded

open Logic FirstOrder StabilityFrame
open PowerlessHereditaryStructure (structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
    SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

def embedding_l : Formula.LevyEmbedding membershipLevyBound (structure_l hℳ B hBase)
    (SecondOrderQuotient.structure_l hℳ) where
  map _ x := x.val
  map_injective _ _ _ h := Subtype.ext h
  function_eq f _ := nomatch f
  relation_iff
    | .membership, .cons _ (.cons _ .nil) => Iff.rfl
  bounded_preimage x y h :=
    ⟨⟨y, PowerlessHereditaryClass.transitive_l hℳ x.property h⟩, rfl⟩

theorem formula_l {Γ Δ : SortContext ℒ} {φ : Formula ℒ Γ Δ}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l hℳ B hBase) Γ Δ) :
    φ.satisfies η ↔ φ.satisfies (PowerlessHereditaryRelativization.env_l η) :=
  Formula.delta0_absolute embedding_l hφ η

#print axioms embedding_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryBounded
