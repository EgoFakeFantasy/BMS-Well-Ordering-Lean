import BMSConstructibleBridge.PowerlessSourceInclusion
import YesMetaZFC.BMS.OrdinalReflectionSyntax

/-!
# 实际传递子域的原源有界绝对性

构造上游原 Lévy 嵌入的全部字段，尤其从子域传递性证明有界原像。
复用上游原 Formula 的 Delta0 绝对性；不假设子域是 ZF 模型或全初等级。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceBounded

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure StabilityFrame

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A U : carrier_l ℳ}
  {hA : ∃ a, member_l ℳ a A} {hU : ∃ a, member_l ℳ a U}

def embedding_l (hAU : subset_l A U) (hAT : PowerlessNaturalOrder.transitive_l A) :
    Formula.LevyEmbedding membershipLevyBound (structure_l A hA) (structure_l U hU) where
  map _ := PowerlessSourceInclusion.inclusion_l hAU
  map_injective _ _ _ h := Subtype.ext (congrArg (fun z : type_l U => z.val) h)
  function_eq f _ := nomatch f
  relation_iff
    | .membership, .cons _ (.cons _ .nil) => Iff.rfl
  bounded_preimage x y h := ⟨⟨y.val, hAT x.val y.val x.property h⟩, Subtype.ext rfl⟩

theorem env_l (hAU : subset_l A U) (hAT : PowerlessNaturalOrder.transitive_l A)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ) :
    (embedding_l (hU := hU) hAU hAT).mapEnv η = PowerlessSourceInclusion.env_l hAU η := rfl

theorem formula_l (hAU : subset_l A U) (hAT : PowerlessNaturalOrder.transitive_l A)
    {Γ Δ : SortContext ℒ} {φ : Formula ℒ Γ Δ} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env (structure_l A hA) Γ Δ) :
    Formula.satisfies (PowerlessSourceInclusion.env_l (hU := hU) hAU η) φ ↔ Formula.satisfies η φ :=
  (Formula.delta0_absolute (embedding_l hAU hAT) hφ η).symm

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceBounded
