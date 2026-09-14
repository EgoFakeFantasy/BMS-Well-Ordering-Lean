import BMSConstructibleBridge.PowerlessSourceBounded

/-!
# 传递成员域到原模型的有界公式嵌入

映射直接读取子类型的实际元素；有界原像由域传递性给出。
无需假设成员域自身满足无幂集核心，也不假定它对所有公式初等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceAmbient

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure StabilityFrame

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A : carrier_l ℳ}
  {hA : ∃ a, member_l ℳ a A}

def embedding_l (hAT : PowerlessNaturalOrder.transitive_l A) :
    Formula.LevyEmbedding membershipLevyBound (structure_l A hA) ℳ where
  map _ x := x.val
  map_injective _ _ _ h := Subtype.ext h
  function_eq f _ := nomatch f
  relation_iff
    | .membership, .cons _ (.cons _ .nil) => Iff.rfl
  bounded_preimage x y h := ⟨⟨y, hAT x.val y x.property h⟩, rfl⟩

def env_l {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ) : Env ℳ Γ Δ where
  boundVal v := (η.boundVal v).val
  freeVal v := (η.freeVal v).val

theorem term_l {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ) (t : Term ℒ Γ Δ .set) :
    t.eval (env_l η) = (t.eval η).val := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem formula_l (hAT : PowerlessNaturalOrder.transitive_l A)
    {Γ Δ : SortContext ℒ} {φ : Formula ℒ Γ Δ} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env (structure_l A hA) Γ Δ) :
    Formula.satisfies η φ ↔ Formula.satisfies (env_l η) φ :=
  Formula.delta0_absolute (embedding_l hAT) hφ η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceAmbient
