import BMSConstructibleBridge.SecondOrderOrdinalBounded
import BMSConstructibleBridge.SecondOrderMemberStructure

/-! # 实际成员呈现的有界公式绝对性

映射读取原商对象，不选择额外代表。母集传递性提供有界原像，因此母集
不必是完整 PowerlessTheory 模型，就可核验内部序数判定与环境判定一致。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberBounded

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (mk_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SecondOrderMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {A : SecondOrderGraph.code_l ℳ}
  {a : SecondOrderModel.num_l ℳ} {ha : SecondOrderPairing.relation_l A.real a A.root}

def embedding_l (hTrans : ∀ x, mem_l hℳ x (mk_l hℳ A) → ∀ y, mem_l hℳ y x → mem_l hℳ y (mk_l hℳ A)) :
    Formula.LevyEmbedding membershipLevyBound (SecondOrderMemberStructure.structure_l hℳ A a ha)
      (SecondOrderQuotient.structure_l hℳ) where
  map _ x := x.val
  map_injective _ _ _ h := Subtype.ext h
  function_eq f _ := nomatch f
  relation_iff
    | .membership, .cons _ (.cons _ .nil) => Iff.rfl
  bounded_preimage x y h := ⟨⟨y, hTrans x.val x.property y h⟩, rfl⟩

def env_l {Γ Δ : SortContext ℒ} (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ) :
    Env (SecondOrderQuotient.structure_l hℳ) Γ Δ where
  boundVal {s} v := match s with | .set => (η.boundVal v).val
  freeVal {s} v := match s with | .set => (η.freeVal v).val

theorem term_l {Γ Δ : SortContext ℒ} (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ)
    (t : Term ℒ Γ Δ .set) : t.eval (env_l η) = (t.eval η).val := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem formula_l (hTrans : ∀ x, mem_l hℳ x (mk_l hℳ A) → ∀ y, mem_l hℳ y x → mem_l hℳ y (mk_l hℳ A))
    {Γ Δ : SortContext ℒ} {φ : Formula ℒ Γ Δ} (hφ : Formula.IsDelta0 membershipLevyBound φ)
    (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ) :
    φ.satisfies η ↔ φ.satisfies (env_l η) := Formula.delta0_absolute (embedding_l hTrans) hφ η

theorem ordinal_l (hTrans : ∀ x, mem_l hℳ x (mk_l hℳ A) → ∀ y, mem_l hℳ y x → mem_l hℳ y (mk_l hℳ A))
    {Γ Δ : SortContext ℒ} (η : Env (SecondOrderMemberStructure.structure_l hℳ A a ha) Γ Δ) (t : Term ℒ Γ Δ .set) :
    (PowerlessOrdinalBounded.ordinal_m t).satisfies η ↔
      SetTheory.Structure.IsOrdinal (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) (t.eval η).val := by
  rw [formula_l hTrans (PowerlessOrdinalBounded.ordinal_delta_l t) η,
    SecondOrderOrdinalBounded.formula_l hℳ, term_l]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderMemberBounded
