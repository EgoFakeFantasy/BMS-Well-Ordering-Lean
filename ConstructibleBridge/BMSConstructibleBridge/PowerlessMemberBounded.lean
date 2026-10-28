import BMSConstructibleBridge.SecondOrderMemberBounded
import BMSConstructibleBridge.PowerlessRelativization

/-! # 任意真实传递成员域的纯 Δ₀ 绝对性

只使用实际成员结构及原隶属关系，不要求母集有数码呈现或满足源公理。
传递性给出有界量词的原像；环境仅取成员的原值，没有 Type 选择。
相对化读取保留全部原绑定／自由槽，为非传递子结构的见证回收提供
传递外层上的核验；不能直接对非传递成员域使用此绝对性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberBounded

open Logic FirstOrder StabilityFrame ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A : carrier_l ℳ}
  {hA : ∃ x, member_l ℳ x A}

def embedding_l (h : ∀ x, member_l ℳ x A → ∀ y, member_l ℳ y x → member_l ℳ y A) :
    Formula.LevyEmbedding membershipLevyBound (structure_l A hA) ℳ where
  map _ x := x.val
  map_injective _ _ _ h := Subtype.ext h
  function_eq f _ := nomatch f
  relation_iff
    | .membership, .cons _ (.cons _ .nil) => Iff.rfl
  bounded_preimage x y hy := ⟨⟨y, h x.val x.property y hy⟩, rfl⟩

theorem formula_l
    (h : ∀ x, member_l ℳ x A → ∀ y, member_l ℳ y x → member_l ℳ y A)
    {Γ Δ : SortContext ℒ} {φ : Formula ℒ Γ Δ}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env (structure_l A hA) Γ Δ) :
    φ.satisfies η ↔ φ.satisfies (PowerlessRelativization.env_l η) :=
  Formula.delta0_absolute (embedding_l h) hφ η

/-- 原赋值的全部参数属于 A 时，原 Δ₀ 矩阵和其 A 相对化同值。 -/
theorem relativized_l
    (h : ∀ x, member_l ℳ x A → ∀ y, member_l ℳ y x → member_l ℳ y A)
    (hA : ∃ x, member_l ℳ x A) {Γ Δ : SortContext ℒ} {φ : Formula ℒ Γ Δ}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) (η : Env ℳ Γ Δ)
    (hBound : ∀ v : Variable Γ .set, member_l ℳ (η.boundVal v) A)
    (hFree : ∀ v : Variable Δ .set, member_l ℳ (η.freeVal v) A) :
    (PowerlessRelativization.formula_m φ).satisfies (η.pushFree A) ↔ φ.satisfies η := by
  let ξ : Env (structure_l A hA) Γ Δ :=
    { boundVal := fun {s} v => match s with | .set => ⟨η.boundVal v, hBound v⟩
      freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hFree v⟩ }
  have hξ : PowerlessRelativization.env_l ξ = η := by
    apply Env.ext
    · intro s v; cases s; rfl
    · intro s v; cases s; rfl
  rw [← hξ]
  exact (PowerlessRelativization.formula_l φ ξ).trans (formula_l h hφ ξ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberBounded
