import BMSConstructibleBridge.PowerlessSourceEnvironment

/-!
# 成员子结构的源环境包含映射

直接保持原模型中的元素值。这里是源公式的语义环境映射，不把它
称为模型内部集合函数；实际编码赋值图沿包含映射保持不变。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceInclusion

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {A U : carrier_l ℳ}
  {hA : ∃ a, member_l ℳ a A} {hU : ∃ a, member_l ℳ a U} {Γ Δ : SortContext ℒ}

def inclusion_l (h : subset_l A U) (x : type_l A) : type_l U := ⟨x.val, h x.val x.property⟩

def env_l (h : subset_l A U) (η : Env (structure_l A hA) Γ Δ) : Env (structure_l U hU) Γ Δ where
  boundVal v := inclusion_l h (η.boundVal v)
  freeVal v := inclusion_l h (η.freeVal v)

theorem compose_l {B : carrier_l ℳ} {hB : ∃ a, member_l ℳ a B}
    (hAB : subset_l A B) (hBU : subset_l B U) (hAU : subset_l A U)
    (η : Env (structure_l A hA) Γ Δ) :
    env_l (hU := hU) hBU (env_l (hU := hB) hAB η) = env_l hAU η := by
  apply Env.ext <;> intro _ _ <;> rfl

theorem term_l (h : subset_l A U) (η : Env (structure_l A hA) Γ Δ) (t : Term ℒ Γ Δ .set) :
    (t.eval (env_l (hU := hU) h η)).val = (t.eval η).val := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem push_l (h : subset_l A U) (η : Env (structure_l A hA) Γ Δ) (x : type_l A) :
    env_l (hU := hU) h (η.pushBound (sort := SetTheory.SetSort.set) x) =
      (env_l h η).pushBound (sort := SetTheory.SetSort.set) (inclusion_l h x) := by
  apply Env.ext
  · intro s v
    cases v <;> rfl
  · intro _ _
    rfl

theorem represents_l (h : subset_l A U) {ξ : Env ℳ Γ Δ} {η : Env (structure_l A hA) Γ Δ}
    {f : carrier_l ℳ} (hη : PowerlessSourceEnvironment.represents_l ξ η f) :
    PowerlessSourceEnvironment.represents_l ξ (env_l (hU := hU) h η) f := by
  intro t
  rw [term_l]
  exact hη t

theorem equal_l (h : subset_l A U) (η : Env (structure_l A hA) Γ Δ) (s t : Term ℒ Γ Δ .set) :
    Formula.satisfies (env_l (hU := hU) h η) (.equal s t) ↔ Formula.satisfies η (.equal s t) := by
  change s.eval (env_l h η) = t.eval (env_l h η) ↔ s.eval η = t.eval η
  constructor
  · intro h₀
    apply Subtype.ext
    simpa only [term_l] using congrArg Subtype.val h₀
  · intro h₀
    apply Subtype.ext
    simpa only [term_l] using congrArg Subtype.val h₀

theorem member_l (h : subset_l A U) (η : Env (structure_l A hA) Γ Δ) (s t : Term ℒ Γ Δ .set) :
    Formula.satisfies (env_l (hU := hU) h η) (.rel .membership (.cons s (.cons t .nil))) ↔
      Formula.satisfies η (.rel .membership (.cons s (.cons t .nil))) := by
  change ThirdOrderSemantics.member_l ℳ (s.eval (env_l h η)).val (t.eval (env_l h η)).val ↔
    ThirdOrderSemantics.member_l ℳ (s.eval η).val (t.eval η).val
  rw [term_l, term_l]

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceInclusion
