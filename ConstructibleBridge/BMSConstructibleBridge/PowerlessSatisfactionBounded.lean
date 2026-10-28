import BMSConstructibleBridge.PowerlessMapBounded

/-! # 合法性与赋值长度守卫的有界求值查询

公式码限制到 ω，赋值限制到 S；同一个内部长度既由合法性图 F 接受，
又是赋值到 A 的精确定义域，随后读取求值关系 G。这里只构造实际纯
Δ₀ 公式及逐环境读数，不假定 F、S、G 已有正确规格，也不宣称完整 Sat。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω A S F G c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (member_m c ω) <| .conj (member_m f S) <|
    membershipLevyBound.boundedExists ω <| .conj
      (PowerlessValueBounded.formula_m (up F) (up c) (.bvar .here)) <| .conj
        (PowerlessMapBounded.formula_m (up f) (.bvar .here) (up A))
        (PowerlessValueBounded.formula_m (up G) (up c) (up f))

theorem delta_l {Γ Δ : SortContext ℒ} (ω A S F G c f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω A S F G c f) :=
  .conj (.rel _ _) <| .conj (.rel _ _) <| .bounded_exists ω <|
    .conj (PowerlessValueBounded.delta_l _ _ _) <|
      .conj (PowerlessMapBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _)

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A S F G c f : carrier_l 𝒩) : Prop :=
  member_l 𝒩 c ω ∧ member_l 𝒩 f S ∧ ∃ l, member_l 𝒩 l ω ∧
    value_l F c l ∧ map_l f l A ∧ value_l G c f

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A S F G c f : Term ℒ Γ Δ .set) :
    (formula_m ω A S F G c f).satisfies η ↔
      holds_l (ω.eval η) (A.eval η) (S.eval η) (F.eval η) (G.eval η) (c.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, PowerlessMapBounded.formula_l,
    member_m, member_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 同一合法长度及赋值规格成立时，带守卫查询精确读取原求值关系。 -/
theorem holds_iff_value_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {ω A S F G c f l : carrier_l 𝒩}
    (hc : member_l 𝒩 c ω) (hf : member_l 𝒩 f S) (hl : member_l 𝒩 l ω)
    (hF : value_l F c l) (hMap : map_l f l A) :
    holds_l ω A S F G c f ↔ value_l G c f := by
  constructor
  · rintro ⟨_, _, _, _, _, _, h⟩
    exact h
  · intro h
    exact ⟨hc, hf, l, hl, hF, hMap, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSatisfactionBounded
