import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseSuccessor
import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseBase

/-! # 局部坍缩预算中的精确域、图外延性及零层

预算归纳同时保留域和图的成员界。域 I∩U 是只含实际层参数的 Δ₀ 切片；
局部图的全 raw 读数由内部一致性取得。零层图由基底固定性识别为恒等图，
其切片不含原全图 H。没有 ClassH、Collection 或宿主良基归纳前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseBudgetSlice

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def identity_m {Γ Δ : SortContext ℒ} (B p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists B <|
    PowerlessPairBounded.ordered_m (.bvar .here) (.bvar .here) (up p)

theorem identity_delta_m {Γ Δ : SortContext ℒ} (B p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (identity_m B p) :=
  .bounded_exists _ (PowerlessPairBounded.ordered_delta_l _ _ _)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem identity_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (B p : Term ℒ Γ Δ .set) : (identity_m B p).satisfies η ↔
      ∃ x, mem_l hℳ x (B.eval η) ∧
        SecondOrderPairObjects.ordered_l hℳ x x (p.eval η) := by
  simp only [identity_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 精确域进入一次 Def，原坍缩图不出现在参数环境中。 -/
theorem domain_member_l {C D I U E : Raw}
    (hDef : SecondOrderMemberDef.spec_l hℳ C D)
    (hTrans : ∀ x, mem_l hℳ x C → ∀ y, mem_l hℳ y x → mem_l hℳ y C)
    (hIC : mem_l hℳ I C) (hUC : mem_l hℳ U C)
    (hE : PowerlessRelativeMembershipCollapseRestriction.domain_l I U E) :
    mem_l hℳ E D := by
  let η : Env 𝒱 [] [.set, .set] := Env.empty |>.pushFree I |>.pushFree U
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .conj (member_m (.fvar .here) (.fvar (.there (.there .here))))
      (member_m (.fvar .here) (.fvar (.there .here)))
  apply SecondOrderMemberDefBoundedSlice.member_l hℳ hDef (φ := φ) hTrans
    (.conj (.rel _ _) (.rel _ _)) η
  · intro s v
    cases s
    match v with
    | .here => exact hUC
    | .there .here => exact hIC
  · intro x
    have hφ : φ.satisfies (η.pushFree x) ↔ mem_l hℳ x I ∧ mem_l hℳ x U := by
      simp only [φ, member_m, Formula.satisfies, Arguments.eval, Term.eval, η]
      rfl
    rw [hφ]
    exact (hE x).trans ⟨fun h => ⟨hTrans I hIC x h.1, h⟩, fun h => h.2⟩

/-- 映射的坐标界把局部逐域读数升级为全部 raw 坐标上的精确限制规格。 -/
theorem value_l {I E T H G : Raw}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hG : PowerlessRelativeMembershipCollapsePartial.partial_l I E T G) :
    ∀ x y, SecondOrderFunctionObjects.value_l hℳ G x y ↔
      mem_l hℳ x E ∧ SecondOrderFunctionObjects.value_l hℳ H x y := by
  intro x y
  constructor
  · intro hxy
    have hx := (SecondOrderFunctionProperties.value_mem_l hℳ hG.2.2.1 hxy).1
    exact ⟨hx, (PowerlessRelativeMembershipCollapsePartial.value_l
      hH.2.1 hH.2.2.2.1 hH.1 hG hx).mp hxy⟩
  · rintro ⟨hx, hxy⟩
    exact (PowerlessRelativeMembershipCollapsePartial.value_l
      hH.2.1 hH.2.2.2.1 hH.1 hG hx).mpr hxy

/-- 同一局部域上的合格图外延相同；不以 Type 层函数取代实际 raw 图。 -/
theorem ext_l {I E T H F G : Raw}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hF : PowerlessRelativeMembershipCollapsePartial.partial_l I E T F)
    (hG : PowerlessRelativeMembershipCollapsePartial.partial_l I E T G) : F = G := by
  apply SecondOrderQuotient.ext_l hℳ
  intro p
  have hInto {F G : Raw}
      (hF : PowerlessRelativeMembershipCollapsePartial.partial_l I E T F)
      (hG : PowerlessRelativeMembershipCollapsePartial.partial_l I E T G)
      (hp : mem_l hℳ p F) : mem_l hℳ p G := by
    obtain ⟨x, y, _hx, _hy, hPair⟩ := hF.2.2.1.1 p hp
    have hFxy : SecondOrderFunctionObjects.value_l hℳ F x y := ⟨p, hp, hPair⟩
    obtain ⟨q, hq, hPair'⟩ := (value_l hH hG x y).mpr ((value_l hH hF x y).mp hFxy)
    have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
    exact hEq ▸ hq
  exact ⟨hInto hF hG, hInto hG hF⟩

/-- 零层的局部图是 B 上恒等图，因此进入真实母层的一次 Def。 -/
theorem base_member_l {B β C D I T H G : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hBI : ∀ x, mem_l hℳ x B → mem_l hℳ x I)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hCD : SecondOrderMemberDef.spec_l hℳ C D) (hBC : mem_l hℳ B C)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hG : PowerlessRelativeMembershipCollapsePartial.partial_l I B T G) : mem_l hℳ G D := by
  let η : Env 𝒱 [] [.set] := Env.empty.pushFree B
  let φ : Formula ℒ [] [.set, .set] := identity_m (.fvar (.there .here)) (.fvar .here)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  apply SecondOrderMemberDefBoundedSlice.member_l hℳ hCD (φ := φ) hTrans
    (identity_delta_m _ _) η
  · intro s v
    cases s
    match v with
    | .here => exact hBC
    | .there v => nomatch v
  · intro p
    rw [identity_formula_l (η.pushFree p) _ _]
    constructor
    · intro hp
      obtain ⟨x, y, hx, _hy, hPair⟩ := hG.2.2.1.1 p hp
      have hHxy := ((value_l hH hG x y).mp ⟨p, hp, hPair⟩).2
      have hyx := PowerlessRelativeMembershipCollapseBase.point_all_l hℳ B I T H
        hBase hBI hH.2.1 hH.2.2.2.1 x hx y hHxy
      subst y
      exact ⟨PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hC
        (hTrans B hBC x hx) (hTrans B hBC x hx) hPair, x, hx, hPair⟩
    · rintro ⟨_, x, hx, hPair⟩
      have hHxx := PowerlessRelativeMembershipCollapseBase.fixed_l hℳ B I T H
        hBase hBI hH.2.1 hH.2.2.2.1 x hx
      obtain ⟨q, hq, hPair'⟩ := (value_l hH hG x x).mpr ⟨hx, hHxx⟩
      have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
      exact hEq ▸ hq

#print axioms identity_delta_m
#print axioms domain_member_l
#print axioms value_l
#print axioms ext_l
#print axioms base_member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseBudgetSlice
