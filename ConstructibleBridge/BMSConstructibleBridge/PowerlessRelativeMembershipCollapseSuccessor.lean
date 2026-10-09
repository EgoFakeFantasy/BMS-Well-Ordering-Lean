import BMSConstructibleBridge.PowerlessRelativeMembershipCollapseRestriction
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 源的 Def 后继层上的实际局部坍缩图

若 U 上已有局部图 G，Def(U) 中每个对象的全部成员都在 U 中。因此
后一层的坍缩值由 G 的前驱像唯一确定，检查式只含 I/U/T/G，不含 H。
在真实共同极限母层 C 中以此 Δ₀ 检查式切片，实际限制图进入 Def(C)。
这是共同预算归纳的后继步，不是完整预算存在或最终 BMS 对象定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSuccessor

open Logic FirstOrder StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def value_m {Γ Δ : SortContext ℒ} (I U T G x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall T <|
    .iff (member_m (.bvar .here) (up y)) <|
      membershipLevyBound.boundedExists (up I) <|
        .conj (member_m (.bvar .here) (up (up U))) <|
          .conj (member_m (.bvar .here) (up (up x)))
            (PowerlessValueBounded.formula_m (up (up G)) (.bvar .here) (.bvar (.there .here)))

def graph_m {Γ Δ : SortContext ℒ} (I U V T G p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists I <| .conj (member_m (.bvar .here) (up V)) <|
    membershipLevyBound.boundedExists (up T) <|
      .conj (PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up p)))
        (value_m (up (up I)) (up (up U)) (up (up T)) (up (up G))
          (.bvar (.there .here)) (.bvar .here))

theorem value_delta_m {Γ Δ : SortContext ℒ} (I U T G x y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (value_m I U T G x y) :=
  .bounded_forall _ (.iff (.rel _ _) (.bounded_exists _
    (.conj (.rel _ _) (.conj (.rel _ _) (PowerlessValueBounded.delta_l _ _ _)))))

theorem graph_delta_m {Γ Δ : SortContext ℒ} (I U V T G p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (graph_m I U V T G p) :=
  .bounded_exists _ (.conj (.rel _ _) (.bounded_exists _
    (.conj (PowerlessPairBounded.ordered_delta_l _ _ _) (value_delta_m _ _ _ _ _ _))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def value_l (I U T G x y : Raw) : Prop :=
  ∀ z, mem_l hℳ z T → (mem_l hℳ z y ↔ ∃ a, mem_l hℳ a I ∧
    mem_l hℳ a U ∧ mem_l hℳ a x ∧ SecondOrderFunctionObjects.value_l hℳ G a z)

theorem value_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I U T G x y : Term ℒ Γ Δ .set) : (value_m I U T G x y).satisfies η ↔
      value_l (I.eval η) (U.eval η) (T.eval η) (G.eval η) (x.eval η) (y.eval η) := by
  simp only [value_m, value_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessValueBounded.formula_l, member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

theorem graph_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (I U V T G p : Term ℒ Γ Δ .set) : (graph_m I U V T G p).satisfies η ↔
      ∃ x, mem_l hℳ x (I.eval η) ∧ mem_l hℳ x (V.eval η) ∧
        ∃ y, mem_l hℳ y (T.eval η) ∧
          SecondOrderPairObjects.ordered_l hℳ x y (p.eval η) ∧
            value_l (I.eval η) (U.eval η) (T.eval η) (G.eval η) x y := by
  simp only [graph_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    value_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- Def 的子集规格提供全部前驱覆盖，不假设 I 传递或 H 属于 Class。 -/
theorem reads_l {I U E V T H G x y : Raw}
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hE : PowerlessRelativeMembershipCollapseRestriction.domain_l I U E)
    (hG : PowerlessRelativeMembershipCollapsePartial.partial_l I E T G)
    (hDef : SecondOrderMemberDef.spec_l hℳ U V)
    (hxI : mem_l hℳ x I) (hxV : mem_l hℳ x V) (hyT : mem_l hℳ y T) :
    value_l I U T G x y ↔ SecondOrderFunctionObjects.value_l hℳ H x y := by
  obtain ⟨y₀, hy₀, _⟩ := hH.2.1.2 x hxI
  have hRead (z : Raw) : mem_l hℳ z y₀ ↔ ∃ a, mem_l hℳ a I ∧
      mem_l hℳ a U ∧ mem_l hℳ a x ∧ SecondOrderFunctionObjects.value_l hℳ G a z := by
    rw [hH.2.2.2.1 x y₀ hxI hy₀.2 z]
    constructor
    · rintro ⟨a, haI, hax, haz⟩
      have haU := SecondOrderMemberDefProperties.subset_l hℳ hDef hxV a hax
      have haE := (hE a).mpr ⟨haI, haU⟩
      exact ⟨a, haI, haU, hax, (PowerlessRelativeMembershipCollapsePartial.value_l
        hH.2.1 hH.2.2.2.1 hH.1 hG haE).mpr haz⟩
    · rintro ⟨a, haI, haU, hax, haz⟩
      exact ⟨a, haI, hax, (PowerlessRelativeMembershipCollapsePartial.value_l
        hH.2.1 hH.2.2.2.1 hH.1 hG ((hE a).mpr ⟨haI, haU⟩)).mp haz⟩
  constructor
  · intro hValue
    have hEq : y = y₀ := by
      apply SecondOrderQuotient.ext_l hℳ
      intro z
      constructor
      · intro hzy
        exact (hRead z).mpr ((hValue z (hH.1 y hyT z hzy)).mp hzy)
      · intro hzy
        exact (hValue z (hH.1 y₀ hy₀.1 z hzy)).mpr ((hRead z).mp hzy)
    exact hEq.symm ▸ hy₀.2
  · intro hxy
    have hEq : y = y₀ := SecondOrderFunctionProperties.value_unique_l hℳ hH.2.1 hxy hy₀.2
    subst y
    exact fun z _ => hRead z

/-- 由实际旧局部图生成后一层限制图及其真实成员界；H 不作切片参数。 -/
theorem member_l {B β C D I U V E T H G : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B β C)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hCD : SecondOrderMemberDef.spec_l hℳ C D)
    (hU : ∀ x, mem_l hℳ x U → ∀ y, mem_l hℳ y x → mem_l hℳ y U)
    (hUV : SecondOrderMemberDef.spec_l hℳ U V)
    (hIC : mem_l hℳ I C) (hUC : mem_l hℳ U C) (hVC : mem_l hℳ V C)
    (hTC : mem_l hℳ T C) (hGC : mem_l hℳ G C)
    (hH : PowerlessRelativeMembershipCollapse.spec_l I T H)
    (hE : PowerlessRelativeMembershipCollapseRestriction.domain_l I U E)
    (hG : PowerlessRelativeMembershipCollapsePartial.partial_l I E T G) :
    ∃ E₁ G₁, PowerlessRelativeMembershipCollapseRestriction.domain_l I V E₁ ∧
      PowerlessRelativeMembershipCollapsePartial.partial_l I E₁ T G₁ ∧
      mem_l hℳ G₁ D ∧ ∀ x y, SecondOrderFunctionObjects.value_l hℳ G₁ x y ↔
        mem_l hℳ x E₁ ∧ SecondOrderFunctionObjects.value_l hℳ H x y := by
  obtain ⟨E₁, G₁, hE₁, hG₁, hRead⟩ := PowerlessRelativeMembershipCollapseRestriction.exists_l
    hH (fun x hx y hy => SecondOrderMemberDefProperties.transitive_l hℳ hUV
      (fun a b ha hb => hU a ha b hb) x y hx hy)
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree I |>.pushFree U |>.pushFree V |>.pushFree T |>.pushFree G
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] := graph_m
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC
  have hMember : mem_l hℳ G₁ D := by
    apply SecondOrderMemberDefBoundedSlice.member_l hℳ hCD (φ := φ)
      (fun x hx y hy => hTrans x hx y hy) (graph_delta_m _ _ _ _ _ _) η
    · intro s v
      cases s
      match v with
      | .here => exact hGC
      | .there .here => exact hTC
      | .there (.there .here) => exact hVC
      | .there (.there (.there .here)) => exact hUC
      | .there (.there (.there (.there .here))) => exact hIC
    · intro p
      rw [graph_formula_l (η.pushFree p) _ _ _ _ _ _]
      constructor
      · intro hp
        obtain ⟨x, y, hxE, hyT, hPair⟩ := hG₁.2.2.1.1 p hp
        obtain ⟨hxI, hxV⟩ := (hE₁ x).mp hxE
        have hHxy := ((hRead x y).mp ⟨p, hp, hPair⟩).2
        exact ⟨PowerlessRelativeLimitClosure.ordered_l hℳ hBase hLimit hC
          (hTrans I hIC x hxI) (hTrans T hTC y hyT) hPair,
          x, hxI, hxV, y, hyT, hPair, (reads_l hH hE hG hUV hxI hxV hyT).mpr hHxy⟩
      · rintro ⟨_, x, hxI, hxV, y, hyT, hPair, hValue⟩
        obtain ⟨q, hq, hPair'⟩ := (hRead x y).mpr
          ⟨(hE₁ x).mpr ⟨hxI, hxV⟩, (reads_l hH hE hG hUV hxI hxV hyT).mp hValue⟩
        have hEq : q = p := SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair
        exact hEq ▸ hq
  exact ⟨E₁, G₁, hE₁, hG₁, hMember, hRead⟩

#print axioms graph_delta_m
#print axioms reads_l
#print axioms member_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeMembershipCollapseSuccessor
