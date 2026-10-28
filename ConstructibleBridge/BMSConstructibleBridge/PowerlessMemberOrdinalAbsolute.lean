import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessRelativeHierarchySemantics

/-! # 传递成员域中的真实内部序数

原内部序数限制到传递成员域后仍是内部序数。反方向只使用原母模型
的基础公理取得任意 raw 非空子集的极小元，再用成员域已给出的线序
取得最小元；不要求该子集属于成员域，也不借用其完整源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberOrdinalAbsolute

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  PowerlessMemberStructure.type_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {W : carrier_l ℳ}
  {hW : ∃ x, member_l ℳ x W}

local notation "𝒱" => SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ
local notation "𝒩₀" => SetTheory.Definitional.Project.FirstOrderSemantics.reduct
  (PowerlessMemberStructure.structure_l W hW)
local notation "M" => PowerlessMemberStructure.type_l (ℳ := ℳ) W

/-- 原序数 AST 在任意纯结构中的语义，不限于原 Z₂ 商结构。 -/
theorem formula_l (hExt : SetTheory.Extensional 𝒱) {Γ Δ : SortContext ℒ}
    (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.ordinal_m a).satisfies η ↔
      SetTheory.Structure.IsOrdinal 𝒱 (a.eval η) := by
  rw [PowerlessRelativeHierarchySyntax.ordinal_m, Formula.satisfies_substitute]
  exact (SetTheory.Definitional.Project.FirstOrderSemantics.formula_correct hExt
    SecondOrderGraphOrdinalFormula.project_m SecondOrderGraphOrdinalFormula.project_closed_m
    (η.pullback (PowerlessRelativeHierarchySyntax.ordinal_substitution_m a))
    (fun _ => a.eval η)).trans (SetTheory.Definitional.Project.Formula.satisfies_isOrdinal_iff _
      SetTheory.Definitional.Term.newest)

/-- 源内部良序的最小元证书限制到同一成员域。 -/
theorem ordinal_l (hTrans : PowerlessNaturalOrder.transitive_l W) (α : M)
    (hα : SetTheory.Structure.IsOrdinal 𝒱 α.val) : SetTheory.Structure.IsOrdinal 𝒩₀ α := by
  have hSame {a b : M} (h : SetTheory.Structure.SameMembers 𝒱 a.val b.val) :
      SetTheory.Structure.SameMembers 𝒩₀ a b := fun z => h z.val
  refine ⟨(fun a ha b hb => hα.transitive a.val ha b.val hb), ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact fun a ha => hα.wellOrder.linear.irrefl a.val ha
    · exact fun a ha b hb c hc => hα.wellOrder.linear.trans a.val ha b.val hb c.val hc
    · intro a ha b hb
      exact (hα.wellOrder.linear.compare a.val ha b.val hb).imp hSame id
  · intro S hSub hNonempty
    obtain ⟨z, hz⟩ := hNonempty
    obtain ⟨a, ha, hLeast⟩ := hα.wellOrder.least S.val
      (fun b hb => hSub ⟨b, hTrans S.val b S.property hb⟩ hb) ⟨z.val, hz⟩
    let a₀ : M := ⟨a, hTrans S.val a S.property ha⟩
    exact ⟨a₀, ha, fun b hb => (hLeast b.val hb).imp hSame id⟩

/-- 任意 raw 子集的最小元由原基础公理与真实线序给出，不缩小子集范围。 -/
theorem source_l (hTrans : PowerlessNaturalOrder.transitive_l W)
    (hFoundation : ∀ S : carrier_l ℳ, (∃ a, member_l ℳ a S) →
      ∃ a, member_l ℳ a S ∧ ∀ b, member_l ℳ b S → ¬member_l ℳ b a)
    (α : M) (hα : SetTheory.Structure.IsOrdinal 𝒩₀ α) : SetTheory.Structure.IsOrdinal 𝒱 α.val := by
  have hSame {a b : M} (h : SetTheory.Structure.SameMembers 𝒩₀ a b) :
      SetTheory.Structure.SameMembers 𝒱 a.val b.val := by
    intro z
    constructor
    · intro hz
      exact (h ⟨z, hTrans a.val z a.property hz⟩).mp hz
    · intro hz
      exact (h ⟨z, hTrans b.val z b.property hz⟩).mpr hz
  have hMember (a : carrier_l ℳ) (ha : member_l ℳ a α.val) : member_l ℳ a W :=
    hTrans α.val a α.property ha
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro a ha b hb
    exact hα.transitive ⟨a, hMember a ha⟩ ha ⟨b, hTrans a b (hMember a ha) hb⟩ hb
  · refine ⟨?_, ?_, ?_⟩
    · exact fun a ha => hα.wellOrder.linear.irrefl ⟨a, hMember a ha⟩ ha
    · exact fun a ha b hb c hc => hα.wellOrder.linear.trans
        ⟨a, hMember a ha⟩ ha ⟨b, hMember b hb⟩ hb ⟨c, hMember c hc⟩ hc
    · intro a ha b hb
      exact (hα.wellOrder.linear.compare ⟨a, hMember a ha⟩ ha
        ⟨b, hMember b hb⟩ hb).imp hSame id
  · intro S hSub hNonempty
    obtain ⟨a, ha, hMinimal⟩ := hFoundation S hNonempty
    refine ⟨a, ha, ?_⟩
    intro b hb
    rcases hα.wellOrder.linear.compare ⟨a, hMember a (hSub a ha)⟩ (hSub a ha)
      ⟨b, hMember b (hSub b hb)⟩ (hSub b hb) with h | h | h
    · exact Or.inl (hSame h)
    · exact Or.inr h
    · exact False.elim (hMinimal b hb h)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberOrdinalAbsolute
