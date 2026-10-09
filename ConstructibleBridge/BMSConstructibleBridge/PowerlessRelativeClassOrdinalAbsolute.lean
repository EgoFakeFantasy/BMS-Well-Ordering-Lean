import BMSConstructibleBridge.PowerlessRelativeClassCoverageAbsolute
import BMSConstructibleBridge.SecondOrderFoundation

/-! # 实际相对类中原序数资格的双向绝对性

对象语言为纯隶属 ℒ，背景为原 Z₂。类内线序读回全部 raw 成员，
而任意 raw 非空子集的极小元由原正则性给出；不要求子集属于 Class。
完整序数资格不是 Δ₀，也不由本模块推断原 Def 或层次公式的绝对性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOrdinalAbsolute

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

/-- 类内资格的反向运输不缩小原最小元条款的子集范围。 -/
theorem source_l (α : M)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩₀) α) :
    SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α.val := by
  have hSame {a b : M} (h : SetTheory.Structure.SameMembers
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩₀) a b) :
      SetTheory.Structure.SameMembers
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) a.val b.val := by
    intro z
    constructor
    · intro hz
      exact (h ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase a.property hz⟩).mp hz
    · intro hz
      exact (h ⟨z, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase b.property hz⟩).mpr hz
  have hMember (a : SecondOrderQuotient.type_l hℳ) (ha : mem_l hℳ a α.val) :
      PowerlessRelativeClassCorrespondence.member_l hℳ B a :=
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase α.property ha
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · intro a ha b hb
    exact hα.transitive ⟨a, hMember a ha⟩ ha
      ⟨b, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase (hMember a ha) hb⟩ hb
  · refine ⟨?_, ?_, ?_⟩
    · exact fun a ha => hα.wellOrder.linear.irrefl ⟨a, hMember a ha⟩ ha
    · exact fun a ha b hb c hc => hα.wellOrder.linear.trans
        ⟨a, hMember a ha⟩ ha ⟨b, hMember b hb⟩ hb ⟨c, hMember c hc⟩ hc
    · intro a ha b hb
      exact (hα.wellOrder.linear.compare ⟨a, hMember a ha⟩ ha
        ⟨b, hMember b hb⟩ hb).imp hSame id
  · intro S hSub hNonempty
    have hFoundation := SecondOrderFoundation.models_l hℳ
    change ∀ S : SecondOrderQuotient.type_l hℳ,
      (∃ a, mem_l hℳ a S) → ∃ a, mem_l hℳ a S ∧
        ∀ b, mem_l hℳ b a → ¬mem_l hℳ b S at hFoundation
    obtain ⟨a, ha, hMinimal⟩ := hFoundation S hNonempty
    refine ⟨a, ha, ?_⟩
    intro b hb
    rcases hα.wellOrder.linear.compare ⟨a, hMember a (hSub a ha)⟩ (hSub a ha)
      ⟨b, hMember b (hSub b hb)⟩ (hSub b hb) with h | h | h
    · exact Or.inl (hSame h)
    · exact Or.inr h
    · exact False.elim (hMinimal b h hb)

theorem ordinal_l (α : M) :
    SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒩₀) α ↔
    SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) α.val :=
  ⟨source_l α, PowerlessRelativeClassCoverageAbsolute.ordinal_l α⟩

/-- 同一个原 ordinal AST，环境只投影已有类内取值。 -/
theorem formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒩₀ Γ Δ)
    (a : Term ℒ Γ Δ .set) :
    (PowerlessRelativeHierarchySyntax.ordinal_m a).satisfies η ↔
      (PowerlessRelativeHierarchySyntax.ordinal_m a).satisfies
        (PowerlessRelativeClassRelativization.env_l η) := by
  rw [PowerlessMemberOrdinalAbsolute.formula_l (PowerlessRelativeClassStructure.ext_l hℳ B hBase),
    PowerlessRelativeHierarchySemantics.ordinal_formula_l]
  have hEval : a.eval (PowerlessRelativeClassRelativization.env_l η) = (a.eval η).val := by
    match a with
    | .bvar _ => rfl
    | .fvar _ => rfl
    | .app f _ => nomatch f
  rw [hEval]
  exact ordinal_l (a.eval η)

#print axioms source_l
#print axioms ordinal_l
#print axioms formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassOrdinalAbsolute
