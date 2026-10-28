import BMSConstructibleBridge.SecondOrderCodedFamilyCollection
import BMSConstructibleBridge.SecondOrderOrdinalBounded
import BMSConstructibleBridge.SecondOrderOrdinalComparison
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage

/-! # 已编码序数族的共同内部上界

先用族实数收集整行序数，再取其并集和后继。序数性由环境正则性及已证
三歧性取得，不对模型序数作宿主归纳，也不使用 Collection。共同上界是
环境序数；已有序数覆盖把它放进任意给定传递基点的相对类，即使族实数
自身不在相对类中。这仍不证明实数见证族的类内闭包或完整理解。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCodedOrdinalFamilyBound

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic
open SecondOrderQuotient (type_l mk_l mem_l)
open SecondOrderCodedFamilyCollection (rows_wf_l member_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}
  {hℳ : Theory.Models ℳ theory_m}

private abbrev reduct_l (hℳ : Theory.Models ℳ theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

def rows_ordinal_l (hℳ : Theory.Models ℳ theory_m) (H I : SecondOrderModel.set_l ℳ) : Prop :=
  ∀ i, SecondOrderModel.mem_l i I → ∀ Y : SecondOrderGraph.code_l ℳ,
    SecondOrderSections.spec_l H i Y.real → Y.root = SecondOrderModel.zero_l ℳ →
      SetTheory.Structure.IsOrdinal (reduct_l hℳ) (mk_l hℳ Y)

/-- 并集序数的构造只要求已有集合的成员都是序数，不假定任意序数族可收集。 -/
theorem union_l {C : type_l hℳ}
    (hC : ∀ a, mem_l hℳ a C → SetTheory.Structure.IsOrdinal (reduct_l hℳ) a) :
    ∃ U : type_l hℳ, SetTheory.Structure.IsOrdinal (reduct_l hℳ) U ∧
      ∀ x, mem_l hℳ x U ↔ ∃ a, mem_l hℳ a C ∧ mem_l hℳ x a := by
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ C : type_l hℳ, ∃ U, ∀ x,
    mem_l hℳ x U ↔ ∃ a, mem_l hℳ a C ∧ mem_l hℳ x a at hUnion
  obtain ⟨U, hU⟩ := hUnion C
  have hMember x (hx : mem_l hℳ x U) : SetTheory.Structure.IsOrdinal (reduct_l hℳ) x := by
    obtain ⟨a, ha, hx⟩ := (hU x).mp hx
    exact SetTheory.Structure.IsOrdinal.mem (hC a ha) hx
  refine ⟨U, SecondOrderOrdinalBounded.of_transitive_l hℳ ?_ ?_ ?_, hU⟩
  · intro x hx y hy
    obtain ⟨a, ha, hx⟩ := (hU x).mp hx
    exact (hU y).mpr ⟨a, ha, (hC a ha).transitive x hx y hy⟩
  · exact fun x hx y hy z hz => (hMember x hx).transitive y hy z hz
  · intro x y hx hy
    rcases SecondOrderOrdinalComparison.compare_l hℳ (hMember x hx) (hMember y hy) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- 并集的后继严格支配收集集中每个序数，包括最大成员和空族情形。 -/
theorem set_bound_l {C : type_l hℳ}
    (hC : ∀ a, mem_l hℳ a C → SetTheory.Structure.IsOrdinal (reduct_l hℳ) a) :
    ∃ δ : type_l hℳ, SetTheory.Structure.IsOrdinal (reduct_l hℳ) δ ∧
      ∀ a, mem_l hℳ a C → mem_l hℳ a δ := by
  obtain ⟨U, hUOrd, hU⟩ := union_l hC
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ U
  obtain ⟨D, hDOrd, _, hD⟩ := SecondOrderOrdinalSuccessor.exists_l hℳ A hUOrd
  refine ⟨mk_l hℳ D, hDOrd, ?_⟩
  intro a ha
  obtain ⟨B, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
  have hSubset x (hx : mem_l hℳ x (mk_l hℳ B)) : mem_l hℳ x (mk_l hℳ A) :=
    (hU x).mpr ⟨mk_l hℳ B, ha, hx⟩
  apply (hD B).mpr
  rcases SecondOrderOrdinalComparison.compare_l hℳ (hC _ ha) hUOrd with h | h | h
  · exact Or.inr ((SecondOrderQuotient.eq_iff_l hℳ B A).mp h)
  · exact Or.inl h
  · exact False.elim (SecondOrderFoundation.irrefl_l hℳ A (hSubset _ h))

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (H I : SecondOrderModel.set_l ℳ)
    (hRows : rows_wf_l H I) (hOrdinal : rows_ordinal_l hℳ H I) :
    ∃ δ : type_l hℳ, SetTheory.Structure.IsOrdinal (reduct_l hℳ) δ ∧
      ∀ D, member_l H I D → mem_l hℳ (mk_l hℳ D) δ := by
  obtain ⟨C, _, hC⟩ := SecondOrderCodedFamilyCollection.exists_l hℳ H I hRows
  have hAll a (ha : mem_l hℳ a (mk_l hℳ C)) : SetTheory.Structure.IsOrdinal (reduct_l hℳ) a := by
    obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
    obtain ⟨i, Y, hi, hY, hZero, hDY⟩ := (hC D).mp ha
    have hEq := (SecondOrderQuotient.eq_iff_l hℳ D Y).mpr hDY
    exact hEq.symm ▸ hOrdinal i hi Y hY hZero
  obtain ⟨δ, hδ, hBound⟩ := set_bound_l hAll
  exact ⟨δ, hδ, fun D hD => hBound (mk_l hℳ D) ((hC D).mpr hD)⟩

/-- 族编码可以在类外；序数上界及其相对层仍实际存在且覆盖整族。 -/
theorem level_exists_l (hℳ : Theory.Models ℳ theory_m)
    (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {B : type_l hℳ} (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (H I : SecondOrderModel.set_l ℳ) (hRows : rows_wf_l H I) (hOrdinal : rows_ordinal_l hℳ H I) :
    ∃ δ L : type_l hℳ, SetTheory.Structure.IsOrdinal (reduct_l hℳ) δ ∧
      PowerlessRelativeClassCorrespondence.member_l hℳ B δ ∧
      PowerlessRelativeHierarchySemantics.level_l hℳ B δ L ∧
      ∀ D, member_l H I D → mem_l hℳ (mk_l hℳ D) δ ∧ mem_l hℳ (mk_l hℳ D) L := by
  obtain ⟨δ, hδ, hBound⟩ := exists_l hℳ H I hRows hOrdinal
  obtain ⟨L, hL⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hδ
  exact ⟨δ, L, hδ, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase hδ, hL,
    fun D hD => ⟨hBound D hD, PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase δ L hL
      (mk_l hℳ D) (hBound D hD)⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCodedOrdinalFamilyBound
