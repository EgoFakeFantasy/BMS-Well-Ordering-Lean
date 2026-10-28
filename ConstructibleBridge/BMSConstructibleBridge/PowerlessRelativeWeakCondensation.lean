import BMSConstructibleBridge.PowerlessRelativeCollapseStageIndex
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 阶段覆盖与原 Def 闭包推出相对弱凝聚

背景为原 Z₂ 的同一图商。T 的实际传递性、基对象成员、内部 ω 覆盖和
配对／二元并闭包均显式消费；不假定 T 是 Class 集合、构造层或完整
源模型。阶段覆盖必须保留 a∈T 与 Lₐ[B]∈T，原 Def 闭包量化任意输出。
语义结论随后由精确对象句及原 Derives 接口回传。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeWeakCondensation

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (empty_l successor_l limit_l level_l)
open PowerlessRelativeCollapseStageIndex (spec_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private theorem zero_value_l {B e c : type_l hℳ} (he : empty_l hℳ e)
    (hc : level_l hℳ B e c) : c = B := by
  obtain ⟨A, f, r, _, heA, hf, hfc⟩ := hc
  rcases hf.2 e c ⟨heA, hfc⟩ with ⟨_, h⟩ | ⟨a, d, hSucc, _, _⟩ | ⟨hLimit, _⟩
  · exact h
  · exact (he a ((hSucc a).mpr (Or.inr rfl))).elim
  · obtain ⟨a, ha⟩ := hLimit.1
    exact (he a ha).elim

/-- 后继阶段和原 Def 输出分别由真实基础闭包和 Def 闭包留在 T。 -/
theorem successor_l {B T J : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hT : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) T)
    (hD : ∀ x, mem_l hℳ x T → ∀ r, SecondOrderMemberDef.spec_l hℳ x r → mem_l hℳ r T)
    (hJ : spec_l B T J) {a : type_l hℳ} (ha : mem_l hℳ a J) :
    ∃ b, mem_l hℳ b J ∧ mem_l hℳ a b := by
  obtain ⟨haT, c, hcT, hc⟩ := (hJ a).mp ha
  obtain ⟨b, d, hSucc, hd, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hB hc
  have hbT := PowerlessRelativeFiniteHullAssignments.adjoin_l hT haT haT hSucc
  exact ⟨b, (hJ b).mpr ⟨hbT, d, hD c hcT d hDef, hd⟩,
    (hSucc a).mpr (Or.inr rfl)⟩

theorem limit_l (K : source_coding_l hℳ) {B T J : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hBT : mem_l hℳ B T) (hω : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x T)
    (hT : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) T)
    (hD : ∀ x, mem_l hℳ x T → ∀ r, SecondOrderMemberDef.spec_l hℳ x r → mem_l hℳ r T)
    (hJ : spec_l B T J) : PowerlessRelativeHierarchySemantics.limit_l hℳ J := by
  let e := (numberCode_l K (SecondOrderModel.zero_l ℳ)).val
  have he : empty_l hℳ e := PowerlessBMSQuotientSuccessor.zero_l K
  have heOrd := SecondOrderOrdinalBounded.of_transitive_l hℳ (a := e)
    (fun x hx => (he x hx).elim) (fun x hx => (he x hx).elim)
    (fun x _ hx => (he x hx).elim)
  obtain ⟨c, hc⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hB heOrd
  have hcB := zero_value_l he hc
  subst c
  refine ⟨⟨e, (hJ e).mpr ⟨hω e (numberCode_l K (SecondOrderModel.zero_l ℳ)).property,
    B, hBT, hc⟩⟩, ?_⟩
  exact fun a ha => successor_l hB hT hD hJ ha

/-- 原极限层的精确并集读取全部目标成员，得到同一 T 的层资格。 -/
theorem exists_l (K : source_coding_l hℳ) {B T : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hT : ∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T)
    (hBT : mem_l hℳ B T) (hω : ∀ x, mem_l hℳ x K.omega → mem_l hℳ x T)
    (hC : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) T)
    (hS : ∀ x, mem_l hℳ x T → ∃ a c, mem_l hℳ a T ∧ mem_l hℳ c T ∧
      level_l hℳ B a c ∧ mem_l hℳ x c)
    (hD : ∀ x, mem_l hℳ x T → ∀ r, SecondOrderMemberDef.spec_l hℳ x r → mem_l hℳ r T) :
    ∃ J, spec_l B T J ∧ SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) J ∧
      PowerlessRelativeHierarchySemantics.limit_l hℳ J ∧ level_l hℳ B J T := by
  obtain ⟨J, hJ⟩ := PowerlessRelativeCollapseStageIndex.exists_l K B T
  have hOrd := PowerlessRelativeCollapseStageIndex.ordinal_l hB hT hJ
  have hLimit := limit_l K hB hBT hω hC hD hJ
  obtain ⟨C, hLevel⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hB hOrd
  have hEq : T = C := by
    apply SecondOrderQuotient.ext_l hℳ
    intro x
    constructor
    · intro hx
      obtain ⟨a, c, haT, hcT, hc, hxc⟩ := hS x hx
      exact (PowerlessRelativeLimitClosure.value_l hℳ hB hLimit hLevel x).mpr
        ⟨a, c, (hJ a).mpr ⟨haT, c, hcT, hc⟩, hc, hxc⟩
    · intro hx
      obtain ⟨a, c, haJ, hc, hxc⟩ :=
        (PowerlessRelativeLimitClosure.value_l hℳ hB hLimit hLevel x).mp hx
      obtain ⟨_, d, hdT, hd⟩ := (hJ a).mp haJ
      have hcd := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hc hd
      exact hT d hdT x (hcd ▸ hxc)
  exact ⟨J, hJ, hOrd, hLimit, hEq.symm ▸ hLevel⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeWeakCondensation
