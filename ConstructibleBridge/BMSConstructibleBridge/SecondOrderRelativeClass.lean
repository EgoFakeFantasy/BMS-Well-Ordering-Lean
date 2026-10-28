import BMSConstructibleBridge.SecondOrderRelativeLevelMonotonicity

/-! # 全部相对层成员组成的类

这是后续 HCL 构造的环境类，不自动满足 Collection。这里仅证明换码保持、
传递性与指定基集成员的覆盖；没有将“环境中可数”误作“类内部可数”。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeClass

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def member_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ)) (X : SecondOrderGraph.code_l ℳ) : Prop :=
  ∃ α C : SecondOrderGraph.code_l ℳ,
    SecondOrderRelativeLevel.spec_l hℳ B hB α C ∧ SecondOrderGraph.mem_l X C

theorem congr_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {X Y : SecondOrderGraph.code_l ℳ}
    (hXY : SecondOrderGraph.eq_l X Y) : member_l hℳ B hB X ↔ member_l hℳ B hB Y := by
  constructor
  · rintro ⟨α, C, hC, hX⟩
    exact ⟨α, C, hC, (SecondOrderGraph.mem_congr_l hℳ hXY (SecondOrderGraph.refl_l hℳ C)).mp hX⟩
  · rintro ⟨α, C, hC, hY⟩
    exact ⟨α, C, hC, (SecondOrderGraph.mem_congr_l hℳ hXY (SecondOrderGraph.refl_l hℳ C)).mpr hY⟩

theorem transitive_l (hℳ : Theory.Models ℳ theory_m) {B : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {X Y : SecondOrderGraph.code_l ℳ}
    (hX : member_l hℳ B hB X) (hYX : SecondOrderGraph.mem_l Y X) : member_l hℳ B hB Y := by
  obtain ⟨α, C, hC, hXC⟩ := hX
  exact ⟨α, C, hC, SecondOrderRelativeLevelProperties.transitive_l hℳ hC X Y hXC hYX⟩

theorem base_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (X : SecondOrderGraph.code_l ℳ) (hX : SecondOrderGraph.mem_l X ⟨B, zero_l ℳ, hB⟩) :
    member_l hℳ B hB X := by
  obtain ⟨α, hα, _⟩ := SecondOrderOrdinalSuccessor.empty_exists_l hℳ
  obtain ⟨C, hC⟩ := SecondOrderRelativeLevel.exists_l hℳ B hB hBase α hα
  exact ⟨α, C, hC, SecondOrderRelativeLevelProperties.base_l hℳ hC X hX⟩

theorem level_l (hℳ : Theory.Models ℳ theory_m) (B : set_l ℳ)
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (α C : SecondOrderGraph.code_l ℳ)
    (hα : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ))
      (SecondOrderQuotient.mk_l hℳ α))
    (hC : SecondOrderRelativeLevel.spec_l hℳ B hB α C) : member_l hℳ B hB C := by
  obtain ⟨β, hβ, hαβ, _⟩ := SecondOrderOrdinalSuccessor.exists_l hℳ α hα
  obtain ⟨C', hC'⟩ := SecondOrderRelativeLevel.exists_l hℳ B hB hBase β hβ
  exact ⟨β, C', hC', SecondOrderRelativeLevelMonotonicity.members_l hℳ
    (SecondOrderGraph.refl_l hℳ ⟨B, zero_l ℳ, hB⟩) hαβ hC hC'⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeClass
