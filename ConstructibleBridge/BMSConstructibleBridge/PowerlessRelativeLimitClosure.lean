import BMSConstructibleBridge.PowerlessRelativeClassBounds
import BMSConstructibleBridge.SecondOrderRelativeLevelLimit
import BMSConstructibleBridge.SecondOrderMemberDefBasicClosure
import BMSConstructibleBridge.SecondOrderOrdinalLimitDerives

/-! # 固定非零极限层内的有限构造闭包

先把每个成员定位到严格较早的层，再证明其后继仍严格低于极限阶段。
配对与并集因此留在同一个给定层中；不是仅留在相对并类中。
这里只建设语义中间接口，正式闭包句及原 Z₂ 推导在后续模块接入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitClosure

open Logic FirstOrder
open SecondOrderQuotient (type_l mk_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

private abbrev quotient_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :=
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)

theorem value_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C) (x : type_l hℳ) :
    mem_l hℳ x C ↔ ∃ a c, mem_l hℳ a β ∧ level_l hℳ B a c ∧ mem_l hℳ x c := by
  obtain ⟨W, hW, rfl, hTrans⟩ := PowerlessRelativeHierarchyDerives.base_code_l hℳ B hBase
  obtain ⟨A, rfl⟩ := SecondOrderQuotient.surj_l hℳ β
  obtain ⟨D, rfl⟩ := SecondOrderQuotient.surj_l hℳ C
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  have hNonempty : ∃ γ : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l γ A := by
    obtain ⟨γ, hγ⟩ := hLimit.1
    obtain ⟨G, rfl⟩ := SecondOrderQuotient.surj_l hℳ γ
    exact ⟨G, hγ⟩
  have hNoMax (γ : SecondOrderGraph.code_l ℳ) (hγ : SecondOrderGraph.mem_l γ A) :
      ∃ δ : SecondOrderGraph.code_l ℳ, SecondOrderGraph.mem_l δ A ∧ SecondOrderGraph.mem_l γ δ := by
    obtain ⟨δ, hδ, hγδ⟩ := hLimit.2 (mk_l hℳ γ) hγ
    obtain ⟨G, rfl⟩ := SecondOrderQuotient.surj_l hℳ δ
    exact ⟨G, hδ, hγδ⟩
  refine (SecondOrderRelativeLevelLimit.value_l hℳ hNonempty hNoMax
    (PowerlessRelativeLevelCorrespondence.reverse_l hℳ hTrans hC) X).trans ?_
  constructor
  · rintro ⟨α, Y, hα, hY, hXY⟩
    exact ⟨mk_l hℳ α, mk_l hℳ Y, hα,
      PowerlessRelativeLevelCorrespondence.forward_l hℳ hTrans hY, hXY⟩
  · rintro ⟨a, c, ha, hc, hXc⟩
    obtain ⟨α, rfl⟩ := SecondOrderQuotient.surj_l hℳ a
    obtain ⟨Y, rfl⟩ := SecondOrderQuotient.surj_l hℳ c
    exact ⟨α, Y, ha, PowerlessRelativeLevelCorrespondence.reverse_l hℳ hTrans hc, hXc⟩

theorem common_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C X Y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hX : mem_l hℳ X C) (hY : mem_l hℳ Y C) :
    ∃ a c, mem_l hℳ a β ∧ level_l hℳ B a c ∧ mem_l hℳ X c ∧ mem_l hℳ Y c := by
  obtain ⟨a, c, ha, hc, hXc⟩ := (value_l hℳ hBase hLimit hC X).mp hX
  obtain ⟨b, d, hb, hd, hYd⟩ := (value_l hℳ hBase hLimit hC Y).mp hY
  rcases SecondOrderOrdinalComparison.compare_l hℳ
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hc) (PowerlessRelativeLevelClosure.ordinal_l hℳ hd) with h | h | h
  · subst b
    have hcd := PowerlessRelativeHierarchyAgreement.level_unique_l hℳ hc hd
    exact ⟨a, c, ha, hc, hXc, hcd.symm ▸ hYd⟩
  · exact ⟨b, d, hb, hd, PowerlessRelativeLevelClosure.subset_l hℳ hBase h hc hd X hXc, hYd⟩
  · exact ⟨a, c, ha, hc, hXc, PowerlessRelativeLevelClosure.subset_l hℳ hBase h hd hc Y hYd⟩

private theorem irrefl_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (x : type_l hℳ) :
    ¬mem_l hℳ x x := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact SecondOrderFoundation.irrefl_l hℳ X

theorem def_bound_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C a c : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (ha : mem_l hℳ a β) (hc : level_l hℳ B a c) :
    ∃ b d, mem_l hℳ b β ∧ level_l hℳ B b d ∧ SecondOrderMemberDef.spec_l hℳ c d := by
  obtain ⟨b, d, hSucc, hd, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hc
  obtain ⟨δ, hδ, haδ⟩ := hLimit.2 a ha
  have hβ : SetTheory.Structure.IsOrdinal (quotient_l hℳ) β :=
    PowerlessRelativeLevelClosure.ordinal_l hℳ hC
  have hδOrd : SetTheory.Structure.IsOrdinal (quotient_l hℳ) δ := by
    apply SetTheory.Structure.IsOrdinal.mem hβ
    exact hδ
  have hbβ : mem_l hℳ b β := by
    rcases SecondOrderOrdinalComparison.compare_l hℳ (PowerlessRelativeLevelClosure.ordinal_l hℳ hd) hδOrd with h | h | h
    · exact h.symm ▸ hδ
    · exact hβ.transitive δ hδ b h
    · rcases (hSucc δ).mp h with hδa | hδa
      · exact (irrefl_l hℳ δ (hδOrd.transitive a haδ δ hδa)).elim
      · exact (irrefl_l hℳ δ (hδa ▸ haδ)).elim
  exact ⟨b, d, hbβ, hd, hDef⟩

theorem pair_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C X Y P : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hX : mem_l hℳ X C) (hY : mem_l hℳ Y C)
    (hP : SecondOrderPairObjects.pair_l hℳ X Y P) : mem_l hℳ P C := by
  obtain ⟨a, c, ha, hc, hXc, hYc⟩ := common_l hℳ hBase hLimit hC hX hY
  obtain ⟨b, d, hb, hd, hDef⟩ := def_bound_l hℳ hBase hLimit hC ha hc
  exact (value_l hℳ hBase hLimit hC P).mpr
    ⟨b, d, hb, hd, SecondOrderMemberDefPair.member_l hℳ hDef hXc hYc hP⟩

theorem ordered_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C X Y P : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hX : mem_l hℳ X C) (hY : mem_l hℳ Y C)
    (hP : SecondOrderPairObjects.ordered_l hℳ X Y P) : mem_l hℳ P C := by
  obtain ⟨s, t, hs, ht, hp⟩ := hP
  exact pair_l hℳ hBase hLimit hC (pair_l hℳ hBase hLimit hC hX hX hs)
    (pair_l hℳ hBase hLimit hC hX hY ht) hp

theorem union_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C X U : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C) (hX : mem_l hℳ X C)
    (hU : ∀ w, mem_l hℳ w U ↔ ∃ y, mem_l hℳ y X ∧ mem_l hℳ w y) : mem_l hℳ U C := by
  obtain ⟨a, c, ha, hc, hXc⟩ := (value_l hℳ hBase hLimit hC X).mp hX
  obtain ⟨b, d, hb, hd, hDef⟩ := def_bound_l hℳ hBase hLimit hC ha hc
  exact (value_l hℳ hBase hLimit hC U).mpr ⟨b, d, hb, hd,
    SecondOrderMemberDefBasicClosure.union_l hℳ hDef hXc
      (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hc) hU⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitClosure
