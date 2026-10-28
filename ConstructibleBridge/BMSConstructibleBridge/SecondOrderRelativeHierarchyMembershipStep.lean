import BMSConstructibleBridge.SecondOrderRelativeHierarchyMonotonicityStep

/-! # 前驱阶段作为对象属于后阶段

区别于子集单调性：后继阶段确实含母集对象，极限阶段使用无最大前驱和
前驱间线序性找到更晚的前驱，再读取精确并集。这是内部归纳的逐步引理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyMembershipStep

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_l (R S : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∀ i, relation_l R i n → ∀ U W
    (hU : SecondOrderDomain.wf_l U (zero_l ℳ)) (hW : SecondOrderDomain.wf_l W (zero_l ℳ)),
    SecondOrderSections.spec_l S i U → SecondOrderSections.spec_l S n W →
      SecondOrderGraph.mem_l ⟨U, zero_l ℳ, hU⟩ ⟨W, zero_l ℳ, hW⟩

def comparable_l (R : set_l ℳ) : Prop :=
  ∀ n i j, relation_l R i n → relation_l R j n → relation_l R i j ∨ i = j ∨ relation_l R j i

theorem later_l {R : set_l ℳ} (hCompare : comparable_l R) {i n : num_l ℳ}
    (hLimit : SecondOrderRelativeHierarchyStep.limit_l R n) (hi : relation_l R i n) :
    ∃ j, relation_l R j n ∧ relation_l R i j := by
  classical
  by_contra hNone
  apply hLimit.2
  refine ⟨i, hi, ?_⟩
  intro j hj
  rcases hCompare n i j hi hj with hij | hij | hji
  · exact False.elim (hNone ⟨j, hj, hij⟩)
  · exact Or.inl hij.symm
  · exact Or.inr hji

theorem successor_member_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    {W : set_l ℳ} (hW : SecondOrderDomain.wf_l W (zero_l ℳ))
    (hDef : SecondOrderCanonicalMemberDefGraph.canonical_l A.real A.root W) :
    SecondOrderGraph.mem_l A ⟨W, zero_l ℳ, hW⟩ := by
  obtain ⟨a, hDefault, V, E, D, Q, R, T, F, G, P, h⟩ := hDef
  exact SecondOrderMemberDefProperties.mother_member_l hℳ
    (SecondOrderCanonicalMemberDefSemantics.represents_l hℳ A hDefault h)

theorem step_l (hℳ : Theory.Models ℳ theory_m) {B R S : set_l ℳ} {n : num_l ℳ}
    (hCompare : comparable_l R)
    (hRows : SecondOrderPredecessorUnionSemantics.rows_wf_l R S n)
    (hTrans : SecondOrderRelativeHierarchyClosure.rows_transitive_l R S n)
    (hPast : ∀ k, relation_l R k n → rows_l R S k)
    (hStage : ∀ W, SecondOrderSections.spec_l S n W → SecondOrderRelativeHierarchyStep.spec_l B R S n W) :
    rows_l R S n := by
  intro i hi U W hU hW hUi hWn
  rcases hStage W hWn with ⟨hMin, _⟩ | ⟨k, Y, hk, hY, hDef⟩ | ⟨hLimit, G, P, hUnion⟩
  · exact False.elim (hMin i hi)
  · have hYw := hRows k hk.1 Y hY
    rcases hk.2 i hi with rfl | hik
    · have hUY := SecondOrderSections.unique_l hℳ hUi hY
      subst Y
      exact successor_member_l hℳ ⟨U, zero_l ℳ, hU⟩ hW hDef
    · exact SecondOrderRelativeHierarchyMonotonicityStep.successor_contains_l hℳ
        ⟨Y, zero_l ℳ, hYw⟩ (hTrans k hk.1 Y hYw hY) hW hDef
        ⟨U, zero_l ℳ, hU⟩ (hPast k hk.1 i hik U Y hU hYw hUi hY)
  · obtain ⟨k, hk, hik⟩ := later_l hCompare hLimit hi
    obtain ⟨Y, hY⟩ := SecondOrderSections.exists_l hℳ S k
    have hYw := hRows k hk Y hY
    exact (SecondOrderPredecessorUnionSemantics.mem_l hℳ hUnion hRows ⟨U, zero_l ℳ, hU⟩).mpr
      ⟨k, ⟨Y, zero_l ℳ, hYw⟩, hk, hY, rfl, hPast k hk i hik U Y hU hYw hUi hY⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyMembershipStep
