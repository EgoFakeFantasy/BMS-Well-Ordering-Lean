import BMSConstructibleBridge.SecondOrderRelativeHierarchyClosure
import BMSConstructibleBridge.SecondOrderGraphSubsetFormula

/-! # 相对层次单调性的三类归纳步

后继使用传递母集包含于 Def；极限使用全部严格前驱行的精确并集。
这里只给出归纳步，完整结论另由实际二阶公式作内部良基归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyMonotonicityStep

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderGraphSubsetFormula (subset_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_l (R S : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∀ i, relation_l R i n → ∀ U W
    (hU : SecondOrderDomain.wf_l U (zero_l ℳ)) (hW : SecondOrderDomain.wf_l W (zero_l ℳ)),
    SecondOrderSections.spec_l S i U → SecondOrderSections.spec_l S n W →
      subset_l ⟨U, zero_l ℳ, hU⟩ ⟨W, zero_l ℳ, hW⟩

theorem successor_contains_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hTrans : SecondOrderTransitiveSuperset.transitive_l A) {W : set_l ℳ}
    (hW : SecondOrderDomain.wf_l W (zero_l ℳ))
    (hDef : SecondOrderCanonicalMemberDefGraph.canonical_l A.real A.root W) :
    subset_l A ⟨W, zero_l ℳ, hW⟩ := by
  obtain ⟨a, hDefault, V, E, D, Q, R, T, F, G, P, h⟩ := hDef
  have hDef' := SecondOrderCanonicalMemberDefSemantics.represents_l hℳ A hDefault h
  have hTrans' : ∀ x z, SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ A) →
      SecondOrderQuotient.mem_l hℳ z x → SecondOrderQuotient.mem_l hℳ z (SecondOrderQuotient.mk_l hℳ A) := by
    intro x z hx hz
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨Z, rfl⟩ := SecondOrderQuotient.surj_l hℳ z
    exact hTrans X Z hx hz
  intro X hx
  exact SecondOrderMemberDefProperties.contains_l hℳ hDef' hTrans'
    (SecondOrderQuotient.mk_l hℳ X) hx

theorem step_l (hℳ : Theory.Models ℳ theory_m) {B R S : set_l ℳ} {n : num_l ℳ}
    (hRows : SecondOrderPredecessorUnionSemantics.rows_wf_l R S n)
    (hTrans : SecondOrderRelativeHierarchyClosure.rows_transitive_l R S n)
    (hPast : ∀ k, relation_l R k n → rows_l R S k)
    (hStage : ∀ W, SecondOrderSections.spec_l S n W → SecondOrderRelativeHierarchyStep.spec_l B R S n W) :
    rows_l R S n := by
  intro i hi U W hU hW hUi hWn
  rcases hStage W hWn with ⟨hMin, _⟩ | ⟨k, Y, hk, hY, hDef⟩ | ⟨_, G, P, hUnion⟩
  · exact False.elim (hMin i hi)
  · have hYw := hRows k hk.1 Y hY
    have hContains := successor_contains_l hℳ ⟨Y, zero_l ℳ, hYw⟩
      (hTrans k hk.1 Y hYw hY) hW hDef
    rcases hk.2 i hi with rfl | hik
    · have hUY := SecondOrderSections.unique_l hℳ hUi hY
      subst Y
      exact hContains
    · intro X hx
      exact hContains X (hPast k hk.1 i hik U Y hU hYw hUi hY X hx)
  · intro X hx
    exact (SecondOrderPredecessorUnionSemantics.mem_l hℳ hUnion hRows X).mpr
      ⟨i, ⟨U, zero_l ℳ, hU⟩, hi, hUi, rfl, hx⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyMonotonicityStep
