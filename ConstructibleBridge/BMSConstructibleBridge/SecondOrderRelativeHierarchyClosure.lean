import BMSConstructibleBridge.SecondOrderRelativeHierarchy
import BMSConstructibleBridge.SecondOrderMemberDefProperties
import BMSConstructibleBridge.SecondOrderTransitiveSuperset

/-! # 相对层次的逐步传递性

传递性在原图商的实际对象上比较；后继阶段消费已验证的 Def 闭包，极限
阶段消费精确前驱并集规格。本文件给出归纳步，不把任意外部性质用于归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyClosure

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_transitive_l (R S : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∀ i, relation_l R i n → ∀ W (hW : SecondOrderDomain.wf_l W (zero_l ℳ)),
    SecondOrderSections.spec_l S i W → SecondOrderTransitiveSuperset.transitive_l ⟨W, zero_l ℳ, hW⟩

theorem successor_transitive_l (hℳ : Theory.Models ℳ theory_m) (A : SecondOrderGraph.code_l ℳ)
    (hA : SecondOrderTransitiveSuperset.transitive_l A) {W : set_l ℳ}
    (hW : SecondOrderDomain.wf_l W (zero_l ℳ))
    (hDef : SecondOrderCanonicalMemberDefGraph.canonical_l A.real A.root W) :
    SecondOrderTransitiveSuperset.transitive_l ⟨W, zero_l ℳ, hW⟩ := by
  obtain ⟨a, hDefault, V, E, D, Q, R, T, F, G, P, h⟩ := hDef
  have hDef' := SecondOrderCanonicalMemberDefSemantics.represents_l hℳ A hDefault h
  have hATrans : ∀ x z, SecondOrderQuotient.mem_l hℳ x (SecondOrderQuotient.mk_l hℳ A) →
      SecondOrderQuotient.mem_l hℳ z x → SecondOrderQuotient.mem_l hℳ z (SecondOrderQuotient.mk_l hℳ A) := by
    intro x z hx hz
    obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
    obtain ⟨Z, rfl⟩ := SecondOrderQuotient.surj_l hℳ z
    exact hA X Z hx hz
  have hTrans := SecondOrderMemberDefProperties.transitive_l hℳ hDef' hATrans
  intro X Z hx hz
  exact hTrans (SecondOrderQuotient.mk_l hℳ X) (SecondOrderQuotient.mk_l hℳ Z) hx hz

theorem union_transitive_l (hℳ : Theory.Models ℳ theory_m) {R S G P W : set_l ℳ} {n : num_l ℳ}
    (h : SecondOrderPredecessorUnion.spec_l R S n G P W)
    (hRows : SecondOrderPredecessorUnionSemantics.rows_wf_l R S n)
    (hTrans : rows_transitive_l R S n) :
    SecondOrderTransitiveSuperset.transitive_l (SecondOrderPredecessorUnionSemantics.code_l hℳ h hRows) := by
  intro X Z hx hz
  obtain ⟨i, Y, hi, hY, hRoot, hxY⟩ := (SecondOrderPredecessorUnionSemantics.mem_l hℳ h hRows X).mp hx
  have hYTrans : SecondOrderTransitiveSuperset.transitive_l Y := by
    have hYw : SecondOrderDomain.wf_l Y.real (zero_l ℳ) := hRoot ▸ Y.wf
    have hT := hTrans i hi Y.real hYw hY
    have hCode : (⟨Y.real, zero_l ℳ, hYw⟩ : SecondOrderGraph.code_l ℳ) = Y := by
      cases Y
      cases hRoot
      rfl
    exact hCode ▸ hT
  apply (SecondOrderPredecessorUnionSemantics.mem_l hℳ h hRows Z).mpr
  exact ⟨i, Y, hi, hY, hRoot, hYTrans X Z hxY hz⟩

theorem step_l (hℳ : Theory.Models ℳ theory_m) {B R S W : set_l ℳ} {n : num_l ℳ}
    (hB : SecondOrderDomain.wf_l B (zero_l ℳ))
    (hBase : SecondOrderTransitiveSuperset.transitive_l ⟨B, zero_l ℳ, hB⟩)
    (hRows : SecondOrderPredecessorUnionSemantics.rows_wf_l R S n)
    (hTrans : rows_transitive_l R S n)
    (hSpec : SecondOrderRelativeHierarchyStep.spec_l B R S n W)
    (hW : SecondOrderDomain.wf_l W (zero_l ℳ)) :
    SecondOrderTransitiveSuperset.transitive_l ⟨W, zero_l ℳ, hW⟩ := by
  rcases hSpec with ⟨_, rfl⟩ | ⟨m, Y, hm, hY, hDef⟩ | ⟨_, G, P, hUnion⟩
  · exact hBase
  · have hYw := hRows m hm.1 Y hY
    exact successor_transitive_l hℳ ⟨Y, zero_l ℳ, hYw⟩ (hTrans m hm.1 Y hYw hY) hW hDef
  · exact union_transitive_l hℳ hUnion hRows hTrans

#print axioms step_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyClosure
