import BMSConstructibleBridge.SecondOrderCanonicalMemberDefCongruence
import BMSConstructibleBridge.SecondOrderPredecessorUnionCongruence
import BMSConstructibleBridge.SecondOrderPredecessorCorrespondence
import BMSConstructibleBridge.SecondOrderRelativeHierarchyStrongTheorem

/-! # 不同索引历史的逐阶段换码步骤

最小阶段读取基图相等；后继阶段读取 Def 唯一性；极限阶段使用前驱并集的
精确成员。归纳前提仅访问当前严格前驱，最终内部归纳在后续公式模块进行。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyAgreementStep

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def rows_l (I S T : set_l ℳ) (n : num_l ℳ) : Prop :=
  ∀ m, relation_l I n m → ∀ U V
    (hU : SecondOrderDomain.wf_l U (zero_l ℳ)) (hV : SecondOrderDomain.wf_l V (zero_l ℳ)),
    SecondOrderSections.spec_l S n U → SecondOrderSections.spec_l T m V →
    SecondOrderGraph.eq_l ⟨U, zero_l ℳ, hU⟩ ⟨V, zero_l ℳ, hV⟩

theorem step_l (hℳ : Theory.Models ℳ theory_m) {B B' R R' I S T : set_l ℳ}
    {hB : SecondOrderDomain.wf_l B (zero_l ℳ)} {hB' : SecondOrderDomain.wf_l B' (zero_l ℳ)}
    (hBB' : SecondOrderGraph.eq_l ⟨B, zero_l ℳ, hB⟩ ⟨B', zero_l ℳ, hB'⟩)
    (hI : SecondOrderPredecessorCorrespondence.spec_l R R' I)
    (hAsymm : ∀ a b, relation_l R' a b → ¬relation_l R' b a)
    (hS : SecondOrderRelativeHierarchyStrongTheorem.spec_l B R S hB)
    (hT : SecondOrderRelativeHierarchyStrongTheorem.spec_l B' R' T hB')
    {n : num_l ℳ} (hPast : ∀ k, relation_l R k n → rows_l I S T k) : rows_l I S T n := by
  intro m hnm W W' hW hW' hWn hW'm
  rcases hS.history n W hWn with ⟨hn, rfl⟩ | ⟨k, Y, hk, hY, hDef⟩ | ⟨hn, G, P, hUnion⟩
  · have hm := (SecondOrderPredecessorCorrespondence.minimal_iff_l hI hnm).mp hn
    rcases hT.history m W' hW'm with ⟨_, rfl⟩ | ⟨l, _, hl, _, _⟩ | ⟨hl, _⟩
    · exact hBB'
    · exact False.elim (hm l hl.1)
    · exact False.elim (hl.1 hm)
  · obtain ⟨j, _, hkj⟩ := hI.forth n m hnm k hk.1
    have hj := (SecondOrderPredecessorCorrespondence.immediate_iff_l hI hkj hnm).mp hk
    rcases hT.history m W' hW'm with ⟨hm, _⟩ | ⟨l, Y', hl, hY', hDef'⟩ | ⟨hl, _⟩
    · exact False.elim (hm j hj.1)
    · have hjl := SecondOrderRelativeHierarchyStep.immediate_unique_l hAsymm hj hl
      subst l
      have hYw := hS.wellFounded k Y hY
      have hY'w := hT.wellFounded j Y' hY'
      exact SecondOrderCanonicalMemberDefCongruence.eq_l hℳ
        ⟨Y, zero_l ℳ, hYw⟩ ⟨Y', zero_l ℳ, hY'w⟩
        (hPast k hk.1 j hkj Y Y' hYw hY'w hY hY') hW hW' hDef hDef'
    · exact False.elim (hl.2 ⟨j, hj⟩)
  · have hm := (SecondOrderPredecessorCorrespondence.limit_iff_l hI hnm).mp hn
    rcases hT.history m W' hW'm with ⟨hl, _⟩ | ⟨l, _, hl, _, _⟩ | ⟨_, G', P', hUnion'⟩
    · exact False.elim (hm.1 hl)
    · exact False.elim (hm.2 ⟨l, hl⟩)
    · exact SecondOrderPredecessorUnionCongruence.eq_l hℳ hUnion hUnion'
        (fun k _ Y hY => hS.wellFounded k Y hY)
        (fun j _ Y hY => hT.wellFounded j Y hY) I
        (hI.forth n m hnm) (hI.back n m hnm)
        (fun k j hkj hk _ U V hU hV hUk hVj => hPast k hk j hkj U V hU hV hUk hVj)

#print axioms step_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRelativeHierarchyAgreementStep
