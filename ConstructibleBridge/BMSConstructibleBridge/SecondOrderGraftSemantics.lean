import BMSConstructibleBridge.SecondOrderGraftDomain
import BMSConstructibleBridge.SecondOrderGraph

/-!
# 内部拼接图的换码及成员规格

实际理解产生旧节点到其后继副本的内部双模拟，再把新根的成员解释准确还原
为选中旧节点的换码。只要求选中节点满足原内部根域；不假定任意外部族可收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftSemantics

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem eq_l (hℳ : Theory.Models ℳ theory_m) (R P G : set_l ℳ)
    (hG : SecondOrderGraft.spec_l R P G) (a : num_l ℳ) :
    SecondOrderBisimulation.eq_l R G a (succ_l a) := by
  let φ : Formula signature_m [] [.num, .num] :=
    .equal (.fvar (.there .here)) (Term.app (σ := signature_m) .succ (.cons (.fvar .here) .nil))
  obtain ⟨H, hH⟩ := SecondOrderRelations.comprehension_l hℳ φ rfl (Env.empty (M := ℳ))
  change ∀ b c, relation_l H b c ↔ c = succ_l b at hH
  refine ⟨H, ?_, (hH a (succ_l a)).mpr rfl⟩
  intro b c h
  obtain rfl := (hH b c).mp h
  constructor
  · intro d h
    exact ⟨succ_l d, (hG.shift d b).mpr h, (hH d (succ_l d)).mpr rfl⟩
  · intro d h
    rcases predecessor_l hℳ d with rfl | ⟨d, rfl⟩
    · exact False.elim (hG.zero (succ_l b) h)
    · exact ⟨d, (hG.shift d b).mp h, (hH d (succ_l d)).mpr rfl⟩

def code_l (hℳ : Theory.Models ℳ theory_m) (R P G : set_l ℳ)
    (hG : SecondOrderGraft.spec_l R P G)
    (hR : ∀ a, mem_l a P → SecondOrderDomain.wf_l R a) : SecondOrderGraph.code_l ℳ :=
  ⟨G, zero_l ℳ, SecondOrderGraftDomain.root_l hℳ R P G hG hR⟩

theorem mem_l (hℳ : Theory.Models ℳ theory_m) (R P G : set_l ℳ)
    (hG : SecondOrderGraft.spec_l R P G)
    (hR : ∀ a, SecondOrderModel.mem_l a P → SecondOrderDomain.wf_l R a)
    (B : SecondOrderGraph.code_l ℳ) :
    SecondOrderGraph.mem_l B (code_l hℳ R P G hG hR) ↔
      ∃ a, SecondOrderModel.mem_l a P ∧ SecondOrderBisimulation.eq_l B.real R B.root a := by
  constructor
  · rintro ⟨b, h, h₁⟩
    rcases predecessor_l hℳ b with rfl | ⟨b, rfl⟩
    · exact False.elim (hG.zero (zero_l ℳ) h)
    · exact ⟨b, (hG.root b).mp h,
        SecondOrderBisimulation.trans_l hℳ B.real G R B.root (succ_l b) b h₁
          (SecondOrderBisimulation.symm_l hℳ R G b (succ_l b) (eq_l hℳ R P G hG b))⟩
  · rintro ⟨a, h, h₁⟩
    exact ⟨succ_l a, (hG.root a).mpr h,
      SecondOrderBisimulation.trans_l hℳ B.real R G B.root a (succ_l a) h₁ (eq_l hℳ R P G hG a)⟩

/-- 对给定内部选择集合，构造具有完整成员规格的内部根域代码。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R P : set_l ℳ)
    (hR : ∀ a, SecondOrderModel.mem_l a P → SecondOrderDomain.wf_l R a) :
    ∃ A : SecondOrderGraph.code_l ℳ, ∀ B,
      SecondOrderGraph.mem_l B A ↔
        ∃ a, SecondOrderModel.mem_l a P ∧ SecondOrderBisimulation.eq_l B.real R B.root a := by
  obtain ⟨G, hG⟩ := SecondOrderGraft.exists_l hℳ R P
  exact ⟨code_l hℳ R P G hG hR, mem_l hℳ R P G hG hR⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderGraftSemantics
