import BMSConstructibleBridge.PowerlessValueAbsolute
import BMSConstructibleBridge.PowerlessEvaluationAgreement

/-!
# 全部内部有限赋值上的查询一致性绝对性

环境中的任意有限赋值图由显式图闭包取回。比较的是同一 F、G 的查询，
不要求它们已经满足求值递归，也不只比较小结构中预先给定的赋值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAgreementAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
  {ω A : type_l B}
  (hG : ∀ m, member_l ℳ m ω.val → ∀ f, map_l f m A.val → member_l ℳ f B)

include hBT hG

theorem point_l {F G c : type_l B} :
    PowerlessEvaluationAgreement.point_l (ℳ := structure_l B hB) ω A F G c ↔
      PowerlessEvaluationAgreement.point_l ω.val A.val F.val G.val c.val := by
  constructor
  · intro h f hf
    obtain ⟨m, hm, hf⟩ := hf
    let g : type_l B := ⟨f, hG m hm f hf⟩
    have h₀ := h g ⟨⟨m, hBT ω.val m ω.property hm⟩, hm,
      (PowerlessSourceGraphAbsolute.map_l hBT).mpr hf⟩
    exact (PowerlessValueAbsolute.query_l hBT).symm.trans (h₀.trans (PowerlessValueAbsolute.query_l hBT))
  · intro h f hf
    obtain ⟨m, hm, hf⟩ := hf
    have h₀ := h f.val ⟨m.val, hm, (PowerlessSourceGraphAbsolute.map_l hBT).mp hf⟩
    exact (PowerlessValueAbsolute.query_l hBT).trans (h₀.trans (PowerlessValueAbsolute.query_l hBT).symm)

theorem agreement_l {F G : type_l B} :
    PowerlessEvaluationAgreement.agreement_l (ℳ := structure_l B hB) ω A F G ↔
      PowerlessEvaluationAgreement.agreement_l ω.val A.val F.val G.val := by
  constructor
  · intro h c hc
    exact (point_l hBT hG).mp (h ⟨c, hBT ω.val c ω.property hc⟩ hc)
  · intro h c hc
    exact (point_l hBT hG).mpr (h c.val hc)

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (w D F G : Term ℒ Γ Δ .set) (hw : w.eval η = ω) (hD : D.eval η = A) :
    Formula.satisfies η (PowerlessEvaluationAgreement.agreement_m w D F G) ↔
      PowerlessEvaluationAgreement.agreement_l ω.val A.val (F.eval η).val (G.eval η).val := by
  rw [PowerlessEvaluationAgreement.agreement_formula_l, hw, hD]
  exact agreement_l hBT hG

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationAgreementAbsolute
