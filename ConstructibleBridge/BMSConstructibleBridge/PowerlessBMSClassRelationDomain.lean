import BMSConstructibleBridge.PowerlessWeakSetInduction
import BMSConstructibleBridge.PowerlessBMSQuotientBoundedImage

/-!
# 可定义集合值映射所诱导的内部关系无下降链

集合值映射不预先假定有集合值域。对假设的内部下降链，只有数值像先组成
集合；输出形成的可定义类用弱集合归纳取得极小元，产生矛盾。故没有循环
调用待证的 Collection，也不假定商宇宙外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSClassRelationDomain

open Logic FirstOrder PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

/-- 任意内部边关系只要被实际可定义的单值集合映射送入隶属，就无内部下降链。 -/
theorem wf_l (C : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env quotient_l [] Δ)
    (R : SecondOrderModel.set_l ℳ)
    (hTotal : ∀ n, ∃ y, φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y))
    (hUnique : ∀ n y z,
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) →
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree z) → y = z)
    (hEdge : ∀ n m, SecondOrderPairing.relation_l R n m → ∃ y z,
      φ.satisfies ((η.pushFree (numberCode_l C n).val).pushFree y) ∧
      φ.satisfies ((η.pushFree (numberCode_l C m).val).pushFree z) ∧
      SecondOrderQuotient.mem_l hℳ y z) : ∀ n, SecondOrderDomain.wf_l R n := by
  classical
  intro n X hX h₀
  by_contra hn
  have hChain i b c (hb : SecondOrderPairing.relation_l X i b)
      (hc : SecondOrderPairing.relation_l X (SecondOrderModel.succ_l i) c) :
      SecondOrderPairing.relation_l R c b := by
    by_contra h
    exact hn ⟨i, b, c, hb, hc, h⟩
  obtain ⟨d, hd⟩ := SecondOrderNaturalSubsets.range_l hℳ C.less C.less_spec X
  have hd' x : SecondOrderQuotient.mem_l hℳ x d ↔ ∃ i b,
      SecondOrderPairing.relation_l X i b ∧ x = (numberCode_l C b).val := hd x
  let ψ := PowerlessBMSQuotientBoundedImage.range_m φ
  let ξ : Env quotient_l [] (.set :: Δ) := η.pushFree d
  have hSeen y : ψ.satisfies (ξ.pushFree y) ↔ ∃ i b,
      SecondOrderPairing.relation_l X i b ∧
        φ.satisfies ((η.pushFree (numberCode_l C b).val).pushFree y) := by
    rw [PowerlessBMSQuotientBoundedImage.range_formula_l]
    constructor
    · rintro ⟨x, hx, hy⟩
      obtain ⟨i, b, hb, rfl⟩ := (hd' x).mp hx
      exact ⟨i, b, hb, hy⟩
    · rintro ⟨i, b, hb, hy⟩
      exact ⟨(numberCode_l C b).val, (hd' _).mpr ⟨i, b, hb, rfl⟩, hy⟩
  obtain ⟨y₀, hy₀⟩ := hTotal n
  obtain ⟨y, hy, hMin⟩ := PowerlessWeakSetInduction.minimum_l
    (SecondOrderWeakSetTheory.models_l hℳ) ψ ξ
      ⟨y₀, (hSeen y₀).mpr ⟨SecondOrderModel.zero_l ℳ, n, h₀, hy₀⟩⟩
  obtain ⟨i, b, hb, hy⟩ := (hSeen y).mp hy
  obtain ⟨c, hc, _⟩ := hX (SecondOrderModel.succ_l i)
  obtain ⟨z, y', hz, hy', hzy⟩ := hEdge c b (hChain i b c hb hc)
  have hEq := hUnique b y' y hy' hy
  subst y'
  exact hMin z hzy ((hSeen z).mpr ⟨SecondOrderModel.succ_l i, c, hc, hz⟩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSClassRelationDomain
