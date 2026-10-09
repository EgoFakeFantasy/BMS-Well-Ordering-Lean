import BMSConstructibleBridge.SecondOrderOrdinalBudgetOrder
import BMSConstructibleBridge.SecondOrderOrdinalTailMembers
import BMSConstructibleBridge.PowerlessRelativeHierarchySemantics

/-! # 预算块的有限后继与非零极限底部

同一指标的有限尾严格表示逐次后继。若起点 ξ 是非零极限，每个预算块的
零尾也是非零极限；任意较早指标的全部有限尾都落在当前零尾里。因此
前史构造需要的两次 Def 余量可以读为 tail(n,2)，而无需先建立完整序数
加乘语言或假定统一枚举历史。全部内部数字都按原模型读数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBudgetFinite

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderOrdinalBudgetGraph SecondOrderOrdinalBudgetOrder
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem not_lt_zero_l (hℳ : Theory.Models ℳ theory_m) (m : num_l ℳ) :
    ¬SecondOrderOrder.lt_l m (zero_l ℳ) := by
  rintro ⟨k, hk⟩
  exact SecondOrderModel.nonzero_l hℳ (add_l m k)
    ((SecondOrderModel.add_succ_l hℳ m k).symm.trans hk)

variable (hℳ : Theory.Models ℳ theory_m) {S R G : set_l ℳ} {r : num_l ℳ}
  (hG : spec_l S r R G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
  (hR : ∀ a, SecondOrderDomain.wf_l R a)

theorem successor_l (n m : num_l ℳ) :
    PowerlessRelativeHierarchySemantics.successor_l hℳ
      (tail_l hℳ hG hS hR n m) (tail_l hℳ hG hS hR n (succ_l m)) := by
  intro x
  rw [reading_l hℳ hG hS hR n (succ_l m) x]
  constructor
  · rintro (hx | ⟨i, j, hij, hx⟩)
    · exact Or.inl ((reading_l hℳ hG hS hR n m x).mpr (Or.inl hx))
    · rcases hij with hi | ⟨hi, hj⟩
      · exact Or.inl ((reading_l hℳ hG hS hR n m x).mpr
          (Or.inr ⟨i, j, Or.inl hi, hx⟩))
      · subst i
        rcases (SecondOrderOrdinalTailMembers.lt_succ_l hℳ j m).mp hj with hj | rfl
        · exact Or.inl ((reading_l hℳ hG hS hR n m x).mpr
            (Or.inr ⟨n, j, Or.inr ⟨rfl, hj⟩, hx⟩))
        · exact Or.inr hx
  · rintro (hx | hx)
    · rcases (reading_l hℳ hG hS hR n m x).mp hx with hx | ⟨i, j, hij, hx⟩
      · exact Or.inl hx
      · refine Or.inr ⟨i, j, ?_, hx⟩
        rcases hij with hi | ⟨hi, hj⟩
        · exact Or.inl hi
        · subst i
          exact Or.inr ⟨rfl, (SecondOrderOrdinalTailMembers.lt_succ_l hℳ j m).mpr (Or.inl hj)⟩
    · exact Or.inr ⟨n, m,
        Or.inr ⟨rfl, (SecondOrderOrdinalTailMembers.lt_succ_l hℳ m m).mpr (Or.inr rfl)⟩, hx⟩

theorem zero_reading_l (n : num_l ℳ) (x : type_l hℳ) :
    mem_l hℳ x (tail_l hℳ hG hS hR n (zero_l ℳ)) ↔
      mem_l hℳ x (base_l hℳ hS r) ∨
        ∃ i j, SecondOrderPairing.relation_l R i n ∧ x = tail_l hℳ hG hS hR i j := by
  rw [reading_l hℳ hG hS hR n (zero_l ℳ) x]
  apply or_congr Iff.rfl
  apply exists_congr
  intro i
  apply exists_congr
  intro j
  apply and_congr ?_ Iff.rfl
  constructor
  · rintro (hi | ⟨_, hj⟩)
    · exact hi
    · exact False.elim (not_lt_zero_l hℳ j hj)
  · exact Or.inl

/-- 起点的每个成员在全部预算块里；它是有限参数层包含性的真正读数。 -/
theorem base_subset_l (n m : num_l ℳ) (x : type_l hℳ)
    (hx : mem_l hℳ x (base_l hℳ hS r)) : mem_l hℳ x (tail_l hℳ hG hS hR n m) :=
  (reading_l hℳ hG hS hR n m x).mpr (Or.inl hx)

theorem zero_eq_base_l (n : num_l ℳ)
    (hn : ∀ i, ¬SecondOrderPairing.relation_l R i n) :
    tail_l hℳ hG hS hR n (zero_l ℳ) = base_l hℳ hS r := by
  apply SecondOrderQuotient.ext_l hℳ
  intro x
  rw [zero_reading_l hℳ hG hS hR n x]
  constructor
  · rintro (hx | ⟨i, _, hi, _⟩)
    · exact hx
    · exact False.elim (hn i hi)
  · exact Or.inl

/-- 每个零尾都非空且没有最大成员，而非只在非零指标上成立。 -/
theorem limit_l
    (hξ : PowerlessRelativeHierarchySemantics.limit_l hℳ (base_l hℳ hS r))
    (n : num_l ℳ) :
    PowerlessRelativeHierarchySemantics.limit_l hℳ (tail_l hℳ hG hS hR n (zero_l ℳ)) := by
  constructor
  · obtain ⟨x, hx⟩ := hξ.1
    exact ⟨x, base_subset_l hℳ hG hS hR n (zero_l ℳ) x hx⟩
  · intro x hx
    rcases (zero_reading_l hℳ hG hS hR n x).mp hx with hx | ⟨i, j, hin, rfl⟩
    · obtain ⟨y, hy, hxy⟩ := hξ.2 x hx
      exact ⟨y, base_subset_l hℳ hG hS hR n (zero_l ℳ) y hy, hxy⟩
    · exact ⟨tail_l hℳ hG hS hR i (succ_l j),
        earlier_l hℳ hG hS hR hin (succ_l j) (zero_l ℳ),
        (successor_l hℳ hG hS hR i j _).mpr (Or.inr rfl)⟩

#print axioms successor_l
#print axioms zero_eq_base_l
#print axioms limit_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBudgetFinite
