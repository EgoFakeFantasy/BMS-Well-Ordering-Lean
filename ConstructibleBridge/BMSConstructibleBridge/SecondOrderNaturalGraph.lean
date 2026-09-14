import BMSConstructibleBridge.SecondOrderDomainClosure
import BMSConstructibleBridge.SecondOrderInterpretation

/-!
# 模型自然数序的内部根域

用实际纯公式构造模型小于关系。对原域公式作二阶公式归纳，证明包括所有
非标准数在内的每个数根都在内部域中；不声称模型数序是外部良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 离散模型序的后继上界，避免调用仅适用于标准 Nat 的比较定理。 -/
theorem lt_succ_l (hℳ : Theory.Models ℳ theory_m) (m n : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    m < succ_l n ↔ m ≤ n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  rw [le_iff_l hℳ]
  change (∃ k, add_l m (succ_l k) = succ_l n) ↔ ∃ k, add_l m k = n
  apply exists_congr
  intro k
  rw [add_succ_l hℳ, (SecondOrderModel.injective_l hℳ).eq_iff]

theorem relation_exists_l (hℳ : Theory.Models ℳ theory_m) :
    ∃ R : set_l ℳ, ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b := by
  let φ : Formula signature_m [] [.num, .num] :=
    PrimitiveFormulas.lt_m (.fvar .here) (.fvar (.there .here))
  obtain ⟨R, hR⟩ := SecondOrderRelations.comprehension_l hℳ φ
    (pure_language_m _ (PrimitiveFormulas.lt_pure_l _ _ rfl rfl)) (Env.empty (M := ℳ))
  refine ⟨R, fun a b => (hR a b).trans ?_⟩
  exact SecondOrderOrder.formula_l _ _ _

/-- 归纳正文恰为原内部域公式，故模型归纳涵盖全部非标准根。 -/
theorem wf_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b) (n : num_l ℳ) :
    SecondOrderDomain.wf_l R n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  let φ : Formula signature_m [] [.num, .set] :=
    GraphTranslation.domain_m (.fvar (.there .here)) (.fvar .here)
  apply induct_l hℳ φ (GraphTranslation.domain_pure_m _ _ rfl rfl)
    ((Env.empty (M := ℳ)).pushFree R) (SecondOrderDomain.wf_l R)
    (fun n => SecondOrderInterpretation.domain_l _ _ _) ?_ ?_ n
  · apply SecondOrderDomain.leaf_l
    intro a h
    exact (not_lt_of_ge (zero_le_l hℳ a)) ((hR a (zero_l ℳ)).mp h)
  · intro n h
    apply SecondOrderDomainClosure.intro_l hℳ
    intro a h₁
    have h₂ := (lt_succ_l hℳ a n).mp ((hR a (succ_l n)).mp h₁)
    rcases eq_or_lt_of_le h₂ with rfl | h₂
    · exact h
    · exact SecondOrderDomain.child_l hℳ R n a h ((hR a n).mpr h₂)

def code_l (hℳ : Theory.Models ℳ theory_m) (R : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b) (n : num_l ℳ) :
    SecondOrderGraph.code_l ℳ := ⟨R, n, wf_l hℳ R hR n⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderNaturalGraph
