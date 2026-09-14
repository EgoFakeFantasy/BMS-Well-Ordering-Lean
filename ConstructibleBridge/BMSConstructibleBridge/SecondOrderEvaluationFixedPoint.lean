import BMSConstructibleBridge.SecondOrderEvaluationRule
import BMSConstructibleBridge.SecondOrderRecursiveRelation

/-!
# 编号递归产生内部求值关系

五种实际求值规则满足严格初段局部性，因此存在唯一内部关系满足全部方程。
对象闭句同时量化结构参数；尚须换码不变性及与源语法的对应，才可用于 Def。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationFixedPoint

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderEvaluationRule

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem conjunction_local_l (hℳ : Theory.Models ℳ theory_m) (X Y : set_l ℳ) (n t p s : num_l ℳ)
    (h : SecondOrderInitialAgreement.agree_l X Y n) (hp : SecondOrderFormulaCode.node_l t p = n) :
    conjunction_l X p s ↔ conjunction_l Y p s := by
  apply exists_congr
  intro i
  apply exists_congr
  intro j
  apply and_congr_right
  intro hij
  have h₀ := SecondOrderFormulaCode.children_l hℳ t i j
  rw [hij, hp] at h₀
  exact and_congr (h i h₀.1 s) (h j h₀.2 s)

theorem existential_local_l (E D X Y : set_l ℳ) (n c p : num_l ℳ)
    (h : ∀ a, relation_l X p a ↔ relation_l Y p a) :
    existential_l E D X n c p ↔ existential_l E D Y n c p := by
  unfold existential_l
  simp only [h]

theorem local_l (hℳ : Theory.Models ℳ theory_m) (E D Q R X Y : set_l ℳ) (n : num_l ℳ)
    (h : SecondOrderInitialAgreement.agree_l X Y n) (s : num_l ℳ) :
    rule_l E D Q R X n s ↔ rule_l E D Q R Y n s := by
  apply exists_congr
  intro l
  apply exists_congr
  intro c
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  apply exists_congr
  intro t
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  have hp₀ := (SecondOrderFormulaCode.bounds_l hℳ t p).2
  rw [hp] at hp₀
  exact or_congr Iff.rfl (or_congr Iff.rfl
    (or_congr (and_congr Iff.rfl (not_congr (h p hp₀ s)))
      (or_congr (and_congr Iff.rfl (conjunction_local_l hℳ X Y n t p s h hp))
        (and_congr Iff.rfl (existential_local_l E D X Y l c p (h p hp₀))))))

theorem environment_l (hℳ : Theory.Models ℳ theory_m) (η : Env ℳ [] [.set, .set, .set, .set]) :
    ∃! S, ∀ n a, relation_l S n a ↔ SecondOrderRecursiveRelation.rule_l formula_m η S n a := by
  apply SecondOrderRecursiveRelation.exists_l hℳ formula_m pure_m η
  intro X Y n hn a
  exact (formula_l (((η.pushFree X).pushFree a).pushFree n)).trans
    ((local_l hℳ _ _ _ _ X Y n hn a).trans
      (formula_l (((η.pushFree Y).pushFree a).pushFree n)).symm)

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (E D Q R : set_l ℳ) :
    ∃! S, ∀ n a, relation_l S n a ↔ rule_l E D Q R S n a := by
  let η := ((((Env.empty (M := ℳ)).pushFree R).pushFree Q).pushFree D).pushFree E
  have h (S : set_l ℳ) (n a : num_l ℳ) :
      SecondOrderRecursiveRelation.rule_l formula_m η S n a ↔ rule_l E D Q R S n a :=
    formula_l (((η.pushFree S).pushFree a).pushFree n)
  obtain ⟨S, hS, hU⟩ := environment_l hℳ η
  exact ⟨S, fun n a => (hS n a).trans (h S n a),
    fun T hT => hU T (fun n a => (hT n a).trans (h T n a).symm)⟩

def sentence_m : Sentence signature_m := Metatheory.Formula.forall_close
  (SecondOrderRankedRecursionTheorem.fixed_m (SecondOrderRecursiveRelation.operator_m formula_m))

/-- 完整结构参数闭句的实际对象推导；没有留下求值操作的局部性假设。 -/
theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  rw [SecondOrderRankedRecursionTheorem.fixed_l]
  let ρ := SecondOrderSetIterationTheorem.parameters_l η
  obtain ⟨S, hS, hU⟩ := environment_l hℳ ρ
  refine ⟨S, (SecondOrderRecursiveRelation.operator_l formula_m ρ S S).mpr hS, ?_⟩
  intro T hT a
  exact (hU T ((SecondOrderRecursiveRelation.operator_l formula_m ρ T T).mp hT)) ▸ Iff.rfl

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderEvaluationFixedPoint
