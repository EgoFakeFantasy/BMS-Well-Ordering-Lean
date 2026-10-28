import BMSConstructibleBridge.SecondOrderFiniteDisjunctionCorrectness
import BMSConstructibleBridge.SecondOrderLegalFormulaIndex

/-! # 内部有限参数值域的合法 Def 行

任意有效内部赋值的有限值域，由同一合法公式族的一行精确表示。先对查询值
前插，再使用全内部析取正确性；不把非标准参数列转成宿主有限变量上下文。
这里只约束数码切片，实际 Def 集合成员和有限集合枚举在后续连接。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteDisjunctionFamily

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)
open SecondOrderSequenceSyntax (read_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem prepend_prefix_l {E Q : set_l ℳ} {c l d x : num_l ℳ}
    (hd : SecondOrderAssignmentSyntax.extension_l E c l d x) :
    SecondOrderFiniteDisjunctionCorrectness.prefix_l E Q d l ↔
      ∃ i y, SecondOrderOrder.lt_l i l ∧ read_l E c i y ∧ relation_l Q x y := by
  constructor
  · rintro ⟨i, hi, a, y, ha, hy, hQ⟩
    obtain rfl := (hd.2.1 a).mp ha
    exact ⟨i, y, hi, (hd.2.2 i y).mp hy, hQ⟩
  · rintro ⟨i, y, hi, hy, hQ⟩
    exact ⟨i, hi, x, y, (hd.2.1 x).mpr rfl, (hd.2.2 i y).mpr hy, hQ⟩

theorem row_l (hℳ : Theory.Models ℳ theory_m) {S V E D Q R T F : set_l ℳ}
    (hS : SecondOrderFiniteDisjunctionSyntax.spec_l S)
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hE : SecondOrderBinaryPowers.spec_l E)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    (hF : SecondOrderDefinableFamily.spec_l E D T F)
    (l c p : num_l ℳ) (hc : SecondOrderAssignmentSyntax.valid_l E c l) (hp : relation_l S l p) :
    SecondOrderLegalFormulaIndex.spec_l V E (SecondOrderDefinableFamily.index_l p l c) ∧
      ∀ x, relation_l F (SecondOrderDefinableFamily.index_l p l c) x ↔
        mem_l x D ∧ ∃ i y, SecondOrderOrder.lt_l i l ∧ read_l E c i y ∧ relation_l Q x y := by
  letI := SecondOrderAlgebra.semiring_l hℳ
  letI := SecondOrderAlgebra.order_l hℳ
  have hLegal : relation_l V p (succ_l l) :=
    SecondOrderFiniteDisjunctionCorrectness.legal_l hℳ hS hV l (succ_l l)
      ((SecondOrderNaturalGraph.lt_succ_l hℳ l l).mpr le_rfl) p hp
  refine ⟨(SecondOrderLegalFormulaIndex.index_l hℳ V E p l c).mpr ⟨hc, hLegal⟩, ?_⟩
  intro x
  rw [SecondOrderDefinableFamily.row_index_l hℳ E D T F hF p l c x]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨_, d, hd, h⟩
    exact (prepend_prefix_l hd).mp
      ((SecondOrderFiniteDisjunctionCorrectness.correct_l hℳ hS hT d (succ_l l) hd.1 l p hp).mp h)
  · intro h
    obtain ⟨d, hd⟩ := SecondOrderAssignmentCongruence.extension_exists_l hℳ hE c l x hc
    exact ⟨hc, d, hd,
      (SecondOrderFiniteDisjunctionCorrectness.correct_l hℳ hS hT d (succ_l l) hd.1 l p hp).mpr
        ((prepend_prefix_l hd).mpr h)⟩

/-- 对任意内部长度直接取得一个合法索引，不要求给定递归码或外部标准性。 -/
theorem exists_l (hℳ : Theory.Models ℳ theory_m) {V E D Q R T F : set_l ℳ}
    (hV : SecondOrderInternalFormulaSyntax.spec_l V)
    (hE : SecondOrderBinaryPowers.spec_l E)
    (hT : SecondOrderEvaluationEquations.spec_l E D Q R T)
    (hF : SecondOrderDefinableFamily.spec_l E D T F)
    (l c : num_l ℳ) (hc : SecondOrderAssignmentSyntax.valid_l E c l) :
    ∃ i, SecondOrderLegalFormulaIndex.spec_l V E i ∧ ∀ x, relation_l F i x ↔
      mem_l x D ∧ ∃ j y, SecondOrderOrder.lt_l j l ∧ read_l E c j y ∧ relation_l Q x y := by
  obtain ⟨S, hS, _⟩ := SecondOrderFiniteDisjunctionSyntax.exists_l hℳ
  obtain ⟨p, hp⟩ := SecondOrderFiniteDisjunctionSyntax.total_l hℳ hS l
  exact ⟨_, row_l hℳ hS hV hE hT hF l c p hc hp⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteDisjunctionFamily
