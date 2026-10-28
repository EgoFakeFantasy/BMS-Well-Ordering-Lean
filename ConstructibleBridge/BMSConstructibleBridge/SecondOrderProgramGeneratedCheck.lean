import BMSConstructibleBridge.SecondOrderProgramGeneratedDecode
import BMSConstructibleBridge.SecondOrderProgramEquality
import BMSConstructibleBridge.SecondOrderProgramConditionalValue

/-!
# 原生成数组严格一步检查器的显式程序

输入pair较小端(pair较大端展开指标)。两端均由原decode程序得到数组码，先检查
较小数组等于较大数组展开结果，再排除两原数组相等。不能改成比较轨迹码：
同一生成数组可能有不同轨迹码。内部结论比较实际解码输出而非输入码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedCheck

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramGeneratedDecode (decode_m decode_eval_l)
open SecondOrderProgramExpansion (expand_m expand_encode_l)
open SecondOrderProgramEquality (equal_m equal_eval_l equal_rel_l)
open SecondOrderProgramConditional (branch_m branch_eval_l)
open SecondOrderProgramConditionalValue (branch_value_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 较小端原轨迹解码后的数组码。 -/
def smaller_m : code_m := .comp decode_m .left

/-- 较大端原轨迹解码后的数组码。 -/
def larger_m : code_m := .comp decode_m (.comp .left .right)

/-- 从较大端展开一次，保留输入的实际指标。 -/
def expanded_m : code_m := .comp expand_m (.pair larger_m (.comp .right .right))

/-- 比较解码数组与实际展开结果，不比较轨迹本身。 -/
def step_test_m : code_m := .comp equal_m (.pair smaller_m expanded_m)

/-- 排除原两数组相等，包括由不同轨迹码表示的同一数组。 -/
def same_test_m : code_m := .comp equal_m (.pair smaller_m larger_m)

/-- 输出1恰表示原非平凡展开；否则输出0。 -/
def check_m : code_m := branch_m step_test_m
  (branch_m same_test_m .zero (PrimitiveProgram.const_m 1)) .zero

private theorem tests_eval_l (b a k : Nat) :
    eval_l step_test_m (Nat.pair b (Nat.pair a k)) =
      (if (ArithmeticPresentation.decode_l b).1.raw =
        BMS.expand (ArithmeticPresentation.decode_l a).1.raw k then 1 else 0) ∧
    eval_l same_test_m (Nat.pair b (Nat.pair a k)) =
      (if (ArithmeticPresentation.decode_l b).1.raw =
        (ArithmeticPresentation.decode_l a).1.raw then 1 else 0) := by
  have hs : eval_l smaller_m (Nat.pair b (Nat.pair a k)) =
      Encodable.encode (ArithmeticPresentation.decode_l b).1.raw := by
    change eval_l decode_m (Nat.pair b (Nat.pair a k)).unpair.1 = _
    rw [Nat.unpair_pair, decode_eval_l]
  have hl : eval_l larger_m (Nat.pair b (Nat.pair a k)) =
      Encodable.encode (ArithmeticPresentation.decode_l a).1.raw := by
    change eval_l decode_m (Nat.pair b (Nat.pair a k)).unpair.2.unpair.1 = _
    rw [Nat.unpair_pair, Nat.unpair_pair, decode_eval_l]
  have he : eval_l expanded_m (Nat.pair b (Nat.pair a k)) =
      Encodable.encode (BMS.expand (ArithmeticPresentation.decode_l a).1.raw k) := by
    change eval_l expand_m (Nat.pair (eval_l larger_m (Nat.pair b (Nat.pair a k)))
      (Nat.pair b (Nat.pair a k)).unpair.2.unpair.2) = _
    rw [hl, Nat.unpair_pair, Nat.unpair_pair, expand_encode_l]
  constructor
  · change eval_l equal_m (Nat.pair (eval_l smaller_m (Nat.pair b (Nat.pair a k)))
      (eval_l expanded_m (Nat.pair b (Nat.pair a k)))) = _
    rw [hs, he, equal_eval_l]
    simp only [Encodable.encode_injective.eq_iff]
  · change eval_l equal_m (Nat.pair (eval_l smaller_m (Nat.pair b (Nat.pair a k)))
      (eval_l larger_m (Nat.pair b (Nat.pair a k)))) = _
    rw [hs, hl, equal_eval_l]
    simp only [Encodable.encode_injective.eq_iff]

private theorem branch_test_l (P Q : Prop) [Decidable P] [Decidable Q] :
    (if (if P then (1 : Nat) else 0) = 0 then 0
      else if (if Q then 1 else 0) = 0 then 1 else 0) = cond (decide (P ∧ ¬Q)) 1 0 := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

/-- 精确连接原check_l，并保留0/1两种输出。 -/
theorem check_encode_l (b a k : Nat) :
    eval_l check_m (Nat.pair b (Nat.pair a k)) = cond (ArithmeticPresentation.check_l b a k) 1 0 := by
  rw [check_m, branch_eval_l, branch_eval_l, (tests_eval_l b a k).1, (tests_eval_l b a k).2,
    PrimitiveProgram.const_l]
  exact branch_test_l _ _

/-- 对所有自然数三元码的原检查器身份，不要求输入是规范轨迹码。 -/
theorem check_eval_l (x : Nat) :
    eval_l check_m x = cond
      (ArithmeticPresentation.check_l x.unpair.1 x.unpair.2.unpair.1 x.unpair.2.unpair.2) 1 0 := by
  have h := check_encode_l x.unpair.1 x.unpair.2.unpair.1 x.unpair.2.unpair.2
  simpa only [Nat.pair_unpair] using h

private theorem equality_value_l (hℳ : Theory.Models ℳ theory_m) :
    letI := Classical.propDecidable
    value_spec_l equal_m (fun x : num_l ℳ =>
      if (SecondOrderUnpairing.value_l hℳ x).1 = (SecondOrderUnpairing.value_l hℳ x).2
      then succ_l (zero_l ℳ) else zero_l ℳ) := by
  classical
  intro E hE x y
  obtain ⟨a, b, rfl⟩ := SecondOrderUnpairing.surjective_l hℳ x
  simp only [equal_rel_l hℳ hE, SecondOrderUnpairing.unpair_l]
  by_cases h : a = b <;> simp [h]

/-- 原图在任意内部输入上返回1的精确条件，给定值来自实际解码/展开图。
不是用标准数组身份外推非标准语义，也不把不同轨迹码误作不同数组。 -/
theorem check_one_l (hℳ : Theory.Models ℳ theory_m) {C D E : set_l ℳ}
    (hC : graph_semantics_l (graph_m check_m) C)
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hE : graph_semantics_l (graph_m expand_m) E) (b a k u v w : num_l ℳ)
    (hb : relation_l D b u) (ha : relation_l D a v) (he : relation_l E (value_l v k) w) :
    relation_l C (value_l b (value_l a k)) (succ_l (zero_l ℳ)) ↔ u = w ∧ u ≠ v := by
  classical
  obtain ⟨d, hd, _⟩ := value_exists_l hℳ decode_m hD
  obtain ⟨e, hh, _⟩ := value_exists_l hℳ expand_m hE
  have hs : value_spec_l smaller_m _ := comp_value_l hℳ hd (left_value_l hℳ)
  have hl : value_spec_l larger_m _ := comp_value_l hℳ hd
    (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ))
  have hx : value_spec_l expanded_m _ := comp_value_l hℳ hh
    (pair_value_l hℳ hl (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)))
  have ht : value_spec_l step_test_m _ := comp_value_l hℳ (equality_value_l hℳ) (pair_value_l hℳ hs hx)
  have ho : value_spec_l same_test_m _ := comp_value_l hℳ (equality_value_l hℳ) (pair_value_l hℳ hs hl)
  have h1 : value_spec_l (PrimitiveProgram.const_m 1) (fun _ : num_l ℳ => succ_l (zero_l ℳ)) :=
    comp_value_l hℳ (succ_value_l hℳ) (zero_value_l hℳ)
  have hv := (branch_value_l hℳ ht (branch_value_l hℳ ho (zero_value_l hℳ) h1) (zero_value_l hℳ))
    hC (value_l b (value_l a k)) (succ_l (zero_l ℳ))
  simp only [SecondOrderUnpairing.unpair_l, (hd hD b u).mp hb, (hd hD a v).mp ha,
    (hh hE (value_l v k) w).mp he] at hv
  rw [hv]
  by_cases huw : u = w <;> by_cases huv : u = v <;>
    simp [huw, huv, nonzero_l hℳ (zero_l ℳ), Ne.symm (nonzero_l hℳ (zero_l ℳ))]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedCheck
