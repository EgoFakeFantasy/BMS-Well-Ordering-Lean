import BMSConstructibleBridge.SecondOrderProgramAscending
import BMSConstructibleBridge.SecondOrderProgramCopyOptional
import BMSConstructibleBridge.SecondOrderProgramOptionalLookup

/-!
# 原 copyBlock 的逐坐标回调

共享参数q为pair A (pair复制次数(pair首列末列))，A为pair数组(pair最大父行父列)。
内层map回调收到pair(pair q 局部列)(pair行原值)。先按同一原参数判断ascending，
再读取首末列该行的原Option码；缺项保留原值，不从补零读取推断可选项存在。
本模块给出完整单坐标更新，外层/内层map及整个原copyBlock身份在后续模块组合。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyEntry

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramConditional (branch_m branch_eval_l)
open SecondOrderProgramConditionalValue (branch_value_l)
open SecondOrderProgramOptionalLookup (optional_m optional_encode_l)
open SecondOrderProgramAscending (ascending_m ascending_encode_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 从内层回调输入取同一共享参数q。 -/
def context_m : code_m := .comp .left .left

/-- 局部列和行的原下标，不与原值混淆。 -/
def coordinate_m : code_m := .pair (.comp .right .left) (.comp .left .right)

/-- 原条目值，非上升或缺项时保持。 -/
def value_m : code_m := .comp .right .right

/-- 原上升条件的完整输入。 -/
def ascending_input_m : code_m := .pair (.comp .left context_m) coordinate_m

/-- 首列原Option读取输入，行号来自内层map。 -/
def first_input_m : code_m := .pair
  (.comp (.comp .left .right) (.comp .right context_m)) (.comp .left .right)

/-- 末列原Option读取输入。 -/
def last_input_m : code_m := .pair
  (.comp (.comp .right .right) (.comp .right context_m)) (.comp .left .right)

/-- 值、复制次数及两个原Option码组成已验数值分支的输入。 -/
def update_input_m : code_m := .pair value_m
  (.pair (.comp (.comp .left .right) context_m)
    (.pair (.comp optional_m first_input_m) (.comp optional_m last_input_m)))

/-- 完整的可选数值更新，不含外层上升测试。 -/
def update_m : code_m := .comp SecondOrderProgramCopyOptional.update_m update_input_m

/-- 原copyBlock单坐标更新：非上升时恒保留原值。 -/
def entry_m : code_m := branch_m (.comp ascending_m ascending_input_m) update_m value_m

/-- 标准坐标接线同时固定上升输入、首末列读取和原值。 -/
theorem inputs_eval_l (A k f l j r v : Nat) :
    let q := Nat.pair (Nat.pair A (Nat.pair k (Nat.pair f l))) j
    eval_l ascending_input_m (Nat.pair q (Nat.pair r v)) = Nat.pair A (Nat.pair j r) ∧
    eval_l first_input_m (Nat.pair q (Nat.pair r v)) = Nat.pair f r ∧
    eval_l last_input_m (Nat.pair q (Nat.pair r v)) = Nat.pair l r ∧
    eval_l value_m (Nat.pair q (Nat.pair r v)) = v := by
  simp only [ascending_input_m, coordinate_m, context_m, first_input_m, last_input_m,
    value_m, eval_l, Nat.unpair_pair, and_self]

/-- 标准首末列任意、行可越界，更新保留原双Option分支。 -/
theorem update_encode_l (A k : Nat) (f l : List Nat) (j r v : Nat) :
    eval_l update_m (Nat.pair
      (Nat.pair (Nat.pair A (Nat.pair k (Nat.pair (Encodable.encode f) (Encodable.encode l)))) j)
      (Nat.pair r v)) =
      match f[r]?, l[r]? with
      | some a, some b => v + k * (b - a)
      | _, _ => v := by
  let q := Nat.pair
    (Nat.pair (Nat.pair A (Nat.pair k (Nat.pair (Encodable.encode f) (Encodable.encode l)))) j)
    (Nat.pair r v)
  have hf : eval_l first_input_m q = Nat.pair (Encodable.encode f) r :=
    (inputs_eval_l A k (Encodable.encode f) (Encodable.encode l) j r v).2.1
  have hl : eval_l last_input_m q = Nat.pair (Encodable.encode l) r :=
    (inputs_eval_l A k (Encodable.encode f) (Encodable.encode l) j r v).2.2.1
  have hv : eval_l value_m q = v :=
    (inputs_eval_l A k (Encodable.encode f) (Encodable.encode l) j r v).2.2.2
  have hk : eval_l (.comp (.comp .left .right) context_m) q = k := by
    simp only [q, context_m, eval_l, Nat.unpair_pair]
  have hu : eval_l update_input_m q =
      Nat.pair v (Nat.pair k (Nat.pair (Encodable.encode (f[r]?)) (Encodable.encode (l[r]?)))) := by
    change Nat.pair (eval_l value_m q) (Nat.pair
      (eval_l (.comp (.comp .left .right) context_m) q)
      (Nat.pair (eval_l optional_m (eval_l first_input_m q))
        (eval_l optional_m (eval_l last_input_m q)))) = _
    rw [hv, hk, hf, hl, optional_encode_l, optional_encode_l]
  change eval_l SecondOrderProgramCopyOptional.update_m (eval_l update_input_m q) = _
  rw [hu, SecondOrderProgramCopyOptional.update_encode_l]
  cases f[r]? <;> cases l[r]? <;> rfl

private theorem branch_bool_l (v t u : Nat) (b : Bool) (hb : decide (t ≠ 0) = b) :
    (if t = 0 then v else u) = (if b then u else v) := by
  by_cases ht : t = 0 <;> simp_all

/-- 所有标准参数的单坐标程序就是原copyBlock的回调正文，无正确性假设。 -/
theorem entry_encode_l (a : BMSArray) (m p k : Nat) (f l : List Nat) (j r v : Nat) :
    eval_l entry_m (Nat.pair
      (Nat.pair (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p))
        (Nat.pair k (Nat.pair (Encodable.encode f) (Encodable.encode l)))) j)
      (Nat.pair r v)) =
      if BMS.ascending a m p j r then
        match f[r]?, l[r]? with
        | some first, some last => v + k * (last - first)
        | _, _ => v
      else v := by
  let A := Nat.pair (Encodable.encode a) (Nat.pair m p)
  let q := Nat.pair
    (Nat.pair (Nat.pair A (Nat.pair k (Nat.pair (Encodable.encode f) (Encodable.encode l)))) j)
    (Nat.pair r v)
  have ht : eval_l (.comp ascending_m ascending_input_m) q =
      eval_l ascending_m (Nat.pair A (Nat.pair j r)) := by
    change eval_l ascending_m (eval_l ascending_input_m q) = _
    rw [(inputs_eval_l A k (Encodable.encode f) (Encodable.encode l) j r v).1]
  have hv : eval_l value_m q = v :=
    (inputs_eval_l A k (Encodable.encode f) (Encodable.encode l) j r v).2.2.2
  change eval_l entry_m q = _
  rw [entry_m, branch_eval_l, ht, hv, update_encode_l]
  exact branch_bool_l v _ _ _ (ascending_encode_l a m p j r)

/-- 全部内部输入的真实程序规格：上升测试失败保留原值，否则调用同一双Option更新。 -/
theorem entry_rel_l (hℳ : Theory.Models ℳ theory_m) {R B O U : set_l ℳ}
    (hR : graph_semantics_l (graph_m entry_m) R)
    (hB : graph_semantics_l (graph_m ascending_m) B)
    (hO : graph_semantics_l (graph_m optional_m) O)
    (hU : graph_semantics_l (graph_m SecondOrderProgramCopyOptional.update_m) U)
    (A k f l j r v y : num_l ℳ) :
    relation_l R (value_l (value_l (value_l A (value_l k (value_l f l))) j) (value_l r v)) y ↔
      (relation_l B (value_l A (value_l j r)) (zero_l ℳ) ∧ v = y) ∨
      (¬relation_l B (value_l A (value_l j r)) (zero_l ℳ) ∧ ∃ first last,
        relation_l O (value_l f r) first ∧ relation_l O (value_l l r) last ∧
          relation_l U (value_l v (value_l k (value_l first last))) y) := by
  classical
  obtain ⟨b, hb, _⟩ := value_exists_l hℳ ascending_m hB
  obtain ⟨o, ho, _⟩ := value_exists_l hℳ optional_m hO
  obtain ⟨u, hu, _⟩ := value_exists_l hℳ SecondOrderProgramCopyOptional.update_m hU
  have hc : value_spec_l context_m _ := comp_value_l hℳ (left_value_l hℳ) (left_value_l hℳ)
  have hr : value_spec_l (.comp .left .right) _ := comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)
  have hj : value_spec_l (.comp .right .left) _ := comp_value_l hℳ (right_value_l hℳ) (left_value_l hℳ)
  have hv : value_spec_l value_m _ := comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ)
  have ha : value_spec_l ascending_input_m _ :=
    pair_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) hc) (pair_value_l hℳ hj hr)
  have hk : value_spec_l (.comp (.comp .left .right) context_m) _ :=
    comp_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)) hc
  have hf : value_spec_l first_input_m _ := pair_value_l hℳ
    (comp_value_l hℳ (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ))
      (comp_value_l hℳ (right_value_l hℳ) hc)) hr
  have hl : value_spec_l last_input_m _ := pair_value_l hℳ
    (comp_value_l hℳ (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ))
      (comp_value_l hℳ (right_value_l hℳ) hc)) hr
  have hi : value_spec_l update_input_m _ := pair_value_l hℳ hv
    (pair_value_l hℳ hk (pair_value_l hℳ (comp_value_l hℳ ho hf) (comp_value_l hℳ ho hl)))
  have he := (branch_value_l hℳ (comp_value_l hℳ hb ha) (comp_value_l hℳ hu hi) hv)
    hR (value_l (value_l (value_l A (value_l k (value_l f l))) j) (value_l r v)) y
  simp only [SecondOrderUnpairing.unpair_l] at he
  rw [he]
  simp only [hb hB, ho hO, hu hU]
  by_cases hz : b (value_l A (value_l j r)) = zero_l ℳ <;> simp [hz]

#print axioms context_m
#print axioms coordinate_m
#print axioms value_m
#print axioms ascending_input_m
#print axioms first_input_m
#print axioms last_input_m
#print axioms update_input_m
#print axioms update_m
#print axioms entry_m
#print axioms inputs_eval_l
#print axioms update_encode_l
#print axioms entry_encode_l
#print axioms entry_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyEntry
