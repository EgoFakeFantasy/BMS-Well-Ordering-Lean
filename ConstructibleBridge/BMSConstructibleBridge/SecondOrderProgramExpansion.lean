import BMSConstructibleBridge.SecondOrderProgramExpansionSuccess
import BMSConstructibleBridge.SecondOrderProgramTrimArray
import BMSConstructibleBridge.SecondOrderProgramConditionalValue

/-!
# 原 expandRaw 与 expand 的完整统一程序

输入pair原数组展开下标。先实际计算最大父行；none删除末列，some则查询该行末列的
父节点，none仍删除末列，some执行原好坏块与复制正文。最后调用实际trimZeroRows。
标准身份覆盖全部原数组、全部下标，不依赖矩形性、生成性或外给父表。
内部图接线使用原Z₂总图；完整非标准数组及生成轨迹的语义仍须后续不变量，不能
从标准身份外推，更不能将这个算法身份当成最终良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansion

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramConditional (branch_m branch_eval_l)
open SecondOrderProgramConditionalValue (branch_value_l)
open SecondOrderProgramListCode (pred_m pred_eval_l)
open SecondOrderProgramListTake (take_m take_array_encode_l)
open SecondOrderProgramMaximalParentRow (last_index_m last_index_encode_l maximal_encode_l)
open SecondOrderProgramUniformParent (parent_m parent_encode_l)
open SecondOrderProgramExpansionSuccess (success_m success_encode_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 父行或父列缺失时删掉原末列，空数组仍得到空数组。 -/
def fallback_m : code_m := .comp take_m (.pair .left (.comp last_index_m .left))

/-- 同一原数组的最大父行Option码。 -/
def maximal_m : code_m := .comp SecondOrderProgramMaximalParentRow.maximal_m .left

/-- 最大父行存在后才去Option壳，保留原数组和展开下标。 -/
def row_input_m : code_m := .pair PrimitiveProgram.id_m (.comp pred_m maximal_m)

/-- 输入pair(pair数组下标)行，查询该行原末列的父节点。 -/
def parent_input_m : code_m := .pair (.pair (.comp .left .left) .right)
  (.comp last_index_m (.comp .left .left))

/-- 原统一父程序的实际Option输出。 -/
def parent_test_m : code_m := .comp parent_m parent_input_m

/-- 父列存在后去Option壳，排成成功正文需要的完整参数。 -/
def success_input_m : code_m := .pair (.comp .left .left)
  (.pair (.comp .right .left) (.pair .right (.comp pred_m parent_test_m)))

/-- 保留原父列缺失分支，不能由理论性质提前删去。 -/
def after_row_m : code_m := branch_m parent_test_m (.comp success_m success_input_m)
  (.comp fallback_m .left)

/-- 未裁剪的原展开，两个Option分支完整保留。 -/
def raw_m : code_m := branch_m maximal_m (.comp after_row_m row_input_m) fallback_m

/-- 原展开完成后实际裁去全零尾行。 -/
def expand_m : code_m := .comp SecondOrderProgramTrimArray.trim_m raw_m

/-- 删除末列分支的标准身份。 -/
theorem fallback_encode_l (a : BMSArray) (n : Nat) :
    eval_l fallback_m (Nat.pair (Encodable.encode a) n) = Encodable.encode (a.take a.length.pred) := by
  change eval_l take_m (Nat.pair (Nat.pair (Encodable.encode a) n).unpair.1
    (eval_l last_index_m (Nat.pair (Encodable.encode a) n).unpair.1)) = _
  rw [Nat.unpair_pair, last_index_encode_l, take_array_encode_l]

/-- 最大父行测试使用原数组，不使用展开下标作行号。 -/
theorem maximal_eval_l (a : BMSArray) (n : Nat) :
    eval_l maximal_m (Nat.pair (Encodable.encode a) n) = Encodable.encode (BMS.maximalParentRow a) := by
  change eval_l SecondOrderProgramMaximalParentRow.maximal_m (Nat.pair (Encodable.encode a) n).unpair.1 = _
  rw [Nat.unpair_pair, maximal_encode_l]

/-- 最大父行some分支的原自然数解包。 -/
theorem row_input_eval_l (a : BMSArray) (n m : Nat) (hm : BMS.maximalParentRow a = some m) :
    eval_l row_input_m (Nat.pair (Encodable.encode a) n) = Nat.pair (Nat.pair (Encodable.encode a) n) m := by
  change Nat.pair (eval_l PrimitiveProgram.id_m (Nat.pair (Encodable.encode a) n))
    (eval_l pred_m (eval_l maximal_m (Nat.pair (Encodable.encode a) n))) = _
  rw [PrimitiveProgram.id_l, maximal_eval_l, hm, pred_eval_l]
  rfl

/-- 所选行的末列父查询精确等于原parent。 -/
theorem parent_test_encode_l (a : BMSArray) (n m : Nat) :
    eval_l parent_test_m (Nat.pair (Nat.pair (Encodable.encode a) n) m) =
      Encodable.encode (BMS.parent m a a.length.pred) := by
  have hi : eval_l parent_input_m (Nat.pair (Nat.pair (Encodable.encode a) n) m) =
      Nat.pair (Nat.pair (Encodable.encode a) m) a.length.pred := by
    simp only [parent_input_m, eval_l, Nat.unpair_pair, last_index_encode_l]
  change eval_l parent_m (eval_l parent_input_m (Nat.pair (Nat.pair (Encodable.encode a) n) m)) = _
  rw [hi, parent_encode_l]

/-- 父列some分支只去掉一个Option后继壳。 -/
theorem success_input_eval_l (a : BMSArray) (n m p : Nat)
    (hp : BMS.parent m a a.length.pred = some p) :
    eval_l success_input_m (Nat.pair (Nat.pair (Encodable.encode a) n) m) =
      Nat.pair (Encodable.encode a) (Nat.pair n (Nat.pair m p)) := by
  let q := Nat.pair (Nat.pair (Encodable.encode a) n) m
  change Nat.pair q.unpair.1.unpair.1 (Nat.pair q.unpair.1.unpair.2
    (Nat.pair q.unpair.2 (eval_l pred_m (eval_l parent_test_m q)))) = _
  rw [parent_test_encode_l, hp, pred_eval_l]
  simp only [q, Nat.unpair_pair, Encodable.encode_some, Encodable.encode_nat, Nat.pred_succ]

/-- 所选行之后仍保留原父列none/some两分支。 -/
theorem after_row_encode_l (a : BMSArray) (n m : Nat) :
    eval_l after_row_m (Nat.pair (Nat.pair (Encodable.encode a) n) m) = Encodable.encode
      (match BMS.parent m a a.length.pred with
      | none => a.take a.length.pred
      | some p => a.take p ++ (List.range (n + 1)).flatMap (fun k =>
          BMS.copyBlock a (BMS.slice a p (a.length.pred - p)) m p k (a[a.length.pred]?.getD []))) := by
  rw [after_row_m, branch_eval_l, parent_test_encode_l]
  cases hp : BMS.parent m a a.length.pred with
  | none =>
      change eval_l fallback_m (Nat.pair (Nat.pair (Encodable.encode a) n) m).unpair.1 = _
      rw [Nat.unpair_pair, fallback_encode_l]
  | some p =>
      rw [show Encodable.encode (some p) = p + 1 from rfl, if_neg (Nat.add_one_ne_zero p)]
      change eval_l success_m (eval_l success_input_m (Nat.pair (Nat.pair (Encodable.encode a) n) m)) = _
      rw [success_input_eval_l a n m p hp, success_encode_l]

private theorem raw_formula_l (a : BMSArray) (n : Nat) :
    BMS.expandRaw a n = (match BMS.maximalParentRow a with
      | none => a.take a.length.pred
      | some m => match BMS.parent m a a.length.pred with
        | none => a.take a.length.pred
        | some p => a.take p ++ (List.range (n + 1)).flatMap (fun k =>
            BMS.copyBlock a (BMS.slice a p (a.length.pred - p)) m p k (a[a.length.pred]?.getD []))) := by
  cases h : a.length with
  | zero =>
      have ha : a = [] := by
        cases a with
        | nil => rfl
        | cons _ _ => simp at h
      subst a
      rfl
  | succ k =>
      simp only [BMS.expandRaw, h, Nat.pred_succ]
      cases BMS.maximalParentRow a with
      | none => rfl
      | some m => cases BMS.parent m a k <;> rfl

/-- 单个固定原程序逐标准输入就是完整expandRaw，不再只是成功分支。 -/
theorem raw_encode_l (a : BMSArray) (n : Nat) :
    eval_l raw_m (Nat.pair (Encodable.encode a) n) = Encodable.encode (BMS.expandRaw a n) := by
  rw [raw_formula_l, raw_m, branch_eval_l, maximal_eval_l]
  cases hm : BMS.maximalParentRow a with
  | none =>
      change eval_l fallback_m (Nat.pair (Encodable.encode a) n) = _
      exact fallback_encode_l a n
  | some m =>
      rw [show Encodable.encode (some m) = m + 1 from rfl, if_neg (Nat.add_one_ne_zero m)]
      change eval_l after_row_m (eval_l row_input_m (Nat.pair (Encodable.encode a) n)) = _
      rw [row_input_eval_l a n m hm, after_row_encode_l]

/-- 实际先展开再裁剪，准确连接原BMS.expand的全部标准输入。 -/
theorem expand_encode_l (a : BMSArray) (n : Nat) :
    eval_l expand_m (Nat.pair (Encodable.encode a) n) = Encodable.encode (BMS.expand a n) := by
  change eval_l SecondOrderProgramTrimArray.trim_m (eval_l raw_m (Nat.pair (Encodable.encode a) n)) = _
  rw [raw_encode_l, SecondOrderProgramTrimArray.array_encode_correct_l]
  rfl

/-- 任意内部输入上的真实顶层分支图，不把标准算法身份用于此证明。 -/
theorem raw_rel_l (hℳ : Theory.Models ℳ theory_m) {R M I A F : set_l ℳ}
    (hR : graph_semantics_l (graph_m raw_m) R)
    (hM : graph_semantics_l (graph_m maximal_m) M)
    (hI : graph_semantics_l (graph_m row_input_m) I)
    (hA : graph_semantics_l (graph_m after_row_m) A)
    (hF : graph_semantics_l (graph_m fallback_m) F) (x y : num_l ℳ) :
    relation_l R x y ↔
      (relation_l M x (zero_l ℳ) ∧ relation_l F x y) ∨
      (¬relation_l M x (zero_l ℳ) ∧ ∃ r, relation_l I x r ∧ relation_l A r y) := by
  classical
  obtain ⟨m, hm, _⟩ := value_exists_l hℳ maximal_m hM
  obtain ⟨i, hi, _⟩ := value_exists_l hℳ row_input_m hI
  obtain ⟨a, ha, _⟩ := value_exists_l hℳ after_row_m hA
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ fallback_m hF
  have hv := (branch_value_l hℳ hm (comp_value_l hℳ ha hi) hf) hR x y
  rw [hv]
  simp only [hm hM, hi hI, ha hA, hf hF, exists_eq_left']
  by_cases hz : m x = zero_l ℳ <;> simp [hz]

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramExpansion
