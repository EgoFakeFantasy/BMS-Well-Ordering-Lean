import BMSConstructibleBridge.SecondOrderProgramCopyEntry
import BMSConstructibleBridge.SecondOrderProgramListMap

/-!
# 原 copyBlock 的完整嵌套映射程序

输入pair块(pair A(pair复制次数末列))，A为pair原数组(pair最大父行父列)。
首列直接从原块读取，不能由调用方另外提供。外层遍历块列、内层遍历原列条目，
两层下标都从零开始；空块、空列和首末列长度不同亦覆盖。标准输出就是原copyBlock。
内部接线只组合真实原图，逐内部下标的完整复制规格还须消费映射归纳模块。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyBlock

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics SecondOrderProgramTotality
open SecondOrderProgramArithmetic SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramCopyEntry (entry_m entry_encode_l)
open SecondOrderProgramListMap (map_m map_encode_l)
open SecondOrderProgramListCode (head_m head_encode_l)
open SecondOrderProgramTrimHeight (array_encode_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 把外层的局部列下标纳入内层共享参数，原列码作被遍历列表。 -/
def column_input_m : code_m := .pair
  (.pair .left (.comp .left .right)) (.comp .right .right)

/-- 对一整列执行原逐条目更新。 -/
def column_m : code_m := .comp (map_m entry_m) column_input_m

/-- 从原块头取得首列，将它与原上升参数、次数及末列组成共享参数。 -/
def parameter_m : code_m := .pair (.comp .left .right)
  (.pair (.comp (.comp .left .right) .right)
    (.pair (.comp head_m .left) (.comp (.comp .right .right) .right)))

/-- 外层映射仍遍历同一原块，不改变块的宽度或顺序。 -/
def copy_input_m : code_m := .pair parameter_m .left

/-- 原copyBlock的单个固定程序。 -/
def copy_m : code_m := .comp (map_m column_m) copy_input_m

/-- 标准外层回调转内层映射的接线。 -/
theorem column_input_eval_l (q j s : Nat) :
    eval_l column_input_m (Nat.pair q (Nat.pair j s)) = Nat.pair (Nat.pair q j) s := by
  simp only [column_input_m, eval_l, Nat.unpair_pair]

/-- 完整一列的逐标准身份，使用原列自身长度而非最大父行作循环界。 -/
theorem column_encode_l (a : BMSArray) (m p k : Nat) (f l s : List Nat) (j : Nat) :
    eval_l column_m (Nat.pair
      (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p))
        (Nat.pair k (Nat.pair (Encodable.encode f) (Encodable.encode l))))
      (Nat.pair j (Encodable.encode s))) =
      Encodable.encode (s.mapIdx (fun r v => if BMS.ascending a m p j r then
        match f[r]?, l[r]? with
        | some first, some last => v + k * (last - first)
        | _, _ => v
      else v)) := by
  change eval_l (map_m entry_m) (eval_l column_input_m
    (Nat.pair (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p))
      (Nat.pair k (Nat.pair (Encodable.encode f) (Encodable.encode l))))
      (Nat.pair j (Encodable.encode s)))) = _
  rw [column_input_eval_l, map_encode_l]
  apply congrArg Encodable.encode
  apply List.mapIdx_eq_mapIdx_iff.mpr
  intro r hr
  exact entry_encode_l a m p k f l j r s[r]

/-- 原嵌套码的头列默认空列，保持原head?.getD[]约定。 -/
theorem head_array_encode_l (b : BMSArray) :
    eval_l head_m (Encodable.encode b) = Encodable.encode (b.head?.getD []) := by
  rw [array_encode_l, head_encode_l]
  cases b <;> rfl

/-- 共享首列实际来自块头；空块得到原空列码。 -/
theorem copy_input_encode_l (b : BMSArray) (A k : Nat) (l : List Nat) :
    eval_l copy_input_m (Nat.pair (Encodable.encode b) (Nat.pair A (Nat.pair k (Encodable.encode l)))) =
      Nat.pair (Nat.pair A (Nat.pair k
        (Nat.pair (Encodable.encode (b.head?.getD [])) (Encodable.encode l)))) (Encodable.encode b) := by
  simp only [copy_input_m, parameter_m, eval_l, Nat.unpair_pair, head_array_encode_l]

/-- 全部原数组和块上的完整标准身份，不要求矩形性、生成性或先验父表。 -/
theorem copy_encode_l (a b : BMSArray) (m p k : Nat) (l : List Nat) :
    eval_l copy_m (Nat.pair (Encodable.encode b)
      (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p)) (Nat.pair k (Encodable.encode l)))) =
      Encodable.encode (BMS.copyBlock a b m p k l) := by
  change eval_l (map_m column_m) (eval_l copy_input_m
    (Nat.pair (Encodable.encode b)
      (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p)) (Nat.pair k (Encodable.encode l))))) = _
  rw [copy_input_encode_l]
  have hm := map_encode_l column_m
    (Nat.pair (Nat.pair (Encodable.encode a) (Nat.pair m p))
      (Nat.pair k (Nat.pair (Encodable.encode (b.head?.getD [])) (Encodable.encode l))))
    (b.map Encodable.encode)
  rw [← array_encode_l b] at hm
  rw [hm, array_encode_l (BMS.copyBlock a b m p k l)]
  apply congrArg Encodable.encode
  apply List.ext_getElem?
  intro i
  simp only [BMS.copyBlock, List.getElem?_map, List.getElem?_mapIdx]
  cases hi : b[i]? with
  | none => rfl
  | some s =>
      simp only [Option.map_some]
      exact congrArg some (column_encode_l a m p k (b.head?.getD []) l s i)

/-- 任意内部数上的列回调准确调用同一内层map图。 -/
theorem column_rel_l (hℳ : Theory.Models ℳ theory_m) {C M : set_l ℳ}
    (hC : graph_semantics_l (graph_m column_m) C)
    (hM : graph_semantics_l (graph_m (map_m entry_m)) M) (q j s y : num_l ℳ) :
    relation_l C (value_l q (value_l j s)) y ↔ relation_l M (value_l (value_l q j) s) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ (map_m entry_m) hM
  have hi : value_spec_l column_input_m _ := pair_value_l hℳ
    (pair_value_l hℳ (left_value_l hℳ) (comp_value_l hℳ (left_value_l hℳ) (right_value_l hℳ)))
    (comp_value_l hℳ (right_value_l hℳ) (right_value_l hℳ))
  have hv := (comp_value_l hℳ hf hi) hC (value_l q (value_l j s)) y
  simpa only [SecondOrderUnpairing.unpair_l, hf hM] using hv

/-- 完整复制图的外层接线，参数仍由同一原parameter_m图实际生成。 -/
theorem copy_rel_l (hℳ : Theory.Models ℳ theory_m) {C M P : set_l ℳ}
    (hC : graph_semantics_l (graph_m copy_m) C)
    (hM : graph_semantics_l (graph_m (map_m column_m)) M)
    (hP : graph_semantics_l (graph_m parameter_m) P) (b t y : num_l ℳ) :
    relation_l C (value_l b t) y ↔
      ∃ q, relation_l P (value_l b t) q ∧ relation_l M (value_l q b) y := by
  obtain ⟨f, hf, _⟩ := value_exists_l hℳ parameter_m hP
  obtain ⟨g, hg, _⟩ := value_exists_l hℳ (map_m column_m) hM
  have hv := (comp_value_l hℳ hg (pair_value_l hℳ hf (left_value_l hℳ)))
    hC (value_l b t) y
  simp only [SecondOrderUnpairing.unpair_l] at hv
  rw [hv]
  simp only [hf hP, hg hM, exists_eq_left']

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramCopyBlock
