import BMSConstructibleBridge.SecondOrderProgramSeed
import BMSConstructibleBridge.SecondOrderProgramRun

/-!
# 生成数组原解码器的单一显式程序

保留ArithmeticPresentation.encode_l/decode_l：输入码是原Encodable的高度与轨迹对。
同一Nat列表编码覆盖所有自然数，所以原Option解码的默认分支实际不可达；先证明
这一点，再给出每个输入上的原解码身份。没有另定义一个替代的生成数组解码器，
也不使用code_l的最小规范化搜索。内部图规格只连接原seed和run图，尚非良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedDecode

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderProgramSemantics
open SecondOrderProgramValue SecondOrderProgramCallbackValue
open SecondOrderProgramSeed (seed_m seed_encode_l)
open SecondOrderProgramRun (run_m run_encode_l)
open PrimitiveProgram (code_m eval_l graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 输入的右坐标是原轨迹码，左坐标用于构造原初始数组。 -/
def input_m : code_m := .pair .right (.comp seed_m .left)

/-- 单一七构造程序：不含解码oracle或无界规范化搜索。 -/
def decode_m : code_m := .comp run_m input_m

/-- 原编码确实覆盖全部自然数；使用相同Encodable实例的列表满射证书。 -/
theorem input_surj_l (x : Nat) : ∃ n s, ArithmeticPresentation.encode_l n s = x := by
  refine ⟨x.unpair.1, Denumerable.ofNat (List Nat) x.unpair.2, ?_⟩
  simp only [ArithmeticPresentation.encode_l, Encodable.encode_prod_val, Encodable.encode_nat,
    Denumerable.encode_ofNat, Nat.pair_unpair]

/-- 原Option解码对每个输入实际成功；原默认分支因此没有被无依据地删去。 -/
theorem decode_present_l (x : Nat) :
    ∃ p : Nat × List Nat, Encodable.decode x = some p := by
  obtain ⟨n, s, rfl⟩ := input_surj_l x
  exact ⟨(n, s), Encodable.encodek (n, s)⟩

/-- 原高度与轨迹码被接入原fold所需的轨迹、初值顺序。 -/
theorem input_encode_l (n : Nat) (s : List Nat) :
    eval_l input_m (ArithmeticPresentation.encode_l n s) =
      Nat.pair (Encodable.encode s) (Encodable.encode (BMS.seed n)) := by
  change Nat.pair (ArithmeticPresentation.encode_l n s).unpair.2
    (eval_l seed_m (ArithmeticPresentation.encode_l n s).unpair.1) = _
  simp only [ArithmeticPresentation.encode_l, Encodable.encode_prod_val, Encodable.encode_nat,
    Nat.unpair_pair, seed_encode_l]

/-- 在原轨迹对的编码上，程序产生原eval_l的数组码。 -/
theorem decode_encode_l (n : Nat) (s : List Nat) :
    eval_l decode_m (ArithmeticPresentation.encode_l n s) =
      Encodable.encode (ArithmeticPresentation.eval_l (n, s)).1.raw := by
  change eval_l run_m (eval_l input_m (ArithmeticPresentation.encode_l n s)) = _
  rw [input_encode_l]
  exact run_encode_l (BMS.validSeed n) s

/-- 每个自然数输入上均等于原decode_l，非仅规范码或预设生成轨迹。 -/
theorem decode_eval_l (x : Nat) :
    eval_l decode_m x = Encodable.encode (ArithmeticPresentation.decode_l x).1.raw := by
  obtain ⟨n, s, rfl⟩ := input_surj_l x
  rw [decode_encode_l, ArithmeticPresentation.decode_encode_l]

/-- 同一输入接线在全部内部数上仍调用实际seed/run图。 -/
theorem decode_rel_l (hℳ : Theory.Models ℳ theory_m) {D S R : set_l ℳ}
    (hD : graph_semantics_l (graph_m decode_m) D)
    (hS : graph_semantics_l (graph_m seed_m) S)
    (hR : graph_semantics_l (graph_m run_m) R) (x y : num_l ℳ) :
    relation_l D x y ↔ ∃ a,
      relation_l S (SecondOrderUnpairing.value_l hℳ x).1 a ∧
      relation_l R (value_l (SecondOrderUnpairing.value_l hℳ x).2 a) y := by
  obtain ⟨s, hs, _⟩ := value_exists_l hℳ seed_m hS
  obtain ⟨r, hr, _⟩ := value_exists_l hℳ run_m hR
  have hi : value_spec_l input_m _ := pair_value_l hℳ (right_value_l hℳ)
    (comp_value_l hℳ hs (left_value_l hℳ))
  have hd : value_spec_l decode_m _ := comp_value_l hℳ hr hi
  rw [hd hD]
  simp only [hs hS, hr hR, exists_eq_left']

#print axioms input_m
#print axioms decode_m
#print axioms input_surj_l
#print axioms decode_present_l
#print axioms input_encode_l
#print axioms decode_encode_l
#print axioms decode_eval_l
#print axioms decode_rel_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramGeneratedDecode
