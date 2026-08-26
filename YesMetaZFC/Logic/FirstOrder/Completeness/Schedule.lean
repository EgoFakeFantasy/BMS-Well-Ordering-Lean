import YesMetaZFC.Logic.FirstOrder.Completeness.Henkin
import YesMetaZFC.Logic.FirstOrder.NatPairing
/-!
# 可数签名的公平 Henkin 调度
本模块把“实际签名可数”分解为两个独立合同：
* `NatCoding` 只要求给出到自然数的单射；
* `Schedule.of_coding` 通过经典逆像选择与公平重复，把公式编码提升为 Henkin 调度。
配对函数使用二进制分解
`2 ^ left * (2 * right + 1)`。左投影读取二因子重数，右投影读取剩余奇数部分；
因此每个编码都能在任意起点之后再次出现，不需要把可计算枚举器塞进证明论核心。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin
universe u v w z
/-! ## 从单射得到枚举 -/
/-- 一个类型到自然数的可审计单射编码。 -/
structure NatCoding (α : Type z) where
  encode : α → Nat
  injective : Function.Injective encode
namespace NatCoding
/-- 自然数的恒等编码。 -/
def nat : NatCoding Nat where
  encode := id
  injective := fun _ _ h => h
/-- 列表编码；零表示空表，正数通过配对保存表头与表尾。 -/
def list_encode {α : Type z} (coding : NatCoding α) : List α → Nat
  | [] => 0
  | head :: tail =>
      NatPairing.pair (coding.encode head) (list_encode coding tail) + 1
/-- 列表编码保持单射。 -/
theorem list_encode_injective {α : Type z} (coding : NatCoding α) :
    Function.Injective (list_encode coding) := by
  intro left
  induction left with
  | nil =>
      intro right hCode
      cases right with
      | nil => rfl
      | cons head tail =>
          simp [list_encode] at hCode
  | cons head tail ih =>
      intro right hCode
      cases right with
      | nil =>
          simp [list_encode] at hCode
      | cons head' tail' =>
          simp only [list_encode] at hCode
          have hPair := Nat.add_right_cancel hCode
          rcases NatPairing.pair_eq_pair_iff.mp hPair with
            ⟨hHead, hTail⟩
          rw [coding.injective hHead, ih hTail]
/-- 单射编码在有限列表上的标准提升。 -/
def list {α : Type z} (coding : NatCoding α) : NatCoding (List α) where
  encode := list_encode coding
  injective := list_encode_injective coding
/--
从单射编码选择对应逆像。
这个函数只服务于非计算性的 Henkin 完备性构造；ATP 搜索本身不执行它。
-/
noncomputable def decode {α : Type z} (coding : NatCoding α) (code : Nat) :
    Option α := by
  classical
  exact
    if hCode : ∃ value, coding.encode value = code then
      some (Classical.choose hCode)
    else
      none
/-- 解码自己的编码精确返回原值。 -/
@[simp]
theorem decode_encode {α : Type z} (coding : NatCoding α) (value : α) :
    coding.decode (coding.encode value) = some value := by
  classical
  unfold decode
  split
  · rename_i hCode
    exact congrArg some (coding.injective (Classical.choose_spec hCode))
  · rename_i hCode
    exact False.elim (hCode ⟨value, rfl⟩)
end NatCoding
/-! ## 公平公式重放 -/
namespace Schedule
/-- 调度索引中公平重复的基础公式编码。 -/
def fair_code (index : Nat) : Nat :=
  NatPairing.first index
/-- 每个自然数编码在任意起点之后都会再次出现。 -/
theorem fair_code_cofinal (code start : Nat) :
    ∃ index, start ≤ index ∧ fair_code index = code := by
  refine ⟨NatPairing.pair code start, NatPairing.le_pair_right code start, ?_⟩
  simp [fair_code]
/--
任意原始公式单射编码都产生公平 Henkin 调度。
非法或未命中的编码统一回落到 `truth`；目标公式若 admissible，则其自身编码分支不会
触发回落，因此仍能在任意起点之后精确重现。
-/
noncomputable def of_coding {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (coding : NatCoding (Formula σ)) :
    Schedule σ := by
  classical
  refine {
    formula := fun index =>
      match coding.decode (fair_code index) with
      | some formula =>
          if Formula.Admissible formula then formula else Formula.truth
      | none => Formula.truth
    admissible := ?_
    cofinal := ?_
  }
  · intro index
    split
    next formula hDecode =>
      split
      next hFormula => exact hFormula
      next _ => exact Formula.Admissible.truth
    next _ =>
      exact Formula.Admissible.truth
  · intro target hTarget start
    rcases fair_code_cofinal (coding.encode target) start with
      ⟨index, hStart, hCode⟩
    refine ⟨index, hStart, ?_⟩
    simp [hCode, hTarget]
end Schedule
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
