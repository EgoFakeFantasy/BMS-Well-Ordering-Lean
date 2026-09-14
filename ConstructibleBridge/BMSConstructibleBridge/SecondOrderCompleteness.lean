import BMSConstructibleBridge.SecondOrderArithmetic
import YesMetaZFC.Automation.SyntaxNatCoding
import YesMetaZFC.Logic.FirstOrder.Completeness.StrongCompleteness

/-!
# 固定二阶算术签名的完备性回传

有限符号编号产生固定的公平 Henkin 调度；现有强完备性仅从所有相应模型中的
真值回传对象推导。单一标准模型真值不满足此前提。此调度不充当对象证明编码，
所得 `Derives` 也不附带原始递归生成器或其在 PRA 中的正确性证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCompleteness

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic
open _root_.YesMetaZFC.Automation.SyntaxNatCoding

set_option autoImplicit false

private def sort : sort_m → Nat
  | .num => 0
  | .set => 1

private def func : func_m → Nat
  | .zero => 0
  | .succ => 1
  | .add => 2
  | .mul => 3
  | .pair => 4

private def rel : rel_m → Nat
  | .mem => 0
  | .start => 1
  | .step => 2

/-- 编码覆盖原完整有限签名；理论仍只给纯片段公理。 -/
def symbols_m : SymbolCoding signature_m where
  sort := ⟨sort, by intro a b h; cases a <;> cases b <;> simp_all [sort]⟩
  function := ⟨func, by intro a b h; cases a <;> cases b <;> simp_all [func]⟩
  relation := ⟨rel, by intro a b h; cases a <;> cases b <;> simp_all [rel]⟩

noncomputable def schedule_m : Completeness.Henkin.Schedule signature_m := schedule symbols_m

/-- 对所有同签名模型成立的闭句可回传为该对象理论的真实推导。 -/
theorem derives_m {φ : Sentence signature_m}
    (h : Theory.SemanticallyEntails.{0, 0, 0, 0} theory_m φ) : Derives theory_m [] φ :=
  Completeness.strong_completeness schedule_m h

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCompleteness
