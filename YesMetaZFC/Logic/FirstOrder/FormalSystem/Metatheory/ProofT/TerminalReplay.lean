import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedCompleteness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay.Failure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedSyntax

/-!
# ProofT terminal-aware replay 结果

该模块把低层 `fs_replay_code` 的 `Option` 结果提升为三个可计算分支：

* 公式或证书解码、逐行回放失败；
* replay 成功但末行不是目标公式；
* replay 成功且目标公式正好是末行。

证明字段只记录已经执行的检查，不改变低层 replay 的计算路径。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace Rosser

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode

set_option autoImplicit false

/-- 精确 terminal-aware proof code 检查的元层结果。 -/
inductive FSProofCodeCheckResult
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (proofCode : Nat)
    (formula : SetFormula) : Type
  | replay_failure
      (failure : FSReplayCodeFailure enumeration proofCode) :
      FSProofCodeCheckResult enumeration proofCode formula
  | terminal_mismatch
      (state : FSReplayState enumeration proofCode)
      (hReplay :
        fs_replay_code enumeration proofCode = some state)
      (hTerminal :
        state.proof.getLast? ≠
          some (Formula.hilbertize SetSort.set formula)) :
      FSProofCodeCheckResult enumeration proofCode formula
  | accept
      (state : FSReplayState enumeration proofCode)
      (hReplay :
        fs_replay_code enumeration proofCode = some state)
      (hTerminal :
        state.proof.getLast? =
          some (Formula.hilbertize SetSort.set formula)) :
      FSProofCodeCheckResult enumeration proofCode formula

/-- 计算 terminal-aware proof code 检查结果。 -/
def fs_terminal_checked_result
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    (proofCode : Nat)
    (formula : SetFormula) :
    FSProofCodeCheckResult enumeration proofCode formula := by
  cases hReplay : fs_replay_code enumeration proofCode with
  | none =>
      exact
        FSProofCodeCheckResult.replay_failure
          (fs_replay_code_failure_of_none
            enumeration proofCode hReplay)
  | some state =>
      cases hLast : state.proof.getLast? with
      | none =>
          exact
            FSProofCodeCheckResult.terminal_mismatch
              state hReplay (by simp [hLast])
      | some last =>
          by_cases hEqual :
              fs_formula_code_eq
                last (Formula.hilbertize SetSort.set formula) = true
          · have hSyntaxEqual :
                last = Formula.hilbertize SetSort.set formula :=
              fs_formula_code_eq_sound hEqual
            subst last
            exact
              FSProofCodeCheckResult.accept
                state hReplay (by simp [hLast])
          · exact
              FSProofCodeCheckResult.terminal_mismatch
                state hReplay (by
                  intro hTarget
                  have hLastEqual :
                      last = Formula.hilbertize SetSort.set formula :=
                    Option.some.inj (hLast.symm.trans hTarget)
                  subst last
                  exact hEqual (by simp [fs_formula_code_eq]))

/-- 接受构造器恰好给出 canonical terminal checked 关系。 -/
theorem FSProofCodeCheckResult.accept_checked
    {theory : SetTheory}
    (enumeration : ProofCode.HilbertTheoryEnumeration theory)
    {proofCode : Nat}
    {formula : SetFormula}
    {state : FSReplayState enumeration proofCode}
    (hReplay :
      fs_replay_code enumeration proofCode = some state)
    (hTerminal :
      state.proof.getLast? =
        some (Formula.hilbertize SetSort.set formula)) :
    fs_terminal_checked_hilbertized_proof_code_for
      enumeration proofCode formula :=
  ⟨state, hReplay, hTerminal⟩

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
