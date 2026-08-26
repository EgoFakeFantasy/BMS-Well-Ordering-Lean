import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedCompleteness
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.RosserFinite

/-!
# `ProofT` 的可判定证明表示

该接口包装任意 Hilbert 理论枚举的 checked replay，并要求调用方把 replay 的成功
与失败分别内部化到同一个对象证明谓词。

这里的“`Delta1`”指标准自然数上的可计算判定及其逐点正负表示。形式化的 Lévy
层级接口位于 `ProofT.Hierarchy`；只有另行给出 `Delta0ProofGraph` 并把它与本
presentation 的 replay 关系接通后，才能宣称得到语法意义上的 `Δ₁` proof graph。
canonical checked 关系要求目标公式正好是 replay 结果末行。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation
open Rosser

set_option autoImplicit false

/--
理论 `Thilbert` 的外部 checked replay 与理论 `Traw` 中对象证明谓词之间的表示合同。

该结构只保存 Rosser 终局实际消费的能力：replay 可靠性与完备性由枚举器导出；
对象侧只需交付真实 quotation 上的存在正表示和逐码负表示。
-/
structure Delta1ProofPresentation
    (Traw Thilbert : SetTheory) where
  enumeration :
    ProofCode.HilbertTheoryEnumeration Thilbert
  hilbert_closed :
    ∀ formula, Thilbert formula →
      Thilbert (Formula.hilbertize SetSort.set formula)
  verifier : ObjectCertificateVerifier
  base : FreeVarId
  realize :
    ∀ {formula : SetFormula} {code : SetTerm},
      GodelQuotation.Numbered.quote? formula = some code →
      HilbertDerives Thilbert formula →
      ∃ proofCode,
        Derives Traw [] (
          proof_condition
            verifier (numₘ(proofCode)) code base)
  reject :
    ∀ (proofCode : Nat) {formula : SetFormula} {code : SetTerm},
      Formula.Admissible formula →
      GodelQuotation.Numbered.quote? formula = some code →
      ¬ fs_terminal_checked_hilbertized_proof_code_for
          enumeration proofCode formula →
      Derives Traw [] (
        ¬ₘ proof_condition
          verifier (numₘ(proofCode)) code base)

namespace Delta1ProofPresentation

/-- presentation 所固定的精确末行 checked 证明码关系。 -/
def checked
    {Traw Thilbert : SetTheory}
  (P : Delta1ProofPresentation Traw Thilbert)
    (proofCode : Nat) (formula : SetFormula) : Prop :=
  fs_terminal_checked_hilbertized_proof_code_for
    P.enumeration proofCode formula

/-- checked replay 成功给出 Hilbert 化目标的真实推导。 -/
theorem checked_sound
    {Traw Thilbert : SetTheory}
    (P : Delta1ProofPresentation Traw Thilbert)
    {proofCode : Nat} {formula : SetFormula}
    (hChecked : P.checked proofCode formula) :
      HilbertDerives Thilbert
      (Formula.hilbertize SetSort.set formula) :=
  fs_terminal_checked_hilbertized_proof_code_for_sound
    P.enumeration hChecked

/-- 每个 Hilbert 可推导公式都有一个被 presentation 接受的 checked proof code。 -/
theorem checked_complete
    {Traw Thilbert : SetTheory}
    (P : Delta1ProofPresentation Traw Thilbert)
    {formula : SetFormula}
    (hDerives : HilbertDerives Thilbert formula) :
    ∃ proofCode, P.checked proofCode formula :=
  fs_terminal_checked_hilbertized_proof_code_for_exists_of_derives
    P.enumeration P.hilbert_closed hDerives

/--
presentation 的 Hilbert 理论吸收自身的再次 Hilbert 化。

这是 `hilbert_closed` 的理论包含形式，供整棵 Hilbert 推导再次编译时使用。
-/
theorem hilbertized_subset
    {Traw Thilbert : SetTheory}
    (P : Delta1ProofPresentation Traw Thilbert) :
    ∀ candidate,
      Theory.hilbertize SetSort.set Thilbert candidate →
        Thilbert candidate := by
  rintro candidate ⟨formula, hFormula, rfl⟩
  exact P.hilbert_closed formula hFormula

end Delta1ProofPresentation
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
