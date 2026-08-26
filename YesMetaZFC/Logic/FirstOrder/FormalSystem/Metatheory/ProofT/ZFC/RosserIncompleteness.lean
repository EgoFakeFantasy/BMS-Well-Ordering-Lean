import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Rosser
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hilbertization
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.RosserFiniteAssembly
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.Delta1ProofPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SupportElimination

/-!
# ZFC 的抽象 Rosser 实例

本模块只把现有 ZFC checked proof presentation、verifier 支撑、有限比较装配、
raw 到 Hilbert 编译桥及对角编码承载打包为 `ProofT.RosserPresentation`。

Rosser 的逐码正负内部化、一致性矛盾和对角终局均由通用定理完成；ZFC 不再维护
一份平行的终局证明。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation
open Rosser

set_option autoImplicit false

namespace ProofT
namespace ZFC

/-- 当前 ZFC verifier 的 Rosser 自由变量支撑合同。 -/
private def rosser_support :
    ProofT.RosserVerifierSupport
      proof_presentation.verifier where
  toVerifierSupport := by
    simpa [proof_presentation] using
      ProofT.ZFC.verifier_support
  formula_freeSupport_subset := by
    intro formula freeVariable hMember
    simpa [proof_presentation,
      fs_zfc_object_certificate_verifier] using
      fs_formula_replay_condition_freeSupport_subset
        formula freeVariable hMember

/-- 当前 ZFC 对象证明码谓词的有限 Rosser 比较装配。 -/
private def rosser_assembly :
    ProofT.RosserAssembly
      fs_zfc_support_raw_theory
      proof_presentation.verifier
      proof_presentation.base where
  code_id :=
    fs_zfc_rosser_code_id
  proof_code_id :=
    fs_zfc_rosser_proof_code_id
  smaller_code_id :=
    fs_zfc_rosser_smaller_code_id
  predicate_at_eq := by
    intro formulaCode hCode
    simpa [proof_presentation,
      fs_zfc_rosser_predicate_at,
      fs_zfc_rosser_predicate,
      ProofT.rosser_predicate_at,
      ProofT.rosser_predicate] using
      predicate_at_eq_comparison formulaCode hCode
  positive := by
    intro proofCode left right
      hLeft hRight hPositive hBranch
    simpa [proof_presentation] using
      comparison_of_numeral_branches
        proofCode left right hLeft hRight
        hPositive hBranch
  negative := by
    intro proofCode left right
      hLeft hRight hRightCode hLeftBranch
    simpa [proof_presentation] using
      comparison_neg_of_right_numeral
        core proofCode left right
        hLeft hRight hRightCode hLeftBranch

/--
ZFC 支持理论的完整 Rosser presentation。

该实例直接复用现有 `Delta1ProofPresentation` 和 `ProofT.Core` 的真实实现；
不增加模型健全性、`1`-一致性或额外 schema 假设。
-/
def rosser_presentation :
    ProofT.RosserPresentation
      fs_zfc_support_raw_theory
      fs_zfc_support_theory where
  proof :=
    proof_presentation
  support :=
    rosser_support
  assembly :=
    rosser_assembly
  raw_hilbert :=
    fs_zfc_support_hilbert_derives_of_raw
  code_naming :=
    fs_zfc_support_theory_extends_code_naming
  theory_sentence :=
    fs_zfc_support_theory_sentence

/-- 当前 ZFC presentation 的任意 Rosser 对角句在一致性下独立。 -/
theorem independence_of_diagonal
    {fixedPoint : SetFormula}
    {fixedPointCode : SetTerm}
    (hSentence : Formula.Sentence fixedPoint)
    (hQuote :
      GodelQuotation.Numbered.quote? fixedPoint =
        some fixedPointCode)
    (hFixedPoint :
      HilbertDerives fs_zfc_support_theory
        (Formula.hilbert_iff fixedPoint
          (Formula.neg
            (rosser_presentation.predicate_instance
              fixedPointCode))))
    (hConsistent :
      Derives.Consistent fs_zfc_support_theory []) :
    (¬ HilbertDerives fs_zfc_support_theory fixedPoint) ∧
      (¬ HilbertDerives fs_zfc_support_theory
        (Formula.neg fixedPoint)) :=
  rosser_presentation.independent
    hSentence hQuote hFixedPoint hConsistent

/--
ZFC 的 Rosser 不完备定理。

若内部 ZFC 支持理论一致，则存在一个闭句，理论既不证明它，也不证明其否定。
-/
theorem rosser_incompleteness
    (hConsistent :
      Derives.Consistent fs_zfc_support_theory []) :
    ∃ fixedPoint : SetFormula,
      Formula.Sentence fixedPoint ∧
        (¬ HilbertDerives fs_zfc_support_theory fixedPoint) ∧
        (¬ HilbertDerives fs_zfc_support_theory
          (Formula.neg fixedPoint)) :=
  ProofT.rosser_incompleteness
    rosser_presentation hConsistent

/--
raw ZFC 支持理论的一致性已经足以推出当前 Rosser 终局。

Hilbert 化不增加矛盾只由纯语法反射定理给出；这里不再要求调用方直接提交
`fs_zfc_support_theory` 的一致性。
-/
theorem rosser_incompleteness_of_raw
    (hConsistent :
      Derives.Consistent
        fs_zfc_support_raw_theory []) :
    ∃ fixedPoint : SetFormula,
      Formula.Sentence fixedPoint ∧
        (¬ HilbertDerives
          fs_zfc_support_theory fixedPoint) ∧
        (¬ HilbertDerives fs_zfc_support_theory
          (Formula.neg fixedPoint)) := by
  apply rosser_incompleteness
  simpa [fs_zfc_support_theory,
    fs_zfc_support_raw_theory,
    fs_internal_project_theory,
    fs_internal_project_raw_theory,
    fs_internal_theory] using
    (ProofT.Hilbertization.consistent
      (anchorSort := SetSort.set)
      hConsistent)

/--
当前已实现函数图消去后的关系化支持理论一致时，推出同一 Rosser 终局。

该接口明确保留内部编码层尚未消去的递归算术与关系投影背景；它是裸 ZFC
保守性桥完成前的真实中间定理。
-/
theorem rosser_incompleteness_of_support_reduct
    (hConsistent :
      Derives.Consistent
        SupportElimination.support_reduct_theory []) :
    ∃ fixedPoint : SetFormula,
      Formula.Sentence fixedPoint ∧
        (¬ HilbertDerives fs_zfc_support_theory fixedPoint) ∧
        (¬ HilbertDerives fs_zfc_support_theory
          (Formula.neg fixedPoint)) :=
  rosser_incompleteness_of_raw
    (SupportElimination.support_raw_consistent
      hConsistent)

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
