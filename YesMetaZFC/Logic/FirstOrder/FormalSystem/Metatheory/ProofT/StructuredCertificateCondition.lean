import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.PairingInversionDirect
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SequenceCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuralSequenceCondition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicFormulaTemplate
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSchemaClosure
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxTransport

/-!
# ProofT 的内在证书条件

本模块迁移证书化 Hilbert 证明码的结构条件。所有对象项和对象公式都通过内在
上下文携带作用域；逐行证书、序列条件和总码条件不再暴露 `FreeVarId`、
`Admissible`、`freeSupport` 或停机/新鲜性旁证。

逻辑公理的具体回放由 `LogicalCondition` 参数提供；公共证明行固定逻辑公理、
理论公理、modus ponens 与类型化全称一般化四类规则。一般化直接验证
`abstractFreeTop` 结构变换，不重新引入变量名或 freshness 证书。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace StructuredCertificateCondition

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode

set_option autoImplicit false

/-! ## 内在参数与上下文提升 -/

/-- 对一个对象项提供逻辑公理分支条件。 -/
abbrev LogicalCondition := FormulaTemplate.Quaternary

/-- 对象证书 verifier 的最小内在签名。 -/
structure ObjectVerifier where
  formula_condition : FormulaTemplate.Unary
  condition : FormulaTemplate.Binary

/-- 同时提供逻辑、理论和公式三类证书条件的 checked verifier。 -/
structure CheckedVerifier extends ObjectVerifier where
  logical_condition : LogicalCondition

namespace CheckedVerifier

/-- 忽略逻辑分支后的基础 verifier 视图。 -/
def as_object (verifier : CheckedVerifier) : ObjectVerifier where
  formula_condition := verifier.formula_condition
  condition := verifier.condition

end CheckedVerifier

/-! ## 证书标签与载荷边界 -/

/-- 逻辑公理证书标签。 -/
def logical_certificate_code {bound free : SetContext}
    (certificate : SetTerm bound free) : SetTerm bound free :=
  godel_pairₘ(numₘ(0), certificate)

/-- 理论公理证书标签。 -/
def theory_certificate_code {bound free : SetContext}
    (certificate : SetTerm bound free) : SetTerm bound free :=
  godel_pairₘ(numₘ(1), certificate)

/-- MP 证书标签。 -/
def modus_ponens_certificate_code {bound free : SetContext}
    (implicationIndex premiseIndex : SetTerm bound free) :
    SetTerm bound free :=
  godel_pairₘ(numₘ(2),
    godel_pairₘ(implicationIndex, premiseIndex))

/-- 全称一般化证书标签；载荷依次记录前行索引与抽象后的量词体码。 -/
def forall_generalization_certificate_code {bound free : SetContext}
    (premiseIndex bodyCode : SetTerm bound free) :
    SetTerm bound free :=
  godel_pairₘ(numₘ(3),
    godel_pairₘ(premiseIndex, bodyCode))

/-- 证书载荷相对当前行证书码的有限界。 -/
def certificate_payload_bound {bound free : SetContext}
    (certificates index payload : SetTerm bound free) :
    SetFormula bound free :=
  payload ∈ₘ Sₘ(certificates ·ₘ index)

/-- 总证明码坐标相对总码的有限界。 -/
def proof_code_component_bound {bound free : SetContext}
    (proofCode component : SetTerm bound free) :
    SetFormula bound free :=
  component ∈ₘ Sₘ(proofCode)

/-- 总证明码的两个内在坐标由规范反配对值唯一决定。 -/
theorem components_unique
    {T : SetTheory}
    (C : ProofT.CertificateCore T)
    {free : SetContext}
    {Γ : Context signature free}
    (number : Nat)
    (formulaCode certificateCode : SetTerm [] free)
    (hFormulaBound :
      Γ ⊢ₘ[T]
        proof_code_component_bound
          (numₘ(number)) formulaCode)
    (hCertificateBound :
      Γ ⊢ₘ[T]
        proof_code_component_bound
          (numₘ(number)) certificateCode)
    (hPair :
      Γ ⊢ₘ[T]
        numₘ(number) ≐ₘ
          godel_pairₘ(formulaCode, certificateCode)) :
    Γ ⊢ₘ[T]
      (formulaCode ≐ₘ
          numₘ((godel_unpair_value number).1)) ∧ₘ
        (certificateCode ≐ₘ
          numₘ((godel_unpair_value number).2)) := by
  have hFormulaBound' :
      Γ ⊢ₘ[T] formulaCode ∈ₘ Sₘ(numₘ(number)) := by
    simpa [proof_code_component_bound] using hFormulaBound
  have hCertificateBound' :
      Γ ⊢ₘ[T] certificateCode ∈ₘ Sₘ(numₘ(number)) := by
    simpa [proof_code_component_bound] using hCertificateBound
  have hLeftEquality :
      Γ ⊢ₘ[T]
        formulaCode ≐ₘ numₘ((godel_unpair_value number).1) :=
    IntrinsicPairing.pair_left_unique
      C number formulaCode certificateCode
      hFormulaBound' hCertificateBound' hPair
  have hPairCongruence :
      Γ ⊢ₘ[T]
        godel_pairₘ(formulaCode, certificateCode) ≐ₘ
          godel_pairₘ(
            numₘ((godel_unpair_value number).1),
            certificateCode) :=
    IntrinsicPairing.pair_congr_of_equalities
      formulaCode
      (numₘ((godel_unpair_value number).1))
      certificateCode certificateCode
      hLeftEquality
      (FirstOrder.Derives.eq_refl
        (T := T) (Γ := Γ) certificateCode)
  have hTaggedPair :
      Γ ⊢ₘ[T]
        numₘ(number) ≐ₘ
          godel_pairₘ(
            numₘ((godel_unpair_value number).1),
            certificateCode) :=
    Metatheory.Derives.equality_trans hPair hPairCongruence
  have hRightEquality :
      Γ ⊢ₘ[T]
        certificateCode ≐ₘ
          numₘ((godel_unpair_value number).2) :=
    IntrinsicPairing.pair_right_unique
      C number
      (godel_unpair_value number).1
      certificateCode
      hCertificateBound' hTaggedPair
  exact FirstOrder.Derives.conj_intro hLeftEquality hRightEquality

/-! ## 逐行证书条件 -/

/-- MP 分支的内在条件；两个索引由连续的 free binder 直接承载。 -/
def modus_ponens_line_condition {bound free : SetContext}
    (sequence certificates index : SetTerm bound free) :
    SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm (SetSort.set :: bound) free :=
    index.weakenBound SetSort.set
  let sequenceTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    sequenceOne.weakenBound SetSort.set
  let certificatesTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    certificatesOne.weakenBound SetSort.set
  let indexTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    indexOne.weakenBound SetSort.set
  let implicationIndexOne : SetTerm (SetSort.set :: bound) free :=
    .bvar .here
  let implicationIndex : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar (.there .here)
  let premiseIndex : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar .here
  let innerBody : SetFormula (SetSort.set :: SetSort.set :: bound) free :=
    ((certificatesTwo ·ₘ indexTwo) ≐ₘ
        modus_ponens_certificate_code implicationIndex premiseIndex) ∧ₘ
      modus_ponensₘ(
        sequenceTwo ·ₘ premiseIndex,
        sequenceTwo ·ₘ implicationIndex,
        sequenceTwo ·ₘ indexTwo)
  let innerWitness : SetFormula (SetSort.set :: bound) free :=
    Formula.LevyBound.boundedExists set_levy_bound
      implicationIndexOne innerBody
  Formula.LevyBound.boundedExists set_levy_bound
    index innerWitness

/-- 理论公理分支的内在条件。 -/
def theory_certificate_line_condition
    (verifier : ObjectVerifier)
    {bound free : SetContext}
    (sequence certificates index : SetTerm bound free) :
    SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm (SetSort.set :: bound) free :=
    index.weakenBound SetSort.set
  let certificateCode : SetTerm (SetSort.set :: bound) free :=
    .bvar .here
  let body : SetFormula (SetSort.set :: bound) free :=
    (certificatesOne ·ₘ indexOne ≐ₘ
        theory_certificate_code certificateCode) ∧ₘ
      verifier.condition
        (sequenceOne ·ₘ indexOne) certificateCode
  Formula.LevyBound.boundedExists set_levy_bound
    (Sₘ(certificates ·ₘ index)) body

/--
全称一般化分支。前行必须严格早于当前行；量词体由前行公式执行一次
`abstractFreeTop` 得到，当前行则恰为该体的全称闭包。
-/
def forall_generalization_line_condition {bound free : SetContext}
    (sequence certificates index : SetTerm bound free) :
    SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm (SetSort.set :: bound) free :=
    index.weakenBound SetSort.set
  let sequenceTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    sequenceOne.weakenBound SetSort.set
  let certificatesTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    certificatesOne.weakenBound SetSort.set
  let indexTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    indexOne.weakenBound SetSort.set
  let premiseIndex : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar (.there .here)
  let bodyCode : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    .bvar .here
  let innerBody : SetFormula (SetSort.set :: SetSort.set :: bound) free :=
    ((certificatesTwo ·ₘ indexTwo) ≐ₘ
        forall_generalization_certificate_code premiseIndex bodyCode) ∧ₘ
      ((formula_code_atₘ(numₘ(1), bodyCode) ∧ₘ
        formula_abstract_free_top_condition
          (sequenceTwo ·ₘ premiseIndex) bodyCode) ∧ₘ
        ((sequenceTwo ·ₘ indexTwo) ≐ₘ all_codeₘ(bodyCode)))
  let bodyWitness : SetFormula (SetSort.set :: bound) free :=
    Formula.LevyBound.boundedExists set_levy_bound
      (ωₘ : SetTerm (SetSort.set :: bound) free) innerBody
  Formula.LevyBound.boundedExists set_levy_bound
    index bodyWitness

/-- 逻辑、理论、MP 和全称一般化四个分支的内在析取结构。 -/
def line_condition_with_logical
    (verifier : ObjectVerifier)
    {bound free : SetContext}
    (sequence certificates index : SetTerm bound free)
    (logicalCondition : LogicalCondition) : SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let indexOne : SetTerm (SetSort.set :: bound) free :=
    index.weakenBound SetSort.set
  let certificateCode : SetTerm (SetSort.set :: bound) free :=
    .bvar .here
  let logicalBody : SetFormula (SetSort.set :: bound) free :=
    (certificatesOne ·ₘ indexOne ≐ₘ
        logical_certificate_code certificateCode) ∧ₘ
      logicalCondition
        sequenceOne certificatesOne indexOne certificateCode
  let logicalBranch : SetFormula bound free :=
    Formula.LevyBound.boundedExists set_levy_bound
      (Sₘ(certificates ·ₘ index)) logicalBody
  logicalBranch ∨ₘ
    (theory_certificate_line_condition
      verifier sequence certificates index ∨ₘ
      (modus_ponens_line_condition sequence certificates index ∨ₘ
        forall_generalization_line_condition
          sequence certificates index))

/-- 逐行条件与任意类型化替换交换，避免下游重复展开四个证书分支。 -/
@[simp] theorem line_condition_with_logical_substituteMapped
    (verifier : ObjectVerifier)
    (logicalCondition : LogicalCondition)
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (sequence certificates index : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (line_condition_with_logical verifier sequence certificates index
          logicalCondition) =
      line_condition_with_logical verifier
        (sequence.substituteMapped boundSubstitution freeSubstitution)
        (certificates.substituteMapped boundSubstitution freeSubstitution)
        (index.substituteMapped boundSubstitution freeSubstitution)
        logicalCondition := by
  simp [line_condition_with_logical, theory_certificate_line_condition,
    modus_ponens_line_condition, forall_generalization_line_condition,
    formula_abstract_free_top_condition,
    logical_certificate_code, theory_certificate_code,
    modus_ponens_certificate_code, forall_generalization_certificate_code,
    FormulaTemplate.apply_two_substituteMapped,
    FormulaTemplate.apply_four_substituteMapped,
    universal_formula_code_term, structural_node_code_term,
    structural_raw_node_code_term, structural_list_code_term,
    Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.liftBound, Term.substituteMapped_weakenBound]

/-! ## 证明序列与总证明码条件 -/

/-- 证明序列在每个定义域索引处满足公式条件和证书分支条件。 -/
def sequence_condition
    (verifier : ObjectVerifier)
    {bound free : SetContext}
    (sequence certificates : SetTerm bound free)
    (logicalCondition : LogicalCondition) : SetFormula bound free :=
  let sequenceOne : SetTerm (SetSort.set :: bound) free :=
    sequence.weakenBound SetSort.set
  let certificatesOne : SetTerm (SetSort.set :: bound) free :=
    certificates.weakenBound SetSort.set
  let index : SetTerm (SetSort.set :: bound) free := .bvar .here
  let lineBody : SetFormula (SetSort.set :: bound) free :=
    verifier.formula_condition
        (sequenceOne ·ₘ index) ∧ₘ
      line_condition_with_logical
        verifier sequenceOne certificatesOne index logicalCondition
  let lineCondition : SetFormula bound free :=
    Formula.LevyBound.boundedForall set_levy_bound
      (domₘ(sequence)) lineBody
  ((((sequence ∈ₘ seq₊_spaceₘ(syntax_formula_code_set_term)) ∧ₘ
      (certificates ∈ₘ seq₊_spaceₘ(ωₘ))) ∧ₘ
      (domₘ(sequence) ≐ₘ domₘ(certificates))) ∧ₘ
      (numₘ(0) ∈ₘ domₘ(sequence))) ∧ₘ lineCondition

/--
总证明码的内在条件。

四个外层有界存在量词依次绑定证明序列、证书序列、公式码和证书码；
序列内部轨迹由 `SequenceCondition` 自身闭合，不再把轨迹编号暴露到公共接口。
-/
def code_condition_body
    (verifier : ObjectVerifier)
    {bound free : SetContext}
    (proofCode conclusion sequence certificates formulaCode certificateCode :
      SetTerm bound free)
  (logicalCondition : LogicalCondition) : SetFormula bound free :=
  ((sequence_condition
      verifier sequence certificates logicalCondition ∧ₘ
    object_sequence_code_condition syntax_formula_code_set_term
      sequence formulaCode) ∧ₘ
    object_sequence_code_condition ωₘ certificates certificateCode) ∧ₘ
    ((proof_code_component_bound proofCode formulaCode ∧ₘ
      proof_code_component_bound proofCode certificateCode) ∧ₘ
      ((proofCode ≐ₘ
          godel_pairₘ(formulaCode, certificateCode)) ∧ₘ
        proof_sequence_terminal_condition sequence conclusion))

theorem code_condition_body_substituteMapped
    (verifier : ObjectVerifier)
    (logicalCondition : LogicalCondition)
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (proofCode conclusion sequence certificates formulaCode certificateCode :
      SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (code_condition_body verifier proofCode conclusion sequence certificates
          formulaCode certificateCode logicalCondition) =
      code_condition_body verifier
        (proofCode.substituteMapped boundSubstitution freeSubstitution)
        (conclusion.substituteMapped boundSubstitution freeSubstitution)
        (sequence.substituteMapped boundSubstitution freeSubstitution)
        (certificates.substituteMapped boundSubstitution freeSubstitution)
        (formulaCode.substituteMapped boundSubstitution freeSubstitution)
        (certificateCode.substituteMapped boundSubstitution freeSubstitution)
        logicalCondition := by
  simp [code_condition_body, sequence_condition, line_condition_with_logical,
    theory_certificate_line_condition, modus_ponens_line_condition,
    forall_generalization_line_condition,
    formula_abstract_free_top_condition,
    object_sequence_code_condition, object_sequence_code_trace_condition,
    object_sequence_code_trace_body, object_sequence_code_pointwise_condition,
    object_sequence_code_row_condition, object_sequence_code_step_condition,
    proof_sequence_terminal_condition,
    proof_code_component_bound, logical_certificate_code,
    theory_certificate_code, modus_ponens_certificate_code,
    forall_generalization_certificate_code,
    sequence_domain_code_bound,
    sequence_trace_code_bound,
    syntax_formula_code_set_term, universal_formula_code_term,
    structural_node_code_term, structural_raw_node_code_term,
    structural_list_code_term,
    Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    Formula.LevyBound.boundedExists, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, VariableSubstitution.liftBound, Term.substituteMapped_weakenBound]

/-- 总证明码四层见证的依赖有界闭包计划。 -/
def code_condition_plan
    {bound free : SetContext}
    (proofCode : SetTerm bound free) :
    BoundedWitnessPlan free bound
      (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: bound) :=
  let proofCodeOne : SetTerm (SetSort.set :: bound) free :=
    proofCode.weakenBound SetSort.set
  let proofCodeTwo : SetTerm (SetSort.set :: SetSort.set :: bound) free :=
    proofCodeOne.weakenBound SetSort.set
  let proofCodeThree : SetTerm
      (SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
    proofCodeTwo.weakenBound SetSort.set
  .cons (seq₊_spaceₘ(syntax_formula_code_set_term))
    (.cons
      (seq₊_spaceₘ(ωₘ))
      (.cons
        (Sₘ(proofCodeTwo))
        (.cons
          (Sₘ(proofCodeThree))
          (.nil _))))

/-- 总证明码模板在四层 bound 上下文中的矩阵。 -/
def code_condition_template_body
    (verifier : ObjectVerifier)
    (logicalCondition : LogicalCondition) :
    SetFormula
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
  let proofCode : SetOpenTerm [SetSort.set, SetSort.set] :=
    .fvar .here
  let conclusion : SetOpenTerm [SetSort.set, SetSort.set] :=
    .fvar (.there .here)
  let proofCodeOne : SetTerm [SetSort.set] [SetSort.set, SetSort.set] :=
    proofCode.weakenBound SetSort.set
  let conclusionOne : SetTerm [SetSort.set] [SetSort.set, SetSort.set] :=
    conclusion.weakenBound SetSort.set
  let proofCodeTwo : SetTerm [SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    proofCodeOne.weakenBound SetSort.set
  let conclusionTwo : SetTerm [SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    conclusionOne.weakenBound SetSort.set
  let proofCodeThree : SetTerm
      [SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    proofCodeTwo.weakenBound SetSort.set
  let conclusionThree : SetTerm
      [SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    conclusionTwo.weakenBound SetSort.set
  let proofCodeFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    proofCodeThree.weakenBound SetSort.set
  let conclusionFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    conclusionThree.weakenBound SetSort.set
  let sequence : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    .bvar (.there (.there (.there .here)))
  let certificates : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    .bvar (.there (.there .here))
  let formulaCode : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    .bvar (.there .here)
  let certificateCode : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set]
      [SetSort.set, SetSort.set] :=
    .bvar .here
  code_condition_body verifier proofCodeFour conclusionFour
    sequence certificates formulaCode certificateCode logicalCondition

/-- 总证明码模板的原始四层计划。 -/
def code_condition_template_plan :
    BoundedWitnessPlan
      [SetSort.set, SetSort.set]
      []
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] :=
  code_condition_plan (.fvar .here)

def code_condition
    (verifier : ObjectVerifier)
    (logicalCondition : LogicalCondition) : FormulaTemplate.Binary where
  body := bounded_witness_closure code_condition_template_plan
    (code_condition_template_body verifier logicalCondition)

/-- 总码模板应用后直接恢复四层依赖有界闭包。 -/
@[simp] theorem code_condition_apply
    (verifier : ObjectVerifier)
    (logicalCondition : LogicalCondition)
    {bound free : SetContext}
    (proofCode conclusion : SetTerm bound free) :
    code_condition verifier logicalCondition proofCode conclusion =
      let proofCodeOne : SetTerm (SetSort.set :: bound) free :=
        proofCode.weakenBound SetSort.set
      let conclusionOne : SetTerm (SetSort.set :: bound) free :=
        conclusion.weakenBound SetSort.set
      let proofCodeTwo : SetTerm
          (SetSort.set :: SetSort.set :: bound) free :=
        proofCodeOne.weakenBound SetSort.set
      let conclusionTwo : SetTerm
          (SetSort.set :: SetSort.set :: bound) free :=
        conclusionOne.weakenBound SetSort.set
      let proofCodeThree : SetTerm
          (SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
        proofCodeTwo.weakenBound SetSort.set
      let conclusionThree : SetTerm
          (SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
        conclusionTwo.weakenBound SetSort.set
      let proofCodeFour : SetTerm
          (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
        proofCodeThree.weakenBound SetSort.set
      let conclusionFour : SetTerm
          (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
        conclusionThree.weakenBound SetSort.set
      let sequence : SetTerm
          (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
        .bvar (.there (.there (.there .here)))
      let certificates : SetTerm
          (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
        .bvar (.there (.there .here))
      let formulaCode : SetTerm
          (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
        .bvar (.there .here)
      let certificateCode : SetTerm
          (SetSort.set :: SetSort.set :: SetSort.set :: SetSort.set :: bound) free :=
        .bvar .here
      bounded_witness_closure (code_condition_plan proofCode)
        (code_condition_body verifier proofCodeFour conclusionFour
          sequence certificates formulaCode certificateCode logicalCondition) := by
  let slotSubstitution :
      VariableSubstitution signature
        [SetSort.set, SetSort.set] bound free :=
    VariableSubstitution.cons proofCode
      (VariableSubstitution.cons conclusion VariableSubstitution.empty)
  have hTransport :=
    bounded_witness_closure_substituteMapped
      (plan := code_condition_template_plan)
      (body := code_condition_template_body verifier logicalCondition)
      (boundSubstitution :=
        (VariableSubstitution.empty :
          VariableSubstitution signature [] bound free))
      (freeSubstitution := slotSubstitution)
  have hPlan :
      (BoundedWitnessPlan.transport code_condition_template_plan
        (VariableSubstitution.empty :
          VariableSubstitution signature [] bound free)
        slotSubstitution).plan =
        code_condition_plan proofCode := by
    rfl
  simp only [hPlan] at hTransport
  simp [ code_condition,
    FormulaTemplate.apply_two,
    FormulaTemplate.instantiate, code_condition_template_plan,
    code_condition_template_body, code_condition_plan,
    bounded_witness_closure, Formula.LevyBound.boundedExists,
    Formula.LevyBound.membership, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons,
    VariableSubstitution.liftBound, VariableSubstitution.weakenBound,
    Term.substituteMapped_weakenBound, code_condition_body_substituteMapped]

/-! ## 总码条件的正向构造 -/

/--
由四个开放见证及其矩阵条件直接构造总证明码条件。

见证顺序固定为证明序列、证书序列、公式码和证书码；所有界条件均在
`BoundedWitnessAssignment` 中按依赖顺序检查，调用方只需提供最终矩阵的
八个原子/复合条件，不再暴露 binder 对齐或 freshness 参数。
-/
theorem code_condition_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : ObjectVerifier)
    (logicalCondition : LogicalCondition)
    (proofCode conclusion sequence certificates formulaCode certificateCode :
      SetOpenTerm free)
    (hSequence : Γ ⊢ₘ[T]
      sequence_condition verifier sequence certificates logicalCondition)
    (hProofSequence : Γ ⊢ₘ[T]
      object_sequence_code_condition syntax_formula_code_set_term
        sequence formulaCode)
    (hCertificateSequence : Γ ⊢ₘ[T]
      object_sequence_code_condition ωₘ certificates certificateCode)
    (hFormulaBound : Γ ⊢ₘ[T]
      proof_code_component_bound proofCode formulaCode)
    (hCertificateBound : Γ ⊢ₘ[T]
      proof_code_component_bound proofCode certificateCode)
    (hPair : Γ ⊢ₘ[T]
      proofCode ≐ₘ godel_pairₘ(formulaCode, certificateCode))
    (hTerminal : Γ ⊢ₘ[T]
      proof_sequence_terminal_condition sequence conclusion) :
    Γ ⊢ₘ[T] code_condition verifier logicalCondition proofCode conclusion := by
  let proofCodeOne : SetTerm [SetSort.set] free :=
    proofCode.weakenBound SetSort.set
  let conclusionOne : SetTerm [SetSort.set] free :=
    conclusion.weakenBound SetSort.set
  let proofCodeTwo : SetTerm [SetSort.set, SetSort.set] free :=
    proofCodeOne.weakenBound SetSort.set
  let conclusionTwo : SetTerm [SetSort.set, SetSort.set] free :=
    conclusionOne.weakenBound SetSort.set
  let proofCodeThree : SetTerm
      [SetSort.set, SetSort.set, SetSort.set] free :=
    proofCodeTwo.weakenBound SetSort.set
  let conclusionThree : SetTerm
      [SetSort.set, SetSort.set, SetSort.set] free :=
    conclusionTwo.weakenBound SetSort.set
  let proofCodeFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
    proofCodeThree.weakenBound SetSort.set
  let conclusionFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
    conclusionThree.weakenBound SetSort.set
  have hSequenceBound : Γ ⊢ₘ[T]
      sequence ∈ₘ seq₊_spaceₘ(syntax_formula_code_set_term) := by
    exact FirstOrder.Derives.conj_elim_left
      (FirstOrder.Derives.conj_elim_left
        (FirstOrder.Derives.conj_elim_left
          (FirstOrder.Derives.conj_elim_left hSequence)))
  have hCertificatesBound : Γ ⊢ₘ[T]
      certificates ∈ₘ seq₊_spaceₘ(ωₘ) := by
    exact FirstOrder.Derives.conj_elim_right
      (FirstOrder.Derives.conj_elim_left
        (FirstOrder.Derives.conj_elim_left
          (FirstOrder.Derives.conj_elim_left hSequence)))
  let assignment :
      BoundedWitnessAssignment T Γ
        (code_condition_plan proofCode)
        (VariableSubstitution.empty :
          VariableSubstitution signature [] [] free) := by
    refine ⟨⟨sequence, ?_⟩, ?_⟩
    · simpa [code_condition_plan, BoundedWitnessAssignment] using! hSequenceBound
    refine ⟨⟨certificates, ?_⟩, ?_⟩
    · simpa [code_condition_plan, BoundedWitnessAssignment] using!
        hCertificatesBound
    refine ⟨⟨formulaCode, ?_⟩, ?_⟩
    · change Γ ⊢ₘ[T] formulaCode ∈ₘ
        (Sₘ(proofCodeTwo)).substituteMapped
          (VariableSubstitution.cons certificates
            (VariableSubstitution.cons sequence VariableSubstitution.empty))
          VariableSubstitution.freeId
      rw [show proofCodeTwo =
          proofCode.embedBoundClosed
            [SetSort.set, SetSort.set] by rfl]
      simp only [Term.substituteMapped, Arguments.substituteMapped]
      rw [Term.embedBoundClosed_substituteMapped]
      simpa [proof_code_component_bound] using! hFormulaBound
    refine ⟨⟨certificateCode, ?_⟩, PUnit.unit⟩
    change Γ ⊢ₘ[T] certificateCode ∈ₘ
      (Sₘ(proofCodeThree)).substituteMapped
        (VariableSubstitution.cons formulaCode
          (VariableSubstitution.cons certificates
            (VariableSubstitution.cons sequence VariableSubstitution.empty)))
        VariableSubstitution.freeId
    rw [show proofCodeThree =
        proofCode.embedBoundClosed
          [SetSort.set, SetSort.set, SetSort.set] by rfl]
    simp only [Term.substituteMapped, Arguments.substituteMapped]
    rw [Term.embedBoundClosed_substituteMapped]
    simpa [proof_code_component_bound] using! hCertificateBound
  have hFinal :
      (assignment.finalSubstitution :
        VariableSubstitution signature
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] [] free) =
      (VariableSubstitution.cons certificateCode
        (VariableSubstitution.cons formulaCode
          (VariableSubstitution.cons certificates
            (VariableSubstitution.cons sequence VariableSubstitution.empty))) :
        VariableSubstitution signature
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] [] free) := by
    funext sort entry
    cases entry <;> rfl
  let sequenceFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
    .bvar (.there (.there (.there .here)))
  let certificatesFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
    .bvar (.there (.there .here))
  let formulaCodeFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
    .bvar (.there .here)
  let certificateCodeFour : SetTerm
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set] free :=
    .bvar .here
  have hProofCodeFour :
      proofCodeFour.substituteMapped
        assignment.finalSubstitution VariableSubstitution.freeId = proofCode := by
    rw [hFinal]
    rw [show proofCodeFour =
        proofCode.embedBoundClosed
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] by rfl]
    rw [Term.embedBoundClosed_substituteMapped]
    exact Term.substituteMapped_empty_freeId_eq_self proofCode
  have hConclusionFour :
      conclusionFour.substituteMapped
        assignment.finalSubstitution VariableSubstitution.freeId = conclusion := by
    rw [hFinal]
    rw [show conclusionFour =
        conclusion.embedBoundClosed
          [SetSort.set, SetSort.set, SetSort.set, SetSort.set] by rfl]
    rw [Term.embedBoundClosed_substituteMapped]
    exact Term.substituteMapped_empty_freeId_eq_self conclusion
  have hSequenceFour :
      sequenceFour.substituteMapped
        assignment.finalSubstitution VariableSubstitution.freeId = sequence := by
    rw [hFinal]
    simp [sequenceFour, Term.substituteMapped, VariableSubstitution.cons]
  have hCertificatesFour :
      certificatesFour.substituteMapped
        assignment.finalSubstitution VariableSubstitution.freeId = certificates := by
    rw [hFinal]
    simp [certificatesFour, Term.substituteMapped, VariableSubstitution.cons]
  have hFormulaCodeFour :
      formulaCodeFour.substituteMapped
        assignment.finalSubstitution VariableSubstitution.freeId = formulaCode := by
    rw [hFinal]
    simp [formulaCodeFour, Term.substituteMapped, VariableSubstitution.cons]
  have hCertificateCodeFour :
      certificateCodeFour.substituteMapped
        assignment.finalSubstitution VariableSubstitution.freeId = certificateCode := by
    rw [hFinal]
    simp [certificateCodeFour, Term.substituteMapped, VariableSubstitution.cons]
  have hMatrix : Γ ⊢ₘ[T]
      (code_condition_body verifier proofCodeFour conclusionFour
        sequenceFour certificatesFour formulaCodeFour certificateCodeFour
        logicalCondition).substituteMapped
        assignment.finalSubstitution VariableSubstitution.freeId := by
    rw [code_condition_body_substituteMapped,
      hProofCodeFour, hConclusionFour, hSequenceFour,
      hCertificatesFour, hFormulaCodeFour, hCertificateCodeFour]
    exact
      FirstOrder.Derives.conj_intro
        (FirstOrder.Derives.conj_intro
          (FirstOrder.Derives.conj_intro hSequence hProofSequence)
          hCertificateSequence)
        (FirstOrder.Derives.conj_intro
          (FirstOrder.Derives.conj_intro hFormulaBound hCertificateBound)
          (FirstOrder.Derives.conj_intro hPair hTerminal))
  rw [code_condition_apply]
  simpa [proofCodeOne, conclusionOne, proofCodeTwo, conclusionTwo,
    proofCodeThree, conclusionThree, proofCodeFour, conclusionFour,
    sequenceFour, certificatesFour, formulaCodeFour, certificateCodeFour] using
    bounded_witness_closure_intro_assignment assignment _ hMatrix

/-! ## checked verifier 入口 -/

namespace CheckedVerifier

/-- checked verifier 的逐行条件。 -/
def line_condition
    (verifier : CheckedVerifier)
    {bound free : SetContext}
    (sequence certificates index : SetTerm bound free) :
    SetFormula bound free :=
  line_condition_with_logical
    verifier.as_object sequence certificates index verifier.logical_condition

/-- checked 逐行条件直接继承四分支条件的替换同态。 -/
@[simp] theorem line_condition_substituteMapped
    (verifier : CheckedVerifier)
    {sourceBound sourceFree targetBound targetFree : SetContext}
    (sequence certificates index : SetTerm sourceBound sourceFree)
    (boundSubstitution :
      VariableSubstitution signature sourceBound targetBound targetFree)
    (freeSubstitution :
      VariableSubstitution signature sourceFree targetBound targetFree) :
    Formula.substituteMapped boundSubstitution freeSubstitution
        (verifier.line_condition sequence certificates index) =
      verifier.line_condition
        (sequence.substituteMapped boundSubstitution freeSubstitution)
        (certificates.substituteMapped boundSubstitution freeSubstitution)
        (index.substituteMapped boundSubstitution freeSubstitution) := by
  exact line_condition_with_logical_substituteMapped
    verifier.as_object verifier.logical_condition sequence certificates index
      boundSubstitution freeSubstitution

/-- checked verifier 的证明序列条件。 -/
def sequence_condition
    (verifier : CheckedVerifier)
    {bound free : SetContext}
    (sequence certificates : SetTerm bound free) :
    SetFormula bound free :=
  StructuredCertificateCondition.sequence_condition
    verifier.as_object sequence certificates verifier.logical_condition

/-- checked verifier 的总证明码条件。 -/
def code_condition
    (verifier : CheckedVerifier)
    : FormulaTemplate.Binary :=
  StructuredCertificateCondition.code_condition
    verifier.as_object verifier.logical_condition

/-- 由序列、分量界和终止条件构造 checked verifier 的总证明码条件。 -/
theorem code_condition_intro
    {T : SetTheory}
    {free : SetContext}
    {Γ : Context signature free}
    (verifier : CheckedVerifier)
    (proofCode conclusion sequence certificates formulaCode certificateCode :
      SetOpenTerm free)
    (hSequence : Γ ⊢ₘ[T]
      verifier.sequence_condition sequence certificates)
    (hProofSequence : Γ ⊢ₘ[T]
      object_sequence_code_condition syntax_formula_code_set_term
        sequence formulaCode)
    (hCertificateSequence : Γ ⊢ₘ[T]
      object_sequence_code_condition ωₘ certificates certificateCode)
    (hFormulaBound : Γ ⊢ₘ[T]
      proof_code_component_bound proofCode formulaCode)
    (hCertificateBound : Γ ⊢ₘ[T]
      proof_code_component_bound proofCode certificateCode)
    (hPair : Γ ⊢ₘ[T]
      proofCode ≐ₘ godel_pairₘ(formulaCode, certificateCode))
    (hTerminal : Γ ⊢ₘ[T]
      proof_sequence_terminal_condition sequence conclusion) :
    Γ ⊢ₘ[T] verifier.code_condition proofCode conclusion := by
  exact StructuredCertificateCondition.code_condition_intro
    verifier.as_object verifier.logical_condition
    proofCode conclusion sequence certificates formulaCode certificateCode
    hSequence hProofSequence hCertificateSequence hFormulaBound
    hCertificateBound hPair hTerminal

end CheckedVerifier

end StructuredCertificateCondition
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
