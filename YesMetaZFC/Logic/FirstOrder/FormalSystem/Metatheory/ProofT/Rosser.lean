import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CheckedSyntax
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Diagonal

/-!
# `ProofT` 的抽象 Rosser 定理

本模块把 Rosser 终局拆成两个可实例化合同：

* `RosserAssembly` 负责对象层证明码比较的闭项代换与有限装配；
* `RosserPresentation` 组合 checked proof presentation、对象谓词支撑、
  raw 到 Hilbert 的编译桥以及对角编码承载。

通用定理在这些合同之上直接完成逐码拒绝、checked soundness、一致性矛盾和
对角化，不引用任何具体集合论、公理模式或 ZFC 专用定义。
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

/-! ## Rosser 谓词的通用句法 -/

/-- 由二元证明码条件构造 Rosser 可证性谓词。 -/
def rosser_predicate
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId base : FreeVarId) :
    SetFormula :=
  provability_body
    verifier codeId proofCodeId smallerCodeId base

/-- Rosser 对角句所使用的否定句体。 -/
def rosser_sentence_body
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId base : FreeVarId) :
    SetFormula :=
  Formula.neg <|
    rosser_predicate
      verifier codeId proofCodeId smallerCodeId base

/-- 把 Rosser 谓词实例化到给定公式码。 -/
def rosser_predicate_at
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId base : FreeVarId)
    (formulaCode : SetTerm) :
    SetFormula :=
  Formula.substituteFree SetSort.set codeId formulaCode <|
    rosser_predicate
      verifier codeId proofCodeId smallerCodeId base

/-- 对角固定点右侧使用的 Hilbert 化 Rosser 谓词。 -/
def rosser_predicate_instance
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId base : FreeVarId)
    (formulaCode : SetTerm) :
    SetFormula :=
  Formula.substituteFree SetSort.set codeId formulaCode <|
    Formula.hilbertize SetSort.set <|
      rosser_predicate
        verifier codeId proofCodeId smallerCodeId base

theorem rosser_predicate_admissible
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId base : FreeVarId) :
    Formula.Admissible
      (rosser_predicate
        verifier codeId proofCodeId smallerCodeId base) := by
  exact provability_body_admissible
    verifier codeId proofCodeId smallerCodeId base

theorem rosser_sentence_body_admissible
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId base : FreeVarId) :
    Formula.Admissible
      (rosser_sentence_body
        verifier codeId proofCodeId smallerCodeId base) := by
  exact Formula.Admissible.neg <|
    rosser_predicate_admissible
      verifier codeId proofCodeId smallerCodeId base

theorem rosser_predicate_instance_eq_hilbertize
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId base : FreeVarId)
    (formulaCode : SetTerm) :
    rosser_predicate_instance
        verifier codeId proofCodeId smallerCodeId base formulaCode =
      Formula.hilbertize SetSort.set
        (rosser_predicate_at
          verifier codeId proofCodeId smallerCodeId base formulaCode) := by
  simpa [rosser_predicate_instance,
    rosser_predicate_at] using
    (Formula.hilbertize_substituteFree
      (anchorSort := SetSort.set)
      (target := SetSort.set)
      (id := codeId)
      (replacement := formulaCode)
      (formula :=
        rosser_predicate
          verifier codeId proofCodeId smallerCodeId base)).symm

/--
Rosser 谓词自由变量审计所需的 verifier 支撑。

对象 verifier 的公式判定只依赖公式码，证书判定只依赖公式码与证书码。
-/
structure RosserVerifierSupport
    (verifier : ObjectCertificateVerifier)
    extends VerifierSupport verifier where
  formula_freeSupport_subset :
    ∀ formula freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (verifier.formula_condition formula) →
        freeVariable ∈ Term.freeSupport formula

/--
Rosser 谓词除公开代码变量外不含其他自由变量。

内部证明码、较小证明码以及证明条件的全部见证均由对象公式自身闭合。
-/
theorem rosser_predicate_only_code_variable
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId base : FreeVarId)
    (S : RosserVerifierSupport verifier) :
    fs_only_code_variable_formula codeId
      (rosser_predicate
        verifier codeId proofCodeId smallerCodeId base) := by
  intro freeVariable hMember
  have hCloseSubset
      (freeVariable : FreeVariable signature)
      (id : FreeVarId)
      (formula : SetFormula)
      (hMember :
        freeVariable ∈
          Formula.freeSupport
            (Formula.closeFreeAt SetSort.set id 0 formula)) :
      freeVariable ∈ Formula.freeSupport formula := by
    by_cases hFresh :
        freeVariable ∈ Formula.freeSupport formula
    · exact hFresh
    · exact False.elim <|
        (Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          freeVariable SetSort.set id 0 formula hFresh) hMember
  have hCloseSupport
      (freeVariable : FreeVariable signature)
      (id : FreeVarId)
      (formula : SetFormula)
      (hMember :
        freeVariable ∈
          Formula.freeSupport
            (Formula.closeFreeAt SetSort.set id 0 formula)) :
      freeVariable ≠ (SetSort.set, id) ∧
        freeVariable ∈ Formula.freeSupport formula := by
    constructor
    · intro hEqual
      subst hEqual
      exact Formula.not_mem_freeSupport_closeFreeAt
        SetSort.set id 0 formula hMember
    · exact hCloseSubset freeVariable id formula hMember
  have hVariableSupport
      (freeVariable : FreeVariable signature)
      (id : FreeVarId)
      (hMember :
        freeVariable ∈ Term.freeSupport (x#id)) :
      freeVariable = (SetSort.set, id) := by
    simpa [Term.freeSupport] using hMember
  have hPositiveSupport :=
    proof_condition_support
      verifier (x#proofCodeId) (x#codeId) base
      S.formula_freeSupport_subset
      S.freeSupport_subset
  have hNegativeSupport :=
    proof_condition_support
      verifier (x#smallerCodeId)
      (neg_codeₘ(x#codeId)) base
      S.formula_freeSupport_subset
      S.freeSupport_subset
  simp only [rosser_predicate,
    provability_body,
    comparison_condition] at hMember
  rcases hCloseSupport freeVariable proofCodeId _ hMember with
    ⟨hProofClosed, hBody⟩
  simp only [Formula.freeSupport, List.mem_append] at hBody
  rcases hBody with hPositive | hNegative
  · rcases hPositiveSupport freeVariable hPositive with
      hProof | hCode
    · exact False.elim <|
        hProofClosed
          (hVariableSupport freeVariable proofCodeId hProof)
    · exact hVariableSupport freeVariable codeId hCode
  · simp only [no_smaller_condition,
      Formula.freeSupport] at hNegative
    rcases hCloseSupport freeVariable smallerCodeId _ hNegative with
      ⟨hSmallerClosed, hNegativeBody⟩
    simp only [Formula.freeSupport, List.mem_append] at hNegativeBody
    rcases hNegativeBody with hBound | hNegativeCode
    · have hBound' :
          freeVariable = (SetSort.set, smallerCodeId) ∨
            freeVariable = (SetSort.set, proofCodeId) := by
        simpa [Term.freeSupport, Term.freeSupportList] using hBound
      rcases hBound' with hSmaller | hProof
      · exact False.elim <| hSmallerClosed hSmaller
      · exact False.elim <| hProofClosed hProof
    · rcases hNegativeSupport freeVariable hNegativeCode with
        hSmaller | hCode
      · exact False.elim <|
          hSmallerClosed
            (hVariableSupport freeVariable smallerCodeId hSmaller)
      · simpa [negation_formula_code_term,
          Term.freeSupport, Term.freeSupportList] using hCode

theorem rosser_sentence_body_only_code_variable
    (verifier : ObjectCertificateVerifier)
    (codeId proofCodeId smallerCodeId base : FreeVarId)
    (S : RosserVerifierSupport verifier) :
    fs_only_code_variable_formula codeId
      (rosser_sentence_body
        verifier codeId proofCodeId smallerCodeId base) := by
  intro freeVariable hMember
  exact
    rosser_predicate_only_code_variable
      verifier codeId proofCodeId smallerCodeId base S
      freeVariable
      (by
        simpa [rosser_sentence_body,
          Formula.freeSupport] using hMember)

/-! ## 对象层有限比较装配 -/

/--
对象证明码谓词的有限 Rosser 比较合同。

该结构不保存最终正负内部化结论，而只保存由标准证明码及逐点拒绝构造比较式的
两个有限算法，以及把公开代码变量闭项代换为比较式的句法等式。
-/
structure RosserAssembly
    (T : SetTheory)
    (verifier : ObjectCertificateVerifier)
    (base : FreeVarId) where
  code_id : FreeVarId
  proof_code_id : FreeVarId
  smaller_code_id : FreeVarId
  predicate_at_eq :
    ∀ (formulaCode : SetTerm),
      GodelQuotation.Numbered.CodeBoundary formulaCode →
      rosser_predicate_at
          verifier code_id proof_code_id smaller_code_id base
          formulaCode =
        comparison_condition
          verifier formulaCode (neg_codeₘ(formulaCode))
          proof_code_id smaller_code_id base
  positive :
    ∀ (proofCode : Nat) (left right : SetTerm),
      GodelQuotation.Numbered.CodeBoundary left →
      GodelQuotation.Numbered.CodeBoundary right →
      Derives T [] (
        proof_condition
          verifier (numₘ(proofCode)) left base) →
      (∀ code, code < proofCode →
        Derives T [] (
          ¬ₘ proof_condition
            verifier (numₘ(code)) right base)) →
      Derives T [] (
        comparison_condition
          verifier left right
          proof_code_id smaller_code_id base)
  negative :
    ∀ (proofCode : Nat) (left right : SetTerm),
      GodelQuotation.Numbered.CodeBoundary left →
      GodelQuotation.Numbered.CodeBoundary right →
      Derives T [] (
        proof_condition
          verifier (numₘ(proofCode)) right base) →
      (∀ code, code ≤ proofCode →
        Derives T [] (
          ¬ₘ proof_condition
            verifier (numₘ(code)) left base)) →
      Derives T [] (
        ¬ₘ comparison_condition
          verifier left right
          proof_code_id smaller_code_id base)

/-! ## 完整 ProofT Rosser presentation -/

/--
足以推出 Rosser 不完备定理的完整理论表示。

`proof` 给出标准自然数上的 checked proof graph；`assembly` 给出对象层有限比较；
其余字段只负责谓词支撑、raw 推导编译与通用对角引理的最弱理论条件。
-/
structure RosserPresentation
    (Traw Thilbert : SetTheory) where
  proof : Delta1ProofPresentation Traw Thilbert
  support : RosserVerifierSupport proof.verifier
  assembly : RosserAssembly Traw proof.verifier proof.base
  raw_hilbert :
    ∀ {formula : SetFormula},
      Derives Traw [] formula →
        HilbertDerives Thilbert
          (Formula.hilbertize SetSort.set formula)
  code_naming :
    GodelQuotation.fs_extends_code_naming Thilbert
  theory_sentence :
    ∀ formula, Thilbert formula → Formula.Sentence formula

namespace RosserPresentation

def predicate
    {Traw Thilbert : SetTheory}
    (R : RosserPresentation Traw Thilbert) :
    SetFormula :=
  rosser_predicate
    R.proof.verifier
    R.assembly.code_id
    R.assembly.proof_code_id
    R.assembly.smaller_code_id
    R.proof.base

def sentence_body
    {Traw Thilbert : SetTheory}
    (R : RosserPresentation Traw Thilbert) :
    SetFormula :=
  rosser_sentence_body
    R.proof.verifier
    R.assembly.code_id
    R.assembly.proof_code_id
    R.assembly.smaller_code_id
    R.proof.base

def predicate_at
    {Traw Thilbert : SetTheory}
    (R : RosserPresentation Traw Thilbert)
    (formulaCode : SetTerm) :
    SetFormula :=
  rosser_predicate_at
    R.proof.verifier
    R.assembly.code_id
    R.assembly.proof_code_id
    R.assembly.smaller_code_id
    R.proof.base
    formulaCode

def predicate_instance
    {Traw Thilbert : SetTheory}
    (R : RosserPresentation Traw Thilbert)
    (formulaCode : SetTerm) :
    SetFormula :=
  rosser_predicate_instance
    R.proof.verifier
    R.assembly.code_id
    R.assembly.proof_code_id
    R.assembly.smaller_code_id
    R.proof.base
    formulaCode

theorem predicate_instance_eq_hilbertize
    {Traw Thilbert : SetTheory}
    (R : RosserPresentation Traw Thilbert)
    (formulaCode : SetTerm) :
    R.predicate_instance formulaCode =
      Formula.hilbertize SetSort.set
        (R.predicate_at formulaCode) := by
  exact rosser_predicate_instance_eq_hilbertize
    R.proof.verifier
    R.assembly.code_id
    R.assembly.proof_code_id
    R.assembly.smaller_code_id
    R.proof.base
    formulaCode

/-- presentation 自身生成 Rosser 对角句，不要求实例额外提供固定点证书。 -/
theorem diagonal
    {Traw Thilbert : SetTheory}
    (R : RosserPresentation Traw Thilbert) :
    ∃ fixedPoint : SetFormula,
      ∃ fixedPointCode : SetTerm,
        Formula.Sentence fixedPoint ∧
        GodelQuotation.Numbered.quote? fixedPoint =
          some fixedPointCode ∧
        HilbertDerives Thilbert
          (Formula.hilbert_iff fixedPoint
            (Formula.neg
              (R.predicate_instance fixedPointCode))) := by
  rcases GodelQuotation.fs_diagonal_lemma
      R.code_naming
      (rosser_sentence_body_admissible
        R.proof.verifier
        R.assembly.code_id
        R.assembly.proof_code_id
        R.assembly.smaller_code_id
        R.proof.base)
      (rosser_sentence_body_only_code_variable
        R.proof.verifier
        R.assembly.code_id
        R.assembly.proof_code_id
        R.assembly.smaller_code_id
        R.proof.base
        R.support)
      R.theory_sentence with
    ⟨fixedPoint, fixedPointCode,
      hSentence, hQuote, hFixedPoint⟩
  refine ⟨fixedPoint, fixedPointCode,
    hSentence, hQuote, ?_⟩
  simpa [GodelQuotation.fs_diagonal_target,
    sentence_body, predicate_instance,
    rosser_sentence_body,
    rosser_predicate_instance,
    Formula.hilbertize,
    Formula.substituteFree] using hFixedPoint

/--
任意 presentation 的 Rosser 对角句在 Hilbert 理论一致时独立。

正向分支由真实证明产生标准证明码，并逐个拒绝更小反证码；负向分支从标准反证码
出发，逐个拒绝不更大的正证明码。两处拒绝都只使用 checked soundness 与一致性。
-/
theorem independent
    {Traw Thilbert : SetTheory}
    (R : RosserPresentation Traw Thilbert)
    {fixedPoint : SetFormula}
    {fixedPointCode : SetTerm}
    (hSentence : Formula.Sentence fixedPoint)
    (hQuote :
      GodelQuotation.Numbered.quote? fixedPoint =
        some fixedPointCode)
    (hFixedPoint :
      HilbertDerives Thilbert
        (Formula.hilbert_iff fixedPoint
          (Formula.neg
            (R.predicate_instance fixedPointCode))))
    (hConsistent :
      Derives.Consistent Thilbert []) :
    (¬ HilbertDerives Thilbert fixedPoint) ∧
      (¬ HilbertDerives Thilbert
        (Formula.neg fixedPoint)) := by
  apply Rosser.independent_of_fixed_point_internalization
    hFixedPoint
  · intro hDerives
    rcases R.proof.realize hQuote hDerives with
      ⟨proofCode, hPositive⟩
    have hNegQuote :
        GodelQuotation.Numbered.quote?
            (Formula.neg fixedPoint) =
          some (neg_codeₘ(fixedPointCode)) :=
      Rosser.quote_negation_code hQuote
    have hComparison :
        Derives Traw [] (
          comparison_condition
            R.proof.verifier
            fixedPointCode
            (neg_codeₘ(fixedPointCode))
            R.assembly.proof_code_id
            R.assembly.smaller_code_id
            R.proof.base) := by
      apply R.assembly.positive
        proofCode fixedPointCode
        (neg_codeₘ(fixedPointCode))
        (GodelQuotation.Numbered.quote?_code_boundary hQuote)
        (GodelQuotation.Numbered.quote?_code_boundary hNegQuote)
        hPositive
      intro code hCode
      apply R.proof.reject
        code (Formula.Admissible.neg hSentence.1) hNegQuote
      intro hChecked
      have hPositiveHilbert :
          HilbertDerives Thilbert
            (Formula.hilbertize SetSort.set fixedPoint) :=
        HilbertDerives.hilbertize SetSort.set
          R.proof.hilbertized_subset hDerives
      have hNegativeHilbert :
          HilbertDerives Thilbert
            (Formula.neg
              (Formula.hilbertize SetSort.set fixedPoint)) := by
        simpa [Formula.hilbertize] using
          R.proof.checked_sound hChecked
      exact hConsistent <|
        (HilbertDerives.neg_elim
          Formula.Admissible.falsum
          hPositiveHilbert hNegativeHilbert).to_derives
    rw [R.predicate_instance_eq_hilbertize]
    apply R.raw_hilbert
    change Derives Traw [] (
      rosser_predicate_at
        R.proof.verifier
        R.assembly.code_id
        R.assembly.proof_code_id
        R.assembly.smaller_code_id
        R.proof.base
        fixedPointCode)
    rw [R.assembly.predicate_at_eq
      fixedPointCode
      (GodelQuotation.Numbered.quote?_code_boundary hQuote)]
    exact hComparison
  · intro hDerives
    have hNegQuote :
        GodelQuotation.Numbered.quote?
            (Formula.neg fixedPoint) =
          some (neg_codeₘ(fixedPointCode)) :=
      Rosser.quote_negation_code hQuote
    rcases R.proof.realize hNegQuote hDerives with
      ⟨proofCode, hNegativeCode⟩
    have hComparisonNeg :
        Derives Traw [] (
          ¬ₘ comparison_condition
            R.proof.verifier
            fixedPointCode
            (neg_codeₘ(fixedPointCode))
            R.assembly.proof_code_id
            R.assembly.smaller_code_id
            R.proof.base) := by
      apply R.assembly.negative
        proofCode fixedPointCode
        (neg_codeₘ(fixedPointCode))
        (GodelQuotation.Numbered.quote?_code_boundary hQuote)
        (GodelQuotation.Numbered.quote?_code_boundary hNegQuote)
        hNegativeCode
      intro code _
      apply R.proof.reject
        code hSentence.1 hQuote
      intro hChecked
      have hPositiveHilbert :=
        R.proof.checked_sound hChecked
      have hNegativeHilbert :
          HilbertDerives Thilbert
            (Formula.neg
              (Formula.hilbertize SetSort.set fixedPoint)) := by
        simpa [Formula.hilbertize] using
          HilbertDerives.hilbertize SetSort.set
            R.proof.hilbertized_subset hDerives
      exact hConsistent <|
        (HilbertDerives.neg_elim
          Formula.Admissible.falsum
          hPositiveHilbert hNegativeHilbert).to_derives
    rw [R.predicate_instance_eq_hilbertize]
    change HilbertDerives Thilbert (
      ¬ₘ Formula.hilbertize SetSort.set
        (rosser_predicate_at
          R.proof.verifier
          R.assembly.code_id
          R.assembly.proof_code_id
          R.assembly.smaller_code_id
          R.proof.base
          fixedPointCode))
    rw [R.assembly.predicate_at_eq
      fixedPointCode
      (GodelQuotation.Numbered.quote?_code_boundary hQuote)]
    simpa [Formula.hilbertize] using
      R.raw_hilbert hComparisonNeg
  · exact hConsistent

end RosserPresentation

/--
抽象 Rosser 不完备定理。

任何实现 `RosserPresentation` 的理论，只要 Hilbert 支持理论一致，就存在一个闭句，
理论既不证明它，也不证明其否定。
-/
theorem rosser_incompleteness
    {Traw Thilbert : SetTheory}
    (R : RosserPresentation Traw Thilbert)
    (hConsistent :
      Derives.Consistent Thilbert []) :
    ∃ fixedPoint : SetFormula,
      Formula.Sentence fixedPoint ∧
        (¬ HilbertDerives Thilbert fixedPoint) ∧
        (¬ HilbertDerives Thilbert
          (Formula.neg fixedPoint)) := by
  rcases R.diagonal with
    ⟨fixedPoint, fixedPointCode,
      hSentence, hQuote, hFixedPoint⟩
  exact
    ⟨fixedPoint, hSentence,
      R.independent
        hSentence hQuote hFixedPoint hConsistent⟩

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
