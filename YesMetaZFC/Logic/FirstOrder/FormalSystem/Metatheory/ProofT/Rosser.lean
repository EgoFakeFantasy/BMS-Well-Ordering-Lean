import YesMetaZFC.Logic.FirstOrder.FormalSystem.QuineEncoding.FormalSystem
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Delta1ProofPresentation
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-!
# `ProofT` 的直接 Rosser 终局

本模块只处理固定点之后的句法终局。证明图、有限码域和 checked 检查器均使用内在
类型；对角固定点的构造不再反向污染 Rosser 终局接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open QuineEncoding

set_option autoImplicit false

/-! 闭代码上的 Rosser 谓词。 -/
def rosser_predicate
    {T : SetTheory}
    (G : Delta0ProofGraph)
    (C : Core T)
    (code : QuineEncoding.Code) :
    SetSentence :=
  G.comparison C.code_domain code (IntrinsicQuotation.negation code)

/-! 证明图与有限比较式之间的对象层装配合同。 -/
structure RosserAssembly
    (T : SetTheory)
    (G : Delta0ProofGraph)
    (C : Core T) where
  positive :
    ∀ (proofCode : Nat)
      (left right : QuineEncoding.Code),
      Derives T [] (G.condition (numₘ(proofCode)) left) →
      (∀ code, code < proofCode →
        Derives T [] (¬ₘ G.condition (numₘ(code)) right)) →
      Derives T [] (G.comparison C.code_domain left right)
  negative :
    ∀ (proofCode : Nat)
      (left right : QuineEncoding.Code),
      Derives T [] (G.condition (numₘ(proofCode)) right) →
      (∀ code, code ≤ proofCode →
        Derives T [] (¬ₘ G.condition (numₘ(code)) left)) →
      Derives T [] (¬ₘ G.comparison C.code_domain left right)

/-! 原始理论与目标理论之间只保留理论包含，不再引入 Hilbert 化桥接。 -/
structure RosserPresentation
    (Traw Thilbert : SetTheory) where
  proof : Delta1ProofPresentation Traw Thilbert
  core : Core Traw
  assembly : RosserAssembly Traw proof.graph core
  raw_subset : Theory.Extends Thilbert Traw

namespace RosserPresentation

variable {Traw Thilbert : SetTheory}

def graph
    (R : RosserPresentation Traw Thilbert) :
    Delta0ProofGraph :=
  R.proof.graph

def predicate
    (R : RosserPresentation Traw Thilbert)
    (code : QuineEncoding.Code) : SetSentence :=
  rosser_predicate R.graph R.core code

def predicate_of
    (R : RosserPresentation Traw Thilbert)
    (formula : SetSentence) : SetSentence :=
  R.predicate (IntrinsicQuotation.quote formula)

private theorem positive_internalization
    (R : RosserPresentation Traw Thilbert)
    (hConsistent :
      Derives.Consistent Thilbert
        ([] : Context signature []))
    {formula : SetSentence}
    (hFormula : Derives Thilbert [] formula) :
    Derives Thilbert [] (R.predicate_of formula) := by
  rcases R.proof.realize hFormula with ⟨proofCode, hPositive⟩
  have hPositive' :
      Derives Traw []
        (R.graph.condition
          (numₘ(proofCode))
          (IntrinsicQuotation.quote formula)) := by
    simpa [Delta1ProofPresentation.code] using! hPositive
  have hNoSmaller :
      ∀ code, code < proofCode →
        Derives Traw []
          (¬ₘ R.graph.condition
            (numₘ(code))
            (IntrinsicQuotation.negation (IntrinsicQuotation.quote formula))) := by
    intro code hCode
    cases hChecked : R.proof.checked code (Formula.neg formula) with
    | false =>
      simpa [Delta1ProofPresentation.code,
          IntrinsicQuotation.quote_negation] using!
          R.proof.reject hChecked
    | true =>
        exact False.elim <| hConsistent
          (Derives.neg_elim hFormula
            (R.proof.checked_sound hChecked))
  have hComparison := R.assembly.positive proofCode
    (IntrinsicQuotation.quote formula)
    (IntrinsicQuotation.negation (IntrinsicQuotation.quote formula))
    hPositive' hNoSmaller
  exact hComparison.theory_weaken R.raw_subset

private theorem negative_internalization
    (R : RosserPresentation Traw Thilbert)
    (hConsistent :
      Derives.Consistent Thilbert
        ([] : Context signature []))
    {formula : SetSentence}
    (hFormula : Derives Thilbert [] (Formula.neg formula)) :
    Derives Thilbert []
      (¬ₘ R.predicate_of formula) := by
  rcases R.proof.realize hFormula with ⟨proofCode, hNegative⟩
  have hNegative' :
      Derives Traw []
        (R.graph.condition
          (numₘ(proofCode))
          (IntrinsicQuotation.negation (IntrinsicQuotation.quote formula))) := by
      simpa [Delta1ProofPresentation.code,
      IntrinsicQuotation.quote_negation] using! hNegative
  have hNoSmaller :
      ∀ code, code ≤ proofCode →
        Derives Traw []
          (¬ₘ R.graph.condition
            (numₘ(code))
            (IntrinsicQuotation.quote formula)) := by
    intro code hCode
    cases hChecked : R.proof.checked code formula with
    | false =>
        simpa [Delta1ProofPresentation.code] using!
          R.proof.reject hChecked
    | true =>
        exact False.elim <| hConsistent
          (Derives.neg_elim
            (R.proof.checked_sound hChecked)
            hFormula)
  have hComparison := R.assembly.negative proofCode
    (IntrinsicQuotation.quote formula)
    (IntrinsicQuotation.negation (IntrinsicQuotation.quote formula))
    hNegative' hNoSmaller
  simpa [predicate_of, predicate, rosser_predicate] using!
    hComparison.theory_weaken R.raw_subset

/-! 固定点合同是本层唯一的对角输入。 -/
theorem independent_of_fixed_point
    (R : RosserPresentation Traw Thilbert)
    {fixedPoint : SetSentence}
    (hFixedPoint :
      Derives Thilbert []
        (fixedPoint ↔ₘ ¬ₘ R.predicate_of fixedPoint))
    (hConsistent :
      Derives.Consistent Thilbert
        ([] : Context signature [])) :
    (¬ Derives Thilbert [] fixedPoint) ∧
      (¬ Derives Thilbert [] (Formula.neg fixedPoint)) := by
  constructor
  · intro hDerives
    have hPredicate := positive_internalization R hConsistent hDerives
    have hNegPredicate :=
      Derives.iff_elim_left hFixedPoint hDerives
    exact hConsistent (Derives.neg_elim hPredicate hNegPredicate)
  · intro hDerives
    have hNegPredicate :=
      negative_internalization R hConsistent hDerives
    have hFixedPointDerives :=
      Derives.iff_elim_right hFixedPoint hNegPredicate
    exact hConsistent (Derives.neg_elim hFixedPointDerives hDerives)

end RosserPresentation

theorem rosser_incompleteness
    {Traw Thilbert : SetTheory}
    (R : RosserPresentation Traw Thilbert)
    {fixedPoint : SetSentence}
    (hFixedPoint :
      Derives Thilbert []
        (fixedPoint ↔ₘ ¬ₘ R.predicate_of fixedPoint))
    (hConsistent :
      Derives.Consistent Thilbert
        ([] : Context signature [])) :
    (¬ Derives Thilbert [] fixedPoint) ∧
      (¬ Derives Thilbert [] (Formula.neg fixedPoint)) :=
  R.independent_of_fixed_point hFixedPoint hConsistent

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
