import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuotation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy

/-!
# `ProofT` 的直接证明表示

证明码检查器直接作用于内在闭句。quotation 保留当前 AST 的全部构造子，
不经过旧 Hilbert 化。闭句的排序、作用域和 quotation 结果由类型与
总函数保证；对象侧只保存一个 `Delta0ProofGraph` 以及检查器的正负表示合同。
旧的 Hilbert 化 replay、`Option` quotation、`Admissible` 和自由变量编号不再进入
接口。
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

/-! 证明码检查器与对象证明图的直接表示合同。 -/
structure Delta1ProofPresentation
    (Traw Thilbert : SetTheory) where
  graph : Delta0ProofGraph
  checked : Nat → SetSentence → Bool
  checked_sound :
    ∀ {proofCode : Nat} {formula : SetSentence},
      checked proofCode formula = true →
        Derives Thilbert [] formula
  checked_complete :
    ∀ {formula : SetSentence},
      Derives Thilbert [] formula →
        ∃ proofCode, checked proofCode formula = true
  condition_positive :
    ∀ {proofCode : Nat} {formula : SetSentence},
      checked proofCode formula = true →
        Derives Traw []
          (graph.condition
            (numₘ(proofCode))
            (IntrinsicQuotation.quote formula))
  condition_negative :
    ∀ {proofCode : Nat} {formula : SetSentence},
      checked proofCode formula = false →
        Derives Traw []
          (¬ₘ graph.condition
            (numₘ(proofCode))
          (IntrinsicQuotation.quote formula))

namespace Delta1ProofPresentation

variable {Traw Thilbert : SetTheory}

def condition
    (P : Delta1ProofPresentation Traw Thilbert) :
    FormulaTemplate.Binary :=
  P.graph.condition

def code
    (P : Delta1ProofPresentation Traw Thilbert)
    (proofCode : Nat) (formula : SetSentence) : SetSentence :=
  P.graph.condition
    (numₘ(proofCode))
    (IntrinsicQuotation.quote formula)

theorem checked_true_of_derives
    (P : Delta1ProofPresentation Traw Thilbert)
    {formula : SetSentence}
    (hDerives : Derives Thilbert [] formula) :
    ∃ proofCode, P.checked proofCode formula = true :=
  P.checked_complete hDerives

theorem sound
    (P : Delta1ProofPresentation Traw Thilbert)
    {proofCode : Nat} {formula : SetSentence}
    (hChecked : P.checked proofCode formula = true) :
    Derives Thilbert [] formula :=
  P.checked_sound hChecked

theorem complete
    (P : Delta1ProofPresentation Traw Thilbert)
    {formula : SetSentence}
    (hDerives : Derives Thilbert [] formula) :
    ∃ proofCode, P.checked proofCode formula = true :=
  P.checked_complete hDerives

theorem realize
    (P : Delta1ProofPresentation Traw Thilbert)
    {formula : SetSentence}
    (hDerives : Derives Thilbert [] formula) :
    ∃ proofCode, Derives Traw [] (P.code proofCode formula) := by
  rcases P.checked_complete hDerives with ⟨proofCode, hChecked⟩
  exact ⟨proofCode, P.condition_positive hChecked⟩

theorem reject
    (P : Delta1ProofPresentation Traw Thilbert)
    {proofCode : Nat} {formula : SetSentence}
    (hChecked : P.checked proofCode formula = false) :
    Derives Traw [] (¬ₘ P.code proofCode formula) :=
  P.condition_negative hChecked

end Delta1ProofPresentation
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
