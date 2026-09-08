import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.SuccessorCodeDomain
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.StructuralSequenceCodeConstruction
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicSyntaxCarrier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicLogicalTranscript
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicRosserAssembly
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicKernel
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicFixedRows
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.IntrinsicVerifier

/-!
# ZFC 的内在证明图与 Rosser 入口

本模块把已经完成的内在算术支撑、后继链码域和 checked verifier 接成一个可消费
的 `Core`/`Delta0ProofGraph`。这里不构造尚未迁移完成的布尔完备性合同，也不向旧
对象层回退；下游可以直接消费这些对象层签名。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace ZFC

open Nonlogical.BasicSetTheory
open ProofCode
open QuineEncoding

open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-! ## 内在对象算术核 -/

/-- ZFC 新理论上的有限 numeral 消去核心。 -/
theorem intrinsic_zfc_finite_core :
    FiniteCore intrinsic_zfc_theory :=
  intrinsic_zfc_proof_support.certificate_core.toFiniteCore

/-- ZFC 新理论上的后继链码域核心。 -/
def intrinsic_zfc_core :
    Core intrinsic_zfc_theory :=
  successor_core intrinsic_zfc_finite_core
    (intrinsic_zfc_proof_support.row_support.toFiniteSequenceSpaceSupport.toArithmeticSupport).contains_successor

/-- 每个外部标准 numeral 都属于内在后继链码域。 -/
theorem intrinsic_zfc_numeral_mem_code_domain
    (number : Nat) :
    Derives intrinsic_zfc_theory ([] : Context signature [])
      (intrinsic_zfc_core.code_domain.condition (numₘ(number))) := by
  exact successor_code_domain_numeral
    intrinsic_zfc_finite_core
    (intrinsic_zfc_proof_support.row_support.toFiniteSequenceSpaceSupport.toArithmeticSupport).contains_successor
    number

/-! ## 直接结构码序列 -/

/-!
ZFC 图层只暴露结构码序列入口。序列元素是宿主列表中的对象项，序列值直接由
结构码递归构造，不再先套一层自然数序列图。
-/

theorem intrinsic_zfc_object_sequence_code_condition
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free)
    (elements : List (SetOpenTerm free))
    (hSourceNonempty : Γ ⊢ₘ[intrinsic_zfc_theory]
      source ≠ₘ ∅ₘ)
    (hElementMember : ∀ element, element ∈ elements →
      Γ ⊢ₘ[intrinsic_zfc_theory] element ∈ₘ source)
    (hElementOmega : ∀ element, element ∈ elements →
      Γ ⊢ₘ[intrinsic_zfc_theory] element ∈ₘ ωₘ) :
    Γ ⊢ₘ[intrinsic_zfc_theory]
      object_sequence_code_condition source
        (standard_sequence elements)
        (object_sequence_code_value elements) :=
  object_sequence_code_condition_intro_standard
    intrinsic_zfc_structural_sequence_support source elements
    hSourceNonempty hElementMember hElementOmega

theorem intrinsic_zfc_logical_transcript_formula_sequence_code_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (rows : List (LogicalTranscriptRow σ sort free)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      object_sequence_code_condition syntax_formula_code_set_term
        (standard_sequence (rows.map logical_transcript_row_formula_code))
        (object_sequence_code_value
          (rows.map logical_transcript_row_formula_code)) := by
  let elements : List (SetOpenTerm []) :=
    rows.map logical_transcript_row_formula_code
  have hSourceNonempty :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        syntax_formula_code_set_term ≠ₘ ∅ₘ :=
    intrinsic_zfc_row_support.formula_code_nonempty
  have hElementMember : ∀ element, element ∈ elements →
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        element ∈ₘ syntax_formula_code_set_term := by
    intro element hElement
    rcases List.mem_map.mp (by simpa [elements] using hElement) with
      ⟨row, hRow, rfl⟩
    exact intrinsic_zfc_logical_transcript_row_formula_code_member row
  have hElementOmega : ∀ element, element ∈ elements →
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        element ∈ₘ ωₘ := by
    intro element hElement
    exact intrinsic_syntax_carrier_formula_mem_implies_omega
      (T := intrinsic_zfc_theory)
      intrinsic_syntax_carrier_theory_subset_intrinsic_zfc_theory
      element (hElementMember element hElement)
  simpa [elements] using
    intrinsic_zfc_object_sequence_code_condition
      (source := (syntax_formula_code_set_term : SetOpenTerm []))
      elements hSourceNonempty hElementMember hElementOmega

theorem intrinsic_zfc_logical_transcript_certificate_sequence_code_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol} {free : SortContext σ}
    (rows : List (LogicalTranscriptRow σ sort free)) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      object_sequence_code_condition ωₘ
        (standard_sequence (rows.map logical_transcript_row_certificate_code))
        (object_sequence_code_value
          (rows.map logical_transcript_row_certificate_code)) := by
  let elements : List (SetOpenTerm []) :=
    rows.map logical_transcript_row_certificate_code
  have hZero :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        (numₘ(0) : SetOpenTerm []) ∈ₘ ωₘ :=
    intrinsic_zfc_structural_sequence_support.finite_numeral_mem_omega 0
  have hSourceNonempty :
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        ωₘ ≠ₘ ∅ₘ :=
    omega_nonempty_of_numeral_member
      intrinsic_zfc_structural_sequence_support 0 hZero
  have hElementMember : ∀ element, element ∈ elements →
      ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
        element ∈ₘ ωₘ := by
    intro element hElement
    rcases List.mem_map.mp (by simpa [elements] using hElement) with
      ⟨row, hRow, rfl⟩
    exact intrinsic_zfc_logical_transcript_row_certificate_member row
  simpa [elements] using
    intrinsic_zfc_object_sequence_code_condition
      (source := (ωₘ : SetOpenTerm []))
      elements hSourceNonempty hElementMember hElementMember

/-! ## 内在证明图 -/

/-- ZFC checked verifier 的直接 `Delta0` 证明图。 -/
def intrinsic_zfc_graph : Delta0ProofGraph :=
  IntrinsicVerifier.delta0_checked_verifier.proof_graph

theorem intrinsic_zfc_graph_condition_delta0
    {bound free : SetContext}
    (proofCode conclusion : SetTerm bound free) :
    Formula.IsDelta0 set_levy_bound
      (intrinsic_zfc_graph.condition proofCode conclusion) :=
  intrinsic_zfc_graph.delta0 proofCode conclusion

theorem intrinsic_zfc_graph_condition_sigma1
    {bound free : SetContext}
    (proofCode conclusion : SetTerm bound free) :
    Formula.IsSigma1 set_levy_bound
      (intrinsic_zfc_graph.condition proofCode conclusion) :=
  intrinsic_zfc_graph.condition_sigma1 proofCode conclusion

theorem intrinsic_zfc_graph_condition_pi1
    {bound free : SetContext}
    (proofCode conclusion : SetTerm bound free) :
    Formula.IsPi1 set_levy_bound
      (intrinsic_zfc_graph.condition proofCode conclusion) :=
  intrinsic_zfc_graph.condition_pi1 proofCode conclusion

/-! ## 固定表实例 -/

/-- ZFC 固定公理表直接满足内在 checked 序列条件。 -/
theorem intrinsic_zfc_fixed_sequence_condition :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      IntrinsicVerifier.checked_verifier.sequence_condition
        fixed_formula_sequence fixed_certificate_sequence :=
  IntrinsicFixedRows.fixed_sequence_condition

/-! ## 逻辑 transcript 公共入口 -/

/-- ZFC 证明图直接消费已迁移的异构逻辑 transcript。 -/
theorem intrinsic_zfc_graph_logical_transcript_condition
    {σ : Signature} [QuotationNumbering σ]
    {sort : σ.SortSymbol}
    {free : SortContext σ}
    (rows : List (LogicalTranscriptRow σ sort free))
    (hNonempty : rows ≠ []) :
    ([] : Context signature []) ⊢ₘ[intrinsic_zfc_theory]
      IntrinsicVerifier.checked_verifier.sequence_condition
        (standard_sequence (rows.map logical_transcript_row_formula_code))
        (standard_sequence (rows.map logical_transcript_row_certificate_code)) :=
  intrinsic_zfc_logical_transcript_condition rows hNonempty

/-- 对象句子的普通内在可证性谓词。 -/
def intrinsic_zfc_provability (formula : SetSentence) : SetSentence :=
  intrinsic_zfc_graph.provability (QuineEncoding.quote formula)

theorem intrinsic_zfc_provability_sigma1
    (formula : SetSentence) :
    Formula.IsSigma1 set_levy_bound
      (intrinsic_zfc_provability formula) := by
  simpa [intrinsic_zfc_provability] using
    intrinsic_zfc_graph.provability_sigma1
      (QuineEncoding.quote formula)

theorem intrinsic_zfc_neg_provability_pi1
    (formula : SetSentence) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ intrinsic_zfc_provability formula) := by
  simpa [intrinsic_zfc_provability] using
    intrinsic_zfc_graph.neg_provability_pi1
      (QuineEncoding.quote formula)

/-! ## 内在 Rosser 谓词 -/

/-- ZFC 内在证明图的完整 Rosser 有限比较装配。 -/
theorem intrinsic_zfc_rosser_assembly :
    RosserAssembly intrinsic_zfc_theory
      intrinsic_zfc_graph intrinsic_zfc_core :=
  rosser_assembly_of_core
    intrinsic_zfc_core intrinsic_zfc_graph
    intrinsic_zfc_numeral_mem_code_domain

/-- 以内在后继链码域为定义域的 Rosser 谓词。 -/
def intrinsic_zfc_rosser_predicate
    (code : QuineEncoding.Code) : SetSentence :=
  intrinsic_zfc_graph.rosser_provability
    intrinsic_zfc_core.code_domain code

theorem intrinsic_zfc_rosser_predicate_sigma1
    (code : QuineEncoding.Code) :
    Formula.IsSigma1 set_levy_bound
      (intrinsic_zfc_rosser_predicate code) := by
  simpa [intrinsic_zfc_rosser_predicate] using
    intrinsic_zfc_graph.rosser_provability_sigma1
      intrinsic_zfc_core.code_domain code

theorem intrinsic_zfc_neg_rosser_predicate_pi1
    (code : QuineEncoding.Code) :
    Formula.IsPi1 set_levy_bound
      (¬ₘ intrinsic_zfc_rosser_predicate code) := by
  simpa [intrinsic_zfc_rosser_predicate] using
    intrinsic_zfc_graph.neg_rosser_provability_pi1
      intrinsic_zfc_core.code_domain code

end ZFC
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
