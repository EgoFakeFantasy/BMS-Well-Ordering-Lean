import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectCertificateRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSupport

/-!
# ZFC schema 打开见证体的支撑投影

这里记录对象层 schema verifier 打开五个坐标后的精确自由支撑。内部 trace
编号均由各编码条件自行闭合，因此见证体只依赖公式码项和五个显式坐标。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

def fs_zfc_schema_open_support
    (formula : SetTerm)
    (base : FreeVarId) :
    List (FreeVariable signature) :=
  Term.freeSupport formula ++
    [((SetSort.set, base) : FreeVariable signature),
      ((SetSort.set, base + 1) : FreeVariable signature),
      ((SetSort.set, base + 2) : FreeVariable signature),
      ((SetSort.set, base + 3) : FreeVariable signature),
      ((SetSort.set, base + 4) : FreeVariable signature)]

/--
分离 schema 的打开见证体只依赖公式码项和五个显式对象坐标。
该接口隐藏所有 nat-sequence、分类器、binary shift 与前缀 trace 编号。
-/
theorem fs_zfc_separation_condition_open_body_freeSupport_subset
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (fs_zfc_separation_condition_open_body
              formula raw base) →
        freeVariable ∈
          fs_zfc_schema_open_support formula base := by
  intro freeVariable hMember
  have hCoordinate0
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_self
  have hCoordinate1
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base + 1)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_of_mem _ List.mem_cons_self
  have hCoordinate2
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base + 2)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ List.mem_cons_self
  have hCoordinate3
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base + 3)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ <|
          List.mem_cons_of_mem _ List.mem_cons_self
  have hCoordinate4
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base + 4)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ <|
          List.mem_cons_of_mem _ <|
            List.mem_cons_of_mem _ List.mem_cons_self
  simp only [
    fs_zfc_separation_condition_open_body,
    fs_zfc_schema_condition_open_body,
    Formula.freeSupport, List.mem_append] at hMember
  rcases hMember with hCertificate | hRest
  · rcases hCertificate with hRaw | hCertificate
    · exact False.elim <| by
        simp [finite_numeral_term_freeSupport] at hRaw
    · have hCoordinate :
          freeVariable = (SetSort.set, base) ∨
            freeVariable = (SetSort.set, base + 1) := by
        simpa [fs_zfc_schema_certificate_term,
          fs_zfc_schema_payload_term,
          fs_zfc_schema_body_payload_term,
          Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport] using hCertificate
      exact hCoordinate.elim hCoordinate0 hCoordinate1
  rcases hRest with hBounds | hRest
  · rcases
        fs_zfc_schema_certificate_bounds_freeSupport_subset
          (numₘ(raw)) (numₘ(0))
          (x#base) (x#(base + 1))
          freeVariable hBounds with
      hRaw | hTag | hParameter | hBodyToken
    · exact False.elim <| by
        simp [finite_numeral_term_freeSupport] at hRaw
    · exact False.elim <| by
        simp [finite_numeral_term_freeSupport] at hTag
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, set_variable] using hParameter
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 1) := by
        simpa [Term.freeSupport, set_variable] using hBodyToken
      exact hCoordinate1 hCoordinate
  simp only [
    fs_zfc_separation_condition_open_rest,
    Formula.freeSupport, List.mem_append] at hRest
  rcases hRest with hParameter | hRest
  · have hCoordinate :
        freeVariable = (SetSort.set, base) := by
      simpa [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport] using hParameter
    exact hCoordinate0 hCoordinate
  rcases hRest with hSequence | hRest
  · rcases
      nat_sequence_freeSupport_subset
        (x#(base + 2)) (x#(base + 1))
        (base + 5) (base + 6)
        freeVariable hSequence with
      hBodyCode | hTokenCode
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 2) := by
        simpa [Term.freeSupport, set_variable] using hBodyCode
      exact hCoordinate2 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 1) := by
        simpa [Term.freeSupport, set_variable] using hTokenCode
      exact hCoordinate1 hCoordinate
  rcases hRest with hClassifier | hRest
  · rcases
      canonical_project_formula_code_freeSupport_subset
        (Sₘ(x#base)) (x#(base + 2))
        (base + 7) (base + 8)
        (base + 9) (base + 10)
        (base + 11) (base + 12)
        (base + 13) (base + 14)
        (base + 15) (base + 16)
        freeVariable hClassifier with
      hEntry | hCode
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, Term.freeSupportList,
          set_variable] using hEntry
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 2) := by
        simpa [Term.freeSupport, set_variable] using hCode
      exact hCoordinate2 hCoordinate
  rcases hRest with hShiftFirst | hRest
  · rcases
      canonical_project_shift_code_freeSupport_subset
        (x#base) (x#(base + 2)) (x#(base + 3))
        (base + 17) (base + 18) (base + 19)
        freeVariable hShiftFirst with
      hCutoff | hSource | hTarget
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, set_variable] using hCutoff
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 2) := by
        simpa [Term.freeSupport, set_variable] using hSource
      exact hCoordinate2 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 3) := by
        simpa [Term.freeSupport, set_variable] using hTarget
      exact hCoordinate3 hCoordinate
  rcases hRest with hShiftSecond | hPrefix
  · rcases
      canonical_project_shift_code_freeSupport_subset
        (x#base) (x#(base + 3)) (x#(base + 4))
        (base + 25) (base + 26) (base + 27)
        freeVariable hShiftSecond with
      hCutoff | hSource | hTarget
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, set_variable] using hCutoff
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 3) := by
        simpa [Term.freeSupport, set_variable] using hSource
      exact hCoordinate3 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 4) := by
        simpa [Term.freeSupport, set_variable] using hTarget
      exact hCoordinate4 hCoordinate
  rcases
      canonical_forall_prefix_code_freeSupport_subset
        (x#base)
        (fs_zfc_separation_core_code
          (x#base) (x#(base + 4)))
        formula (base + 33) (base + 34)
        freeVariable hPrefix with
    hBinderCount | hCore | hFormula
  · have hCoordinate :
        freeVariable = (SetSort.set, base) := by
      simpa [Term.freeSupport, set_variable] using hBinderCount
    exact hCoordinate0 hCoordinate
  · rcases
      fs_zfc_separation_core_code_freeSupport_subset
        (x#base) (x#(base + 4))
        freeVariable hCore with
      hParameter | hShiftTwo
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, set_variable] using hParameter
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 4) := by
        simpa [Term.freeSupport, set_variable] using hShiftTwo
      exact hCoordinate4 hCoordinate
  · exact List.mem_append.mpr (Or.inl hFormula)

/--
收集 schema 的打开见证体同样只依赖公式码项和五个显式对象坐标。
与分离情形相比，分类器入口多提升一次，核心码同时读取两次 shift 的结果。
-/
theorem fs_zfc_collection_condition_open_body_freeSupport_subset
    (formula : SetTerm)
    (raw : Nat)
    (base : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (fs_zfc_collection_condition_open_body
              formula raw base) →
        freeVariable ∈
          fs_zfc_schema_open_support formula base := by
  intro freeVariable hMember
  have hCoordinate0
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_self
  have hCoordinate1
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base + 1)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_of_mem _ List.mem_cons_self
  have hCoordinate2
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base + 2)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ List.mem_cons_self
  have hCoordinate3
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base + 3)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ <|
          List.mem_cons_of_mem _ List.mem_cons_self
  have hCoordinate4
      {fv : FreeVariable signature}
      (h : fv = (SetSort.set, base + 4)) :
      fv ∈ fs_zfc_schema_open_support formula base := by
    subst fv
    exact List.mem_append.mpr <| Or.inr <|
      List.mem_cons_of_mem _ <|
        List.mem_cons_of_mem _ <|
          List.mem_cons_of_mem _ <|
            List.mem_cons_of_mem _ List.mem_cons_self
  simp only [
    fs_zfc_collection_condition_open_body,
    fs_zfc_schema_condition_open_body,
    Formula.freeSupport, List.mem_append] at hMember
  rcases hMember with hCertificate | hRest
  · rcases hCertificate with hRaw | hCertificate
    · exact False.elim <| by
        simp [finite_numeral_term_freeSupport] at hRaw
    · have hCoordinate :
          freeVariable = (SetSort.set, base) ∨
            freeVariable = (SetSort.set, base + 1) := by
        simpa [fs_zfc_schema_certificate_term,
          fs_zfc_schema_payload_term,
          fs_zfc_schema_body_payload_term,
          Term.freeSupport, Term.freeSupportList,
          finite_numeral_term_freeSupport] using hCertificate
      exact hCoordinate.elim hCoordinate0 hCoordinate1
  rcases hRest with hBounds | hRest
  · rcases
        fs_zfc_schema_certificate_bounds_freeSupport_subset
          (numₘ(raw)) (numₘ(1))
          (x#base) (x#(base + 1))
          freeVariable hBounds with
      hRaw | hTag | hParameter | hBodyToken
    · exact False.elim <| by
        simp [finite_numeral_term_freeSupport] at hRaw
    · exact False.elim <| by
        simp [finite_numeral_term_freeSupport] at hTag
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, set_variable] using hParameter
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 1) := by
        simpa [Term.freeSupport, set_variable] using hBodyToken
      exact hCoordinate1 hCoordinate
  simp only [
    fs_zfc_collection_condition_open_rest,
    Formula.freeSupport, List.mem_append] at hRest
  rcases hRest with hParameter | hRest
  · have hCoordinate :
        freeVariable = (SetSort.set, base) := by
      simpa [Term.freeSupport, Term.freeSupportList,
        finite_numeral_term_freeSupport] using hParameter
    exact hCoordinate0 hCoordinate
  rcases hRest with hSequence | hRest
  · rcases
      nat_sequence_freeSupport_subset
        (x#(base + 2)) (x#(base + 1))
        (base + 5) (base + 6)
        freeVariable hSequence with
      hBodyCode | hTokenCode
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 2) := by
        simpa [Term.freeSupport, set_variable] using hBodyCode
      exact hCoordinate2 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 1) := by
        simpa [Term.freeSupport, set_variable] using hTokenCode
      exact hCoordinate1 hCoordinate
  rcases hRest with hClassifier | hRest
  · rcases
      canonical_project_formula_code_freeSupport_subset
        (Sₘ(Sₘ(x#base))) (x#(base + 2))
        (base + 7) (base + 8)
        (base + 9) (base + 10)
        (base + 11) (base + 12)
        (base + 13) (base + 14)
        (base + 15) (base + 16)
        freeVariable hClassifier with
      hEntry | hCode
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, Term.freeSupportList,
          set_variable] using hEntry
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 2) := by
        simpa [Term.freeSupport, set_variable] using hCode
      exact hCoordinate2 hCoordinate
  rcases hRest with hShiftFirst | hRest
  · rcases
      canonical_project_shift_code_freeSupport_subset
        (x#base) (x#(base + 2)) (x#(base + 3))
        (base + 17) (base + 18) (base + 19)
        freeVariable hShiftFirst with
      hCutoff | hSource | hTarget
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, set_variable] using hCutoff
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 2) := by
        simpa [Term.freeSupport, set_variable] using hSource
      exact hCoordinate2 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 3) := by
        simpa [Term.freeSupport, set_variable] using hTarget
      exact hCoordinate3 hCoordinate
  rcases hRest with hShiftSecond | hPrefix
  · rcases
      canonical_project_shift_code_freeSupport_subset
        (x#base) (x#(base + 3)) (x#(base + 4))
        (base + 25) (base + 26) (base + 27)
        freeVariable hShiftSecond with
      hCutoff | hSource | hTarget
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, set_variable] using hCutoff
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 3) := by
        simpa [Term.freeSupport, set_variable] using hSource
      exact hCoordinate3 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 4) := by
        simpa [Term.freeSupport, set_variable] using hTarget
      exact hCoordinate4 hCoordinate
  rcases
      canonical_forall_prefix_code_freeSupport_subset
        (x#base)
        (fs_zfc_collection_core_code
          (x#base) (x#(base + 3)) (x#(base + 4)))
        formula (base + 33) (base + 34)
        freeVariable hPrefix with
    hBinderCount | hCore | hFormula
  · have hCoordinate :
        freeVariable = (SetSort.set, base) := by
      simpa [Term.freeSupport, set_variable] using hBinderCount
    exact hCoordinate0 hCoordinate
  · rcases
      fs_zfc_collection_core_code_freeSupport_subset
        (x#base) (x#(base + 3)) (x#(base + 4))
        freeVariable hCore with
      hParameter | hShiftOne | hShiftTwo
    · have hCoordinate :
          freeVariable = (SetSort.set, base) := by
        simpa [Term.freeSupport, set_variable] using hParameter
      exact hCoordinate0 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 3) := by
        simpa [Term.freeSupport, set_variable] using hShiftOne
      exact hCoordinate3 hCoordinate
    · have hCoordinate :
          freeVariable = (SetSort.set, base + 4) := by
        simpa [Term.freeSupport, set_variable] using hShiftTwo
      exact hCoordinate4 hCoordinate
  · exact List.mem_append.mpr (Or.inl hFormula)

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
