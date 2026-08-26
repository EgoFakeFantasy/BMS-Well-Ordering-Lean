import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCProjectDecodeFailureAdapter
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.CanonicalFormulaTraceLegality.FormulaTrace

/-!
# Project 公式码条件的解码失败适配

本模块只消去完整公式码条件中的两条有限序列与末行见证，再调用逐行失败适配器。
trace 仅作为证明内部的对象公式出现，不进入 Rosser 的公开二元关系。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open _root_.YesMetaZFC.SetTheory
open _root_.YesMetaZFC.SetTheory.Definitional
open _root_.YesMetaZFC.SetTheory.Definitional.Project
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

/--
宿主 Project decoder 在标准 token 序列上失败时，连续编号版的对象公式码条件不可成立。
证明只展开外层序列见证与末行合同；实际公式构造失败由既有逐行递归适配器承担。
-/
theorem
    fs_zfc_support_raw_canonical_project_formula_code_condition_from_base_neg_of_project_decode_none
    (entryDepth : Nat)
    (tokens : List Nat)
    (base : FreeVarId)
    (hDecode :
      fs_project_hilbert_tokens_decode entryDepth tokens = none) :
    Derives fs_zfc_support_raw_theory [] (
      ¬ₘ canonical_project_formula_code_condition_with_ids
        (numₘ(entryDepth))
        (standard_token_sequence tokens)
        base (base + 1) (base + 2) (base + 3)
        (base + 4) (base + 5)
        (base + 6) (base + 7)
        (base + 8) (base + 9)) := by
  let condition : SetFormula :=
    canonical_project_formula_code_condition_with_ids
      (numₘ(entryDepth))
      (standard_token_sequence tokens)
      base (base + 1) (base + 2) (base + 3)
      (base + 4) (base + 5)
      (base + 6) (base + 7)
      (base + 8) (base + 9)
  have hConditionAdmissible :
      Formula.Admissible condition := by
    simpa [condition] using
      canonical_project_formula_code_condition_with_ids_admissible
        (numₘ(entryDepth))
        (standard_token_sequence tokens)
        base (base + 1) (base + 2) (base + 3)
        (base + 4) (base + 5)
        (base + 6) (base + 7)
        (base + 8) (base + 9)
        (finite_numeral_term_admissible entryDepth)
        (standard_token_sequence_admissible tokens)
  nd_apply FirstOrder.Derives.negIntro
    (T := fs_zfc_support_raw_theory)
    (Γ := ([] : Context Nonlogical.BasicSetTheory.signature))
    (body := condition)
    (hBodyCheck :=
      Formula.check_admissible_complete hConditionAdmissible)
  let Γ : Context Nonlogical.BasicSetTheory.signature := [condition]
  let traceBody : SetFormula :=
    canonical_project_formula_trace_condition_with_ids
      (numₘ(entryDepth))
      (standard_token_sequence tokens)
      (x#base) (x#(base + 1))
      (base + 2) (base + 3)
      (base + 4) (base + 5)
      (base + 6) (base + 7)
      (base + 8) (base + 9)
  have hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] condition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hCodeExists :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, base],
          (x#base ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
            (∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, base + 1],
              traceBody) := by
    simpa [condition, traceBody,
      canonical_project_formula_code_condition_with_ids] using
      FirstOrder.Derives.conjElimRight hCondition
  apply fs_zfc_support_raw_exists_elim_fresh
    [
      base + 1, base + 2, base + 3,
      base + 4, base + 5, base + 6,
      base + 7, base + 8, base + 9,
      base + 10, base + 11]
    base
    ((x#base ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
      (∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, base + 1],
        traceBody))
    Formula.falsum hCodeExists
  intro codesEigen hCodesFresh hCodeOpenedCheck
  let codes : SetTerm := x#codesEigen
  let outerOpened : SetFormula :=
    Formula.substituteFree
      Nonlogical.BasicSetTheory.SetSort.set base codes
      ((x#base ∈ₘ seq₊_spaceₘ(FormulaCodeₘ)) ∧ₘ
        (∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, base + 1],
          traceBody))
  let Ω : Context Nonlogical.BasicSetTheory.signature :=
    outerOpened :: Γ
  have hCodesAdmissible :
      Term.Admissible codes
        Nonlogical.BasicSetTheory.SetSort.set :=
    set_variable_admissible codesEigen
  have hCodeOpened :
      Ω ⊢ₘ[fs_zfc_support_raw_theory] outerOpened :=
    FirstOrder.Derives.assumption
      (by simp [Ω]) hCodeOpenedCheck
  have hBaseSuccNe :
      base ≠ base + 1 :=
    Nat.ne_of_lt <| Nat.lt_add_of_pos_right (by decide)
  have hComm :
      Formula.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          base codes
          (Formula.closeFreeAt
            Nonlogical.BasicSetTheory.SetSort.set
            (base + 1) 0 traceBody) =
        Formula.closeFreeAt
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 1) 0
          (Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            base codes traceBody) :=
    (Formula.closeFreeAt_substituteFree_comm
      Nonlogical.BasicSetTheory.SetSort.set
      base (base + 1) 0 codes traceBody hBaseSuccNe
      hCodesAdmissible.2
      (by
        intro hEqual
        apply hCodesFresh (base + 1) (by simp)
        change
          (Nonlogical.BasicSetTheory.SetSort.set,
            base + 1) ∈
            [(Nonlogical.BasicSetTheory.SetSort.set,
              codesEigen)]
        change
          (Nonlogical.BasicSetTheory.SetSort.set,
            base + 1) ∈
            [(Nonlogical.BasicSetTheory.SetSort.set,
              codesEigen)]
          at hEqual
        exact hEqual)).symm
  have hDepthExists :
      Ω ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, base + 1],
          Formula.substituteFree
            Nonlogical.BasicSetTheory.SetSort.set
            base codes traceBody := by
    simpa [outerOpened, Formula.substituteFree, hComm] using
      FirstOrder.Derives.conjElimRight hCodeOpened
  apply fs_zfc_support_raw_exists_elim_fresh
    [
      base + 1, base + 2, base + 3,
      base + 4, base + 5, base + 6,
      base + 7, base + 8, base + 9,
      base + 10, base + 11]
    (base + 1)
    (Formula.substituteFree
      Nonlogical.BasicSetTheory.SetSort.set
      base codes traceBody)
    Formula.falsum hDepthExists
  intro depthsEigen hDepthsFresh hOpenedCheck
  let depths : SetTerm := x#depthsEigen
  let firstSubstitution : SetFormula :=
    Formula.substituteFree
      Nonlogical.BasicSetTheory.SetSort.set base codes traceBody
  let opened : SetFormula :=
    Formula.substituteFree
      Nonlogical.BasicSetTheory.SetSort.set (base + 1) depths
      firstSubstitution
  let Θ : Context Nonlogical.BasicSetTheory.signature :=
    opened :: Ω
  have hDepthsAdmissible :
      Term.Admissible depths
        Nonlogical.BasicSetTheory.SetSort.set :=
    set_variable_admissible depthsEigen
  have hCodesCheck :
      Term.CheckCertificate codes
        Nonlogical.BasicSetTheory.SetSort.set :=
    Term.check_admissible_complete hCodesAdmissible
  have hDepthsCheck :
      Term.CheckCertificate depths
        Nonlogical.BasicSetTheory.SetSort.set :=
    Term.check_admissible_complete hDepthsAdmissible
  have hOpened :
      Θ ⊢ₘ[fs_zfc_support_raw_theory] opened :=
    FirstOrder.Derives.assumption
      (by simp [Θ]) hOpenedCheck
  have hBaseNe (offset : Nat) (hPositive : 0 < offset) :
      base ≠ base + offset :=
    Nat.ne_of_lt (Nat.lt_add_of_pos_right hPositive)
  have hBaseSuccNe (offset : Nat) (hOffset : 1 < offset) :
      base + 1 ≠ base + offset :=
    Nat.ne_of_lt (Nat.add_lt_add_left hOffset base)
  have hNumeralFirst :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          base codes (numₘ(entryDepth)) =
        numₘ(entryDepth) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hCodeFirst :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          base codes (standard_token_sequence tokens) =
        standard_token_sequence tokens := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [standard_token_sequence_freeSupport_nil]
    exact List.not_mem_nil
  have hCodesVariable :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          base codes (x#base) =
        codes := by
    simp [Term.substituteFree, set_variable]
  have hDepthsVariableFixed :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          base codes (x#(base + 1)) =
        x#(base + 1) := by
    simp [Term.substituteFree, set_variable]
  have hFirstSubstitution :
      firstSubstitution =
        canonical_project_formula_trace_condition_with_ids
          (numₘ(entryDepth))
          (standard_token_sequence tokens)
          codes (x#(base + 1))
          (base + 2) (base + 3)
          (base + 4) (base + 5)
          (base + 6) (base + 7)
          (base + 8) (base + 9) := by
    simpa [firstSubstitution, traceBody] using
      canonical_project_formula_trace_condition_with_ids_substitute_free
        (numₘ(entryDepth))
        (standard_token_sequence tokens)
        (x#base) (x#(base + 1))
        codes
        (numₘ(entryDepth))
        (standard_token_sequence tokens)
        codes (x#(base + 1))
        base
        (base + 2) (base + 3)
        (base + 4) (base + 5)
        (base + 6) (base + 7)
        (base + 8) (base + 9)
        (hBaseNe 2 (by decide)) (hBaseNe 3 (by decide))
        (hBaseNe 4 (by decide)) (hBaseNe 5 (by decide))
        (hBaseNe 6 (by decide)) (hBaseNe 7 (by decide))
        (hBaseNe 8 (by decide)) (hBaseNe 9 (by decide))
        hCodesAdmissible
        (hCodesFresh (base + 2) (by simp))
        (hCodesFresh (base + 3) (by simp))
        (hCodesFresh (base + 4) (by simp))
        (hCodesFresh (base + 5) (by simp))
        (hCodesFresh (base + 6) (by simp))
        (hCodesFresh (base + 7) (by simp))
        (hCodesFresh (base + 8) (by simp))
        (hCodesFresh (base + 9) (by simp))
        hNumeralFirst hCodeFirst
        hCodesVariable hDepthsVariableFixed
  have hNumeralSecond :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 1) depths (numₘ(entryDepth)) =
        numₘ(entryDepth) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hCodeSecond :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 1) depths
          (standard_token_sequence tokens) =
        standard_token_sequence tokens := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [standard_token_sequence_freeSupport_nil]
    exact List.not_mem_nil
  have hCodesSecond :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 1) depths codes =
        codes :=
    Term.substituteFree_eq_self_of_not_mem
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 1) depths codes <| by
        exact hCodesFresh (base + 1) (by simp)
  have hDepthsVariable :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 1) depths (x#(base + 1)) =
        depths := by
    simp [Term.substituteFree, set_variable]
  have hSecondSubstitution :
      Formula.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 1) depths
          (canonical_project_formula_trace_condition_with_ids
            (numₘ(entryDepth))
            (standard_token_sequence tokens)
            codes (x#(base + 1))
            (base + 2) (base + 3)
            (base + 4) (base + 5)
            (base + 6) (base + 7)
            (base + 8) (base + 9)) =
        canonical_project_formula_trace_condition_with_ids
          (numₘ(entryDepth))
          (standard_token_sequence tokens)
          codes depths
          (base + 2) (base + 3)
          (base + 4) (base + 5)
          (base + 6) (base + 7)
          (base + 8) (base + 9) := by
    exact
      canonical_project_formula_trace_condition_with_ids_substitute_free
        (numₘ(entryDepth))
        (standard_token_sequence tokens)
        codes (x#(base + 1))
        depths
        (numₘ(entryDepth))
        (standard_token_sequence tokens)
        codes depths
        (base + 1)
        (base + 2) (base + 3)
        (base + 4) (base + 5)
        (base + 6) (base + 7)
        (base + 8) (base + 9)
        (hBaseSuccNe 2 (by decide))
        (hBaseSuccNe 3 (by decide))
        (hBaseSuccNe 4 (by decide))
        (hBaseSuccNe 5 (by decide))
        (hBaseSuccNe 6 (by decide))
        (hBaseSuccNe 7 (by decide))
        (hBaseSuccNe 8 (by decide))
        (hBaseSuccNe 9 (by decide))
        hDepthsAdmissible
        (hDepthsFresh (base + 2) (by simp))
        (hDepthsFresh (base + 3) (by simp))
        (hDepthsFresh (base + 4) (by simp))
        (hDepthsFresh (base + 5) (by simp))
        (hDepthsFresh (base + 6) (by simp))
        (hDepthsFresh (base + 7) (by simp))
        (hDepthsFresh (base + 8) (by simp))
        (hDepthsFresh (base + 9) (by simp))
        hNumeralSecond hCodeSecond
        hCodesSecond hDepthsVariable
  have hTrace :
      Θ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_formula_trace_condition_with_ids
          (numₘ(entryDepth))
          (standard_token_sequence tokens)
          codes depths
          (base + 2) (base + 3)
          (base + 4) (base + 5)
          (base + 6) (base + 7)
          (base + 8) (base + 9) := by
    simpa [opened, hFirstSubstitution,
      hSecondSubstitution] using hOpened
  have hPositive :
      Θ ⊢ₘ[fs_zfc_support_raw_theory]
        codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ) :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimLeft hTrace
  have hAll :
      Θ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[Nonlogical.BasicSetTheory.SetSort.set, base + 3],
          (x#(base + 3) ∈ₘ domₘ(codes)) ⟶ₘ
            canonical_project_formula_line_condition_with_ids
              codes depths (x#(base + 3))
              (base + 4) (base + 5)
              (base + 6) (base + 7)
              (base + 8) (base + 9) :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hTrace
  let terminalBody : SetFormula :=
    canonical_project_formula_terminal_condition
      (numₘ(entryDepth))
      (standard_token_sequence tokens)
      codes depths (x#(base + 2))
  have hTerminalExists :
      Θ ⊢ₘ[fs_zfc_support_raw_theory]
        ∃ₘ[Nonlogical.BasicSetTheory.SetSort.set, base + 2],
          terminalBody := by
    simpa [terminalBody] using
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hTrace
  apply fs_zfc_support_raw_exists_elim_fresh
    [
      base + 3, base + 4, base + 5,
      base + 6, base + 7, base + 8,
      base + 9, base + 10, base + 11]
    (base + 2) terminalBody Formula.falsum
    hTerminalExists
  intro pointEigen hPointFresh hTerminalOpenedCheck
  let point : SetTerm := x#pointEigen
  let terminalOpened : SetFormula :=
    Formula.substituteFree
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 2) point terminalBody
  let Λ : Context Nonlogical.BasicSetTheory.signature :=
    terminalOpened :: Θ
  have hPointAdmissible :
      Term.Admissible point
        Nonlogical.BasicSetTheory.SetSort.set :=
    set_variable_admissible pointEigen
  have hPointCheck :
      Term.CheckCertificate point
        Nonlogical.BasicSetTheory.SetSort.set :=
    Term.check_admissible_complete hPointAdmissible
  have hTerminalOpened :
      Λ ⊢ₘ[fs_zfc_support_raw_theory] terminalOpened :=
    FirstOrder.Derives.assumption
      (by simp [Λ]) hTerminalOpenedCheck
  have hEntryFixed :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 2) point (numₘ(entryDepth)) =
        numₘ(entryDepth) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hCodeFixed :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 2) point
          (standard_token_sequence tokens) =
        standard_token_sequence tokens := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [standard_token_sequence_freeSupport_nil]
    exact List.not_mem_nil
  have hCodesFixed :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 2) point codes =
        codes :=
    Term.substituteFree_eq_self_of_not_mem
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 2) point codes <| by
        exact hCodesFresh (base + 2) (by simp)
  have hDepthsFixed :
      Term.substituteFree
          Nonlogical.BasicSetTheory.SetSort.set
          (base + 2) point depths =
        depths :=
    Term.substituteFree_eq_self_of_not_mem
      Nonlogical.BasicSetTheory.SetSort.set
      (base + 2) point depths <| by
        exact hDepthsFresh (base + 2) (by simp)
  have hTerminal :
      Λ ⊢ₘ[fs_zfc_support_raw_theory]
        canonical_project_formula_terminal_condition
          (numₘ(entryDepth))
          (standard_token_sequence tokens)
          codes depths point := by
    simpa [terminalOpened, terminalBody,
      canonical_project_formula_terminal_condition,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hEntryFixed, hCodeFixed,
      hCodesFixed, hDepthsFixed] using
      hTerminalOpened
  have hDomain :
      Λ ⊢ₘ[fs_zfc_support_raw_theory]
        point ∈ₘ domₘ(codes) :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimLeft hTerminal
  have hCodeAt :
      Λ ⊢ₘ[fs_zfc_support_raw_theory]
        (codes ·ₘ point) ≐ₘ
          standard_token_sequence tokens :=
    Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight hTerminal
  have hDepthAt :
      Λ ⊢ₘ[fs_zfc_support_raw_theory]
        (depths ·ₘ point) ≐ₘ numₘ(entryDepth) :=
    Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hTerminal
  have hPositiveAt :
      Λ ⊢ₘ[fs_zfc_support_raw_theory]
        codes ∈ₘ seq₊_spaceₘ(FormulaCodeₘ) :=
    FirstOrder.Derives.context_weaken_cons hPositive
  have hAllAt :
      Λ ⊢ₘ[fs_zfc_support_raw_theory]
        ∀ₘ[Nonlogical.BasicSetTheory.SetSort.set, base + 3],
          (x#(base + 3) ∈ₘ domₘ(codes)) ⟶ₘ
            canonical_project_formula_line_condition_with_ids
              codes depths (x#(base + 3))
              (base + 4) (base + 5)
              (base + 6) (base + 7)
              (base + 8) (base + 9) :=
    FirstOrder.Derives.context_weaken_cons hAll
  have hCodesRowFresh :
      ∀ id, id ∈ [
        base + 3, base + 4, base + 5,
        base + 6, base + 7, base + 8,
        base + 9, base + 10, base + 11] →
        (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
          Term.freeSupport codes := by
    intro id hId
    apply hCodesFresh id
    simp only [List.mem_cons] at hId ⊢
    exact Or.inr <| Or.inr hId
  have hDepthsRowFresh :
      ∀ id, id ∈ [
        base + 3, base + 4, base + 5,
        base + 6, base + 7, base + 8,
        base + 9, base + 10, base + 11] →
        (Nonlogical.BasicSetTheory.SetSort.set, id) ∉
          Term.freeSupport depths := by
    intro id hId
    apply hDepthsFresh id
    simp only [List.mem_cons] at hId ⊢
    exact Or.inr <| Or.inr hId
  exact
    fs_zfc_support_raw_project_line_falsum_of_decode_none
      entryDepth tokens base
      codes depths point
      hCodesCheck hDepthsCheck hPointCheck
      hCodesRowFresh hDepthsRowFresh hPointFresh
      hPositiveAt hAllAt hDomain hCodeAt hDepthAt hDecode

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
