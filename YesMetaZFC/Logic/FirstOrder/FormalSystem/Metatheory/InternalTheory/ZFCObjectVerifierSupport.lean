import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCObjectVerifierSubstitution

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

private theorem term_mem_freeSupport_closeFreeAt_of_mem_of_ne
    (freeVariable : FreeVariable (signature))
    (target : signature.SortSymbol)
    (id : FreeVarId)
    (depth : Nat)
    (term : SetTerm)
    (hMember : freeVariable ∈ Term.freeSupport term)
    (hNe : freeVariable ≠ (target, id)) :
    freeVariable ∈
      Term.freeSupport
        (Term.closeFreeAt target id depth term) := by
  refine Term.rec (motive_1 := fun term =>
      freeVariable ∈ Term.freeSupport term →
        freeVariable ≠ (target, id) →
          freeVariable ∈
            Term.freeSupport
              (Term.closeFreeAt target id depth term))
    (motive_2 := fun terms =>
      freeVariable ∈ Term.freeSupportList terms →
        freeVariable ≠ (target, id) →
          freeVariable ∈
            Term.freeSupportList
              (terms.map (Term.closeFreeAt target id depth)))
    ?_ ?_ ?_ ?_ term hMember hNe
  · intro sourceVar hMember hNe
    cases sourceVar with
    | bvar sort index =>
        simp [Term.freeSupport] at hMember
    | fvar sort freeId =>
        by_cases hClose : sort = target ∧ freeId = id
        · exact False.elim <| hNe (by
            have hVariable :
                freeVariable = (sort, freeId) :=
              List.mem_singleton.mp hMember
            exact hVariable.trans (by
              rcases hClose with ⟨rfl, rfl⟩
              rfl))
        · simpa [Term.closeFreeAt, Term.freeSupport, hClose] using hMember
  · intro function arguments ih hMember hNe
    simpa [Term.closeFreeAt, Term.freeSupport] using
      ih hMember hNe
  · intro hMember hNe
    simp [Term.freeSupportList] at hMember
  · intro head tail ihHead ihTail hMember hNe
    rcases List.mem_append.mp hMember with hHead | hTail
    · have hClosedHead :=
        ihHead hHead hNe
      exact List.mem_append.mpr (Or.inl hClosedHead)
    · have hClosedTail :=
        ihTail hTail hNe
      exact List.mem_append.mpr (Or.inr hClosedTail)

private theorem formula_mem_freeSupport_closeFreeAt_of_mem_of_ne
    (freeVariable : FreeVariable (signature))
    (target : signature.SortSymbol)
    (id : FreeVarId)
    (depth : Nat)
    (formula : SetFormula)
    (hMember : freeVariable ∈ Formula.freeSupport formula)
    (hNe : freeVariable ≠ (target, id)) :
    freeVariable ∈
      Formula.freeSupport
        (Formula.closeFreeAt target id depth formula) := by
  revert hMember hNe
  induction formula generalizing depth with
  | falsum =>
      intro hMember hNe
      simp [Formula.freeSupport] at hMember
  | truth =>
      intro hMember hNe
      simp [Formula.freeSupport] at hMember
  | rel relation arguments =>
      intro hMember hNe
      change freeVariable ∈ Term.freeSupportList arguments at hMember
      change freeVariable ∈
        Term.freeSupportList
          (arguments.map (Term.closeFreeAt target id depth))
      revert hMember hNe
      induction arguments with
      | nil =>
          intro hNe hMember
          exact False.elim (List.not_mem_nil hMember)
      | cons head tail ihTail =>
          intro hNe hMember
          rcases List.mem_append.mp hMember with hHead | hTail
          · exact List.mem_append.mpr (Or.inl <|
              term_mem_freeSupport_closeFreeAt_of_mem_of_ne
                freeVariable target id depth head hHead hNe)
          · exact List.mem_append.mpr (Or.inr <|
              ihTail hNe hTail)
  | equal left right =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          term_mem_freeSupport_closeFreeAt_of_mem_of_ne
            freeVariable target id depth left hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          term_mem_freeSupport_closeFreeAt_of_mem_of_ne
            freeVariable target id depth right hRight hNe)
  | neg body ih =>
      intro hMember hNe
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih depth hMember hNe
  | conj left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | disj left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | imp left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | iff left right ihLeft ihRight =>
      intro hMember hNe
      rcases List.mem_append.mp hMember with hLeft | hRight
      · exact List.mem_append.mpr (Or.inl <|
          ihLeft depth hLeft hNe)
      · exact List.mem_append.mpr (Or.inr <|
          ihRight depth hRight hNe)
  | forallE sort body ih =>
      intro hMember hNe
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if sort = target then depth + 1 else depth) hMember hNe
  | existsE sort body ih =>
      intro hMember hNe
      simpa [Formula.closeFreeAt, Formula.freeSupport] using
        ih (if sort = target then depth + 1 else depth) hMember hNe

private theorem formula_mem_freeSupport_closeFreeAt_iff
    (freeVariable : FreeVariable (signature))
    (target : signature.SortSymbol)
    (id : FreeVarId)
    (depth : Nat)
    (formula : SetFormula) :
    freeVariable ∈
        Formula.freeSupport
          (Formula.closeFreeAt target id depth formula) ↔
      freeVariable ∈ Formula.freeSupport formula ∧
        freeVariable ≠ (target, id) := by
  constructor
  · intro hMember
    refine ⟨?_, ?_⟩
    · by_cases hFresh : freeVariable ∈ Formula.freeSupport formula
      · exact hFresh
      · exact False.elim <|
          (Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
            freeVariable target id depth formula hFresh) hMember
    · intro hEqual
      subst hEqual
      exact Formula.not_mem_freeSupport_closeFreeAt
        target id depth formula hMember
  · intro hMember
    exact formula_mem_freeSupport_closeFreeAt_of_mem_of_ne
      freeVariable target id depth formula hMember.1 hMember.2

private theorem term_mem_freeSupport_closeFreeAt_iff
    (freeVariable : FreeVariable (signature))
    (target : signature.SortSymbol)
    (id : FreeVarId)
    (depth : Nat)
    (term : SetTerm) :
    freeVariable ∈
        Term.freeSupport
          (Term.closeFreeAt target id depth term) ↔
      freeVariable ∈ Term.freeSupport term ∧
        freeVariable ≠ (target, id) := by
  constructor
  · intro hMember
    refine ⟨?_, ?_⟩
    · by_cases hFresh : freeVariable ∈ Term.freeSupport term
      · exact hFresh
      · exact False.elim <|
          (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
            freeVariable target id depth term hFresh) hMember
    · intro hEqual
      subst hEqual
      exact Term.not_mem_freeSupport_closeFreeAt
        target id depth term hMember
  · intro hMember
    exact term_mem_freeSupport_closeFreeAt_of_mem_of_ne
      freeVariable target id depth term hMember.1 hMember.2

theorem nat_sequence_freeSupport_subset
    (sequence code : SetTerm)
    (traceId indexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (nat_sequence_code_condition_with_ids
              sequence code traceId indexId) →
      freeVariable ∈ Term.freeSupport sequence ∨
        freeVariable ∈ Term.freeSupport code := by
  intro freeVariable hMember
  by_cases hSequence :
      freeVariable ∈ Term.freeSupport sequence
  · exact Or.inl hSequence
  by_cases hCode :
      freeVariable ∈ Term.freeSupport code
  · exact Or.inr hCode
  · exfalso
    simp_all [
      nat_sequence_code_condition_with_ids,
      sequence_domain_code_bound,
      nat_sequence_value_code_bound_with_id,
      sequence_trace_code_bound_with_id,
      nat_sequence_code_step_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport,
      formula_mem_freeSupport_closeFreeAt_iff,

      List.mem_append]
    grind

theorem canonical_project_formula_code_freeSupport_subset
    (entryDepth code : SetTerm)
    (codesId depthsId lastIndexId indexId
      firstPremiseId secondPremiseId
      leftVariableCodeId rightVariableCodeId
      leftVariableDepthId rightVariableDepthId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_project_formula_code_condition_with_ids
              entryDepth code
              codesId depthsId lastIndexId indexId
              firstPremiseId secondPremiseId
              leftVariableCodeId rightVariableCodeId
              leftVariableDepthId rightVariableDepthId) →
      freeVariable ∈ Term.freeSupport entryDepth ∨
        freeVariable ∈ Term.freeSupport code := by
  intro freeVariable hMember
  by_cases hEntry : freeVariable ∈ Term.freeSupport entryDepth
  · exact Or.inl hEntry
  by_cases hCode : freeVariable ∈ Term.freeSupport code
  · exact Or.inr hCode
  · exfalso
    simp_all [
      canonical_project_formula_code_condition_with_ids,
      canonical_project_formula_trace_condition_with_ids,
      canonical_project_formula_line_condition_with_ids,
      canonical_project_formula_terminal_condition,
      canonical_project_atomic_code_condition_with_ids,
      canonical_scoped_variable_code_condition_with_id,
      Formula.freeSupport, Term.freeSupport, Term.freeSupportList,
      GodelQuotation.Numbered.argument_sequence,
      GodelQuotation.standard_sequence,
      GodelQuotation.standard_sequence_from,
      finite_numeral_term_freeSupport,
      formula_mem_freeSupport_closeFreeAt_iff,

      List.mem_append]
    grind

theorem canonical_project_shift_code_freeSupport_subset
    (cutoff sourceCode targetCode : SetTerm)
    (indexId sourceDepthId targetDepthId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_project_shift_code_condition_with_ids
              cutoff sourceCode targetCode
              indexId sourceDepthId targetDepthId) →
      freeVariable ∈ Term.freeSupport cutoff ∨
        freeVariable ∈ Term.freeSupport sourceCode ∨
          freeVariable ∈ Term.freeSupport targetCode := by
  intro freeVariable hMember
  by_cases hCutoff : freeVariable ∈ Term.freeSupport cutoff
  · exact Or.inl hCutoff
  by_cases hSourceCode : freeVariable ∈ Term.freeSupport sourceCode
  · exact Or.inr (Or.inl hSourceCode)
  by_cases hTargetCode : freeVariable ∈ Term.freeSupport targetCode
  · exact Or.inr (Or.inr hTargetCode)
  · exfalso
    simp_all [
      canonical_project_shift_code_condition_with_ids,
      canonical_project_shift_token_condition_with_ids,
      canonical_project_shift_fixed_token_condition,
      mem_freeSupport_canonical_binder_shift_fixed_token_condition_iff,
      canonical_shifted_depth_condition,
      finite_sequence_condition,
      Formula.freeSupport, Term.freeSupport, Term.freeSupportList,



      finite_numeral_term_freeSupport,
      formula_mem_freeSupport_closeFreeAt_iff,

      List.mem_append]
    grind

theorem canonical_forall_prefix_code_freeSupport_subset
    (binderCount core code : SetTerm)
    (traceId indexId : FreeVarId) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (canonical_forall_prefix_code_condition_with_ids
              binderCount core code traceId indexId) →
      freeVariable ∈ Term.freeSupport binderCount ∨
        freeVariable ∈ Term.freeSupport core ∨
          freeVariable ∈ Term.freeSupport code := by
  intro freeVariable hMember
  by_cases hBinderCount : freeVariable ∈ Term.freeSupport binderCount
  · exact Or.inl hBinderCount
  by_cases hCore : freeVariable ∈ Term.freeSupport core
  · exact Or.inr (Or.inl hCore)
  by_cases hCode : freeVariable ∈ Term.freeSupport code
  · exact Or.inr (Or.inr hCode)
  · exfalso
    simp_all [
      canonical_forall_prefix_code_condition_with_ids,
      canonical_forall_prefix_trace_condition,
      canonical_forall_prefix_step_condition,
      Formula.freeSupport, Term.freeSupport, Term.freeSupportList,



      finite_numeral_term_freeSupport,
      formula_mem_freeSupport_closeFreeAt_iff,

      List.mem_append]
    grind

theorem fs_zfc_separation_core_code_freeSupport_subset
    (parameterCount shiftTwo : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Term.freeSupport
            (fs_zfc_separation_core_code
              parameterCount shiftTwo) →
        freeVariable ∈ Term.freeSupport parameterCount ∨
          freeVariable ∈ Term.freeSupport shiftTwo := by
  intro freeVariable hMember
  simp [
    fs_zfc_separation_core_code,
    fs_zfc_hilbert_iff_code,
    conjunction_formula_code_term,
    implication_formula_code_term,
    Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport,
    List.mem_append] at hMember ⊢
  grind

theorem fs_zfc_collection_core_code_freeSupport_subset
    (parameterCount shiftOne shiftTwo : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Term.freeSupport
            (fs_zfc_collection_core_code
              parameterCount shiftOne shiftTwo) →
        freeVariable ∈ Term.freeSupport parameterCount ∨
          freeVariable ∈ Term.freeSupport shiftOne ∨
            freeVariable ∈ Term.freeSupport shiftTwo := by
  intro freeVariable hMember
  simp [
    fs_zfc_collection_core_code,
    conjunction_formula_code_term,
    implication_formula_code_term,
    Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport,
    List.mem_append] at hMember ⊢
  grind

theorem fs_zfc_replacement_core_code_freeSupport_subset
    (parameterCount firstOutputCode secondOutputCode imageCode : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Term.freeSupport
            (fs_zfc_replacement_core_code
              parameterCount firstOutputCode secondOutputCode imageCode) →
        freeVariable ∈ Term.freeSupport parameterCount ∨
          freeVariable ∈ Term.freeSupport firstOutputCode ∨
            freeVariable ∈ Term.freeSupport secondOutputCode ∨
              freeVariable ∈ Term.freeSupport imageCode := by
  intro freeVariable hMember
  simp [
    fs_zfc_replacement_core_code,
    fs_zfc_hilbert_iff_code,
    conjunction_formula_code_term,
    implication_formula_code_term,
    equality_formula_code_term,
    membership_atomic_formula_code_term,
    canonical_binder_variable_code_term,
    Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport,
    List.mem_append] at hMember ⊢
  grind

theorem fs_zfc_schema_certificate_term_freeSupport_subset
    (schemaTag parameterCount bodyTokenCode : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Term.freeSupport
            (fs_zfc_schema_certificate_term
              schemaTag parameterCount bodyTokenCode) →
        freeVariable ∈ Term.freeSupport schemaTag ∨
          freeVariable ∈ Term.freeSupport parameterCount ∨
            freeVariable ∈ Term.freeSupport bodyTokenCode := by
  intro freeVariable hMember
  simp [
    fs_zfc_schema_certificate_term,
    fs_zfc_schema_payload_term,
    fs_zfc_schema_body_payload_term,
    Term.freeSupport, Term.freeSupportList,
    finite_numeral_term_freeSupport,
    List.mem_append] at hMember ⊢
  grind

/-- schema 证书有限边界只依赖其四个显式实参。 -/
theorem fs_zfc_schema_certificate_bounds_freeSupport_subset
    (certificate schemaTag parameterCount bodyTokenCode : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (fs_zfc_schema_certificate_bounds
              certificate schemaTag parameterCount bodyTokenCode) →
        freeVariable ∈ Term.freeSupport certificate ∨
          freeVariable ∈ Term.freeSupport schemaTag ∨
            freeVariable ∈ Term.freeSupport parameterCount ∨
              freeVariable ∈ Term.freeSupport bodyTokenCode := by
  intro freeVariable hMember
  simp only [fs_zfc_schema_certificate_bounds,
    fs_zfc_schema_payload_term, fs_zfc_schema_body_payload_term,
    Formula.freeSupport, Term.freeSupport, Term.freeSupportList,
    List.mem_append] at hMember
  grind

theorem fs_zfc_object_certificate_condition_freeSupport_subset
    (formula certificate : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (fs_zfc_object_certificate_condition formula certificate) →
      freeVariable ∈ Term.freeSupport formula ∨
          freeVariable ∈ Term.freeSupport certificate := by
  have hCloseSubset
      (freeVariable : FreeVariable (signature))
      (target : signature.SortSymbol)
      (id : FreeVarId)
      (depth : Nat)
      (body : SetFormula)
      (hMember :
        freeVariable ∈
          Formula.freeSupport
            (Formula.closeFreeAt target id depth body)) :
      freeVariable ∈ Formula.freeSupport body := by
    by_cases hFresh : freeVariable ∈ Formula.freeSupport body
    · exact hFresh
    · exact False.elim <|
        (Formula.not_mem_freeSupport_closeFreeAt_of_not_mem
          freeVariable target id depth body hFresh) hMember
  have hTermCloseSubset
      (freeVariable : FreeVariable (signature))
      (target : signature.SortSymbol)
      (id : FreeVarId)
      (depth : Nat)
      (term : SetTerm)
      (hMember :
        freeVariable ∈
          Term.freeSupport
            (Term.closeFreeAt target id depth term)) :
      freeVariable ∈ Term.freeSupport term := by
    by_cases hFresh : freeVariable ∈ Term.freeSupport term
    · exact hFresh
    · exact False.elim <|
        (Term.not_mem_freeSupport_closeFreeAt_of_not_mem
          freeVariable target id depth term hFresh) hMember
  have hFixedTable
      (rows : List (Nat × SetTerm))
      (freeVariable : FreeVariable (signature))
      (hRowsClosed :
        ∀ row, row ∈ rows → Term.freeSupport row.2 = [])
      (hMember :
        freeVariable ∈
          Formula.freeSupport
            (ProofT.FixedAxiomTable.condition_rows
              rows formula certificate)) :
      freeVariable ∈ Term.freeSupport formula ∨
        freeVariable ∈ Term.freeSupport certificate := by
    induction rows with
    | nil =>
        change freeVariable ∈ [] at hMember
        exact False.elim (List.not_mem_nil hMember)
    | cons row rows ih =>
        change freeVariable ∈
          Formula.freeSupport
            ((((certificate ≐ₘ numₘ(row.1)) ∧ₘ
                (formula ≐ₘ row.2)) ∨ₘ
              ProofT.FixedAxiomTable.condition_rows
                rows formula certificate)) at hMember
        simp only [Formula.freeSupport, List.mem_append] at hMember
        rcases hMember with hHead | hTail
        · rcases hHead with hCertificate | hFormula
          · rcases hCertificate with hCertificate | hNumeral
            · exact Or.inr hCertificate
            · exact False.elim <|
                (by
                  simp [finite_numeral_term_freeSupport] at hNumeral)
          · rcases hFormula with hFormula | hRow
            · exact Or.inl hFormula
            · have hRowClosed := hRowsClosed row (by simp)
              exact False.elim <|
                (by simp [hRowClosed] at hRow)
        · exact ih (fun item hItem =>
            hRowsClosed item (by simp [hItem])) hTail
  intro freeVariable hMember
  have hNotVariable
      (id : FreeVarId)
      (hNe : freeVariable ≠ (SetSort.set, id))
      (hMember : freeVariable ∈ Term.freeSupport (x#id)) :
      False := by
    apply hNe
    simpa [Term.freeSupport, set_variable] using hMember
  have hNotVariableList
      (id : FreeVarId)
      (hNe : freeVariable ≠ (SetSort.set, id))
      (hMember : freeVariable ∈ Term.freeSupportList [x#id]) :
      False := by
    apply hNe
    simpa [Term.freeSupportList, Term.freeSupport, set_variable] using hMember
  change freeVariable ∈
      Formula.freeSupport
          (fs_zfc_fixed_axiom_table.condition formula certificate) ++
        Formula.freeSupport
          ((fs_zfc_separation_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate])) ∨ₘ
            (fs_zfc_collection_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate]))) at hMember
  rcases List.mem_append.mp hMember with hFixed | hSchema
  · exact hFixedTable fs_zfc_fixed_table_rows freeVariable
      (fun row hRow => fs_zfc_fixed_table_rows_freeSupport_nil hRow)
      hFixed
  · change freeVariable ∈
        Formula.freeSupport
            (fs_zfc_separation_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate])) ++
          Formula.freeSupport
            (fs_zfc_collection_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate])) at hSchema
    rcases List.mem_append.mp hSchema with hSeparation | hCollection
    ·
      simp only [fs_zfc_separation_condition_with_base, Formula.freeSupport] at hSeparation
      have hBody₁ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate]) 0 _ hSeparation
      have hNe0 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate]) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate]) 0 _)
          hSeparation
      have hNe1 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate] + 1) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate] + 1) 0 _)
          (by simpa only [Formula.freeSupport] using hBody₁)
      have hBody₂ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate] + 1) 0 _ hBody₁
      have hNe2 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate] + 2) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate] + 2) 0 _)
          (by simpa only [Formula.freeSupport] using hBody₂)
      have hBody₃ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate] + 2) 0 _ hBody₂
      have hNe3 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate] + 3) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate] + 3) 0 _)
          (by simpa only [Formula.freeSupport] using hBody₃)
      have hBody₄ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate] + 3) 0 _ hBody₃
      have hNe4 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate] + 4) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate] + 4) 0 _)
          (by simpa only [Formula.freeSupport] using hBody₄)
      have hBody₅ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate] + 4) 0 _ hBody₄
      simp only [Formula.freeSupport, List.mem_append] at hBody₅
      rcases hBody₅ with hCertificate | hRest
      · rcases hCertificate with hCertificate | hCertificateCode
        · exact Or.inr hCertificate
        · have hCertificateCode' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate]) ∨
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 1) := by
            simpa [fs_zfc_schema_certificate_term,
              fs_zfc_schema_payload_term,
              fs_zfc_schema_body_payload_term,
              Term.freeSupport, Term.freeSupportList,
              finite_numeral_term_freeSupport] using hCertificateCode
          exact False.elim <| by
            rcases hCertificateCode' with hEqual | hEqual
            · exact hNe0 hEqual
            · exact hNe1 hEqual
      rcases hRest with hBounds | hRest
      · rcases
            fs_zfc_schema_certificate_bounds_freeSupport_subset
              certificate (numₘ(0))
              (x#(ProofT.schema_base [formula, certificate]))
              (x#(ProofT.schema_base [formula, certificate] + 1))
              freeVariable hBounds with
          hCertificate | hSchemaTag | hParameter | hBodyToken
        · exact Or.inr hCertificate
        · exact False.elim <| by
            simp [finite_numeral_term_freeSupport] at hSchemaTag
        · exact False.elim <| hNe0 <| by
            simpa [Term.freeSupport, set_variable] using hParameter
        · exact False.elim <| hNe1 <| by
            simpa [Term.freeSupport, set_variable] using hBodyToken
      rcases hRest with hParameter | hRest
      · have hParameter' :
            freeVariable = (SetSort.set,
              ProofT.schema_base [formula, certificate]) := by
          simpa [Term.freeSupport, Term.freeSupportList,
            finite_numeral_term_freeSupport] using hParameter
        exact False.elim (hNe0 hParameter')
      rcases hRest with hSequence | hRest
      · have hSequence' :=
          nat_sequence_freeSupport_subset
            (x#(ProofT.schema_base [formula, certificate] + 2))
            (x#(ProofT.schema_base [formula, certificate] + 1))
            (ProofT.schema_base [formula, certificate] + 5)
            (ProofT.schema_base [formula, certificate] + 6)
            freeVariable hSequence
        rcases hSequence' with hBodyCode | hTokenCode
        · have hBodyCode' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 2) := by
            simpa [Term.freeSupport, set_variable] using hBodyCode
          exact False.elim (hNe2 hBodyCode')
        · have hTokenCode' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 1) := by
            simpa [Term.freeSupport, set_variable] using hTokenCode
          exact False.elim (hNe1 hTokenCode')
      rcases hRest with hClassifier | hRest
      · have hClassifier' :=
          canonical_project_formula_code_freeSupport_subset
            (Sₘ(x#(ProofT.schema_base [formula, certificate])))
            (x#(ProofT.schema_base [formula, certificate] + 2))
            (ProofT.schema_base [formula, certificate] + 7)
            (ProofT.schema_base [formula, certificate] + 8)
            (ProofT.schema_base [formula, certificate] + 9)
            (ProofT.schema_base [formula, certificate] + 10)
            (ProofT.schema_base [formula, certificate] + 11)
            (ProofT.schema_base [formula, certificate] + 12)
            (ProofT.schema_base [formula, certificate] + 13)
            (ProofT.schema_base [formula, certificate] + 14)
            (ProofT.schema_base [formula, certificate] + 15)
            (ProofT.schema_base [formula, certificate] + 16)
            freeVariable hClassifier
        rcases hClassifier' with hEntry | hCode
        · exact False.elim <|
            hNotVariableList
              (ProofT.schema_base [formula, certificate]) hNe0 hEntry
        · have hCode' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 2) := by
            simpa [Term.freeSupport, set_variable] using hCode
          exact False.elim (hNe2 hCode')
      rcases hRest with hShiftFirst | hRest
      · have hShiftFirst' :=
          canonical_project_shift_code_freeSupport_subset
            (x#(ProofT.schema_base [formula, certificate]))
            (x#(ProofT.schema_base [formula, certificate] + 2))
            (x#(ProofT.schema_base [formula, certificate] + 3))
            (ProofT.schema_base [formula, certificate] + 17)
            (ProofT.schema_base [formula, certificate] + 18)
            (ProofT.schema_base [formula, certificate] + 19)
            freeVariable hShiftFirst
        rcases hShiftFirst' with hCutoff | hRest
        · have hCutoff' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate]) := by
            simpa [Term.freeSupport, set_variable] using hCutoff
          exact False.elim (hNe0 hCutoff')
        rcases hRest with hLeft | hRight
        · have hLeft' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 2) := by
            simpa [Term.freeSupport, set_variable] using hLeft
          exact False.elim (hNe2 hLeft')
        · have hRight' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 3) := by
            simpa [Term.freeSupport, set_variable] using hRight
          exact False.elim (hNe3 hRight')
      rcases hRest with hShiftSecond | hPrefixMember
      · have hShiftSecond' :=
          canonical_project_shift_code_freeSupport_subset
            (x#(ProofT.schema_base [formula, certificate]))
            (x#(ProofT.schema_base [formula, certificate] + 3))
            (x#(ProofT.schema_base [formula, certificate] + 4))
            (ProofT.schema_base [formula, certificate] + 25)
            (ProofT.schema_base [formula, certificate] + 26)
            (ProofT.schema_base [formula, certificate] + 27)
            freeVariable hShiftSecond
        rcases hShiftSecond' with hCutoff | hRest
        · have hCutoff' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate]) := by
            simpa [Term.freeSupport, set_variable] using hCutoff
          exact False.elim (hNe0 hCutoff')
        rcases hRest with hLeft | hRight
        · have hLeft' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 3) := by
            simpa [Term.freeSupport, set_variable] using hLeft
          exact False.elim (hNe3 hLeft')
        · have hRight' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 4) := by
            simpa [Term.freeSupport, set_variable] using hRight
          exact False.elim (hNe4 hRight')
      have hPrefix :=
        canonical_forall_prefix_code_freeSupport_subset
          (x#(ProofT.schema_base [formula, certificate]))
          (fs_zfc_separation_core_code
            (x#(ProofT.schema_base [formula, certificate]))
            (x#(ProofT.schema_base [formula, certificate] + 4)))
          formula
          (ProofT.schema_base [formula, certificate] + 33)
          (ProofT.schema_base [formula, certificate] + 34)
          freeVariable hPrefixMember
      rcases hPrefix with hBinderCount | hRest
      · have hBinderCount' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate]) := by
          simpa [Term.freeSupport, set_variable] using hBinderCount
        exact False.elim (hNe0 hBinderCount')
      rcases hRest with hCore | hFormula
      · have hCore' :
            freeVariable = (SetSort.set,
              ProofT.schema_base [formula, certificate]) ∨
            freeVariable = (SetSort.set,
              ProofT.schema_base [formula, certificate] + 4) ∨
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate]) ∨
                freeVariable = (SetSort.set,
                  ProofT.schema_base [formula, certificate] + 4) ∨
                freeVariable = (SetSort.set,
                  ProofT.schema_base [formula, certificate]) := by
          simpa [fs_zfc_separation_core_code,
            fs_zfc_hilbert_iff_code, conjunction_formula_code_term,
            implication_formula_code_term, Term.freeSupport,
            Term.freeSupportList, finite_numeral_term_freeSupport] using hCore
        exact False.elim <| by
          grind
      · exact Or.inl hFormula
    ·
      simp only [fs_zfc_collection_condition_with_base, Formula.freeSupport] at hCollection
      have hBody₁ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate]) 0 _ hCollection
      have hNe0 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate]) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate]) 0 _)
          hCollection
      have hNe1 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate] + 1) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate] + 1) 0 _)
          (by simpa only [Formula.freeSupport] using hBody₁)
      have hBody₂ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate] + 1) 0 _ hBody₁
      have hNe2 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate] + 2) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate] + 2) 0 _)
          (by simpa only [Formula.freeSupport] using hBody₂)
      have hBody₃ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate] + 2) 0 _ hBody₂
      have hNe3 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate] + 3) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate] + 3) 0 _)
          (by simpa only [Formula.freeSupport] using hBody₃)
      have hBody₄ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate] + 3) 0 _ hBody₃
      have hNe4 : freeVariable ≠
          (SetSort.set, ProofT.schema_base [formula, certificate] + 4) := by
        intro hEqual
        subst hEqual
        exact (Formula.not_mem_freeSupport_closeFreeAt
          (σ := signature) SetSort.set
          (ProofT.schema_base [formula, certificate] + 4) 0 _)
          (by simpa only [Formula.freeSupport] using hBody₄)
      have hBody₅ :=
        hCloseSubset freeVariable SetSort.set
          (ProofT.schema_base [formula, certificate] + 4) 0 _ hBody₄
      simp only [Formula.freeSupport, List.mem_append] at hBody₅
      rcases hBody₅ with hCertificate | hRest
      · rcases hCertificate with hCertificate | hCertificateCode
        · exact Or.inr hCertificate
        · have hCertificateCode' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate]) ∨
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 1) := by
            simpa [fs_zfc_schema_certificate_term,
              fs_zfc_schema_payload_term,
              fs_zfc_schema_body_payload_term,
              Term.freeSupport, Term.freeSupportList,
              finite_numeral_term_freeSupport] using hCertificateCode
          exact False.elim <| by
            rcases hCertificateCode' with hEqual | hEqual
            · exact hNe0 hEqual
            · exact hNe1 hEqual
      rcases hRest with hBounds | hRest
      · rcases
            fs_zfc_schema_certificate_bounds_freeSupport_subset
              certificate (numₘ(1))
              (x#(ProofT.schema_base [formula, certificate]))
              (x#(ProofT.schema_base [formula, certificate] + 1))
              freeVariable hBounds with
          hCertificate | hSchemaTag | hParameter | hBodyToken
        · exact Or.inr hCertificate
        · exact False.elim <| by
            simp [finite_numeral_term_freeSupport] at hSchemaTag
        · exact False.elim <| hNe0 <| by
            simpa [Term.freeSupport, set_variable] using hParameter
        · exact False.elim <| hNe1 <| by
            simpa [Term.freeSupport, set_variable] using hBodyToken
      rcases hRest with hParameter | hRest
      · have hParameter' :
            freeVariable = (SetSort.set,
              ProofT.schema_base [formula, certificate]) := by
          simpa [Term.freeSupport, Term.freeSupportList,
            finite_numeral_term_freeSupport] using hParameter
        exact False.elim (hNe0 hParameter')
      rcases hRest with hSequence | hRest
      · have hSequence' :=
          nat_sequence_freeSupport_subset
            (x#(ProofT.schema_base [formula, certificate] + 2))
            (x#(ProofT.schema_base [formula, certificate] + 1))
            (ProofT.schema_base [formula, certificate] + 5)
            (ProofT.schema_base [formula, certificate] + 6)
            freeVariable hSequence
        rcases hSequence' with hBodyCode | hTokenCode
        · have hBodyCode' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 2) := by
            simpa [Term.freeSupport, set_variable] using hBodyCode
          exact False.elim (hNe2 hBodyCode')
        · have hTokenCode' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 1) := by
            simpa [Term.freeSupport, set_variable] using hTokenCode
          exact False.elim (hNe1 hTokenCode')
      rcases hRest with hClassifier | hRest
      · have hClassifier' :=
          canonical_project_formula_code_freeSupport_subset
            (Sₘ(Sₘ(x#(ProofT.schema_base [formula, certificate]))))
            (x#(ProofT.schema_base [formula, certificate] + 2))
            (ProofT.schema_base [formula, certificate] + 7)
            (ProofT.schema_base [formula, certificate] + 8)
            (ProofT.schema_base [formula, certificate] + 9)
            (ProofT.schema_base [formula, certificate] + 10)
            (ProofT.schema_base [formula, certificate] + 11)
            (ProofT.schema_base [formula, certificate] + 12)
            (ProofT.schema_base [formula, certificate] + 13)
            (ProofT.schema_base [formula, certificate] + 14)
            (ProofT.schema_base [formula, certificate] + 15)
            (ProofT.schema_base [formula, certificate] + 16)
            freeVariable hClassifier
        rcases hClassifier' with hEntry | hCode
        · exact False.elim <|
            hNotVariableList
              (ProofT.schema_base [formula, certificate]) hNe0 hEntry
        · have hCode' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 2) := by
            simpa [Term.freeSupport, set_variable] using hCode
          exact False.elim (hNe2 hCode')
      rcases hRest with hShiftFirst | hRest
      · have hShiftFirst' :=
          canonical_project_shift_code_freeSupport_subset
            (x#(ProofT.schema_base [formula, certificate]))
            (x#(ProofT.schema_base [formula, certificate] + 2))
            (x#(ProofT.schema_base [formula, certificate] + 3))
            (ProofT.schema_base [formula, certificate] + 17)
            (ProofT.schema_base [formula, certificate] + 18)
            (ProofT.schema_base [formula, certificate] + 19)
            freeVariable hShiftFirst
        rcases hShiftFirst' with hCutoff | hRest
        · have hCutoff' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate]) := by
            simpa [Term.freeSupport, set_variable] using hCutoff
          exact False.elim (hNe0 hCutoff')
        rcases hRest with hLeft | hRight
        · have hLeft' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 2) := by
            simpa [Term.freeSupport, set_variable] using hLeft
          exact False.elim (hNe2 hLeft')
        · have hRight' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 3) := by
            simpa [Term.freeSupport, set_variable] using hRight
          exact False.elim (hNe3 hRight')
      rcases hRest with hShiftSecond | hPrefixMember
      · have hShiftSecond' :=
          canonical_project_shift_code_freeSupport_subset
            (x#(ProofT.schema_base [formula, certificate]))
            (x#(ProofT.schema_base [formula, certificate] + 3))
            (x#(ProofT.schema_base [formula, certificate] + 4))
            (ProofT.schema_base [formula, certificate] + 25)
            (ProofT.schema_base [formula, certificate] + 26)
            (ProofT.schema_base [formula, certificate] + 27)
            freeVariable hShiftSecond
        rcases hShiftSecond' with hCutoff | hRest
        · have hCutoff' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate]) := by
            simpa [Term.freeSupport, set_variable] using hCutoff
          exact False.elim (hNe0 hCutoff')
        rcases hRest with hLeft | hRight
        · have hLeft' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 3) := by
            simpa [Term.freeSupport, set_variable] using hLeft
          exact False.elim (hNe3 hLeft')
        · have hRight' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate] + 4) := by
            simpa [Term.freeSupport, set_variable] using hRight
          exact False.elim (hNe4 hRight')
      have hPrefix :=
        canonical_forall_prefix_code_freeSupport_subset
          (x#(ProofT.schema_base [formula, certificate]))
          (fs_zfc_collection_core_code
            (x#(ProofT.schema_base [formula, certificate]))
            (x#(ProofT.schema_base [formula, certificate] + 3))
            (x#(ProofT.schema_base [formula, certificate] + 4)))
          formula
          (ProofT.schema_base [formula, certificate] + 33)
          (ProofT.schema_base [formula, certificate] + 34)
          freeVariable hPrefixMember
      rcases hPrefix with hBinderCount | hRest
      · have hBinderCount' :
              freeVariable = (SetSort.set,
                ProofT.schema_base [formula, certificate]) := by
          simpa [Term.freeSupport, set_variable] using hBinderCount
        exact False.elim (hNe0 hBinderCount')
      rcases hRest with hCore | hFormula
      · have hCore' :
            freeVariable = (SetSort.set,
              ProofT.schema_base [formula, certificate]) ∨
            freeVariable = (SetSort.set,
              ProofT.schema_base [formula, certificate] + 3) ∨
                freeVariable = (SetSort.set,
                  ProofT.schema_base [formula, certificate]) ∨
                freeVariable = (SetSort.set,
                  ProofT.schema_base [formula, certificate] + 4) := by
          simpa [fs_zfc_collection_core_code,
            fs_zfc_hilbert_iff_code, conjunction_formula_code_term,
            implication_formula_code_term, Term.freeSupport,
            Term.freeSupportList, finite_numeral_term_freeSupport] using hCore
        exact False.elim <| by
          grind
      · exact Or.inl hFormula

/--
replacement 对象 verifier 的公开自由支持仍只来自公式码与证书码。

固定表与 separation 分支复用现有 presentation 的支撑定理；新增工作仅是
消去 replacement 分支的十个内部见证及三段捕获规避替换规格。
-/
theorem fs_zfc_replacement_object_certificate_condition_freeSupport_subset
    (formula certificate : SetTerm) :
    ∀ freeVariable,
      freeVariable ∈
          Formula.freeSupport
            (fs_zfc_replacement_object_certificate_condition
              formula certificate) →
        freeVariable ∈ Term.freeSupport formula ∨
          freeVariable ∈ Term.freeSupport certificate := by
  intro freeVariable hMember
  change freeVariable ∈
      Formula.freeSupport
          (fs_zfc_fixed_axiom_table.condition formula certificate) ++
        Formula.freeSupport
          ((fs_zfc_separation_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate])) ∨ₘ
            (fs_zfc_replacement_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate]))) at hMember
  rcases List.mem_append.mp hMember with hFixed | hSchemas
  · apply fs_zfc_object_certificate_condition_freeSupport_subset
      formula certificate freeVariable
    change freeVariable ∈
      Formula.freeSupport
          (fs_zfc_fixed_axiom_table.condition formula certificate) ++
        Formula.freeSupport
          ((fs_zfc_separation_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate])) ∨ₘ
            (fs_zfc_collection_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate])))
    exact List.mem_append.mpr (Or.inl hFixed)
  · change freeVariable ∈
        Formula.freeSupport
            (fs_zfc_separation_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate])) ++
          Formula.freeSupport
            (fs_zfc_replacement_condition_with_base
              formula certificate
              (ProofT.schema_base [formula, certificate])) at hSchemas
    rcases List.mem_append.mp hSchemas with hSeparation | hReplacement
    · apply fs_zfc_object_certificate_condition_freeSupport_subset
        formula certificate freeVariable
      change freeVariable ∈
        Formula.freeSupport
            (fs_zfc_fixed_axiom_table.condition formula certificate) ++
          Formula.freeSupport
            ((fs_zfc_separation_condition_with_base
                formula certificate
                (ProofT.schema_base [formula, certificate])) ∨ₘ
              (fs_zfc_collection_condition_with_base
                formula certificate
                (ProofT.schema_base [formula, certificate])))
      exact List.mem_append.mpr <| Or.inr <|
        List.mem_append.mpr (Or.inl hSeparation)
    · by_cases hFormula :
          freeVariable ∈ Term.freeSupport formula
      · exact Or.inl hFormula
      by_cases hCertificate :
          freeVariable ∈ Term.freeSupport certificate
      · exact Or.inr hCertificate
      exfalso
      let base : FreeVarId :=
        ProofT.schema_base [formula, certificate]
      have hReplacementAt :
          freeVariable ∈
            Formula.freeSupport
              (fs_zfc_replacement_condition_with_base
                formula certificate base) := by
        simpa [base] using hReplacement
      rw [fs_zfc_replacement_condition_exists_shape] at hReplacementAt
      rcases
          (ProofT.SchemaPlugin.mem_freeSupport_witness_closure_iff
            freeVariable
            (List.range 10 |>.map (base + ·))
            (fs_zfc_replacement_condition_open_body
              formula certificate base)).mp hReplacementAt with
        ⟨hOpen, hFresh⟩
      have hFreshAt (offset : Nat) (hOffset : offset < 10) :
          freeVariable ≠ (SetSort.set, base + offset) :=
        hFresh (base + offset) <|
          List.mem_map.mpr
            ⟨offset, List.mem_range.mpr hOffset, rfl⟩
      have hVariableFresh (offset : Nat) (hOffset : offset < 10) :
          freeVariable ∉ Term.freeSupport (x#(base + offset)) := by
        intro hMember
        exact hFreshAt offset hOffset <| by
          simpa [Term.freeSupport, set_variable] using hMember
      simp only [
        fs_zfc_replacement_condition_open_body,
        fs_zfc_replacement_condition_body,
        fs_zfc_schema_condition_open_body,
        fs_zfc_replacement_condition_rest,
        Formula.freeSupport, List.mem_append] at hOpen
      rcases hOpen with hCertificateEquality | hBounds | hRest
      · rcases hCertificateEquality with hCertificateMember | hCode
        · exact hCertificate hCertificateMember
        · rcases
              fs_zfc_schema_certificate_term_freeSupport_subset
                (numₘ(2)) (x#base) (x#(base + 1))
                freeVariable hCode with
            hTag | hParameter | hBodyToken
          · simp [finite_numeral_term_freeSupport] at hTag
          · exact hVariableFresh 0 (by decide) hParameter
          · exact hVariableFresh 1 (by decide) hBodyToken
      · rcases
            fs_zfc_schema_certificate_bounds_freeSupport_subset
              certificate (numₘ(2)) (x#base) (x#(base + 1))
              freeVariable hBounds with
          hCertificateMember | hTag | hParameter | hBodyToken
        · exact hCertificate hCertificateMember
        · simp [finite_numeral_term_freeSupport] at hTag
        · exact hVariableFresh 0 (by decide) hParameter
        · exact hVariableFresh 1 (by decide) hBodyToken
      · rcases hRest with
          hParameter | hSequence | hClassifier |
          hFirstOutput | hSecondOutput | hUnderOne | hUnderTwo |
          hTemporary | hSwappedInput | hImage | hPrefix
        · exact hVariableFresh 0 (by decide) <| by
            simpa [Term.freeSupport, Term.freeSupportList] using hParameter
        · rcases
              nat_sequence_freeSupport_subset
                (x#(base + 2)) (x#(base + 1))
                (base + 10) (base + 11)
                freeVariable hSequence with
            hBodyCode | hBodyToken
          · exact hVariableFresh 2 (by decide) hBodyCode
          · exact hVariableFresh 1 (by decide) hBodyToken
        · rcases
              canonical_project_formula_code_freeSupport_subset
                (Sₘ(Sₘ(x#base))) (x#(base + 2))
                (base + 12) (base + 13)
                (base + 14) (base + 15)
                (base + 16) (base + 17)
                (base + 18) (base + 19)
                (base + 20) (base + 21)
                freeVariable hClassifier with
            hEntry | hBodyCode
          · exact hVariableFresh 0 (by decide) <| by
              simpa [Term.freeSupport, Term.freeSupportList] using hEntry
          · exact hVariableFresh 2 (by decide) hBodyCode
        · rcases
              canonical_project_shift_code_freeSupport_subset
                (Sₘ(Sₘ(x#base))) (x#(base + 2)) (x#(base + 3))
                (base + 22) (base + 23) (base + 24)
                freeVariable hFirstOutput with
            hCutoff | hBodyCode | hOutput
          · exact hVariableFresh 0 (by decide) <| by
              simpa [Term.freeSupport, Term.freeSupportList] using hCutoff
          · exact hVariableFresh 2 (by decide) hBodyCode
          · exact hVariableFresh 3 (by decide) hOutput
        · rcases
              canonical_project_shift_code_freeSupport_subset
                (Sₘ(x#base)) (x#(base + 2)) (x#(base + 4))
                (base + 30) (base + 31) (base + 32)
                freeVariable hSecondOutput with
            hCutoff | hBodyCode | hOutput
          · exact hVariableFresh 0 (by decide) <| by
              simpa [Term.freeSupport, Term.freeSupportList] using hCutoff
          · exact hVariableFresh 2 (by decide) hBodyCode
          · exact hVariableFresh 4 (by decide) hOutput
        · rcases
              canonical_project_shift_code_freeSupport_subset
                (x#base) (x#(base + 2)) (x#(base + 5))
                (base + 38) (base + 39) (base + 40)
                freeVariable hUnderOne with
            hCutoff | hBodyCode | hOutput
          · exact hVariableFresh 0 (by decide) hCutoff
          · exact hVariableFresh 2 (by decide) hBodyCode
          · exact hVariableFresh 5 (by decide) hOutput
        · rcases
              canonical_project_shift_code_freeSupport_subset
                (x#base) (x#(base + 5)) (x#(base + 6))
                (base + 46) (base + 47) (base + 48)
                freeVariable hUnderTwo with
            hCutoff | hSource | hOutput
          · exact hVariableFresh 0 (by decide) hCutoff
          · exact hVariableFresh 5 (by decide) hSource
          · exact hVariableFresh 6 (by decide) hOutput
        · rcases
              code_substitution_spec_freeSupport_subset
                (x#(base + 6))
                (canonical_binder_variable_code_term (Sₘ(Sₘ(Sₘ(x#base)))))
                (GodelQuotation.Numbered.named_variable_code
                  (GodelQuotation.free_name 0))
                (x#(base + 7))
                freeVariable hTemporary with
            hSource | hBound | hNamed | hOutput
          · exact hVariableFresh 6 (by decide) hSource
          · exact hVariableFresh 0 (by decide) <| by
              simpa [canonical_binder_variable_code_term,
                Term.freeSupport, Term.freeSupportList,
                finite_numeral_term_freeSupport] using hBound
          · rw [GodelQuotation.named_variable_code_freeSupport] at hNamed
            exact List.not_mem_nil hNamed
          · exact hVariableFresh 7 (by decide) hOutput
        · rcases
              code_substitution_spec_freeSupport_subset
                (x#(base + 7))
                (canonical_binder_variable_code_term (Sₘ(Sₘ(x#base))))
                (canonical_binder_variable_code_term (Sₘ(Sₘ(Sₘ(x#base)))))
                (x#(base + 8))
                freeVariable hSwappedInput with
            hSource | hInput | hOutputVariable | hOutput
          · exact hVariableFresh 7 (by decide) hSource
          · exact hVariableFresh 0 (by decide) <| by
              simpa [canonical_binder_variable_code_term,
                Term.freeSupport, Term.freeSupportList,
                finite_numeral_term_freeSupport] using hInput
          · exact hVariableFresh 0 (by decide) <| by
              simpa [canonical_binder_variable_code_term,
                Term.freeSupport, Term.freeSupportList,
                finite_numeral_term_freeSupport] using hOutputVariable
          · exact hVariableFresh 8 (by decide) hOutput
        · rcases
              code_substitution_spec_freeSupport_subset
                (x#(base + 8))
                (GodelQuotation.Numbered.named_variable_code
                  (GodelQuotation.free_name 0))
                (canonical_binder_variable_code_term (Sₘ(Sₘ(x#base))))
                (x#(base + 9))
                freeVariable hImage with
            hSource | hNamed | hInput | hOutput
          · exact hVariableFresh 8 (by decide) hSource
          · rw [GodelQuotation.named_variable_code_freeSupport] at hNamed
            exact List.not_mem_nil hNamed
          · exact hVariableFresh 0 (by decide) <| by
              simpa [canonical_binder_variable_code_term,
                Term.freeSupport, Term.freeSupportList,
                finite_numeral_term_freeSupport] using hInput
          · exact hVariableFresh 9 (by decide) hOutput
        · rcases
              canonical_forall_prefix_code_freeSupport_subset
                (x#base)
                (fs_zfc_replacement_core_code
                  (x#base) (x#(base + 3))
                  (x#(base + 4)) (x#(base + 9)))
                formula (base + 54) (base + 55)
                freeVariable hPrefix with
            hBinderCount | hCore | hFormulaMember
          · exact hVariableFresh 0 (by decide) hBinderCount
          · rcases
                fs_zfc_replacement_core_code_freeSupport_subset
                  (x#base) (x#(base + 3))
                  (x#(base + 4)) (x#(base + 9))
                  freeVariable hCore with
              hParameter | hFirst | hSecond | hImageCode
            · exact hVariableFresh 0 (by decide) hParameter
            · exact hVariableFresh 3 (by decide) hFirst
            · exact hVariableFresh 4 (by decide) hSecond
            · exact hVariableFresh 9 (by decide) hImageCode
          · exact hFormula hFormulaMember

/-! ## 负向 replay 的 verifier 支撑实例 -/

/-- separation+collection verifier 的支撑合同。 -/
def ProofT.ZFC.verifier_support :
    ProofT.VerifierSupport
      fs_zfc_object_certificate_verifier where
  freeSupport_subset := by
    intro formula certificate freeVariable hMember
    simpa [fs_zfc_object_certificate_verifier] using
      fs_zfc_object_certificate_condition_freeSupport_subset
        formula certificate freeVariable hMember

/-- separation+replacement verifier 的支撑合同。 -/
def ProofT.ZFCRep.verifier_support :
    ProofT.VerifierSupport
      fs_zfc_replacement_object_certificate_verifier where
  freeSupport_subset := by
    intro formula certificate freeVariable hMember
    simpa [fs_zfc_replacement_object_certificate_verifier] using
      fs_zfc_replacement_object_certificate_condition_freeSupport_subset
        formula certificate freeVariable hMember

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
