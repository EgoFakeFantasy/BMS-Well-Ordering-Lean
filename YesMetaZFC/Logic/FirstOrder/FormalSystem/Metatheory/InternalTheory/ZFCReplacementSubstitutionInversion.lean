import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCReplacementVerifier
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Substitution.SpecificationUniqueness

/-!
# replacement 三段 substitution 的对象层反演

本模块只证明 replacement verifier 中三段捕获规避替换的函数性。输入是任意对象
见证满足的三条规格，以及规范 replay 给出的三条规格；输出是最终 image 码等式。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open GodelQuotation

set_option autoImplicit false

private theorem fs_zfc_support_raw_substitution_spec_transport_variable
    {Γ : Context signature}
    (parameter : FreeVarId)
    (substitute source boundVariable replacement candidate : SetTerm)
    (hFresh :
      ReservedIdsFresh [310, 311]
        [substitute, source, boundVariable, replacement, candidate])
    (hSubstitute :
      Term.CheckCertificate substitute SetSort.set)
    (hSource :
      Term.CheckCertificate source SetSort.set)
    (hBoundVariable :
      Term.CheckCertificate boundVariable SetSort.set)
    (hReplacement :
      Term.CheckCertificate replacement SetSort.set)
    (hCandidate :
      Term.CheckCertificate candidate SetSort.set)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#parameter ≐ₘ substitute)
    (hSpecification :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          source boundVariable replacement candidate) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      code_substitution_spec
        (Term.substituteFree SetSort.set parameter substitute source)
        (Term.substituteFree
          SetSort.set parameter substitute boundVariable)
        (Term.substituteFree
          SetSort.set parameter substitute replacement)
        (Term.substituteFree
          SetSort.set parameter substitute candidate) := by
  let specification : SetFormula :=
    code_substitution_spec
      source boundVariable replacement candidate
  have hSubstitution :=
    GodelQuotation.code_substitution_spec_substituteFree
      parameter substitute source boundVariable replacement candidate
      hFresh hSubstitute hSource hBoundVariable hReplacement hCandidate
  have hSourceAt :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Formula.substituteFree
          SetSort.set parameter (x#parameter) specification := by
    simpa [specification, Formula.substituteFree_self] using
      hSpecification
  have hTransport :=
    FirstOrder.Derives.eq_subst_m
      (hRightCheck := hSubstitute) hEquality hSourceAt
  simpa [specification, hSubstitution] using hTransport

/--
三段 `code_substitution_spec` 唯一决定 replacement 的 image 码。

固定编号 `310`、`311`、`312` 只服务于 substitution 规格内部的存在消去；
`base ≥ 904` 保证这些编号不会捕获 verifier 的十个公开见证。
-/
theorem fs_zfc_support_raw_replacement_substitution_chain_unique
    {Γ : Context signature}
    (parameterCount : Nat)
    (base : FreeVarId)
    (underTwoCode temporaryCode swappedInputCode imageCode : SetTerm)
    (hBase : 904 ≤ base)
    (hUnderTwo :
      GodelQuotation.Numbered.CodeBoundary underTwoCode)
    (hTemporary :
      GodelQuotation.Numbered.CodeBoundary temporaryCode)
    (hSwappedInput :
      GodelQuotation.Numbered.CodeBoundary swappedInputCode)
    (hImage :
      GodelQuotation.Numbered.CodeBoundary imageCode)
    (hParameterEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#base ≐ₘ numₘ(parameterCount))
    (hUnderTwoEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#(base + 6) ≐ₘ underTwoCode)
    (hSpecificationOne :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          (x#(base + 6))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(x#base)))))
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          (x#(base + 7)))
    (hSpecificationTwo :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          (x#(base + 7))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(x#base))))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(x#base)))))
          (x#(base + 8)))
    (hSpecificationThree :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          (x#(base + 8))
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(x#base))))
          (x#(base + 9)))
    (hCanonicalOne :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          underTwoCode
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          temporaryCode))
    (hCanonicalTwo :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          temporaryCode
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(numₘ(parameterCount)))))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(numₘ(parameterCount))))))
          swappedInputCode))
    (hCanonicalThree :
      Derives fs_zfc_support_raw_theory [] (
        code_substitution_spec
          swappedInputCode
          (GodelQuotation.Numbered.named_variable_code
            (GodelQuotation.free_name 0))
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(numₘ(parameterCount)))))
          imageCode)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      x#(base + 9) ≐ₘ imageCode := by
  let inputVariable : SetTerm :=
    canonical_binder_variable_code_term
      (Sₘ(Sₘ(numₘ(parameterCount))))
  let outputVariable : SetTerm :=
    canonical_binder_variable_code_term
      (Sₘ(Sₘ(Sₘ(numₘ(parameterCount)))))
  let temporaryVariable : SetTerm :=
    GodelQuotation.Numbered.named_variable_code
      (GodelQuotation.free_name 0)
  have hNumeral :
      GodelQuotation.Numbered.CodeBoundary (numₘ(parameterCount)) :=
    ⟨finite_numeral_term_admissible parameterCount,
      finite_numeral_term_freeSupport parameterCount⟩
  have hInput :
      GodelQuotation.Numbered.CodeBoundary inputVariable := by
    constructor
    · exact canonical_binder_variable_code_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (finite_numeral_term_admissible parameterCount)))
    · simp [inputVariable, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport]
  have hOutput :
      GodelQuotation.Numbered.CodeBoundary outputVariable := by
    constructor
    · exact canonical_binder_variable_code_term_admissible _
        (successor_term_admissible _
          (successor_term_admissible _
            (successor_term_admissible _
              (finite_numeral_term_admissible parameterCount))))
    · simp [outputVariable, Term.freeSupport,
        Term.freeSupportList, finite_numeral_term_freeSupport]
  have hTemporaryVariable :
      GodelQuotation.Numbered.CodeBoundary temporaryVariable :=
    ⟨variable_code_term_admissible _
        (finite_numeral_term_admissible
          (GodelQuotation.free_name 0)),
      by
        simp [temporaryVariable,
          GodelQuotation.named_variable_code_freeSupport]⟩
  have hVariableCheck (offset : Nat) :
      Term.CheckCertificate (x#(base + offset)) SetSort.set :=
    Term.check_admissible_complete
      (set_variable_admissible (base + offset))
  have hNumeralFixed
      (sourceId : FreeVarId)
      (substitute : SetTerm)
      (number : Nat) :
      Term.substituteFree SetSort.set sourceId substitute
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hClosedFixed
      (sourceId : FreeVarId)
      (substitute term : SetTerm)
      (hTerm : GodelQuotation.Numbered.CodeBoundary term) :
      Term.substituteFree SetSort.set sourceId substitute term =
        term := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [hTerm.2]
    exact List.not_mem_nil
  have hReservedVariable
      (offset : Nat) (id : FreeVarId)
      (hId : id ∈ [310, 311, 312]) :
      (SetSort.set, id) ∉
        Term.freeSupport (x#(base + offset)) := by
    intro hMember
    change (SetSort.set, id) ∈
      [(SetSort.set, base + offset)] at hMember
    have hEquality :
        id = base + offset :=
      congrArg Prod.snd (List.mem_singleton.mp hMember)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
    have hBaseOffset : base ≤ base + offset :=
      Nat.le_add_right base offset
    rcases hId with rfl | rfl | rfl
    · exact
        (Nat.ne_of_lt <|
          Nat.lt_of_lt_of_le
            (by decide : 310 < 904)
            (Nat.le_trans hBase hBaseOffset))
          hEquality
    · exact
        (Nat.ne_of_lt <|
          Nat.lt_of_lt_of_le
            (by decide : 311 < 904)
            (Nat.le_trans hBase hBaseOffset))
          hEquality
    · exact
        (Nat.ne_of_lt <|
          Nat.lt_of_lt_of_le
            (by decide : 312 < 904)
            (Nat.le_trans hBase hBaseOffset))
          hEquality
  have hReservedPairToTriple
      (id : FreeVarId)
      (hId : id ∈ [310, 311]) :
      id ∈ [310, 311, 312] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hId ⊢
    rcases hId with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hReservedRawInput
      (id : FreeVarId) (hId : id ∈ [310, 311, 312]) :
      (SetSort.set, id) ∉
        Term.freeSupport
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(x#base)))) := by
    simpa [canonical_binder_variable_code_term,
      canonical_binder_name_term, Term.freeSupport,
      Term.freeSupportList] using
      hReservedVariable 0 id hId
  have hReservedRawOutput
      (id : FreeVarId) (hId : id ∈ [310, 311, 312]) :
      (SetSort.set, id) ∉
        Term.freeSupport
          (canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(x#base))))) := by
    simpa [canonical_binder_variable_code_term,
      canonical_binder_name_term, Term.freeSupport,
      Term.freeSupportList] using
      hReservedVariable 0 id hId
  have hClosedFresh
      (term : SetTerm)
      (hTerm : GodelQuotation.Numbered.CodeBoundary term)
      (id : FreeVarId) :
      (SetSort.set, id) ∉ Term.freeSupport term := by
    rw [hTerm.2]
    exact List.not_mem_nil
  have hFreshRawOne :
      ReservedIdsFresh [310, 311]
        [numₘ(parameterCount), x#(base + 6),
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(x#base)))),
          temporaryVariable, x#(base + 7)] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh _ hNumeral id
    · exact hReservedVariable 6 id
        (hReservedPairToTriple id hId)
    · exact hReservedRawOutput id
        (hReservedPairToTriple id hId)
    · exact hClosedFresh _ hTemporaryVariable id
    · exact hReservedVariable 7 id
        (hReservedPairToTriple id hId)
  have hSpecificationOneParameter :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          (x#(base + 6)) outputVariable temporaryVariable
          (x#(base + 7)) := by
    have hTransport :=
      fs_zfc_support_raw_substitution_spec_transport_variable
        base (numₘ(parameterCount))
        (x#(base + 6))
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(Sₘ(x#base)))))
        temporaryVariable (x#(base + 7))
        hFreshRawOne hNumeral.check_certificate
        (hVariableCheck 6)
        (Term.check_admissible_complete <|
          canonical_binder_variable_code_term_admissible _
            (successor_term_admissible _
              (successor_term_admissible _
                (successor_term_admissible _
                  (set_variable_admissible base)))))
        hTemporaryVariable.check_certificate
        (hVariableCheck 7)
        hParameterEquality hSpecificationOne
    simpa [inputVariable, outputVariable, temporaryVariable,
      Term.substituteFree, set_variable, hNumeralFixed] using hTransport
  have hFreshSourceOne :
      ReservedIdsFresh [310, 311]
        [underTwoCode, x#(base + 6), outputVariable,
          temporaryVariable, x#(base + 7)] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh _ hUnderTwo id
    · exact hReservedVariable 6 id
        (hReservedPairToTriple id hId)
    · exact hClosedFresh _ hOutput id
    · exact hClosedFresh _ hTemporaryVariable id
    · exact hReservedVariable 7 id
        (hReservedPairToTriple id hId)
  have hSpecificationOneCanonical :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          underTwoCode outputVariable temporaryVariable
          (x#(base + 7)) := by
    have hTransport :=
      fs_zfc_support_raw_substitution_spec_transport_variable
        (base + 6) underTwoCode
        (x#(base + 6)) outputVariable temporaryVariable
        (x#(base + 7))
        hFreshSourceOne hUnderTwo.check_certificate
        (hVariableCheck 6) hOutput.check_certificate
        hTemporaryVariable.check_certificate (hVariableCheck 7)
        hUnderTwoEquality hSpecificationOneParameter
    have hOutputFixed :
        Term.substituteFree SetSort.set (base + 6)
            underTwoCode outputVariable =
          outputVariable :=
      hClosedFixed (base + 6) underTwoCode outputVariable hOutput
    have hTemporaryVariableFixed :
        Term.substituteFree SetSort.set (base + 6)
            underTwoCode temporaryVariable =
          temporaryVariable :=
      hClosedFixed (base + 6) underTwoCode
        temporaryVariable hTemporaryVariable
    simpa [Term.substituteFree, set_variable,
      hOutputFixed, hTemporaryVariableFixed] using hTransport
  have hFreshUniqueOne :
      ReservedIdsFresh [310, 311, 312]
        [underTwoCode, outputVariable, temporaryVariable,
          x#(base + 7), temporaryCode] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh _ hUnderTwo id
    · exact hClosedFresh _ hOutput id
    · exact hClosedFresh _ hTemporaryVariable id
    · exact hReservedVariable 7 id hId
    · exact hClosedFresh _ hTemporary id
  have hTemporaryEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#(base + 7) ≐ₘ temporaryCode := by
    have hUnique :=
      fs_zfc_support_raw_derives_of_godel_quotation <|
        GodelQuotation.code_substitution_spec_unique_without_precondition
          underTwoCode outputVariable temporaryVariable
          (x#(base + 7)) temporaryCode hFreshUniqueOne
          hUnderTwo.1 hOutput.1 hTemporaryVariable.1
          (set_variable_admissible (base + 7)) hTemporary.1
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) hUnique)
        hSpecificationOneCanonical)
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (by simpa [outputVariable, temporaryVariable] using
          hCanonicalOne))
  have hFreshRawTwo :
      ReservedIdsFresh [310, 311]
        [numₘ(parameterCount), x#(base + 7),
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(x#base))),
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(Sₘ(x#base)))),
          x#(base + 8)] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh _ hNumeral id
    · exact hReservedVariable 7 id
        (hReservedPairToTriple id hId)
    · exact hReservedRawInput id
        (hReservedPairToTriple id hId)
    · exact hReservedRawOutput id
        (hReservedPairToTriple id hId)
    · exact hReservedVariable 8 id
        (hReservedPairToTriple id hId)
  have hSpecificationTwoParameter :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          (x#(base + 7)) inputVariable outputVariable
          (x#(base + 8)) := by
    have hTransport :=
      fs_zfc_support_raw_substitution_spec_transport_variable
        base (numₘ(parameterCount))
        (x#(base + 7))
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(x#base))))
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(Sₘ(x#base)))))
        (x#(base + 8))
        hFreshRawTwo hNumeral.check_certificate
        (hVariableCheck 7)
        (Term.check_admissible_complete <|
          canonical_binder_variable_code_term_admissible _
            (successor_term_admissible _
              (successor_term_admissible _
                (set_variable_admissible base))))
        (Term.check_admissible_complete <|
          canonical_binder_variable_code_term_admissible _
            (successor_term_admissible _
              (successor_term_admissible _
                (successor_term_admissible _
                  (set_variable_admissible base)))))
        (hVariableCheck 8)
        hParameterEquality hSpecificationTwo
    simpa [inputVariable, outputVariable,
      Term.substituteFree, set_variable, hNumeralFixed] using hTransport
  have hFreshSourceTwo :
      ReservedIdsFresh [310, 311]
        [temporaryCode, x#(base + 7), inputVariable,
          outputVariable, x#(base + 8)] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh _ hTemporary id
    · exact hReservedVariable 7 id
        (hReservedPairToTriple id hId)
    · exact hClosedFresh _ hInput id
    · exact hClosedFresh _ hOutput id
    · exact hReservedVariable 8 id
        (hReservedPairToTriple id hId)
  have hSpecificationTwoCanonical :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          temporaryCode inputVariable outputVariable
          (x#(base + 8)) := by
    have hTransport :=
      fs_zfc_support_raw_substitution_spec_transport_variable
        (base + 7) temporaryCode
        (x#(base + 7)) inputVariable outputVariable
        (x#(base + 8))
        hFreshSourceTwo hTemporary.check_certificate
        (hVariableCheck 7) hInput.check_certificate
        hOutput.check_certificate (hVariableCheck 8)
        hTemporaryEquality hSpecificationTwoParameter
    have hInputFixed :
        Term.substituteFree SetSort.set (base + 7)
            temporaryCode inputVariable =
          inputVariable :=
      hClosedFixed (base + 7) temporaryCode inputVariable hInput
    have hOutputFixed :
        Term.substituteFree SetSort.set (base + 7)
            temporaryCode outputVariable =
          outputVariable :=
      hClosedFixed (base + 7) temporaryCode outputVariable hOutput
    simpa [Term.substituteFree, set_variable,
      hInputFixed, hOutputFixed] using hTransport
  have hFreshUniqueTwo :
      ReservedIdsFresh [310, 311, 312]
        [temporaryCode, inputVariable, outputVariable,
          x#(base + 8), swappedInputCode] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh _ hTemporary id
    · exact hClosedFresh _ hInput id
    · exact hClosedFresh _ hOutput id
    · exact hReservedVariable 8 id hId
    · exact hClosedFresh _ hSwappedInput id
  have hSwappedInputEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        x#(base + 8) ≐ₘ swappedInputCode := by
    have hUnique :=
      fs_zfc_support_raw_derives_of_godel_quotation <|
        GodelQuotation.code_substitution_spec_unique_without_precondition
          temporaryCode inputVariable outputVariable
          (x#(base + 8)) swappedInputCode hFreshUniqueTwo
          hTemporary.1 hInput.1 hOutput.1
          (set_variable_admissible (base + 8)) hSwappedInput.1
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) hUnique)
        hSpecificationTwoCanonical)
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (by simpa [inputVariable, outputVariable] using
          hCanonicalTwo))
  have hFreshRawThree :
      ReservedIdsFresh [310, 311]
        [numₘ(parameterCount), x#(base + 8),
          temporaryVariable,
          canonical_binder_variable_code_term
            (Sₘ(Sₘ(x#base))),
          x#(base + 9)] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh _ hNumeral id
    · exact hReservedVariable 8 id
        (hReservedPairToTriple id hId)
    · exact hClosedFresh _ hTemporaryVariable id
    · exact hReservedRawInput id
        (hReservedPairToTriple id hId)
    · exact hReservedVariable 9 id
        (hReservedPairToTriple id hId)
  have hSpecificationThreeParameter :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          (x#(base + 8)) temporaryVariable inputVariable
          (x#(base + 9)) := by
    have hTransport :=
      fs_zfc_support_raw_substitution_spec_transport_variable
        base (numₘ(parameterCount))
        (x#(base + 8)) temporaryVariable
        (canonical_binder_variable_code_term
          (Sₘ(Sₘ(x#base))))
        (x#(base + 9))
        hFreshRawThree hNumeral.check_certificate
        (hVariableCheck 8) hTemporaryVariable.check_certificate
        (Term.check_admissible_complete <|
          canonical_binder_variable_code_term_admissible _
            (successor_term_admissible _
              (successor_term_admissible _
                (set_variable_admissible base))))
        (hVariableCheck 9)
        hParameterEquality hSpecificationThree
    simpa [inputVariable, temporaryVariable,
      Term.substituteFree, set_variable, hNumeralFixed] using hTransport
  have hFreshSourceThree :
      ReservedIdsFresh [310, 311]
        [swappedInputCode, x#(base + 8), temporaryVariable,
          inputVariable, x#(base + 9)] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh _ hSwappedInput id
    · exact hReservedVariable 8 id
        (hReservedPairToTriple id hId)
    · exact hClosedFresh _ hTemporaryVariable id
    · exact hClosedFresh _ hInput id
    · exact hReservedVariable 9 id
        (hReservedPairToTriple id hId)
  have hSpecificationThreeCanonical :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        code_substitution_spec
          swappedInputCode temporaryVariable inputVariable
          (x#(base + 9)) := by
    have hTransport :=
      fs_zfc_support_raw_substitution_spec_transport_variable
        (base + 8) swappedInputCode
        (x#(base + 8)) temporaryVariable inputVariable
        (x#(base + 9))
        hFreshSourceThree hSwappedInput.check_certificate
        (hVariableCheck 8) hTemporaryVariable.check_certificate
        hInput.check_certificate (hVariableCheck 9)
        hSwappedInputEquality hSpecificationThreeParameter
    have hTemporaryVariableFixed :
        Term.substituteFree SetSort.set (base + 8)
            swappedInputCode temporaryVariable =
          temporaryVariable :=
      hClosedFixed (base + 8) swappedInputCode
        temporaryVariable hTemporaryVariable
    have hInputFixed :
        Term.substituteFree SetSort.set (base + 8)
            swappedInputCode inputVariable =
          inputVariable :=
      hClosedFixed (base + 8) swappedInputCode inputVariable hInput
    simpa [Term.substituteFree, set_variable,
      hTemporaryVariableFixed, hInputFixed] using hTransport
  have hFreshUniqueThree :
      ReservedIdsFresh [310, 311, 312]
        [swappedInputCode, temporaryVariable, inputVariable,
          x#(base + 9), imageCode] := by
    intro term hTerm id hId
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hTerm
    rcases hTerm with rfl | rfl | rfl | rfl | rfl
    · exact hClosedFresh _ hSwappedInput id
    · exact hClosedFresh _ hTemporaryVariable id
    · exact hClosedFresh _ hInput id
    · exact hReservedVariable 9 id hId
    · exact hClosedFresh _ hImage id
  have hUnique :=
    fs_zfc_support_raw_derives_of_godel_quotation <|
      GodelQuotation.code_substitution_spec_unique_without_precondition
        swappedInputCode temporaryVariable inputVariable
        (x#(base + 9)) imageCode hFreshUniqueThree
        hSwappedInput.1 hTemporaryVariable.1 hInput.1
        (set_variable_admissible (base + 9)) hImage.1
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hUnique)
      hSpecificationThreeCanonical)
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (by simpa [inputVariable, temporaryVariable] using
        hCanonicalThree))

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
