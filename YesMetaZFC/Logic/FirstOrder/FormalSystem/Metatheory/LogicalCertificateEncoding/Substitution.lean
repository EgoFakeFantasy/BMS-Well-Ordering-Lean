import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Support

/-!
# 完整逻辑证书条件的闭项替换

本模块只处理显式 binder 版本的捕获规避替换。自动 fresh 包装器适合闭合入口，
不适合作为需要对象层换元的关系接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

namespace CertifiedProof

/--
对内部 binder 新鲜的替换逐参数穿过代码替换规格。

该关系内部只关闭编号 `310`、`311`；公开的四个代码项可以任意含自由变量，
调用者只需精确保证替换目标与替换项都避开这两个 binder。
-/
theorem code_substitution_spec_substitute_fresh
    (sourceCode variableCode replacementCode resultCode substitute
      sourceCodeResult variableCodeResult replacementCodeResult
      resultCodeResult : SetTerm)
    (sourceId : FreeVarId)
    (hSourceFresh : sourceId ∉ [310, 311])
    (hSubstituteAdmissible :
      Term.Admissible substitute SetSort.set)
    (hSubstituteFresh :
      ∀ closedId,
        closedId ∈ [310, 311] →
          (SetSort.set, closedId) ∉ Term.freeSupport substitute)
    (hSourceCodeSubstitution :
      Term.substituteFree SetSort.set sourceId substitute sourceCode =
        sourceCodeResult)
    (hVariableCodeSubstitution :
      Term.substituteFree SetSort.set sourceId substitute variableCode =
        variableCodeResult)
    (hReplacementCodeSubstitution :
      Term.substituteFree SetSort.set sourceId substitute replacementCode =
        replacementCodeResult)
    (hResultCodeSubstitution :
      Term.substituteFree SetSort.set sourceId substitute resultCode =
        resultCodeResult) :
    Formula.substituteFree SetSort.set sourceId substitute
        (code_substitution_spec
          sourceCode variableCode replacementCode resultCode) =
      code_substitution_spec
        sourceCodeResult variableCodeResult
        replacementCodeResult resultCodeResult := by
  have hSourceNe310 : sourceId ≠ 310 := by
    intro hEq
    apply hSourceFresh
    simp [hEq]
  have hSourceNe311 : sourceId ≠ 311 := by
    intro hEq
    apply hSourceFresh
    simp [hEq]
  have h310 (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId substitute
          (Formula.closeFreeAt SetSort.set 310 depth formula) =
        Formula.closeFreeAt SetSort.set 310 depth
          (Formula.substituteFree SetSort.set sourceId substitute
            formula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId 310 depth substitute formula
      hSourceNe310 hSubstituteAdmissible.2
      (hSubstituteFresh 310 (by simp))).symm
  have h311 (depth : Nat) (formula : SetFormula) :
      Formula.substituteFree SetSort.set sourceId substitute
          (Formula.closeFreeAt SetSort.set 311 depth formula) =
        Formula.closeFreeAt SetSort.set 311 depth
          (Formula.substituteFree SetSort.set sourceId substitute
            formula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId 311 depth substitute formula
      hSourceNe311 hSubstituteAdmissible.2
      (hSubstituteFresh 311 (by simp))).symm
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId substitute
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  unfold code_substitution_spec
  simp [
    substitution_piece_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable, h310, h311,

    Ne.symm hSourceNe310, Ne.symm hSourceNe311,
    hNumeralFixed,
    hSourceCodeSubstitution,
    hVariableCodeSubstitution,
    hReplacementCodeSubstitution,
    hResultCodeSubstitution]

/--
捕获规避替换逐参数穿过 canonical 全称闭包关系。

`310`、`311` 属于代码替换规格，`460` 至 `470` 属于闭包与 binder-shift
关系；调用者只需精确给出替换项对这些内部 binder 的新鲜性。
-/
theorem canonical_forall_closure_code_condition_substitute_fresh
    (sourceCode variableCode targetCode replacement
      sourceCodeResult variableCodeResult targetCodeResult : SetTerm)
    (sourceId : FreeVarId)
    (hSourceFresh :
      sourceId ∉
        [310, 311, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ closedId,
        closedId ∈
            [310, 311, 460, 461, 462, 463, 464,
              465, 466, 467, 468, 469, 470] →
          (SetSort.set, closedId) ∉
            Term.freeSupport replacement)
    (hSourceCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sourceCode =
        sourceCodeResult)
    (hVariableCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement variableCode =
        variableCodeResult)
    (hTargetCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement targetCode =
        targetCodeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) =
      canonical_forall_closure_code_condition
        sourceCodeResult variableCodeResult targetCodeResult := by
  have hSourceNe
      (closedId : FreeVarId)
      (hClosedId :
        closedId ∈
          [310, 311, 460, 461, 462, 463, 464,
            465, 466, 467, 468, 469, 470]) :
      sourceId ≠ closedId := by
    intro hEq
    subst closedId
    exact hSourceFresh hClosedId
  have hCommute
      (closedId depth : Nat)
      (formula : SetFormula)
      (hClosedId :
        closedId ∈
          [310, 311, 460, 461, 462, 463, 464,
            465, 466, 467, 468, 469, 470]) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set sourceId replacement
            formula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId closedId depth replacement formula
      (hSourceNe closedId hClosedId)
      hReplacementAdmissible.2
      (hReplacementFresh closedId hClosedId)).symm
  have h310 (depth : Nat) (formula : SetFormula) :=
    hCommute 310 depth formula (by simp)
  have h311 (depth : Nat) (formula : SetFormula) :=
    hCommute 311 depth formula (by simp)
  have h460 (depth : Nat) (formula : SetFormula) :=
    hCommute 460 depth formula (by simp)
  have h461 (depth : Nat) (formula : SetFormula) :=
    hCommute 461 depth formula (by simp)
  have h462 (depth : Nat) (formula : SetFormula) :=
    hCommute 462 depth formula (by simp)
  have h463 (depth : Nat) (formula : SetFormula) :=
    hCommute 463 depth formula (by simp)
  have h464 (depth : Nat) (formula : SetFormula) :=
    hCommute 464 depth formula (by simp)
  have h465 (depth : Nat) (formula : SetFormula) :=
    hCommute 465 depth formula (by simp)
  have h466 (depth : Nat) (formula : SetFormula) :=
    hCommute 466 depth formula (by simp)
  have h467 (depth : Nat) (formula : SetFormula) :=
    hCommute 467 depth formula (by simp)
  have h468 (depth : Nat) (formula : SetFormula) :=
    hCommute 468 depth formula (by simp)
  have h469 (depth : Nat) (formula : SetFormula) :=
    hCommute 469 depth formula (by simp)
  have h470 (depth : Nat) (formula : SetFormula) :=
    hCommute 470 depth formula (by simp)
  have hNe310 : sourceId ≠ 310 :=
    hSourceNe 310 (by simp)
  have hNe311 : sourceId ≠ 311 :=
    hSourceNe 311 (by simp)
  have hNe460 : sourceId ≠ 460 :=
    hSourceNe 460 (by simp)
  have hNe461 : sourceId ≠ 461 :=
    hSourceNe 461 (by simp)
  have hNe462 : sourceId ≠ 462 :=
    hSourceNe 462 (by simp)
  have hNe463 : sourceId ≠ 463 :=
    hSourceNe 463 (by simp)
  have hNe464 : sourceId ≠ 464 :=
    hSourceNe 464 (by simp)
  have hNe465 : sourceId ≠ 465 :=
    hSourceNe 465 (by simp)
  have hNe466 : sourceId ≠ 466 :=
    hSourceNe 466 (by simp)
  have hNe467 : sourceId ≠ 467 :=
    hSourceNe 467 (by simp)
  have hNe468 : sourceId ≠ 468 :=
    hSourceNe 468 (by simp)
  have hNe469 : sourceId ≠ 469 :=
    hSourceNe 469 (by simp)
  have hNe470 : sourceId ≠ 470 :=
    hSourceNe 470 (by simp)
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  unfold canonical_forall_closure_code_condition
  unfold canonical_forall_closure_code_condition_with_ids
  simp [
    canonical_free_variable_code_condition_with_id,
    canonical_binder_shift_code_condition_with_ids,
    canonical_binder_shift_token_condition_with_ids,
    code_substitution_spec, substitution_piece_condition,
    Formula.substituteFree, Term.substituteFree,
    set_variable,
    h310, h311, h460, h461, h462, h463, h464,
    h465, h466, h467, h468, h469, h470,



    Ne.symm hNe310, Ne.symm hNe311,
    Ne.symm hNe460, Ne.symm hNe461, Ne.symm hNe462,
    Ne.symm hNe463, Ne.symm hNe464, Ne.symm hNe465,
    Ne.symm hNe466, Ne.symm hNe467, Ne.symm hNe468,
    Ne.symm hNe469, Ne.symm hNe470,
    hNumeralFixed,
    hSourceCodeSubstitution,
    hVariableCodeSubstitution,
    hTargetCodeSubstitution]

/--
闭代码替换逐参数穿过 canonical 全称闭包关系。

闭项自动避开全部内部 binder；该接口是精确新鲜性版本的直接特例。
-/
theorem canonical_forall_closure_code_condition_substitute_closed
    (sourceCode variableCode targetCode replacement
      sourceCodeResult variableCodeResult targetCodeResult : SetTerm)
    (sourceId : FreeVarId)
    (hSourceFresh :
      sourceId ∉
        [310, 311, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementClosed :
      Term.freeSupport replacement = [])
    (hSourceCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sourceCode =
        sourceCodeResult)
    (hVariableCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement variableCode =
        variableCodeResult)
    (hTargetCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement targetCode =
        targetCodeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (canonical_forall_closure_code_condition
          sourceCode variableCode targetCode) =
      canonical_forall_closure_code_condition
        sourceCodeResult variableCodeResult targetCodeResult := by
  exact canonical_forall_closure_code_condition_substitute_fresh
    sourceCode variableCode targetCode replacement
    sourceCodeResult variableCodeResult targetCodeResult
    sourceId hSourceFresh hReplacementAdmissible
    (fun closedId _ => by
      rw [hReplacementClosed]
      exact List.not_mem_nil)
    hSourceCodeSubstitution
    hVariableCodeSubstitution
    hTargetCodeSubstitution

/--
捕获规避替换逐参数穿过 canonical 全称开式关系。

该关系复用 `460` 至 `468` 作为局部 binder；它与闭包关系处于不同合取支，
因此编号复用不产生捕获，也不扩大 transcript 的保留编号集合。
-/
theorem canonical_forall_open_code_condition_substitute_fresh
    (sourceCode variableCode targetCode replacement
      sourceCodeResult variableCodeResult targetCodeResult : SetTerm)
    (sourceId : FreeVarId)
    (hSourceFresh :
      sourceId ∉ [460, 461, 462, 463, 464, 465, 466, 467, 468])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ closedId,
        closedId ∈ [460, 461, 462, 463, 464, 465, 466, 467, 468] →
          (SetSort.set, closedId) ∉ Term.freeSupport replacement)
    (hSourceCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement sourceCode =
        sourceCodeResult)
    (hVariableCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement variableCode =
        variableCodeResult)
    (hTargetCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement targetCode =
        targetCodeResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (canonical_forall_open_code_condition
          sourceCode variableCode targetCode) =
      canonical_forall_open_code_condition
        sourceCodeResult variableCodeResult targetCodeResult := by
  have hSourceNe
      (closedId : FreeVarId)
      (hClosedId :
        closedId ∈ [460, 461, 462, 463, 464, 465, 466, 467, 468]) :
      sourceId ≠ closedId := by
    intro hEq
    subst closedId
    exact hSourceFresh hClosedId
  have hCommute
      (closedId depth : Nat)
      (formula : SetFormula)
      (hClosedId :
        closedId ∈ [460, 461, 462, 463, 464, 465, 466, 467, 468]) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set closedId depth formula) =
        Formula.closeFreeAt SetSort.set closedId depth
          (Formula.substituteFree SetSort.set sourceId replacement formula) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId closedId depth replacement formula
      (hSourceNe closedId hClosedId)
      hReplacementAdmissible.2
      (hReplacementFresh closedId hClosedId)).symm
  have h460 (depth : Nat) (formula : SetFormula) :=
    hCommute 460 depth formula (by simp)
  have h461 (depth : Nat) (formula : SetFormula) :=
    hCommute 461 depth formula (by simp)
  have h462 (depth : Nat) (formula : SetFormula) :=
    hCommute 462 depth formula (by simp)
  have h463 (depth : Nat) (formula : SetFormula) :=
    hCommute 463 depth formula (by simp)
  have h464 (depth : Nat) (formula : SetFormula) :=
    hCommute 464 depth formula (by simp)
  have h465 (depth : Nat) (formula : SetFormula) :=
    hCommute 465 depth formula (by simp)
  have h466 (depth : Nat) (formula : SetFormula) :=
    hCommute 466 depth formula (by simp)
  have h467 (depth : Nat) (formula : SetFormula) :=
    hCommute 467 depth formula (by simp)
  have h468 (depth : Nat) (formula : SetFormula) :=
    hCommute 468 depth formula (by simp)
  have hNe460 : sourceId ≠ 460 := hSourceNe 460 (by simp)
  have hNe461 : sourceId ≠ 461 := hSourceNe 461 (by simp)
  have hNe462 : sourceId ≠ 462 := hSourceNe 462 (by simp)
  have hNe463 : sourceId ≠ 463 := hSourceNe 463 (by simp)
  have hNe464 : sourceId ≠ 464 := hSourceNe 464 (by simp)
  have hNe465 : sourceId ≠ 465 := hSourceNe 465 (by simp)
  have hNe466 : sourceId ≠ 466 := hSourceNe 466 (by simp)
  have hNe467 : sourceId ≠ 467 := hSourceNe 467 (by simp)
  have hNe468 : sourceId ≠ 468 := hSourceNe 468 (by simp)
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  unfold canonical_forall_open_code_condition
  unfold canonical_forall_open_code_condition_with_ids
  simp [
    canonical_forall_open_token_condition_with_ids,
    canonical_forall_open_reverse_guard_with_id,
    canonical_binder_shift_token_condition_with_ids,
    Formula.substituteFree, Term.substituteFree, set_variable,
    h460, h461, h462, h463, h464, h465, h466, h467, h468,


    Ne.symm hNe460, Ne.symm hNe461, Ne.symm hNe462,
    Ne.symm hNe463, Ne.symm hNe464, Ne.symm hNe465,
    Ne.symm hNe466, Ne.symm hNe467, Ne.symm hNe468,
    hNumeralFixed,
    hSourceCodeSubstitution,
    hVariableCodeSubstitution,
    hTargetCodeSubstitution]

/--
Canonical 全称开式关系沿三个闭代码等式同时运输。

该接口只使用开式关系的替换自然性，因此适用于任意对象理论与上下文。
-/
theorem canonical_forall_open_code_condition_of_equalities
    {T : SetTheory} {Γ : Context signature}
    (source variableTerm target
      sourceCode variableCode targetCode : SetTerm)
    (hSource : GodelQuotation.Numbered.CodeBoundary source)
    (hVariable :
      GodelQuotation.Numbered.CodeBoundary variableTerm)
    (hTarget : GodelQuotation.Numbered.CodeBoundary target)
    (hSourceCode :
      GodelQuotation.Numbered.CodeBoundary sourceCode)
    (hVariableCode :
      GodelQuotation.Numbered.CodeBoundary variableCode)
    (hTargetCode :
      GodelQuotation.Numbered.CodeBoundary targetCode)
    (hSourceEquality :
      Γ ⊢ₘ[T] source ≐ₘ sourceCode)
    (hVariableEquality :
      Γ ⊢ₘ[T] variableTerm ≐ₘ variableCode)
    (hTargetEquality :
      Γ ⊢ₘ[T] target ≐ₘ targetCode)
    (hCanonical :
      Γ ⊢ₘ[T]
        canonical_forall_open_code_condition
          sourceCode variableCode targetCode) :
    Γ ⊢ₘ[T]
      canonical_forall_open_code_condition
        source variableTerm target := by
  have hClosedSubstitute
      (term replacement : SetTerm)
      (hTerm : GodelQuotation.Numbered.CodeBoundary term)
      (id : FreeVarId) :
      Term.substituteFree SetSort.set id replacement term = term :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement term (by
        rw [hTerm.2]
        exact List.not_mem_nil)
  have hReplacementFresh
      (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement)
      (closedId : FreeVarId)
      (_ :
        closedId ∈
          [460, 461, 462, 463, 464, 465, 466, 467, 468]) :
      (SetSort.set, closedId) ∉ Term.freeSupport replacement := by
    rw [hReplacement.2]
    exact List.not_mem_nil
  have hNormalizeSource
      (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set 600 replacement
          (canonical_forall_open_code_condition
            (x#600) variableTerm target) =
        canonical_forall_open_code_condition
          replacement variableTerm target := by
    exact canonical_forall_open_code_condition_substitute_fresh
      (x#600) variableTerm target replacement
      replacement variableTerm target 600
      (by native_decide)
      hReplacement.1
      (hReplacementFresh replacement hReplacement)
      (by simp [Term.substituteFree, set_variable])
      (hClosedSubstitute variableTerm replacement hVariable 600)
      (hClosedSubstitute target replacement hTarget 600)
  have hSourceIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) (sort := SetSort.set)
      (eigen := 600) (left := source) (right := sourceCode)
      (body :=
        canonical_forall_open_code_condition
          (x#600) variableTerm target)
      hSourceEquality
      (hLeftCheck := hSource.check_certificate)
      (hRightCheck := hSourceCode.check_certificate)
      (hBodyCheck := Formula.check_certificate_of_admissible <| by
        exact canonical_forall_open_code_condition_admissible
          (x#600) variableTerm target
          (set_variable_admissible 600)
          hVariable.1 hTarget.1)
  have hSourceIff :
      Γ ⊢ₘ[T]
        canonical_forall_open_code_condition
            source variableTerm target ↔ₘ
          canonical_forall_open_code_condition
            sourceCode variableTerm target := by
    simpa only [
      hNormalizeSource source hSource,
      hNormalizeSource sourceCode hSourceCode] using
      hSourceIffRaw
  have hNormalizeVariable
      (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set 601 replacement
          (canonical_forall_open_code_condition
            sourceCode (x#601) target) =
        canonical_forall_open_code_condition
          sourceCode replacement target := by
    exact canonical_forall_open_code_condition_substitute_fresh
      sourceCode (x#601) target replacement
      sourceCode replacement target 601
      (by native_decide)
      hReplacement.1
      (hReplacementFresh replacement hReplacement)
      (hClosedSubstitute sourceCode replacement hSourceCode 601)
      (by simp [Term.substituteFree, set_variable])
      (hClosedSubstitute target replacement hTarget 601)
  have hVariableIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) (sort := SetSort.set)
      (eigen := 601)
      (left := variableTerm) (right := variableCode)
      (body :=
        canonical_forall_open_code_condition
          sourceCode (x#601) target)
      hVariableEquality
      (hLeftCheck := hVariable.check_certificate)
      (hRightCheck := hVariableCode.check_certificate)
      (hBodyCheck := Formula.check_certificate_of_admissible <| by
        exact canonical_forall_open_code_condition_admissible
          sourceCode (x#601) target
          hSourceCode.1
          (set_variable_admissible 601) hTarget.1)
  have hVariableIff :
      Γ ⊢ₘ[T]
        canonical_forall_open_code_condition
            sourceCode variableTerm target ↔ₘ
          canonical_forall_open_code_condition
            sourceCode variableCode target := by
    simpa only [
      hNormalizeVariable variableTerm hVariable,
      hNormalizeVariable variableCode hVariableCode] using
      hVariableIffRaw
  have hNormalizeTarget
      (replacement : SetTerm)
      (hReplacement :
        GodelQuotation.Numbered.CodeBoundary replacement) :
      Formula.substituteFree SetSort.set 602 replacement
          (canonical_forall_open_code_condition
            sourceCode variableCode (x#602)) =
        canonical_forall_open_code_condition
          sourceCode variableCode replacement := by
    exact canonical_forall_open_code_condition_substitute_fresh
      sourceCode variableCode (x#602) replacement
      sourceCode variableCode replacement 602
      (by native_decide)
      hReplacement.1
      (hReplacementFresh replacement hReplacement)
      (hClosedSubstitute sourceCode replacement hSourceCode 602)
      (hClosedSubstitute variableCode replacement hVariableCode 602)
      (by simp [Term.substituteFree, set_variable])
  have hTargetIffRaw :=
    Metatheory.Derives.equality_iff_of_equality
      (T := T) (Γ := Γ) (sort := SetSort.set)
      (eigen := 602) (left := target) (right := targetCode)
      (body :=
        canonical_forall_open_code_condition
          sourceCode variableCode (x#602))
      hTargetEquality
      (hLeftCheck := hTarget.check_certificate)
      (hRightCheck := hTargetCode.check_certificate)
      (hBodyCheck := Formula.check_certificate_of_admissible <| by
        exact canonical_forall_open_code_condition_admissible
          sourceCode variableCode (x#602)
          hSourceCode.1 hVariableCode.1
          (set_variable_admissible 602))
  have hTargetIff :
      Γ ⊢ₘ[T]
        canonical_forall_open_code_condition
            sourceCode variableCode target ↔ₘ
          canonical_forall_open_code_condition
            sourceCode variableCode targetCode := by
    simpa only [
      hNormalizeTarget target hTarget,
      hNormalizeTarget targetCode hTargetCode] using
      hTargetIffRaw
  exact FirstOrder.Derives.iffElimLeft hSourceIff <|
    FirstOrder.Derives.iffElimLeft hVariableIff <|
      FirstOrder.Derives.iffElimLeft hTargetIff hCanonical

/--
捕获规避替换逐参数穿过 transcript 的单步全称闭包关系。

该接口把索引运输与外层 witness 实例化统一为同一个替换定理；内部使用的
canonical 闭包 binder 新鲜性条件与底层关系完全一致。
-/
theorem logical_closure_certificate_step_condition_substitute_fresh
    (certificateSequence formulaTrace index replacement
      certificateSequenceResult formulaTraceResult indexResult : SetTerm)
    (sourceId : FreeVarId)
    (hSourceFresh :
      sourceId ∉
        [310, 311, 312, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      ∀ closedId,
        closedId ∈
            [310, 311, 312, 460, 461, 462, 463, 464,
              465, 466, 467, 468, 469, 470] →
          (SetSort.set, closedId) ∉
            Term.freeSupport replacement)
    (hCertificateSequenceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          certificateSequence =
        certificateSequenceResult)
    (hFormulaTraceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaTrace =
        formulaTraceResult)
    (hIndexSubstitution :
      Term.substituteFree SetSort.set sourceId replacement index =
        indexResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_closure_certificate_step_condition
          certificateSequence formulaTrace index) =
      logical_closure_certificate_step_condition
        certificateSequenceResult formulaTraceResult indexResult := by
  have hNumeralFixed (number : Nat) :
      Term.substituteFree SetSort.set sourceId replacement
          (numₘ(number)) =
        numₘ(number) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hSourceCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          (formulaTrace ·ₘ Sₘ(index)) =
        formulaTraceResult ·ₘ Sₘ(indexResult) := by
    simp [Term.substituteFree,
      hFormulaTraceSubstitution, hIndexSubstitution]
  have hVariableCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          (var_codeₘ(numₘ(2) *ₘ
            (certificateSequence ·ₘ index))) =
        var_codeₘ(numₘ(2) *ₘ
          (certificateSequenceResult ·ₘ indexResult)) := by
    simp [Term.substituteFree, hNumeralFixed,
      hCertificateSequenceSubstitution, hIndexSubstitution]
  have hTargetCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          (formulaTrace ·ₘ index) =
        formulaTraceResult ·ₘ indexResult := by
    simp [Term.substituteFree,
      hFormulaTraceSubstitution, hIndexSubstitution]
  have hSourceNe312 : sourceId ≠ 312 := by
    intro hEq
    apply hSourceFresh
    simp [hEq]
  have hCanonicalSourceFresh :
      sourceId ∉
        [310, 311, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470] := by
    intro hId
    apply hSourceFresh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hId ⊢
    grind
  have hCanonicalReplacementFresh :
      ∀ id,
        id ∈
            [310, 311, 460, 461, 462, 463, 464,
              465, 466, 467, 468, 469, 470] →
          (SetSort.set, id) ∉ Term.freeSupport replacement := by
    intro id hId
    apply hReplacementFresh id
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hId ⊢
    grind
  have hOpenSourceFresh :
      sourceId ∉ [460, 461, 462, 463, 464, 465, 466, 467, 468] := by
    intro hId
    apply hCanonicalSourceFresh
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hId ⊢
    grind
  have hOpenReplacementFresh :
      ∀ id,
        id ∈ [460, 461, 462, 463, 464, 465, 466, 467, 468] →
          (SetSort.set, id) ∉ Term.freeSupport replacement := by
    intro id hId
    apply hCanonicalReplacementFresh id
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hId ⊢
    grind
  have hOccurrence :=
    variable_symbol_occurs_condition_substituteFree
      sourceId replacement
      (var_codeₘ(numₘ(2) *ₘ
        (certificateSequence ·ₘ index)))
      (formulaTrace ·ₘ index)
      (var_codeₘ(numₘ(2) *ₘ
        (certificateSequenceResult ·ₘ indexResult)))
      (formulaTraceResult ·ₘ indexResult)
      hSourceNe312
      hReplacementAdmissible
      (hReplacementFresh 312 (by simp))
      hVariableCodeSubstitution hTargetCodeSubstitution
  have hClosure :=
    canonical_forall_closure_code_condition_substitute_fresh
      (formulaTrace ·ₘ Sₘ(index))
      (var_codeₘ(numₘ(2) *ₘ
        (certificateSequence ·ₘ index)))
      (formulaTrace ·ₘ index)
      replacement
      (formulaTraceResult ·ₘ Sₘ(indexResult))
      (var_codeₘ(numₘ(2) *ₘ
        (certificateSequenceResult ·ₘ indexResult)))
      (formulaTraceResult ·ₘ indexResult)
      sourceId hCanonicalSourceFresh
      hReplacementAdmissible
      hCanonicalReplacementFresh
      hSourceCodeSubstitution
      hVariableCodeSubstitution
      hTargetCodeSubstitution
  have hOpen :=
    canonical_forall_open_code_condition_substitute_fresh
      (formulaTrace ·ₘ index)
      (var_codeₘ(numₘ(2) *ₘ
        (certificateSequence ·ₘ index)))
      (formulaTrace ·ₘ Sₘ(index))
      replacement
      (formulaTraceResult ·ₘ indexResult)
      (var_codeₘ(numₘ(2) *ₘ
        (certificateSequenceResult ·ₘ indexResult)))
      (formulaTraceResult ·ₘ Sₘ(indexResult))
      sourceId hOpenSourceFresh
      hReplacementAdmissible hOpenReplacementFresh
      hTargetCodeSubstitution
      hVariableCodeSubstitution
      hSourceCodeSubstitution
  simp [logical_closure_certificate_step_condition,
    Formula.substituteFree, hOccurrence, hClosure, hOpen]

/--
闭代码替换逐参数穿过 transcript 的单步全称闭包关系。

闭项自动满足底层 canonical 闭包关系的全部内部 binder 新鲜性。
-/
theorem logical_closure_certificate_step_condition_substitute_closed
    (certificateSequence formulaTrace index replacement
      certificateSequenceResult formulaTraceResult indexResult : SetTerm)
    (sourceId : FreeVarId)
    (hSourceFresh :
      sourceId ∉
        [310, 311, 312, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470])
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementClosed :
      Term.freeSupport replacement = [])
    (hCertificateSequenceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement
          certificateSequence =
        certificateSequenceResult)
    (hFormulaTraceSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaTrace =
        formulaTraceResult)
    (hIndexSubstitution :
      Term.substituteFree SetSort.set sourceId replacement index =
        indexResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_closure_certificate_step_condition
          certificateSequence formulaTrace index) =
      logical_closure_certificate_step_condition
        certificateSequenceResult formulaTraceResult indexResult := by
  exact logical_closure_certificate_step_condition_substitute_fresh
    certificateSequence formulaTrace index replacement
    certificateSequenceResult formulaTraceResult indexResult
    sourceId hSourceFresh hReplacementAdmissible
    (fun closedId _ => by
      rw [hReplacementClosed]
      exact List.not_mem_nil)
    hCertificateSequenceSubstitution
    hFormulaTraceSubstitution
    hIndexSubstitution

/--
完整逻辑证书条件逐公开参数保持捕获规避的闭项替换。

所需的新鲜性恰好来自三个外层存在 binder 与自然数序列编码的两个内部 binder。
闭包步的行编号只在一个不含公开参数的闭合字段中出现，因此无需额外条件。
-/
theorem logical_certificate_condition_with_ids_substitute_closed
    (formulaCode certificatePayload replacement
      formulaCodeResult certificatePayloadResult : SetTerm)
    (sourceId certificateSequenceId formulaTraceId lastIndexId
      lineIndexId codeTraceId codeIndexId : FreeVarId)
    (hSourceNeCertificateSequence : sourceId ≠ certificateSequenceId)
    (hSourceNeFormulaTrace : sourceId ≠ formulaTraceId)
    (hSourceNeLastIndex : sourceId ≠ lastIndexId)
    (hSourceNeCodeTrace : sourceId ≠ codeTraceId)
    (hSourceNeCodeIndex : sourceId ≠ codeIndexId)
    (hReplacementClosed : Term.BoundClosed replacement)
    (hReplacementFreshCertificateSequence :
      (SetSort.set, certificateSequenceId) ∉ Term.freeSupport replacement)
    (hReplacementFreshFormulaTrace :
      (SetSort.set, formulaTraceId) ∉ Term.freeSupport replacement)
    (hReplacementFreshLastIndex :
      (SetSort.set, lastIndexId) ∉ Term.freeSupport replacement)
    (hReplacementFreshCodeTrace :
      (SetSort.set, codeTraceId) ∉ Term.freeSupport replacement)
    (hReplacementFreshCodeIndex :
      (SetSort.set, codeIndexId) ∉ Term.freeSupport replacement)
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaCode =
        formulaCodeResult)
    (hCertificatePayloadSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificatePayload =
        certificatePayloadResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_certificate_condition_with_ids
          formulaCode certificatePayload
          certificateSequenceId formulaTraceId lastIndexId lineIndexId
          codeTraceId codeIndexId) =
      logical_certificate_condition_with_ids
        formulaCodeResult certificatePayloadResult
        certificateSequenceId formulaTraceId lastIndexId lineIndexId
        codeTraceId codeIndexId := by
  have hCommute
      (closedId : FreeVarId)
      (hDistinct : sourceId ≠ closedId)
      (hFresh :
        (SetSort.set, closedId) ∉ Term.freeSupport replacement)
      (body : SetFormula) :
      Formula.substituteFree SetSort.set sourceId replacement
          (Formula.closeFreeAt SetSort.set closedId 0 body) =
        Formula.closeFreeAt SetSort.set closedId 0
          (Formula.substituteFree SetSort.set sourceId replacement body) :=
    (Formula.closeFreeAt_substituteFree_comm
      SetSort.set sourceId closedId 0 replacement body
      hDistinct hReplacementClosed hFresh).symm
  have hCertificateSequenceCommute :=
    hCommute certificateSequenceId hSourceNeCertificateSequence
      hReplacementFreshCertificateSequence
  have hFormulaTraceCommute :=
    hCommute formulaTraceId hSourceNeFormulaTrace
      hReplacementFreshFormulaTrace
  have hLastIndexCommute :=
    hCommute lastIndexId hSourceNeLastIndex
      hReplacementFreshLastIndex
  have hCertificateSequenceFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (x#certificateSequenceId) =
        x#certificateSequenceId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeCertificateSequence]
  have hFormulaTraceFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (x#formulaTraceId) =
        x#formulaTraceId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeFormulaTrace]
  have hLastIndexFixed :
      Term.substituteFree SetSort.set sourceId replacement
          (x#lastIndexId) =
        x#lastIndexId := by
    simp [Term.substituteFree, set_variable,
      Ne.symm hSourceNeLastIndex]
  have hZeroFixed :
      Term.substituteFree SetSort.set sourceId replacement (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hCertificateCode :=
    nat_sequence_code_condition_with_ids_substitute_closed
      (x#certificateSequenceId) certificatePayload replacement
      (x#certificateSequenceId) certificatePayloadResult
      sourceId codeTraceId codeIndexId
      hSourceNeCodeTrace hSourceNeCodeIndex
      hReplacementClosed
      hReplacementFreshCodeTrace hReplacementFreshCodeIndex
      hCertificateSequenceFixed hCertificatePayloadSubstitution
  have hBaseFixed :
      Formula.substituteFree SetSort.set sourceId replacement
          (logical_base_certificate_condition_with_base
            (x#formulaTraceId ·ₘ x#lastIndexId)
            (x#certificateSequenceId ·ₘ x#lastIndexId)
            (logical_certificate_body_base_with_ids
              certificateSequenceId formulaTraceId lastIndexId)) =
        logical_base_certificate_condition_with_base
          (x#formulaTraceId ·ₘ x#lastIndexId)
          (x#certificateSequenceId ·ₘ x#lastIndexId)
          (logical_certificate_body_base_with_ids
            certificateSequenceId formulaTraceId lastIndexId) := by
    change
      Formula.substituteFree SetSort.set sourceId replacement
          (logical_base_certificate_condition
            (x#formulaTraceId ·ₘ x#lastIndexId)
            (x#certificateSequenceId ·ₘ x#lastIndexId)) =
        logical_base_certificate_condition
          (x#formulaTraceId ·ₘ x#lastIndexId)
          (x#certificateSequenceId ·ₘ x#lastIndexId)
    apply Formula.substituteFree_eq_self_of_not_mem
    intro hMember
    rcases logical_base_certificate_condition_freeSupport_subset
        (x#formulaTraceId ·ₘ x#lastIndexId)
        (x#certificateSequenceId ·ₘ x#lastIndexId)
        (SetSort.set, sourceId) hMember with
      hFormula | hCertificate
    · simp [Term.freeSupport, Term.freeSupportList,
        hSourceNeFormulaTrace,
        hSourceNeLastIndex] at hFormula
    · simp [Term.freeSupport, Term.freeSupportList,
        hSourceNeCertificateSequence,
        hSourceNeLastIndex] at hCertificate
  have hClosureStepsFixed :
      Formula.substituteFree SetSort.set sourceId replacement
          (∀ₘ[SetSort.set, lineIndexId],
            (x#lineIndexId ∈ₘ x#lastIndexId) ⟶ₘ
              logical_closure_certificate_step_condition
                (x#certificateSequenceId) (x#formulaTraceId)
                (x#lineIndexId)) =
        (∀ₘ[SetSort.set, lineIndexId],
          (x#lineIndexId ∈ₘ x#lastIndexId) ⟶ₘ
            logical_closure_certificate_step_condition
              (x#certificateSequenceId) (x#formulaTraceId)
              (x#lineIndexId)) := by
    apply Formula.substituteFree_eq_self_of_not_mem
    intro hMember
    rcases logical_closure_certificate_steps_freeSupport_subset
        (x#certificateSequenceId) (x#formulaTraceId) (x#lastIndexId)
        lineIndexId (SetSort.set, sourceId) hMember with
      hCertificate | hTrace | hLast
    · simp [Term.freeSupport,
        hSourceNeCertificateSequence
        ] at hCertificate
    · simp [Term.freeSupport,
        hSourceNeFormulaTrace
        ] at hTrace
    · simp [Term.freeSupport,
        hSourceNeLastIndex
        ] at hLast
  unfold logical_certificate_condition_with_ids
  simp only [Formula.substituteFree]
  rw [hCertificateSequenceCommute]
  simp only [Formula.substituteFree]
  rw [hFormulaTraceCommute]
  simp only [Formula.substituteFree]
  rw [hLastIndexCommute]
  simp only [Formula.substituteFree]
  unfold logical_certificate_body_with_ids
  rw [logical_certificate_conjunction_substituteFree]
  simp only [List.map]
  rw [hCertificateCode, hBaseFixed, hClosureStepsFixed]
  simp [Formula.substituteFree, Term.substituteFree,
    hFormulaCodeSubstitution,
    hCertificateSequenceFixed, hFormulaTraceFixed, hLastIndexFixed,
    hZeroFixed]

end CertifiedProof
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
