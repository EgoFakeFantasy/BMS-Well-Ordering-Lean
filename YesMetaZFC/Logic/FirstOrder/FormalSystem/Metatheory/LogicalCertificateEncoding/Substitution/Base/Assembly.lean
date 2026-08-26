import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.LogicalCertificateEncoding.Substitution.Base.Branches

/-!
# 基础逻辑证书替换的统一调度

本模块汇总十二类基础逻辑证书分支的精确新鲜替换接口。
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

/-! ## 十二类基础证书的统一替换 -/

/--
基础证书总条件的精确替换新鲜性。

动态 binder 使用偏移 `0..36` 与 `40..62`；`37..39` 没有被占用。第二部分恰好
是 canonical 闭包与代码替换规格使用的固定 binder。
-/
def LogicalBaseCertificateSubstitutionFresh
    (sourceId base : FreeVarId) : Prop :=
  (∀ offset,
      offset < 37 ∨ (40 ≤ offset ∧ offset < 63) →
        sourceId ≠ base + offset) ∧
    sourceId ∉
      [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
        465, 466, 467, 468, 469, 470]

/-- 位于动态基址之前且避开固定 binder 时满足统一替换新鲜性。 -/
theorem logical_base_certificate_substitution_fresh_of_lt
    (sourceId base : FreeVarId)
    (hBelow : sourceId < base)
    (hCanonical :
      sourceId ∉
        [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470]) :
    LogicalBaseCertificateSubstitutionFresh sourceId base := by
  unfold LogicalBaseCertificateSubstitutionFresh
  constructor
  · intro offset _ hEq
    exact
      (Nat.not_lt_of_ge (Nat.le_add_right base offset))
        (hEq ▸ hBelow)
  · exact hCanonical

/--
基础证书总条件对 replacement 的精确新鲜性。

动态 binder 使用 `base + 0..36` 与 `base + 40..62`；固定 binder 来自
canonical 闭包与代码替换规格。该条件直接描述 replacement 支持只能落在这些
编号的补集中。
-/
def LogicalBaseCertificateReplacementFresh
    (replacement : SetTerm) (base : FreeVarId) : Prop :=
  ∀ id,
    (SetSort.set, id) ∈ Term.freeSupport replacement →
      (id < base ∨
        (base + 37 ≤ id ∧ id < base + 40) ∨
        base + 63 ≤ id) ∧
      id ∉
        [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
          465, 466, 467, 468, 469, 470]

/--
对全部实际 binder 新鲜的替换逐公开参数穿过十二类基础逻辑证书的总析取。

该定理是 transcript 主体替换唯一需要了解的基础证书接口；各分支的存在见证和
checked 关系均留在本模块内部。
-/
theorem logical_base_certificate_condition_with_base_substitute_fresh
    (formulaCode certificate replacement
      formulaCodeResult certificateResult : SetTerm)
    (base sourceId : FreeVarId)
    (hSourceFresh :
      LogicalBaseCertificateSubstitutionFresh sourceId base)
    (hReplacementAdmissible :
      Term.Admissible replacement SetSort.set)
    (hReplacementFresh :
      LogicalBaseCertificateReplacementFresh replacement base)
    (hFormulaCodeSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formulaCode =
        formulaCodeResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (logical_base_certificate_condition_with_base
          formulaCode certificate base) =
      logical_base_certificate_condition_with_base
        formulaCodeResult certificateResult base := by
  unfold LogicalBaseCertificateReplacementFresh at hReplacementFresh
  have hBaseNe
      (offset : Nat)
      (hOffset :
        offset < 37 ∨ (40 ≤ offset ∧ offset < 63)) :
      sourceId ≠ base + offset :=
    hSourceFresh.1 offset hOffset
  have hBaseZero : sourceId ≠ base := by
    simpa using hBaseNe 0 (by omega)
  have hCanonicalNe
      (id : FreeVarId)
      (hId :
        id ∈
          [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
            465, 466, 467, 468, 469, 470]) :
      sourceId ≠ id := by
    intro hEq
    subst id
    exact hSourceFresh.2 hId
  have hReplacementDynamic
      (id : FreeVarId)
      (hUsed :
        (base ≤ id ∧ id < base + 37) ∨
          (base + 40 ≤ id ∧ id < base + 63)) :
      (SetSort.set, id) ∉ Term.freeSupport replacement := by
    intro hMember
    have hAllowed := (hReplacementFresh id hMember).1
    rcases hAllowed with hBelow | hGap | hAbove
    · rcases hUsed with hLow | hHigh
      · exact (Nat.not_lt_of_ge hLow.1) hBelow
      · exact (Nat.not_lt_of_ge
          (Nat.le_trans (Nat.le_add_right base 40) hHigh.1)) hBelow
    · rcases hUsed with hLow | hHigh
      · exact (Nat.not_lt_of_ge hGap.1) hLow.2
      · exact (Nat.not_lt_of_ge hHigh.1) hGap.2
    · rcases hUsed with hLow | hHigh
      · exact (Nat.not_lt_of_ge
          (Nat.le_trans
            (Nat.add_le_add_left (by decide : 37 ≤ 63) base)
            hAbove)) hLow.2
      · exact (Nat.not_lt_of_ge hAbove) hHigh.2
  have hReplacementCanonical
      (id : FreeVarId)
      (hId :
        id ∈
          [310, 311, 320, 321, 322, 460, 461, 462, 463, 464,
            465, 466, 467, 468, 469, 470]) :
      (SetSort.set, id) ∉ Term.freeSupport replacement := by
    intro hMember
    exact (hReplacementFresh id hMember).2 hId
  have hReplacementDynamicOffset
      (offset : Nat)
      (hOffset :
        offset < 37 ∨ (40 ≤ offset ∧ offset < 63)) :
      (base ≤ base + offset ∧ base + offset < base + 37) ∨
        (base + 40 ≤ base + offset ∧ base + offset < base + 63) := by
    rcases hOffset with hLow | hGap
    · exact Or.inl
        ⟨Nat.le_add_right base offset,
          Nat.add_lt_add_left hLow base⟩
    · exact Or.inr
        ⟨Nat.add_le_add_left hGap.1 base,
          Nat.add_lt_add_left hGap.2 base⟩
  have hTernary0Fresh :
      sourceId ∉
        [base, base + 1, base + 2, base + 3, base + 4,
          base + 40, base + 41] := by
    simp [hBaseZero, hBaseNe]
  have hUnary1Fresh :
      sourceId ∉
        [base + 5, base + 6, base + 7, base + 40, base + 41] := by
    simp [hBaseNe]
  have hBinary2Fresh :
      sourceId ∉
        [base + 8, base + 9, base + 10, base + 11,
          base + 40, base + 41] := by
    simp [hBaseNe]
  have hBinary3Fresh :
      sourceId ∉
        [base + 12, base + 13, base + 14, base + 15,
          base + 40, base + 41] := by
    simp [hBaseNe]
  have hUnary4Fresh :
      sourceId ∉
        [base + 16, base + 17, base + 18, base + 40, base + 41] := by
    simp [hBaseNe]
  have hBinary5Fresh :
      sourceId ∉
        [base + 19, base + 20, base + 21, base + 22,
          base + 40, base + 41] := by
    simp [hBaseNe]
  have hBinary6Fresh :
      sourceId ∉
        [base + 23, base + 24, base + 25, base + 26,
          base + 40, base + 41] := by
    simp [hBaseNe]
  have hSpecializationFresh :
      sourceId ∉
        [base + 27, base + 28, base + 29, base + 30,
          base + 31, base + 32, base + 33, base + 34,
          base + 35, base + 36, base + 40, base + 41] := by
    simp [hBaseNe]
  have hDistributionFresh :
      sourceId ∉
        [base + 42, base + 43, base + 44, base + 45,
          base + 46, base + 47, base + 48, base + 49,
          base + 50, base + 51, base + 40, base + 41] := by
    simp [hBaseNe]
  have hVacuousFresh :
      sourceId ∉
        [base + 52, base + 53, base + 54, base + 55,
          base + 56, base + 57, base + 40, base + 41] := by
    simp [hBaseNe]
  have hEqualitySubstitutionFresh :
      sourceId ∉
        [base + 58, base + 59, base + 60, base + 61,
          base + 40, base + 41, 310, 311] := by
    simp [hBaseNe, hCanonicalNe]
  have hDistribution :=
    logical_ternary_base_certificate_condition_with_ids_substitute_fresh
      0 implication_distribution_axiom_code_term
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      base (base + 1) (base + 2) (base + 3) (base + 4)
      (base + 40) (base + 41) sourceId
      hTernary0Fresh hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId | hId | hId
          · subst id
            simp
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      (by
        intro first second third
        simp [implication_distribution_axiom_code_term,
          Term.substituteFree])
      hFormulaCodeSubstitution hCertificateSubstitution
  have hSelf :=
    logical_unary_base_certificate_condition_with_ids_substitute_fresh
      1 self_implication_axiom_code_term
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 5) (base + 6) (base + 7)
      (base + 40) (base + 41) sourceId
      hUnary1Fresh hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      (by
        intro component
        simp [self_implication_axiom_code_term,
          Term.substituteFree])
      hFormulaCodeSubstitution hCertificateSubstitution
  have hWeakening :=
    logical_binary_base_certificate_condition_with_ids_substitute_fresh
      2 weakening_axiom_code_term
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 8) (base + 9) (base + 10) (base + 11)
      (base + 40) (base + 41) sourceId
      hBinary2Fresh hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      (by
        intro left right
        simp [weakening_axiom_code_term, Term.substituteFree])
      hFormulaCodeSubstitution hCertificateSubstitution
  have hContradiction :=
    logical_binary_base_certificate_condition_with_ids_substitute_fresh
      3 contradiction_axiom_code_term
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 12) (base + 13) (base + 14) (base + 15)
      (base + 40) (base + 41) sourceId
      hBinary3Fresh hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      (by
        intro left right
        simp [contradiction_axiom_code_term, Term.substituteFree])
      hFormulaCodeSubstitution hCertificateSubstitution
  have hClassical :=
    logical_unary_base_certificate_condition_with_ids_substitute_fresh
      4 classical_axiom_code_term
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 16) (base + 17) (base + 18)
      (base + 40) (base + 41) sourceId
      hUnary4Fresh hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      (by
        intro component
        simp [classical_axiom_code_term, Term.substituteFree])
      hFormulaCodeSubstitution hCertificateSubstitution
  have hExplosion :=
    logical_binary_base_certificate_condition_with_ids_substitute_fresh
      5 explosion_axiom_code_term
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 19) (base + 20) (base + 21) (base + 22)
      (base + 40) (base + 41) sourceId
      hBinary5Fresh hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      (by
        intro left right
        simp [explosion_axiom_code_term, Term.substituteFree])
      hFormulaCodeSubstitution hCertificateSubstitution
  have hCases :=
    logical_binary_base_certificate_condition_with_ids_substitute_fresh
      6 case_analysis_axiom_code_term
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 23) (base + 24) (base + 25) (base + 26)
      (base + 40) (base + 41) sourceId
      hBinary6Fresh hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      (by
        intro left right
        simp [case_analysis_axiom_code_term, Term.substituteFree])
      hFormulaCodeSubstitution hCertificateSubstitution
  have hSpecialization :=
    logical_specialization_certificate_condition_with_ids_substitute_fresh
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 27) (base + 28) (base + 29) (base + 30)
      (base + 31) (base + 32) (base + 33) (base + 34)
      (base + 35) (base + 36) (base + 40) (base + 41) sourceId
      hSpecializationFresh hSourceFresh.2
      hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId | hId |
            hId | hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      hReplacementCanonical
      hFormulaCodeSubstitution hCertificateSubstitution
  have hForallDistribution :=
    logical_forall_distribution_certificate_condition_with_ids_substitute_fresh
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 42) (base + 43) (base + 44) (base + 45)
      (base + 46) (base + 47) (base + 48) (base + 49)
      (base + 50) (base + 51) (base + 40) (base + 41) sourceId
      hDistributionFresh hSourceFresh.2
      hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId | hId |
            hId | hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      hReplacementCanonical
      hFormulaCodeSubstitution hCertificateSubstitution
  have hVacuous :=
    logical_vacuous_forall_certificate_condition_with_ids_substitute_fresh
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 52) (base + 53) (base + 54) (base + 55)
      (base + 56) (base + 57) (base + 40) (base + 41) sourceId
      hVacuousFresh
      (fun h =>
        hSourceFresh.2 (logical_base_closure_reserved_mem h))
      hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      (fun id h =>
        hReplacementCanonical id
          (logical_base_closure_reserved_mem h))
      hFormulaCodeSubstitution hCertificateSubstitution
  have hEqualitySubstitution :=
    logical_equality_substitution_certificate_condition_with_ids_substitute_fresh
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 58) (base + 59) (base + 60) (base + 61)
      (base + 40) (base + 41) sourceId
      hEqualitySubstitutionFresh
      hReplacementAdmissible
      (fun id hId =>
        hReplacementDynamic id (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hId
          rcases hId with hId | hId | hId | hId | hId | hId
          all_goals subst id
          all_goals apply hReplacementDynamicOffset <;> decide))
      (fun id hId =>
        hReplacementCanonical id
          (logical_base_closure_reserved_mem <| by
            simpa using
              List.mem_append_left
                [460, 461, 462, 463, 464, 465,
                  466, 467, 468, 469, 470] hId))
      hFormulaCodeSubstitution hCertificateSubstitution
  have hReflexivity :=
    logical_equality_reflexivity_certificate_condition_with_id_substitute_fresh
      formulaCode certificate replacement
      formulaCodeResult certificateResult
      (base + 62) sourceId
      (hBaseNe 62 (by omega))
      hReplacementAdmissible
      (hReplacementDynamic (base + 62)
        (hReplacementDynamicOffset 62 (Or.inr ⟨by omega, by omega⟩)))
      hFormulaCodeSubstitution hCertificateSubstitution
  unfold logical_base_certificate_condition_with_base
  simp only [Formula.substituteFree]
  rw [hDistribution, hSelf, hWeakening, hContradiction,
    hClassical, hExplosion, hCases, hSpecialization,
    hForallDistribution, hVacuous,
    hEqualitySubstitution, hReflexivity]


end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
