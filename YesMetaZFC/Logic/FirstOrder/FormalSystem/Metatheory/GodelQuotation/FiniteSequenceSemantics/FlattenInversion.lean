import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FiniteSequenceSemantics.FlattenBound

/-!
# 有限序列族折叠的逐点反演

本模块把 `flattenₘ` 累积器中的一个分片点沿后续拼接逐步传播到最终折叠，并与
闭的标准 token 序列逐点对齐。核心归纳只运行在外部有限自然数上，对象层仅
消费有限序列关系。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 对象函数在外部 numeral 位置上的值项。 -/
private abbrev fsfi_at
    (sequence : SetTerm) (index : Nat) : SetTerm :=
  sequence ·ₘ numₘ(index)

/--
`flattenₘ` 累积器的逐点 checked replay。

已知第 `selected` 个分片的长度、此前缀累积器的长度以及分片内位置 `point` 后，
先把该点平移到累积器的全局位置 `offset + point`，再沿剩余拼接保持其点值。
最终通过标准 token 序列等式恢复该点的具体 numeral。
-/
theorem gq_flatten_checked_replay_point_value
    {Γ : Context signature}
    (family accumulator : SetTerm)
    (tokens : List Nat)
    (count selected offset point length token : Nat)
    (hFamily : Term.Admissible family SetSort.set)
    (hAccumulator :
      Term.Admissible accumulator SetSort.set)
    (hSelected : selected < count)
    (hPoint : point < length)
    (hAccumulatorFinite :
      ∀ index, index ≤ count →
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition
            (fsfi_at accumulator index))
    (hFamilyFinite :
      ∀ index, index < count →
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition
            (fsfi_at family index))
    (hStep :
      ∀ index, index < count →
        Γ ⊢ₘ[godel_quotation_theory]
          fsfi_at accumulator (index + 1) ≐ₘ
            (fsfi_at accumulator index ⌢ₘ
              fsfi_at family index))
    (hPrefixDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(fsfi_at accumulator selected) ≐ₘ
          numₘ(offset))
    (hSelectedDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(fsfi_at family selected) ≐ₘ
          numₘ(length))
    (hTerminal :
      Γ ⊢ₘ[godel_quotation_theory]
        flattenₘ(family) ≐ₘ
          fsfi_at accumulator count)
    (hStandard :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          flattenₘ(family))
    (hGet :
      tokens[offset + point]? = some token) :
    Γ ⊢ₘ[godel_quotation_theory]
      (fsfi_at family selected ·ₘ numₘ(point)) ≐ₘ
        numₘ(token) := by
  have hAccumulatorAt
      (index : Nat) :
      Term.CheckCertificate
        (fsfi_at accumulator index) SetSort.set :=
    Term.check_admissible_complete <|
      function_application_term_admissible
        accumulator (numₘ(index))
        hAccumulator
        (finite_numeral_term_admissible index)
  have hFamilyAt
      (index : Nat) :
      Term.CheckCertificate
        (fsfi_at family index) SetSort.set :=
    Term.check_admissible_complete <|
      function_application_term_admissible
        family (numₘ(index))
        hFamily
        (finite_numeral_term_admissible index)
  have hPointNumeral :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(point) ∈ₘ numₘ(length) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_finite_numeral_mem_of_lt
            point length hPoint
  have hPointInSelected :
      Γ ⊢ₘ[godel_quotation_theory]
        numₘ(point) ∈ₘ
          domₘ(fsfi_at family selected) :=
    FirstOrder.Derives.iffElimLeft
      (membership_right_iff_of_equality
        (numₘ(point))
        (domₘ(fsfi_at family selected))
        (numₘ(length))
        (finite_numeral_term_admissible point)
        (domain_term_admissible
          (fsfi_at family selected)
          (hFamilyAt selected).admissible)
        (finite_numeral_term_admissible length)
        hSelectedDomain)
      hPointNumeral
  have hFirstRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(offset + point) ∈ₘ
            domₘ(fsfi_at accumulator selected ⌢ₘ
              fsfi_at family selected)) ∧ₘ
          (((fsfi_at accumulator selected ⌢ₘ
                fsfi_at family selected) ·ₘ
              numₘ(offset + point)) ≐ₘ
            (fsfi_at family selected ·ₘ
              numₘ(point)))) :=
    gq_concatenation_right_point_at_numeral_offset
      (fsfi_at accumulator selected)
      (fsfi_at family selected)
      offset point
      (hAccumulatorFinite selected
        (Nat.le_of_lt hSelected))
      (hFamilyFinite selected hSelected)
      hPrefixDomain hPointInSelected
      (hLeft := hAccumulatorAt selected)
      (hRight := hFamilyAt selected)
  have hFirst :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(offset + point) ∈ₘ
            domₘ(fsfi_at accumulator
              (selected + 1))) ∧ₘ
          ((fsfi_at accumulator
                (selected + 1) ·ₘ
              numₘ(offset + point)) ≐ₘ
            (fsfi_at family selected ·ₘ
              numₘ(point)))) :=
    gq_point_inversion_of_equality
      (fsfi_at accumulator (selected + 1))
      (fsfi_at accumulator selected ⌢ₘ
        fsfi_at family selected)
      (numₘ(offset + point))
      (fsfi_at family selected ·ₘ numₘ(point))
      (hStep selected hSelected)
      hFirstRaw
      (hLeft := hAccumulatorAt (selected + 1))
      (hRight := by prove_term_check)
      (hIndex := by prove_term_check)
  have hAfter :
      ∀ extra,
        selected + 1 + extra ≤ count →
          Γ ⊢ₘ[godel_quotation_theory]
            ((numₘ(offset + point) ∈ₘ
                domₘ(fsfi_at accumulator
                  (selected + 1 + extra))) ∧ₘ
              ((fsfi_at accumulator
                    (selected + 1 + extra) ·ₘ
                  numₘ(offset + point)) ≐ₘ
                (fsfi_at family selected ·ₘ
                  numₘ(point)))) := by
    intro extra
    induction extra with
    | zero =>
        intro _
        simpa using hFirst
    | succ extra ih =>
        intro hBound
        let index : Nat :=
          selected + 1 + extra
        have hIndexLt :
            index < count := by
          simpa [index, Nat.succ_eq_add_one,
            Nat.add_assoc] using hBound
        have hPrevious :
            Γ ⊢ₘ[godel_quotation_theory]
              ((numₘ(offset + point) ∈ₘ
                  domₘ(fsfi_at accumulator index)) ∧ₘ
                ((fsfi_at accumulator index ·ₘ
                    numₘ(offset + point)) ≐ₘ
                  (fsfi_at family selected ·ₘ
                    numₘ(point)))) := by
          simpa [index] using
            ih (Nat.le_of_lt hIndexLt)
        have hRaw :
            Γ ⊢ₘ[godel_quotation_theory]
              ((numₘ(offset + point) ∈ₘ
                  domₘ(fsfi_at accumulator index ⌢ₘ
                    fsfi_at family index)) ∧ₘ
                (((fsfi_at accumulator index ⌢ₘ
                      fsfi_at family index) ·ₘ
                    numₘ(offset + point)) ≐ₘ
                  (fsfi_at family selected ·ₘ
                    numₘ(point)))) :=
          gq_concatenation_left_point
            (fsfi_at accumulator index)
            (fsfi_at family index)
            (numₘ(offset + point))
            (fsfi_at family selected ·ₘ
              numₘ(point))
            (hAccumulatorFinite index
              (Nat.le_of_lt hIndexLt))
            (hFamilyFinite index hIndexLt)
            (FirstOrder.Derives.conjElimLeft
              hPrevious)
            (FirstOrder.Derives.conjElimRight
              hPrevious)
            (hLeft := hAccumulatorAt index)
            (hRight := hFamilyAt index)
            (hIndex := by prove_term_check)
        have hNext :=
          gq_point_inversion_of_equality
            (fsfi_at accumulator (index + 1))
            (fsfi_at accumulator index ⌢ₘ
              fsfi_at family index)
            (numₘ(offset + point))
            (fsfi_at family selected ·ₘ
              numₘ(point))
            (hStep index hIndexLt)
            hRaw
            (hLeft := hAccumulatorAt (index + 1))
            (hRight := by prove_term_check)
            (hIndex := by prove_term_check)
        simpa [index, Nat.succ_eq_add_one,
          Nat.add_assoc] using hNext
  obtain ⟨remaining, hCount⟩ :=
    Nat.exists_eq_add_of_le
      (Nat.succ_le_of_lt hSelected)
  have hAtTerminal :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(offset + point) ∈ₘ
            domₘ(fsfi_at accumulator count)) ∧ₘ
          ((fsfi_at accumulator count ·ₘ
              numₘ(offset + point)) ≐ₘ
            (fsfi_at family selected ·ₘ
              numₘ(point)))) := by
    subst count
    simpa [Nat.add_assoc] using
      hAfter remaining (Nat.le_refl _)
  have hAtFlatten :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(offset + point) ∈ₘ
            domₘ(flattenₘ(family))) ∧ₘ
          ((flattenₘ(family) ·ₘ
              numₘ(offset + point)) ≐ₘ
            (fsfi_at family selected ·ₘ
              numₘ(point)))) :=
    gq_point_inversion_of_equality
      (flattenₘ(family))
      (fsfi_at accumulator count)
      (numₘ(offset + point))
      (fsfi_at family selected ·ₘ numₘ(point))
      hTerminal hAtTerminal
      (hLeft := by prove_term_check)
      (hRight := hAccumulatorAt count)
      (hIndex := by prove_term_check)
  have hStandardPoint :
      Γ ⊢ₘ[godel_quotation_theory]
        ((numₘ(offset + point) ∈ₘ
            domₘ(flattenₘ(family))) ∧ₘ
          ((flattenₘ(family) ·ₘ
              numₘ(offset + point)) ≐ₘ
            numₘ(token))) :=
    gq_standard_token_sequence_point_inversion
      (flattenₘ(family)) tokens
      (Metatheory.Derives.equality_symm
        hStandard)
      hGet
  exact Metatheory.Derives.equality_trans
    (Metatheory.Derives.equality_symm <|
      FirstOrder.Derives.conjElimRight
        hAtFlatten)
    (FirstOrder.Derives.conjElimRight
      hStandardPoint)

/--
`flattenₘ` 累积器的前缀长度 checked replay。

`pieceLength` 给出每段的外部长度，`prefixLength` 给出从零开始的部分和。对象层
只消费每段定义域证书与拼接等式，逐步恢复累积器各位置的 numeral 定义域。
-/
theorem gq_flatten_checked_replay_prefix_domain
    {Γ : Context signature}
    (family accumulator : SetTerm)
    (count : Nat)
    (pieceLength prefixLength : Nat → Nat)
    (hFamily : Term.Admissible family SetSort.set)
    (hAccumulator :
      Term.Admissible accumulator SetSort.set)
    (hPrefixZero : prefixLength 0 = 0)
    (hPrefixStep :
      ∀ index, index < count →
        prefixLength (index + 1) =
          prefixLength index + pieceLength index)
    (hAccumulatorFinite :
      ∀ index, index ≤ count →
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition
            (fsfi_at accumulator index))
    (hFamilyFinite :
      ∀ index, index < count →
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition
            (fsfi_at family index))
    (hInitial :
      Γ ⊢ₘ[godel_quotation_theory]
        fsfi_at accumulator 0 ≐ₘ ∅ₘ)
    (hStep :
      ∀ index, index < count →
        Γ ⊢ₘ[godel_quotation_theory]
          fsfi_at accumulator (index + 1) ≐ₘ
            (fsfi_at accumulator index ⌢ₘ
              fsfi_at family index))
    (hPieceDomain :
      ∀ index, index < count →
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(fsfi_at family index) ≐ₘ
            numₘ(pieceLength index)) :
    ∀ index, index ≤ count →
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(fsfi_at accumulator index) ≐ₘ
          numₘ(prefixLength index) := by
  have hAccumulatorAt
      (index : Nat) :
      Term.CheckCertificate
        (fsfi_at accumulator index) SetSort.set :=
    Term.check_admissible_complete <|
      function_application_term_admissible
        accumulator (numₘ(index))
        hAccumulator
        (finite_numeral_term_admissible index)
  have hFamilyAt
      (index : Nat) :
      Term.CheckCertificate
        (fsfi_at family index) SetSort.set :=
    Term.check_admissible_complete <|
      function_application_term_admissible
        family (numₘ(index))
        hFamily
        (finite_numeral_term_admissible index)
  have hEmptyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(∅ₘ) ≐ₘ numₘ(0) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <| by
          simpa [standard_sequence,
            standard_sequence_from] using
            (standard_sequence_domain_eq_numeral_length
              (elements := [])
              (by simp)
              (by simp)
              (by simp))
  intro index hIndex
  induction index with
  | zero =>
      have hDomainCongruence :
          Γ ⊢ₘ[godel_quotation_theory]
            domₘ(fsfi_at accumulator 0) ≐ₘ
              domₘ(∅ₘ) :=
        domain_term_congr_of_equality
          (fsfi_at accumulator 0) ∅ₘ
          (hAccumulatorAt 0).admissible
          empty_set_term_admissible
          hInitial
      simpa [hPrefixZero] using
        Metatheory.Derives.equality_trans
          hDomainCongruence hEmptyDomain
  | succ index ih =>
      have hIndexLt :
          index < count :=
        Nat.lt_of_succ_le hIndex
      have hPrevious :
          Γ ⊢ₘ[godel_quotation_theory]
            domₘ(fsfi_at accumulator index) ≐ₘ
              numₘ(prefixLength index) :=
        ih (Nat.le_of_lt hIndexLt)
      have hConcatenationDomain :
          Γ ⊢ₘ[godel_quotation_theory]
            domₘ(fsfi_at accumulator index ⌢ₘ
                fsfi_at family index) ≐ₘ
              numₘ(prefixLength index +
                pieceLength index) :=
        gq_concatenation_domain_eq_numeral_lengths_of_theory
          (fun _ hAxiom => hAxiom)
          (fsfi_at accumulator index)
          (fsfi_at family index)
          (prefixLength index)
          (pieceLength index)
          (hAccumulatorFinite index
            (Nat.le_of_lt hIndexLt))
          (hFamilyFinite index hIndexLt)
          hPrevious
          (hPieceDomain index hIndexLt)
          (hLeft := hAccumulatorAt index)
          (hRight := hFamilyAt index)
      have hStepDomain :
          Γ ⊢ₘ[godel_quotation_theory]
            domₘ(fsfi_at accumulator
                (index + 1)) ≐ₘ
              domₘ(fsfi_at accumulator index ⌢ₘ
                fsfi_at family index) :=
        domain_term_congr_of_equality
          (fsfi_at accumulator (index + 1))
          (fsfi_at accumulator index ⌢ₘ
            fsfi_at family index)
          (hAccumulatorAt (index + 1)).admissible
          (finite_sequence_concatenation_term_admissible
            (fsfi_at accumulator index)
            (fsfi_at family index)
            (hAccumulatorAt index).admissible
            (hFamilyAt index).admissible)
          (hStep index hIndexLt)
      simpa [Nat.succ_eq_add_one,
        hPrefixStep index hIndexLt] using
        Metatheory.Derives.equality_trans
          hStepDomain hConcatenationDomain

/--
有限 numeral 定义域上的 `flattenₘ` 总长度前缀和。

该接口把全部分片定义域证书汇总为最终 flatten 定义域，不向调用方暴露对象
累积器。
-/
theorem gq_flatten_numeral_domain_eq_prefix_length
    {Γ : Context signature}
    (family : SetTerm)
    (count : Nat)
    (pieceLength prefixLength : Nat → Nat)
    (hFamily : Term.Admissible family SetSort.set)
    (hFamilyCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition family)
    (hFamilyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(family) ≐ₘ numₘ(count))
    (hPrefixZero : prefixLength 0 = 0)
    (hPrefixStep :
      ∀ index, index < count →
        prefixLength (index + 1) =
          prefixLength index + pieceLength index)
    (hPieceDomain :
      ∀ index, index < count →
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(family ·ₘ numₘ(index)) ≐ₘ
            numₘ(pieceLength index)) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(flattenₘ(family)) ≐ₘ
        numₘ(prefixLength count) := by
  let conclusion : SetFormula :=
    domₘ(flattenₘ(family)) ≐ₘ
      numₘ(prefixLength count)
  let eigen : FreeVarId :=
    FreshVariable.fresh_id SetSort.set
      (conclusion :: (family ≐ₘ family) :: Γ)
  let accumulator : SetTerm := x#eigen
  let body : SetFormula :=
    finite_sequence_condition accumulator ∧ₘ
      ((domₘ(accumulator) ≐ₘ
          Sₘ(domₘ(family))) ∧ₘ
        (((accumulator ·ₘ numₘ(0)) ≐ₘ ∅ₘ) ∧ₘ
          ((∀ₘ[SetSort.set],
              finite_sequence_flatten_step_condition
                family accumulator bₛ#0) ∧ₘ
            (flattenₘ(family) ≐ₘ
              (accumulator ·ₘ domₘ(family))))))
  have hFamilyFresh :
      (SetSort.set, eigen) ∉
        Term.freeSupport family := by
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas :=
          conclusion :: (family ≐ₘ family) :: Γ)
        (formula := family ≐ₘ family)
        (by simp)
    simpa [eigen, Formula.freeSupport] using hFresh
  have hFamilyClose
      (depth : Nat) :
      Term.closeFreeAt SetSort.set eigen depth family =
        family :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set eigen depth family
      hFamily.2 hFamilyFresh
  have hFamilyOpen
      (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement family =
        family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement family hFamily.2
  have hSpec :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_flatten_spec
          family (flattenₘ(family)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            finite_sequence_flatten_term_spec_derives
              family hFamily)
      hFamilyCondition
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, eigen], body := by
    simpa [finite_sequence_flatten_spec,
      finite_sequence_flatten_step_condition,
      finite_sequence_condition, is_function_formula,
      body, accumulator,
      Formula.closeFreeAt, Term.closeFreeAt,
      Formula.next_depth, domain_term,
      successor_term, function_application_term,
      finite_sequence_concatenation_term,
      finite_sequence_flatten_term,
      finite_numeral_term, set_variable,
      set_bound_variable, hFamilyClose] using
      FirstOrder.Derives.conjElimRight hSpec
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := eigen)
    (body := body)
    (conclusion := conclusion)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    exact FreshVariable.fresh_id_not_mem_m
      (sort := SetSort.set)
      (formulas :=
        conclusion :: (family ≐ₘ family) :: Γ)
      (formula := formula)
      (by simp [hFormula])
  · exact FreshVariable.fresh_id_not_mem_m
      (sort := SetSort.set)
      (formulas :=
        conclusion :: (family ≐ₘ family) :: Γ)
      (formula := conclusion)
      (by simp)
  · exact hExists
  · let Δ : Context signature := body :: Γ
    have hAccumulator :
        Term.Admissible accumulator SetSort.set := by
      simpa [accumulator] using
        set_variable_admissible eigen
    have hAccumulatorAt
        (index : Nat) :
        Term.Admissible
          (accumulator ·ₘ numₘ(index)) SetSort.set :=
      function_application_term_admissible
        accumulator (numₘ(index))
        hAccumulator
        (finite_numeral_term_admissible index)
    have hFamilyAt
        (index : Nat) :
        Term.Admissible
          (family ·ₘ numₘ(index)) SetSort.set :=
      function_application_term_admissible
        family (numₘ(index))
        hFamily
        (finite_numeral_term_admissible index)
    have hAccumulatorOpen
        (depth : Nat) (replacement : SetTerm) :
        Term.openAt SetSort.set depth replacement
            accumulator =
          accumulator :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set depth replacement accumulator
        hAccumulator.2
    have hBody :
        Δ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hData :=
      FirstOrder.Derives.conjElimRight hBody
    have hInitial :
        Δ ⊢ₘ[godel_quotation_theory]
          (accumulator ·ₘ numₘ(0)) ≐ₘ ∅ₘ := by
      simpa [body] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hData
    have hStepForall :
        Δ ⊢ₘ[godel_quotation_theory]
          ∀ₘ[SetSort.set],
            finite_sequence_flatten_step_condition
              family accumulator bₛ#0 := by
      simpa [body] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight <|
            FirstOrder.Derives.conjElimRight hData
    have hTerminalAtDomain :
        Δ ⊢ₘ[godel_quotation_theory]
          flattenₘ(family) ≐ₘ
            (accumulator ·ₘ domₘ(family)) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight <|
            FirstOrder.Derives.conjElimRight hData
    have hFamilyConditionΔ :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_family_condition family :=
      FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ) (by
          intro formula hFormula
          exact List.mem_cons_of_mem body hFormula)
        hFamilyCondition
    have hFamilyDomainΔ :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(family) ≐ₘ numₘ(count) :=
      FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ) (by
          intro formula hFormula
          exact List.mem_cons_of_mem body hFormula)
        hFamilyDomain
    have hPointDomain
        (index : Nat) (hIndex : index < count) :
        Δ ⊢ₘ[godel_quotation_theory]
          numₘ(index) ∈ₘ domₘ(family) := by
      have hNumeral :
          Δ ⊢ₘ[godel_quotation_theory]
            numₘ(index) ∈ₘ numₘ(count) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_weaken_standard_sequence <|
              standard_sequence_finite_numeral_mem_of_lt
                index count hIndex
      exact FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          (numₘ(index))
          (domₘ(family))
          (numₘ(count))
          (finite_numeral_term_admissible index)
          (domain_term_admissible family hFamily)
          (finite_numeral_term_admissible count)
          hFamilyDomainΔ)
        hNumeral
    have hFamilyFinite :
        ∀ index, index < count →
          Δ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition
              (family ·ₘ numₘ(index)) := by
      intro index hIndex
      have hAll :=
        FirstOrder.Derives.conjElimRight
          hFamilyConditionΔ
      have hAt :=
        FirstOrder.Derives.forall_elim
          (term := numₘ(index)) hAll
      have hImp :
          Δ ⊢ₘ[godel_quotation_theory]
            (numₘ(index) ∈ₘ domₘ(family)) ⟶ₘ
              finite_sequence_condition
                (family ·ₘ numₘ(index)) := by
        simpa [finite_sequence_family_condition,
          finite_sequence_condition,
          Formula.openAt, Formula.next_depth,
          Formula.substituteFree,
          Term.openAt, Term.substituteFree,
          domain_term, function_application_term,
          is_function_formula,
          set_bound_variable,
          hFamilyOpen] using hAt
      exact FirstOrder.Derives.impElim
        hImp (hPointDomain index hIndex)
    have hStep :
        ∀ index, index < count →
          Δ ⊢ₘ[godel_quotation_theory]
            (accumulator ·ₘ numₘ(index + 1)) ≐ₘ
              ((accumulator ·ₘ numₘ(index)) ⌢ₘ
                (family ·ₘ numₘ(index))) := by
      intro index hIndex
      have hAt :=
        FirstOrder.Derives.forall_elim
          (term := numₘ(index)) hStepForall
      have hImp :
          Δ ⊢ₘ[godel_quotation_theory]
            (numₘ(index) ∈ₘ domₘ(family)) ⟶ₘ
              ((accumulator ·ₘ numₘ(index + 1)) ≐ₘ
                ((accumulator ·ₘ numₘ(index)) ⌢ₘ
                  (family ·ₘ numₘ(index)))) := by
        simpa [finite_sequence_flatten_step_condition,
          Formula.openAt, Formula.next_depth,
          Formula.substituteFree,
          Term.openAt, Term.substituteFree,
          successor_term, domain_term,
          function_application_term,
          finite_sequence_concatenation_term,
          finite_numeral_term,
          set_bound_variable,
          hFamilyOpen, hAccumulatorOpen] using hAt
      exact FirstOrder.Derives.impElim
        hImp (hPointDomain index hIndex)
    have hEmptyFinite :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition ∅ₘ := by
      apply FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ])
      apply gq_weaken_standard_sequence
      simpa [standard_sequence,
        standard_sequence_from] using
        (standard_sequence_finite_sequence_condition
          (elements := [])
          (by simp)
          (by simp)
          (by simp)
          (by simp))
    have hAccumulatorFinite :
        ∀ index, index ≤ count →
          Δ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition
              (accumulator ·ₘ numₘ(index)) := by
      intro index
      induction index with
      | zero =>
          intro _
          exact FirstOrder.Derives.iffElimLeft
            (finite_sequence_condition_iff_of_equality
              (accumulator ·ₘ numₘ(0)) ∅ₘ
              (hAccumulatorAt 0)
              empty_set_term_admissible hInitial)
            hEmptyFinite
      | succ index ih =>
          intro hIndex
          have hIndexLt :
              index < count :=
            Nat.lt_of_succ_le hIndex
          have hPrevious :=
            ih (Nat.le_of_lt hIndexLt)
          have hCurrent :=
            hFamilyFinite index hIndexLt
          have hConcatenation :=
            gq_concatenation_finite
              (accumulator ·ₘ numₘ(index))
              (family ·ₘ numₘ(index))
              hPrevious hCurrent
          simpa [Nat.succ_eq_add_one] using
            (FirstOrder.Derives.iffElimLeft
              (finite_sequence_condition_iff_of_equality
                (accumulator ·ₘ numₘ(index + 1))
                ((accumulator ·ₘ numₘ(index)) ⌢ₘ
                  (family ·ₘ numₘ(index)))
                (hAccumulatorAt (index + 1))
                (finite_sequence_concatenation_term_admissible
                  (accumulator ·ₘ numₘ(index))
                  (family ·ₘ numₘ(index))
                  (hAccumulatorAt index)
                  (hFamilyAt index))
                (hStep index hIndexLt))
              hConcatenation)
    have hPieceDomainΔ :
        ∀ index, index < count →
          Δ ⊢ₘ[godel_quotation_theory]
            domₘ(family ·ₘ numₘ(index)) ≐ₘ
              numₘ(pieceLength index) := by
      intro index hIndex
      exact FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ) (by
          intro formula hFormula
          exact List.mem_cons_of_mem body hFormula)
        (hPieceDomain index hIndex)
    have hAccumulatorDomain :=
      gq_flatten_checked_replay_prefix_domain
        (Γ := Δ)
        family accumulator count
        pieceLength prefixLength
        hFamily hAccumulator
        hPrefixZero hPrefixStep
        hAccumulatorFinite hFamilyFinite
        hInitial hStep hPieceDomainΔ
        count (Nat.le_refl count)
    have hTerminalArgument :
        Δ ⊢ₘ[godel_quotation_theory]
          (accumulator ·ₘ domₘ(family)) ≐ₘ
            (accumulator ·ₘ numₘ(count)) :=
      function_application_term_congr_argument_of_equality
        accumulator (domₘ(family)) (numₘ(count))
        hAccumulator
        (domain_term_admissible family hFamily)
        (finite_numeral_term_admissible count)
        hFamilyDomainΔ
    have hTerminal :
        Δ ⊢ₘ[godel_quotation_theory]
          flattenₘ(family) ≐ₘ
            (accumulator ·ₘ numₘ(count)) :=
      Metatheory.Derives.equality_trans
        hTerminalAtDomain hTerminalArgument
    have hTerminalDomain :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(flattenₘ(family)) ≐ₘ
            domₘ(accumulator ·ₘ numₘ(count)) :=
      domain_term_congr_of_equality
        (flattenₘ(family))
        (accumulator ·ₘ numₘ(count))
        (finite_sequence_flatten_term_admissible
          family hFamily)
        (hAccumulatorAt count)
        hTerminal
    simpa [conclusion] using
      Metatheory.Derives.equality_trans
        hTerminalDomain hAccumulatorDomain

/--
有限 numeral 定义域上的 `flattenₘ` 分片标准切片反演。

调用方只提供各分片长度及其前缀和；累积器存在见证、新鲜变量与逐步点传播全部
在本证明内部消去。`hSliceBound` 是外部 checked shape payload，避免从对象等式
反向提升宿主自然数相等。
-/
theorem gq_flatten_numeral_point_eq_standard_slice
    {Γ : Context signature}
    (family : SetTerm)
    (tokens : List Nat)
    (count selected : Nat)
    (pieceLength prefixLength : Nat → Nat)
    (hFamily : Term.Admissible family SetSort.set)
    (hFamilyCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition family)
    (hFamilyDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(family) ≐ₘ numₘ(count))
    (hPrefixZero : prefixLength 0 = 0)
    (hPrefixStep :
      ∀ index, index < count →
        prefixLength (index + 1) =
          prefixLength index + pieceLength index)
    (hPieceDomain :
      ∀ index, index < count →
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(family ·ₘ numₘ(index)) ≐ₘ
            numₘ(pieceLength index))
    (hStandard :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          flattenₘ(family))
    (hSelected : selected < count)
    (hSliceBound :
      prefixLength selected +
          pieceLength selected ≤
        tokens.length) :
    Γ ⊢ₘ[godel_quotation_theory]
      (family ·ₘ numₘ(selected)) ≐ₘ
        standard_token_sequence
          ((tokens.drop (prefixLength selected)).take
            (pieceLength selected)) := by
  let selectedTokens : List Nat :=
    (tokens.drop (prefixLength selected)).take
      (pieceLength selected)
  let conclusion : SetFormula :=
    (family ·ₘ numₘ(selected)) ≐ₘ
      standard_token_sequence selectedTokens
  let eigen : FreeVarId :=
    FreshVariable.fresh_id SetSort.set
      (conclusion :: (family ≐ₘ family) :: Γ)
  let accumulator : SetTerm := x#eigen
  let body : SetFormula :=
    finite_sequence_condition accumulator ∧ₘ
      ((domₘ(accumulator) ≐ₘ
          Sₘ(domₘ(family))) ∧ₘ
        (((accumulator ·ₘ numₘ(0)) ≐ₘ ∅ₘ) ∧ₘ
          ((∀ₘ[SetSort.set],
              finite_sequence_flatten_step_condition
                family accumulator bₛ#0) ∧ₘ
            (flattenₘ(family) ≐ₘ
              (accumulator ·ₘ domₘ(family))))))
  have hSelectedTokensLength :
      selectedTokens.length =
        pieceLength selected := by
    simp only [selectedTokens, List.length_take,
      List.length_drop]
    omega
  have hFamilyFresh :
      (SetSort.set, eigen) ∉
        Term.freeSupport family := by
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m
        (sort := SetSort.set)
        (formulas :=
          conclusion :: (family ≐ₘ family) :: Γ)
        (formula := family ≐ₘ family)
        (by simp)
    simpa [eigen, Formula.freeSupport] using hFresh
  have hFamilyClose
      (depth : Nat) :
      Term.closeFreeAt SetSort.set eigen depth family =
        family :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set eigen depth family
      hFamily.2 hFamilyFresh
  have hFamilyOpen
      (depth : Nat) (replacement : SetTerm) :
      Term.openAt SetSort.set depth replacement family =
        family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth replacement family hFamily.2
  have hSpec :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_flatten_spec
          family (flattenₘ(family)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_weaken_standard_sequence <|
            finite_sequence_flatten_term_spec_derives
              family hFamily)
      hFamilyCondition
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, eigen], body := by
    simpa [finite_sequence_flatten_spec,
      finite_sequence_flatten_step_condition,
      finite_sequence_condition, is_function_formula,
      body, accumulator,
      Formula.closeFreeAt, Term.closeFreeAt,
      Formula.next_depth, domain_term,
      successor_term, function_application_term,
      finite_sequence_concatenation_term,
      finite_sequence_flatten_term,
      finite_numeral_term, set_variable,
      set_bound_variable, hFamilyClose] using
      FirstOrder.Derives.conjElimRight hSpec
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := eigen)
    (body := body)
    (conclusion := conclusion)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    exact FreshVariable.fresh_id_not_mem_m
      (sort := SetSort.set)
      (formulas :=
        conclusion :: (family ≐ₘ family) :: Γ)
      (formula := formula)
      (by simp [hFormula])
  · exact FreshVariable.fresh_id_not_mem_m
      (sort := SetSort.set)
      (formulas :=
        conclusion :: (family ≐ₘ family) :: Γ)
      (formula := conclusion)
      (by simp)
  · exact hExists
  · let Δ : Context signature := body :: Γ
    have hAccumulator :
        Term.Admissible accumulator SetSort.set := by
      simpa [accumulator] using
        set_variable_admissible eigen
    have hAccumulatorAt
        (index : Nat) :
        Term.Admissible
          (accumulator ·ₘ numₘ(index)) SetSort.set :=
      function_application_term_admissible
        accumulator (numₘ(index))
        hAccumulator
        (finite_numeral_term_admissible index)
    have hFamilyAt
        (index : Nat) :
        Term.Admissible
          (family ·ₘ numₘ(index)) SetSort.set :=
      function_application_term_admissible
        family (numₘ(index))
        hFamily
        (finite_numeral_term_admissible index)
    have hAccumulatorOpen
        (depth : Nat) (replacement : SetTerm) :
        Term.openAt SetSort.set depth replacement
            accumulator =
          accumulator :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set depth replacement accumulator
        hAccumulator.2
    have hBody :
        Δ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hData :=
      FirstOrder.Derives.conjElimRight hBody
    have hInitial :
        Δ ⊢ₘ[godel_quotation_theory]
          (accumulator ·ₘ numₘ(0)) ≐ₘ ∅ₘ := by
      simpa [body] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hData
    have hStepForall :
        Δ ⊢ₘ[godel_quotation_theory]
          ∀ₘ[SetSort.set],
            finite_sequence_flatten_step_condition
              family accumulator bₛ#0 := by
      simpa [body] using
        FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight <|
            FirstOrder.Derives.conjElimRight hData
    have hTerminalAtDomain :
        Δ ⊢ₘ[godel_quotation_theory]
          flattenₘ(family) ≐ₘ
            (accumulator ·ₘ domₘ(family)) := by
      simpa [body] using
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight <|
            FirstOrder.Derives.conjElimRight hData
    have hFamilyConditionΔ :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_family_condition family :=
      FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ) (by
          intro formula hFormula
          exact List.mem_cons_of_mem body hFormula)
        hFamilyCondition
    have hFamilyDomainΔ :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(family) ≐ₘ numₘ(count) :=
      FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ) (by
          intro formula hFormula
          exact List.mem_cons_of_mem body hFormula)
        hFamilyDomain
    have hStandardΔ :
        Δ ⊢ₘ[godel_quotation_theory]
          standard_token_sequence tokens ≐ₘ
            flattenₘ(family) :=
      FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ) (by
          intro formula hFormula
          exact List.mem_cons_of_mem body hFormula)
        hStandard
    have hPointDomain
        (index : Nat) (hIndex : index < count) :
        Δ ⊢ₘ[godel_quotation_theory]
          numₘ(index) ∈ₘ domₘ(family) := by
      have hNumeral :
          Δ ⊢ₘ[godel_quotation_theory]
            numₘ(index) ∈ₘ numₘ(count) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_weaken_standard_sequence <|
              standard_sequence_finite_numeral_mem_of_lt
                index count hIndex
      exact FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          (numₘ(index))
          (domₘ(family))
          (numₘ(count))
          (finite_numeral_term_admissible index)
          (domain_term_admissible family hFamily)
          (finite_numeral_term_admissible count)
          hFamilyDomainΔ)
        hNumeral
    have hFamilyFinite :
        ∀ index, index < count →
          Δ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition
              (family ·ₘ numₘ(index)) := by
      intro index hIndex
      have hAll :=
        FirstOrder.Derives.conjElimRight
          hFamilyConditionΔ
      have hAt :=
        FirstOrder.Derives.forall_elim
          (term := numₘ(index)) hAll
      have hImp :
          Δ ⊢ₘ[godel_quotation_theory]
            (numₘ(index) ∈ₘ domₘ(family)) ⟶ₘ
              finite_sequence_condition
                (family ·ₘ numₘ(index)) := by
        simpa [finite_sequence_family_condition,
          finite_sequence_condition,
          Formula.openAt, Formula.next_depth,
          Formula.substituteFree,
          Term.openAt, Term.substituteFree,
          domain_term, function_application_term,
          is_function_formula,
          set_bound_variable,
          hFamilyOpen] using hAt
      exact FirstOrder.Derives.impElim
        hImp (hPointDomain index hIndex)
    have hStep :
        ∀ index, index < count →
          Δ ⊢ₘ[godel_quotation_theory]
            (accumulator ·ₘ numₘ(index + 1)) ≐ₘ
              ((accumulator ·ₘ numₘ(index)) ⌢ₘ
                (family ·ₘ numₘ(index))) := by
      intro index hIndex
      have hAt :=
        FirstOrder.Derives.forall_elim
          (term := numₘ(index)) hStepForall
      have hImp :
          Δ ⊢ₘ[godel_quotation_theory]
            (numₘ(index) ∈ₘ domₘ(family)) ⟶ₘ
              ((accumulator ·ₘ numₘ(index + 1)) ≐ₘ
                ((accumulator ·ₘ numₘ(index)) ⌢ₘ
                  (family ·ₘ numₘ(index)))) := by
        simpa [finite_sequence_flatten_step_condition,
          Formula.openAt, Formula.next_depth,
          Formula.substituteFree,
          Term.openAt, Term.substituteFree,
          successor_term, domain_term,
          function_application_term,
          finite_sequence_concatenation_term,
          finite_numeral_term,
          set_bound_variable,
          hFamilyOpen, hAccumulatorOpen] using hAt
      exact FirstOrder.Derives.impElim
        hImp (hPointDomain index hIndex)
    have hEmptyFinite :
        Δ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition ∅ₘ := by
      apply FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ])
      apply gq_weaken_standard_sequence
      simpa [standard_sequence,
        standard_sequence_from] using
        (standard_sequence_finite_sequence_condition
          (elements := [])
          (by simp)
          (by simp)
          (by simp)
          (by simp))
    have hAccumulatorFinite :
        ∀ index, index ≤ count →
          Δ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition
              (accumulator ·ₘ numₘ(index)) := by
      intro index
      induction index with
      | zero =>
          intro _
          exact FirstOrder.Derives.iffElimLeft
            (finite_sequence_condition_iff_of_equality
              (accumulator ·ₘ numₘ(0)) ∅ₘ
              (hAccumulatorAt 0)
              empty_set_term_admissible hInitial)
            hEmptyFinite
      | succ index ih =>
          intro hIndex
          have hIndexLt :
              index < count :=
            Nat.lt_of_succ_le hIndex
          have hPrevious :=
            ih (Nat.le_of_lt hIndexLt)
          have hCurrent :=
            hFamilyFinite index hIndexLt
          have hConcatenation :=
            gq_concatenation_finite
              (accumulator ·ₘ numₘ(index))
              (family ·ₘ numₘ(index))
              hPrevious hCurrent
          simpa [Nat.succ_eq_add_one] using
            (FirstOrder.Derives.iffElimLeft
              (finite_sequence_condition_iff_of_equality
                (accumulator ·ₘ numₘ(index + 1))
                ((accumulator ·ₘ numₘ(index)) ⌢ₘ
                  (family ·ₘ numₘ(index)))
                (hAccumulatorAt (index + 1))
                (finite_sequence_concatenation_term_admissible
                  (accumulator ·ₘ numₘ(index))
                  (family ·ₘ numₘ(index))
                  (hAccumulatorAt index)
                  (hFamilyAt index))
                (hStep index hIndexLt))
              hConcatenation)
    have hPieceDomainΔ :
        ∀ index, index < count →
          Δ ⊢ₘ[godel_quotation_theory]
            domₘ(family ·ₘ numₘ(index)) ≐ₘ
              numₘ(pieceLength index) := by
      intro index hIndex
      exact FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ) (by
          intro formula hFormula
          exact List.mem_cons_of_mem body hFormula)
        (hPieceDomain index hIndex)
    have hPrefixDomain :=
      gq_flatten_checked_replay_prefix_domain
        (Γ := Δ)
        family accumulator count
        pieceLength prefixLength
        hFamily hAccumulator
        hPrefixZero hPrefixStep
        hAccumulatorFinite hFamilyFinite
        hInitial hStep hPieceDomainΔ
        selected (Nat.le_of_lt hSelected)
    have hTerminalArgument :
        Δ ⊢ₘ[godel_quotation_theory]
          (accumulator ·ₘ domₘ(family)) ≐ₘ
            (accumulator ·ₘ numₘ(count)) :=
      function_application_term_congr_argument_of_equality
        accumulator (domₘ(family)) (numₘ(count))
        hAccumulator
        (domain_term_admissible family hFamily)
        (finite_numeral_term_admissible count)
        hFamilyDomainΔ
    have hTerminal :
        Δ ⊢ₘ[godel_quotation_theory]
          flattenₘ(family) ≐ₘ
            (accumulator ·ₘ numₘ(count)) :=
      Metatheory.Derives.equality_trans
        hTerminalAtDomain hTerminalArgument
    have hSelectedFinite :=
      hFamilyFinite selected hSelected
    have hSelectedFunction :
        Δ ⊢ₘ[godel_quotation_theory]
          is_function_formula
            (family ·ₘ numₘ(selected)) := by
      simpa [finite_sequence_condition] using
        FirstOrder.Derives.conjElimLeft
          hSelectedFinite
    have hSelectedDomain :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(family ·ₘ numₘ(selected)) ≐ₘ
            numₘ(selectedTokens.length) := by
      simpa [hSelectedTokensLength] using
        hPieceDomainΔ selected hSelected
    change
      Δ ⊢ₘ[godel_quotation_theory]
        (family ·ₘ numₘ(selected)) ≐ₘ
          standard_token_sequence selectedTokens
    apply
      gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
        (T := godel_quotation_theory)
        (Γ := Δ)
        (fun _ hAxiom => Or.inl hAxiom)
        (fun _ hFormula =>
          godel_quotation_theory_sentence hFormula)
        (family ·ₘ numₘ(selected))
        selectedTokens
        hSelectedFunction hSelectedDomain
        (hSource := by prove_term_check)
    intro index token hGet
    have hIndex :
        index < selectedTokens.length :=
      (List.getElem?_eq_some_iff.mp hGet).1
    have hSliceIndex :
        index < pieceLength selected := by
      simpa [hSelectedTokensLength] using hIndex
    have hDropGet :
        (tokens.drop
            (prefixLength selected))[index]? =
          some token := by
      rw [List.getElem?_take_of_lt hSliceIndex] at hGet
      simpa [selectedTokens] using hGet
    have hTokenGet :
        tokens[prefixLength selected + index]? =
          some token := by
      simpa using hDropGet
    exact gq_flatten_checked_replay_point_value
      (Γ := Δ)
      family accumulator tokens count selected
      (prefixLength selected) index
      (pieceLength selected) token
      hFamily hAccumulator
      hSelected hSliceIndex
      hAccumulatorFinite hFamilyFinite hStep
      hPrefixDomain
      (hPieceDomainΔ selected hSelected)
      hTerminal hStandardΔ hTokenGet

/--
有限 numeral family 的单片反演可沿任意包含 Gödel quotation 的理论使用。

所有逐片定义域等式只作为有限临时上下文进入固定内核定理；该接口仅要求这些
有限局部前提。
-/
theorem gq_flatten_numeral_point_eq_standard_slice_of_theory
    {T : Theory signature}
    {Γ : Context signature}
    (hTheory :
      ∀ formula,
        godel_quotation_theory formula →
          T formula)
    (family : SetTerm)
    (tokens : List Nat)
    (count selected : Nat)
    (pieceLength prefixLength : Nat → Nat)
    (hFamily :
      Term.Admissible family SetSort.set)
    (hFamilyCondition :
      Γ ⊢ₘ[T]
        finite_sequence_family_condition family)
    (hFamilyDomain :
      Γ ⊢ₘ[T]
        domₘ(family) ≐ₘ numₘ(count))
    (hPrefixZero : prefixLength 0 = 0)
    (hPrefixStep :
      ∀ index, index < count →
        prefixLength (index + 1) =
          prefixLength index + pieceLength index)
    (hPieceDomain :
      ∀ index, index < count →
        Γ ⊢ₘ[T]
          domₘ(family ·ₘ numₘ(index)) ≐ₘ
            numₘ(pieceLength index))
    (hStandard :
      Γ ⊢ₘ[T]
        standard_token_sequence tokens ≐ₘ
          flattenₘ(family))
    (hSelected : selected < count)
    (hSliceBound :
      prefixLength selected +
          pieceLength selected ≤
        tokens.length) :
    Γ ⊢ₘ[T]
      (family ·ₘ numₘ(selected)) ≐ₘ
        standard_token_sequence
          ((tokens.drop (prefixLength selected)).take
            (pieceLength selected)) := by
  let piecePremises : Context signature :=
    (List.range count).map fun index =>
      domₘ(family ·ₘ numₘ(index)) ≐ₘ
        numₘ(pieceLength index)
  let Δ : Context signature :=
    [finite_sequence_family_condition family,
      domₘ(family) ≐ₘ numₘ(count),
      standard_token_sequence tokens ≐ₘ
        flattenₘ(family)] ++ piecePremises
  have hFamilyConditionAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition family :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hFamilyDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(family) ≐ₘ numₘ(count) :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hStandardAt :
      Δ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          flattenₘ(family) :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hPieceDomainAt :
      ∀ index, index < count →
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(family ·ₘ numₘ(index)) ≐ₘ
            numₘ(pieceLength index) := by
    intro index hIndex
    apply FirstOrder.Derives.assumption
    · apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      exact ⟨index, by simpa using hIndex, rfl⟩
    · exact Formula.check_admissible_complete <|
        Formula.Admissible.equal
          (domain_term_admissible
            (family ·ₘ numₘ(index))
            (function_application_term_admissible
              family (numₘ(index)) hFamily
              (finite_numeral_term_admissible index)))
          (finite_numeral_term_admissible
            (pieceLength index))
  have hResult :
      Δ ⊢ₘ[godel_quotation_theory]
        (family ·ₘ numₘ(selected)) ≐ₘ
          standard_token_sequence
            ((tokens.drop (prefixLength selected)).take
              (pieceLength selected)) :=
    gq_flatten_numeral_point_eq_standard_slice
      family tokens count selected
      pieceLength prefixLength hFamily
      hFamilyConditionAt hFamilyDomainAt
      hPrefixZero hPrefixStep hPieceDomainAt
      hStandardAt hSelected hSliceBound
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    rcases List.mem_append.mp hFormula with
      hHead | hPiece
    · simp only [List.mem_cons, List.mem_nil_iff,
        or_false]
        at hHead
      rcases hHead with rfl | rfl | rfl
      · exact hFamilyCondition
      · exact hFamilyDomain
      · exact hStandard
    · rcases List.mem_map.mp hPiece with
        ⟨index, hIndex, rfl⟩
      exact hPieceDomain index (by simpa using hIndex)
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hResult).context_weaken_append

/--
二元、每片长度为一的参数族仅由 family guard 与分片定义域恢复 flatten 总长度。

该接口不依赖 flatten 已经等于某个标准 token 串，因此可以先为统一应用正文切片
提供长度，再进入逐片反演。
-/
theorem gq_flatten_pair_domain_eq_two_of_theory
    {T : Theory signature}
    {Γ : Context signature}
    (hTheory :
      ∀ formula,
        godel_quotation_theory formula →
          T formula)
    (family : SetTerm)
    (hFamilyCondition :
      Γ ⊢ₘ[T]
        finite_sequence_family_condition family)
    (hFamilyDomain :
      Γ ⊢ₘ[T]
        domₘ(family) ≐ₘ numₘ(2))
    (hFirstDomain :
      Γ ⊢ₘ[T]
        domₘ(family ·ₘ numₘ(0)) ≐ₘ numₘ(1))
    (hSecondDomain :
      Γ ⊢ₘ[T]
        domₘ(family ·ₘ numₘ(1)) ≐ₘ numₘ(1))
    (hFamilyCheck :
      Term.CheckCertificate family SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[T]
      domₘ(flattenₘ(family)) ≐ₘ numₘ(2) := by
  let first : SetTerm := family ·ₘ numₘ(0)
  let second : SetTerm := family ·ₘ numₘ(1)
  let Δ : Context signature := [
    finite_sequence_family_condition family,
    (domₘ(family) ≐ₘ numₘ(2)),
    (domₘ(first) ≐ₘ numₘ(1)),
    (domₘ(second) ≐ₘ numₘ(1))]
  have hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
    prove_term_check
  have hSecondCheck :
      Term.CheckCertificate second SetSort.set := by
    prove_term_check
  have hFamilyConditionAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition family :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (by prove_nd_formula_check)
  have hFamilyDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(family) ≐ₘ numₘ(2) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (domain_term_admissible
            family hFamilyCheck.admissible)
          (finite_numeral_term_admissible 2)))
  have hFirstDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (domain_term_admissible
            first hFirstCheck.admissible)
          (finite_numeral_term_admissible 1)))
  have hSecondDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(second) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (domain_term_admissible
            second hSecondCheck.admissible)
          (finite_numeral_term_admissible 1)))
  let pieceLength : Nat → Nat := fun _ => 1
  let prefixLength : Nat → Nat := fun index => index
  have hPieceDomain :
      ∀ index, index < 2 →
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(family ·ₘ numₘ(index)) ≐ₘ
            numₘ(pieceLength index) := by
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 := by
      omega
    rcases hCases with rfl | rfl
    · simpa [first, pieceLength] using
        hFirstDomainAt
    · simpa [second, pieceLength] using
        hSecondDomainAt
  have hDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(flattenₘ(family)) ≐ₘ numₘ(2) := by
    simpa [prefixLength] using
      gq_flatten_numeral_domain_eq_prefix_length
        family 2 pieceLength prefixLength
        hFamilyCheck.admissible
        hFamilyConditionAt hFamilyDomainAt
        (by simp [prefixLength])
        (by
          intro index hIndex
          simp [prefixLength, pieceLength])
        hPieceDomain
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    simp [Δ, first, second] at hFormula
    rcases hFormula with
      rfl | rfl | rfl | rfl
    · exact hFamilyCondition
    · exact hFamilyDomain
    · exact hFirstDomain
    · exact hSecondDomain
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hDomain).context_weaken_append

/--
二元、每片长度为一的参数族同时恢复 flatten 总长度与两个标准切片。

这是二元函数和谓词应用反演的公共 checked replay。全部对象前提仅进入有限临时
上下文。
-/
theorem gq_flatten_pair_domain_and_parts_of_theory
    {T : Theory signature}
    {Γ : Context signature}
    (hTheory :
      ∀ formula,
        godel_quotation_theory formula →
          T formula)
    (family : SetTerm)
    (tokens : List Nat)
    (hFamilyCondition :
      Γ ⊢ₘ[T]
        finite_sequence_family_condition family)
    (hFamilyDomain :
      Γ ⊢ₘ[T]
        domₘ(family) ≐ₘ numₘ(2))
    (hFirstDomain :
      Γ ⊢ₘ[T]
        domₘ(family ·ₘ numₘ(0)) ≐ₘ numₘ(1))
    (hSecondDomain :
      Γ ⊢ₘ[T]
        domₘ(family ·ₘ numₘ(1)) ≐ₘ numₘ(1))
    (hStandard :
      Γ ⊢ₘ[T]
        standard_token_sequence tokens ≐ₘ
          flattenₘ(family))
    (hSliceBound : 2 ≤ tokens.length)
    (hFamilyCheck :
      Term.CheckCertificate family SetSort.set := by
        prove_term_check) :
    Γ ⊢ₘ[T]
      (domₘ(flattenₘ(family)) ≐ₘ numₘ(2)) ∧ₘ
        (((family ·ₘ numₘ(0)) ≐ₘ
            standard_token_sequence
              ((tokens.drop 0).take 1)) ∧ₘ
          ((family ·ₘ numₘ(1)) ≐ₘ
            standard_token_sequence
              ((tokens.drop 1).take 1))) := by
  let first : SetTerm := family ·ₘ numₘ(0)
  let second : SetTerm := family ·ₘ numₘ(1)
  let Δ : Context signature := [
    finite_sequence_family_condition family,
    (domₘ(family) ≐ₘ numₘ(2)),
    (domₘ(first) ≐ₘ numₘ(1)),
    (domₘ(second) ≐ₘ numₘ(1)),
    (standard_token_sequence tokens ≐ₘ
      flattenₘ(family))]
  have hFirstCheck :
      Term.CheckCertificate first SetSort.set := by
    prove_term_check
  have hSecondCheck :
      Term.CheckCertificate second SetSort.set := by
    prove_term_check
  have hFlattenCheck :
      Term.CheckCertificate
        (flattenₘ(family)) SetSort.set := by
    prove_term_check
  have hFamilyConditionAt :
      Δ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition family :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (by prove_nd_formula_check)
  have hFamilyDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(family) ≐ₘ numₘ(2) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (domain_term_admissible
            family hFamilyCheck.admissible)
          (finite_numeral_term_admissible 2)))
  have hFirstDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(first) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (domain_term_admissible
            first hFirstCheck.admissible)
          (finite_numeral_term_admissible 1)))
  have hSecondDomainAt :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(second) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (domain_term_admissible
            second hSecondCheck.admissible)
          (finite_numeral_term_admissible 1)))
  have hStandardAt :
      Δ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence tokens ≐ₘ
          flattenₘ(family) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
      (Formula.check_admissible_complete
        (Formula.Admissible.equal
          (standard_token_sequence_admissible tokens)
          hFlattenCheck.admissible))
  let pieceLength : Nat → Nat := fun _ => 1
  let prefixLength : Nat → Nat := fun index => index
  have hPieceDomain :
      ∀ index, index < 2 →
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(family ·ₘ numₘ(index)) ≐ₘ
            numₘ(pieceLength index) := by
    intro index hIndex
    have hCases : index = 0 ∨ index = 1 := by
      omega
    rcases hCases with rfl | rfl
    · simpa [first, pieceLength] using
        hFirstDomainAt
    · simpa [second, pieceLength] using
        hSecondDomainAt
  have hDomain :
      Δ ⊢ₘ[godel_quotation_theory]
        domₘ(flattenₘ(family)) ≐ₘ numₘ(2) := by
    simpa [prefixLength] using
      gq_flatten_numeral_domain_eq_prefix_length
        family 2 pieceLength prefixLength
        hFamilyCheck.admissible
        hFamilyConditionAt hFamilyDomainAt
        (by simp [prefixLength])
        (by
          intro index hIndex
          simp [prefixLength, pieceLength])
        hPieceDomain
  have hFirst :
      Δ ⊢ₘ[godel_quotation_theory]
        (family ·ₘ numₘ(0)) ≐ₘ
          standard_token_sequence
            ((tokens.drop 0).take 1) := by
    simpa [pieceLength, prefixLength] using
      gq_flatten_numeral_point_eq_standard_slice
        family tokens 2 0 pieceLength prefixLength
        hFamilyCheck.admissible
        hFamilyConditionAt hFamilyDomainAt
        (by simp [prefixLength])
        (by
          intro index hIndex
          simp [prefixLength, pieceLength])
        hPieceDomain hStandardAt
        (by omega)
        (by
          have hBound : 1 ≤ tokens.length := by
            omega
          simpa [prefixLength, pieceLength] using
            hBound)
  have hSecond :
      Δ ⊢ₘ[godel_quotation_theory]
        (family ·ₘ numₘ(1)) ≐ₘ
          standard_token_sequence
            ((tokens.drop 1).take 1) := by
    simpa [pieceLength, prefixLength] using
      gq_flatten_numeral_point_eq_standard_slice
        family tokens 2 1 pieceLength prefixLength
        hFamilyCheck.admissible
        hFamilyConditionAt hFamilyDomainAt
        (by simp [prefixLength])
        (by
          intro index hIndex
          simp [prefixLength, pieceLength])
        hPieceDomain hStandardAt
        (by omega)
        (by
          simpa [prefixLength, pieceLength] using
            hSliceBound)
  have hResult :
      Δ ⊢ₘ[godel_quotation_theory]
        (domₘ(flattenₘ(family)) ≐ₘ numₘ(2)) ∧ₘ
          (((family ·ₘ numₘ(0)) ≐ₘ
              standard_token_sequence
                ((tokens.drop 0).take 1)) ∧ₘ
            ((family ·ₘ numₘ(1)) ≐ₘ
              standard_token_sequence
                ((tokens.drop 1).take 1))) :=
    FirstOrder.Derives.conjIntro hDomain <|
      FirstOrder.Derives.conjIntro hFirst hSecond
  apply FirstOrder.Derives.multi_cut
    (T := T) (Γ := Γ) (premises := Δ)
  · intro formula hFormula
    simp [Δ, first, second] at hFormula
    rcases hFormula with
      rfl | rfl | rfl | rfl | rfl
    · exact hFamilyCondition
    · exact hFamilyDomain
    · exact hFirstDomain
    · exact hSecondDomain
    · exact hStandard
  · exact
      (FirstOrder.Derives.theory_weaken
        hTheory hResult).context_weaken_append

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
