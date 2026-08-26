import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SequenceBound

/-!
# 有限序列族折叠的逐分片长度上界

本模块对 `flattenₘ` 规格中的有限累积器执行 checked replay。核心归纳完全发生在
Lean 宿主的外部有限自然数上；每一步只重放对象层拼接等式和对象自然加法上界。
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
private abbrev fsfb_at
    (sequence : SetTerm) (index : Nat) : SetTerm :=
  sequence ·ₘ numₘ(index)

/--
相等有限序列之间可反向运输定义域的非严格上界。
-/
private theorem fsfb_domain_le_transport
    {Γ : Context signature}
    (point source target : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hSource : Term.Admissible source SetSort.set)
    (hTarget : Term.Admissible target SetSort.set)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        source ≐ₘ target)
    (hBound :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ Sₘ(domₘ(target))) :
    Γ ⊢ₘ[godel_quotation_theory]
      point ∈ₘ Sₘ(domₘ(source)) := by
  have hDomainEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(source) ≐ₘ domₘ(target) :=
    domain_term_congr_of_equality
      source target hSource hTarget hEquality
  have hSuccessorEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        Sₘ(domₘ(source)) ≐ₘ
          Sₘ(domₘ(target)) :=
    successor_term_congr_of_equality
      (domₘ(source)) (domₘ(target))
      (domain_term_admissible source hSource)
      (domain_term_admissible target hTarget)
      hDomainEquality
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      point
      (Sₘ(domₘ(source)))
      (Sₘ(domₘ(target)))
      hPoint
      (successor_term_admissible
        (domₘ(source))
        (domain_term_admissible source hSource))
      (successor_term_admissible
        (domₘ(target))
        (domain_term_admissible target hTarget))
      hSuccessorEquality)
    hBound

/--
`flattenₘ` 累积器的有界 checked replay。

给定长度为 `count` 的参数族、累积器零值、每一步拼接证书和最终值证书，任意
`index < count` 的分片长度都不超过最终折叠长度。
-/
theorem gq_flatten_checked_replay_point_domain_le
    {Γ : Context signature}
    (family accumulator : SetTerm)
    (count index : Nat)
    (hFamily : Term.Admissible family SetSort.set)
    (hAccumulator : Term.Admissible accumulator SetSort.set)
    (hIndex : index < count)
    (hPointFinite :
      ∀ point, point < count →
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition
            (fsfb_at family point))
    (hInitial :
      Γ ⊢ₘ[godel_quotation_theory]
        fsfb_at accumulator 0 ≐ₘ ∅ₘ)
    (hStep :
      ∀ point, point < count →
        Γ ⊢ₘ[godel_quotation_theory]
          fsfb_at accumulator (point + 1) ≐ₘ
            (fsfb_at accumulator point ⌢ₘ
              fsfb_at family point))
    (hTerminal :
      Γ ⊢ₘ[godel_quotation_theory]
        flattenₘ(family) ≐ₘ
          fsfb_at accumulator count) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(fsfb_at family index) ∈ₘ
        Sₘ(domₘ(flattenₘ(family))) := by
  have hAccumulatorAt
      (point : Nat) :
      Term.Admissible
        (fsfb_at accumulator point) SetSort.set :=
    function_application_term_admissible
      accumulator (numₘ(point))
      hAccumulator
      (finite_numeral_term_admissible point)
  have hFamilyAt
      (point : Nat) :
      Term.Admissible
        (fsfb_at family point) SetSort.set :=
    function_application_term_admissible
      family (numₘ(point))
      hFamily
      (finite_numeral_term_admissible point)
  have hEmptyFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition ∅ₘ := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    apply gq_weaken_standard_sequence
    simpa [standard_sequence, standard_sequence_from] using
      (standard_sequence_finite_sequence_condition
        (elements := [])
        (by simp)
        (by simp)
        (by simp)
        (by simp))
  have hAccumulatorPointFinite :
      ∀ point, point ≤ count →
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition
            (fsfb_at accumulator point) := by
    intro point
    induction point with
    | zero =>
        intro _
        exact FirstOrder.Derives.iffElimLeft
          (finite_sequence_condition_iff_of_equality
            (fsfb_at accumulator 0) ∅ₘ
            (hAccumulatorAt 0)
            empty_set_term_admissible hInitial)
          hEmptyFinite
    | succ point ih =>
        intro hPointLe
        have hPointLt :
            point < count :=
          Nat.lt_of_succ_le hPointLe
        have hPreviousFinite :
            Γ ⊢ₘ[godel_quotation_theory]
              finite_sequence_condition
                (fsfb_at accumulator point) :=
          ih (Nat.le_of_lt hPointLt)
        have hCurrentFinite :
            Γ ⊢ₘ[godel_quotation_theory]
              finite_sequence_condition
                (fsfb_at family point) :=
          hPointFinite point hPointLt
        have hConcatenationFinite :
            Γ ⊢ₘ[godel_quotation_theory]
              finite_sequence_condition
                (fsfb_at accumulator point ⌢ₘ
                  fsfb_at family point) :=
          gq_concatenation_finite
            (fsfb_at accumulator point)
            (fsfb_at family point)
            hPreviousFinite hCurrentFinite
        have hStepEquality := hStep point hPointLt
        simpa [Nat.succ_eq_add_one] using
          (FirstOrder.Derives.iffElimLeft
            (finite_sequence_condition_iff_of_equality
              (fsfb_at accumulator (point + 1))
              (fsfb_at accumulator point ⌢ₘ
                fsfb_at family point)
              (hAccumulatorAt (point + 1))
              (finite_sequence_concatenation_term_admissible
                (fsfb_at accumulator point)
                (fsfb_at family point)
                (hAccumulatorAt point)
                (hFamilyAt point))
              hStepEquality)
            hConcatenationFinite)
  have hSelectedFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition
          (fsfb_at family index) :=
    hPointFinite index hIndex
  have hSelectedDomain :
      Term.Admissible
        (domₘ(fsfb_at family index)) SetSort.set :=
    domain_term_admissible
      (fsfb_at family index)
      (hFamilyAt index)
  have hSelectedOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(fsfb_at family index) ∈ₘ ωₘ := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hSelectedFinite
  have hFirstBound :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(fsfb_at family index) ∈ₘ
          Sₘ(domₘ(fsfb_at accumulator (index + 1))) := by
    have hPrefixFinite :
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition
            (fsfb_at accumulator index) :=
      hAccumulatorPointFinite index
        (Nat.le_of_lt hIndex)
    have hRawBound :=
      gq_concatenation_right_domain_le
        (fsfb_at accumulator index)
        (fsfb_at family index)
        (hAccumulatorAt index)
        (hFamilyAt index)
        hPrefixFinite hSelectedFinite
    exact fsfb_domain_le_transport
      (domₘ(fsfb_at family index))
      (fsfb_at accumulator (index + 1))
      (fsfb_at accumulator index ⌢ₘ
        fsfb_at family index)
      hSelectedDomain
      (hAccumulatorAt (index + 1))
      (finite_sequence_concatenation_term_admissible
        (fsfb_at accumulator index)
        (fsfb_at family index)
        (hAccumulatorAt index)
        (hFamilyAt index))
      (hStep index hIndex)
      hRawBound
  have hBoundAfter :
      ∀ offset, index + 1 + offset ≤ count →
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(fsfb_at family index) ∈ₘ
            Sₘ(domₘ(
              fsfb_at accumulator
                (index + 1 + offset))) := by
    intro offset
    induction offset with
    | zero =>
        intro _
        simpa using hFirstBound
    | succ offset ih =>
        intro hOffsetLe
        let point : Nat := index + 1 + offset
        have hPointLt :
            point < count := by
          simpa [point, Nat.succ_eq_add_one,
            Nat.add_assoc] using hOffsetLe
        have hPreviousBound :
            Γ ⊢ₘ[godel_quotation_theory]
              domₘ(fsfb_at family index) ∈ₘ
                Sₘ(domₘ(fsfb_at accumulator point)) := by
          simpa [point] using
            ih (Nat.le_of_lt hPointLt)
        have hPreviousFinite :
            Γ ⊢ₘ[godel_quotation_theory]
              finite_sequence_condition
                (fsfb_at accumulator point) :=
          hAccumulatorPointFinite point
            (Nat.le_of_lt hPointLt)
        have hCurrentFinite :
            Γ ⊢ₘ[godel_quotation_theory]
              finite_sequence_condition
                (fsfb_at family point) :=
          hPointFinite point hPointLt
        have hRawBound :=
          gq_concatenation_left_bound_le
            (domₘ(fsfb_at family index))
            (fsfb_at accumulator point)
            (fsfb_at family point)
            hSelectedDomain
            (hAccumulatorAt point)
            (hFamilyAt point)
            hSelectedOmega
            hPreviousFinite hCurrentFinite
            hPreviousBound
        have hTransported :=
          fsfb_domain_le_transport
            (domₘ(fsfb_at family index))
            (fsfb_at accumulator (point + 1))
            (fsfb_at accumulator point ⌢ₘ
              fsfb_at family point)
            hSelectedDomain
            (hAccumulatorAt (point + 1))
            (finite_sequence_concatenation_term_admissible
              (fsfb_at accumulator point)
              (fsfb_at family point)
              (hAccumulatorAt point)
              (hFamilyAt point))
            (hStep point hPointLt)
            hRawBound
        simpa [point, Nat.succ_eq_add_one,
          Nat.add_assoc] using hTransported
  obtain ⟨offset, hCount⟩ :=
    Nat.exists_eq_add_of_le
      (Nat.succ_le_of_lt hIndex)
  have hFinalAccumulatorBound :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(fsfb_at family index) ∈ₘ
          Sₘ(domₘ(fsfb_at accumulator count)) := by
    subst count
    simpa [Nat.add_assoc] using
      hBoundAfter offset (Nat.le_refl _)
  exact fsfb_domain_le_transport
    (domₘ(fsfb_at family index))
    (flattenₘ(family))
    (fsfb_at accumulator count)
    hSelectedDomain
    (finite_sequence_flatten_term_admissible
      family hFamily)
    (hAccumulatorAt count)
    hTerminal
    hFinalAccumulatorBound

/--
有限 numeral 定义域上的 `flattenₘ` 分片长度上界。

该公共接口只要求有限序列族 guard 与定义域的 numeral 证书。累积器见证和其新鲜
变量均在证明内部从 `finite_sequence_flatten_spec` 动态消去，不进入调用方接口。
-/
theorem gq_flatten_numeral_point_domain_le
    {Γ : Context signature}
    (family : SetTerm)
    (count index : Nat)
    (hFamily : Term.Admissible family SetSort.set)
    (hFamilyCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_family_condition family)
    (hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(family) ≐ₘ numₘ(count))
    (hIndex : index < count) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(family ·ₘ numₘ(index)) ∈ₘ
        Sₘ(domₘ(flattenₘ(family))) := by
  let conclusion : SetFormula :=
    domₘ(family ·ₘ numₘ(index)) ∈ₘ
      Sₘ(domₘ(flattenₘ(family)))
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
          fsfb_at accumulator 0 ≐ₘ ∅ₘ := by
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
          simpa only [Δ, List.mem_cons] using
            (Or.inr hFormula :
              formula = body ∨ formula ∈ Γ))
        hFamilyCondition
    have hDomainΔ :
        Δ ⊢ₘ[godel_quotation_theory]
          domₘ(family) ≐ₘ numₘ(count) :=
      FirstOrder.Derives.context_weaken
        (Γ := Γ) (Δ := Δ) (by
          intro formula hFormula
          simpa only [Δ, List.mem_cons] using
            (Or.inr hFormula :
              formula = body ∨ formula ∈ Γ))
        hDomain
    have hPointDomain
        (point : Nat) (hPoint : point < count) :
        Δ ⊢ₘ[godel_quotation_theory]
          numₘ(point) ∈ₘ domₘ(family) := by
      have hNumeral :
          Δ ⊢ₘ[godel_quotation_theory]
            numₘ(point) ∈ₘ numₘ(count) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_weaken_standard_sequence <|
              standard_sequence_finite_numeral_mem_of_lt
                point count hPoint
      exact FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          (numₘ(point))
          (domₘ(family))
          (numₘ(count))
          (finite_numeral_term_admissible point)
          (domain_term_admissible family hFamily)
          (finite_numeral_term_admissible count)
          hDomainΔ)
        hNumeral
    have hPointFinite :
        ∀ point, point < count →
          Δ ⊢ₘ[godel_quotation_theory]
            finite_sequence_condition
              (fsfb_at family point) := by
      intro point hPoint
      have hAll :=
        FirstOrder.Derives.conjElimRight
          hFamilyConditionΔ
      have hAt :=
        FirstOrder.Derives.forall_elim
          (term := numₘ(point)) hAll
      have hImp :
          Δ ⊢ₘ[godel_quotation_theory]
            (numₘ(point) ∈ₘ domₘ(family)) ⟶ₘ
              finite_sequence_condition
                (fsfb_at family point) := by
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
        hImp (hPointDomain point hPoint)
    have hStep :
        ∀ point, point < count →
          Δ ⊢ₘ[godel_quotation_theory]
            fsfb_at accumulator (point + 1) ≐ₘ
              (fsfb_at accumulator point ⌢ₘ
                fsfb_at family point) := by
      intro point hPoint
      have hAt :=
        FirstOrder.Derives.forall_elim
          (term := numₘ(point)) hStepForall
      have hImp :
          Δ ⊢ₘ[godel_quotation_theory]
            (numₘ(point) ∈ₘ domₘ(family)) ⟶ₘ
              (fsfb_at accumulator (point + 1) ≐ₘ
                (fsfb_at accumulator point ⌢ₘ
                  fsfb_at family point)) := by
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
        hImp (hPointDomain point hPoint)
    have hTerminalArgument :
        Δ ⊢ₘ[godel_quotation_theory]
          (accumulator ·ₘ domₘ(family)) ≐ₘ
            fsfb_at accumulator count :=
      function_application_term_congr_argument_of_equality
        accumulator (domₘ(family)) (numₘ(count))
        hAccumulator
        (domain_term_admissible family hFamily)
        (finite_numeral_term_admissible count)
        hDomainΔ
    have hTerminal :
        Δ ⊢ₘ[godel_quotation_theory]
          flattenₘ(family) ≐ₘ
            fsfb_at accumulator count :=
      Metatheory.Derives.equality_trans
        hTerminalAtDomain hTerminalArgument
    simpa [conclusion] using
      gq_flatten_checked_replay_point_domain_le
        (Γ := Δ)
        family accumulator count index
        hFamily hAccumulator hIndex
        hPointFinite hInitial hStep hTerminal

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
