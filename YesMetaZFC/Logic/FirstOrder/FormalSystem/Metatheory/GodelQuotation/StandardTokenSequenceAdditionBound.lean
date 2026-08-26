import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequence

/-!
# 固定正 numeral 左加法的对象层上界

本模块只提取 quotation 反演实际需要的最弱算术事实：任意对象自然数严格小于
一个正的外部 numeral 与它的和。证明直接重放加法递归图，不使用交换律、
结合律或对象归纳。
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

/--
对象自然加法同时支配任一侧的已有非严格上界。

调用方显式给出三个自然数事实与 `point ≤ left ∨ point ≤ right`；本定理只负责
实例化公共对象算术公理。
-/
theorem standard_sequence_natural_addition_upper_bound
    {Γ : Context signature}
    (point left right : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hPointOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ∈ₘ ωₘ)
    (hLeftOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        left ∈ₘ ωₘ)
    (hRightOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        right ∈ₘ ωₘ)
    (hBound :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (point ∈ₘ Sₘ(left)) ∨ₘ
          (point ∈ₘ Sₘ(right))) :
    Γ ⊢ₘ[standard_sequence_semantics_theory]
      point ∈ₘ Sₘ(left +ₘ right) := by
  have hInstance :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_upper_bound_instance
          point left right :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        standard_sequence_weaken_natural_addition_bound <|
          natural_addition_upper_bound_instance_derives
            point left right hPoint hLeft hRight
  exact FirstOrder.Derives.impElim hInstance <|
    FirstOrder.Derives.conjIntro hPointOmega <|
      FirstOrder.Derives.conjIntro hLeftOmega <|
        FirstOrder.Derives.conjIntro hRightOmega hBound

/--
正左加法把右侧已有的非严格上界提升为严格上界。
-/
theorem
    standard_sequence_natural_positive_left_addition_strict_bound
    {Γ : Context signature}
    (point left right : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hPointOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ∈ₘ ωₘ)
    (hLeftOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        left ∈ₘ ωₘ)
    (hRightOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        right ∈ₘ ωₘ)
    (hLeftPositive :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        ∅ₘ ∈ₘ left)
    (hBound :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        point ∈ₘ Sₘ(right)) :
    Γ ⊢ₘ[standard_sequence_semantics_theory]
      point ∈ₘ (left +ₘ right) := by
  have hInstance :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        natural_positive_left_addition_strict_bound_instance
          point left right :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        standard_sequence_weaken_natural_addition_bound <|
          natural_positive_left_addition_strict_bound_instance_derives
            point left right hPoint hLeft hRight
  exact FirstOrder.Derives.impElim hInstance <|
    FirstOrder.Derives.conjIntro hPointOmega <|
      FirstOrder.Derives.conjIntro hLeftOmega <|
        FirstOrder.Derives.conjIntro hRightOmega <|
          FirstOrder.Derives.conjIntro
            hLeftPositive hBound

/--
若 `right` 是对象自然数，则它严格属于 `num(left + 1) + right`。

证明在加法递归图上做外部有限归纳：初值是 `right`，每一步取后继，因此走过
至少一步后的终值必严格包含初值。该接口不要求或导出加法交换律。
-/
theorem standard_sequence_right_mem_positive_numeral_addition
    (left : Nat)
    (right : SetTerm)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[standard_sequence_semantics_theory]
      (right ∈ₘ ωₘ) ⟶ₘ
        (right ∈ₘ
          (numₘ(left + 1) +ₘ right)) := by
  let count : Nat := left + 1
  let condition : SetFormula := right ∈ₘ ωₘ
  let result : SetTerm := numₘ(count) +ₘ right
  let conclusion : SetFormula := right ∈ₘ result
  let Γ : Context signature := [condition]
  nd_apply FirstOrder.Derives.impIntro
  have hRightOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        right ∈ₘ ωₘ := by
    simpa [Γ, condition] using
      (FirstOrder.Derives.assumption
        (T := standard_sequence_semantics_theory)
        (Γ := Γ) (φ := condition) (by simp [Γ]))
  have hCountOmega :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        numₘ(count) ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ])
      (standard_sequence_finite_numeral_mem_omega count)
  have hResult :
      Term.Admissible result SetSort.set := by
    simpa [result] using
      natural_addition_term_admissible
        (numₘ(count)) right
        (finite_numeral_term_admissible count)
        hRight
  have hDefinition :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_definition_instance
          (numₘ(count)) right result := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ])
    apply standard_sequence_weaken_natural_exponentiation
    apply FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        natural_multiplication_theory_subset_natural_exponentiation_theory <|
          natural_addition_theory_subset_natural_multiplication_theory
            hFormula)
    exact
      natural_addition_definition_instance_derives
        (numₘ(count)) right result
        (finite_numeral_term_admissible count)
        hRight hResult
  have hContract :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        (result ≐ₘ (numₘ(count) +ₘ right)) ↔ₘ
          natural_addition_spec
            (numₘ(count)) right result :=
    FirstOrder.Derives.impElim hDefinition <|
      FirstOrder.Derives.conjIntro
        hCountOmega hRightOmega
  have hResultReflexive :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        result ≐ₘ (numₘ(count) +ₘ right) := by
    simpa [result] using
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) result)
  have hSpec :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        natural_addition_spec
          (numₘ(count)) right result :=
    FirstOrder.Derives.iffElimRight
      hContract hResultReflexive
  have hExists :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        ∃ₘ[SetSort.set],
          natural_addition_bound_graph_condition
            (numₘ(count)) right result :=
    FirstOrder.Derives.conjElimRight hSpec
  let graphId : FreeVarId :=
    FreshVariable.fresh_id SetSort.set
      [condition, conclusion]
  let graph : SetTerm := x#graphId
  let graphCondition : SetFormula :=
    natural_addition_graph_condition
      (numₘ(count)) right result graph
  have hGraphIdConditionFresh :
      (SetSort.set, graphId) ∉
        Formula.freeSupport condition :=
    FreshVariable.fresh_id_not_mem_m
      (sort := SetSort.set)
      (formulas := [condition, conclusion])
      (formula := condition) (by simp)
  have hGraphIdConclusionFresh :
      (SetSort.set, graphId) ∉
        Formula.freeSupport conclusion :=
    FreshVariable.fresh_id_not_mem_m
      (sort := SetSort.set)
      (formulas := [condition, conclusion])
      (formula := conclusion) (by simp)
  have hRightFresh :
      (SetSort.set, graphId) ∉
        Term.freeSupport right := by
    intro hMember
    apply hGraphIdConditionFresh
    change (SetSort.set, graphId) ∈
      Formula.freeSupport (right ∈ₘ ωₘ)
    change (SetSort.set, graphId) ∈
      Term.freeSupportList [right, ωₘ]
    exact
      Term.mem_freeSupportList_of_mem
        (by simp) hMember
  have hResultFresh :
      (SetSort.set, graphId) ∉
        Term.freeSupport result := by
    intro hMember
    apply hGraphIdConclusionFresh
    change (SetSort.set, graphId) ∈
      Formula.freeSupport (right ∈ₘ result)
    change (SetSort.set, graphId) ∈
      Term.freeSupportList [right, result]
    exact
      Term.mem_freeSupportList_of_mem
        (by simp) hMember
  have hCountClose
      (depth : Nat) :
      Term.closeFreeAt SetSort.set graphId depth
          (numₘ(count)) =
        numₘ(count) :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set graphId depth
      (numₘ(count))
      (finite_numeral_term_admissible count).2
      (by
        simp [finite_numeral_term_freeSupport])
  have hRightClose :
      Term.closeFreeAt SetSort.set graphId 0 right =
        right :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set graphId 0 right
      hRight.2 hRightFresh
  have hResultClose :
      Term.closeFreeAt SetSort.set graphId 0 result =
        result :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set graphId 0 result
      hResult.2 hResultFresh
  have hExists' :
      Γ ⊢ₘ[standard_sequence_semantics_theory]
        ∃ₘ[SetSort.set, graphId], graphCondition := by
    simpa [graphCondition, graph,
      natural_addition_bound_graph_condition,
      natural_addition_graph_condition,
      Formula.closeFreeAt, Formula.next_depth,
      Term.closeFreeAt, set_variable,
      set_bound_variable, finite_numeral_term,
      hCountClose, hRightClose, hResultClose] using hExists
  have hGraphConditionCheck :
      Formula.CheckCertificate graphCondition := by
    have hOpened :=
      Formula.Admissible.exists_openAt
        (body :=
          Formula.closeFreeAt SetSort.set graphId 0
            graphCondition)
        (term := graph)
        SetSort.set hExists'.admissible
        (by
          simpa [graph] using
            set_variable_admissible graphId)
    exact Formula.check_admissible_complete <| by
      simpa [graph,
        Formula.openAt_closeFreeAt] using hOpened
  apply FirstOrder.Derives.exists_elim
    (T := standard_sequence_semantics_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := graphId)
    (body := graphCondition)
    (conclusion := conclusion)
    (hBodyCheck := hGraphConditionCheck)
  · intro formula hFormula
    rw [(standard_sequence_semantics_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    exact hGraphIdConditionFresh
  · exact hGraphIdConclusionFresh
  · exact hExists'
  · let Δ : Context signature :=
      [graphCondition, condition]
    have hGraphCondition :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          graphCondition :=
      FirstOrder.Derives.assumption
        (hCheck := hGraphConditionCheck)
        (by simp [Δ])
    have hInitial :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          (graph ·ₘ numₘ(0)) ≐ₘ right := by
      simpa [graphCondition,
        natural_addition_graph_condition,
        finite_numeral_term] using
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight
            hGraphCondition)
    have hStep :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          ∀ₘ[SetSort.set],
            (bₛ#0 ∈ₘ numₘ(count)) ⟶ₘ
              ((graph ·ₘ Sₘ(bₛ#0)) ≐ₘ
                Sₘ(graph ·ₘ bₛ#0)) :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight <| by
            simpa [graphCondition,
              natural_addition_graph_condition] using
              hGraphCondition
    have hTerminal :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          (graph ·ₘ numₘ(count)) ≐ₘ result :=
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight <| by
            simpa [graphCondition,
              natural_addition_graph_condition] using
              hGraphCondition
    have hGraphAt
        (index : Nat) :
        Term.Admissible
          (graph ·ₘ numₘ(index)) SetSort.set :=
      function_application_term_admissible
        graph (numₘ(index))
        (set_variable_admissible graphId)
        (finite_numeral_term_admissible index)
    have hStepAt
        (index : Nat)
        (hIndex : index < count) :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          (graph ·ₘ numₘ(index + 1)) ≐ₘ
            Sₘ(graph ·ₘ numₘ(index)) := by
      have hRaw :=
        FirstOrder.Derives.forall_elim
          (term := numₘ(index)) hStep
      have hCountOpen
          (depth : Nat)
          (replacement : SetTerm) :
          Term.openAt SetSort.set depth replacement
              (numₘ(count)) =
            numₘ(count) :=
        Term.openAt_eq_self_of_boundClosed
          SetSort.set depth replacement
          (numₘ(count))
          (finite_numeral_term_admissible count).2
      have hAt :
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            (numₘ(index) ∈ₘ numₘ(count)) ⟶ₘ
              ((graph ·ₘ numₘ(index + 1)) ≐ₘ
                Sₘ(graph ·ₘ numₘ(index))) := by
        simpa [finite_numeral_term,
          Formula.openAt, Term.openAt,
          graph, set_variable,
          hCountOpen] using hRaw
      have hIndexMember :
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            numₘ(index) ∈ₘ numₘ(count) :=
        FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ])
          (standard_sequence_finite_numeral_mem_of_lt
            index count hIndex)
      exact FirstOrder.Derives.impElim
        hAt hIndexMember
    have hRightInGraphSuccessor :
        ∀ index, index < count →
          Δ ⊢ₘ[standard_sequence_semantics_theory]
            right ∈ₘ
              (graph ·ₘ numₘ(index + 1)) := by
      intro index
      induction index with
      | zero =>
          intro hIndex
          have hStepZero := hStepAt 0 hIndex
          have hGraphZeroInSuccessor :
              Δ ⊢ₘ[standard_sequence_semantics_theory]
                (graph ·ₘ numₘ(0)) ∈ₘ
                  Sₘ(graph ·ₘ numₘ(0)) :=
            FirstOrder.Derives.context_weaken
              (Γ := []) (Δ := Δ) (by simp [Δ]) <|
              standard_sequence_weaken_successor <|
                mem_successor_self
                  (graph ·ₘ numₘ(0))
                  (hGraphAt 0)
          have hRightInSuccessor :
              Δ ⊢ₘ[standard_sequence_semantics_theory]
                right ∈ₘ
                  Sₘ(graph ·ₘ numₘ(0)) :=
            FirstOrder.Derives.iffElimRight
              (membership_left_iff_of_equality
                (graph ·ₘ numₘ(0)) right
                (Sₘ(graph ·ₘ numₘ(0)))
                (hGraphAt 0) hRight
                (successor_term_admissible
                  (graph ·ₘ numₘ(0))
                  (hGraphAt 0))
                hInitial)
              hGraphZeroInSuccessor
          exact
            FirstOrder.Derives.iffElimLeft
              (membership_right_iff_of_equality
                right
                (graph ·ₘ numₘ(0 + 1))
                (Sₘ(graph ·ₘ numₘ(0)))
                hRight
                (hGraphAt (0 + 1))
                (successor_term_admissible
                  (graph ·ₘ numₘ(0))
                  (hGraphAt 0))
                hStepZero)
              hRightInSuccessor
      | succ index ih =>
          intro hIndex
          have hPrevious :
              Δ ⊢ₘ[standard_sequence_semantics_theory]
                right ∈ₘ
                  (graph ·ₘ numₘ(index + 1)) :=
            ih (Nat.lt_of_succ_lt hIndex)
          have hPreviousInSuccessor :
              Δ ⊢ₘ[standard_sequence_semantics_theory]
                right ∈ₘ
                  Sₘ(graph ·ₘ numₘ(index + 1)) :=
            FirstOrder.Derives.impElim
              (FirstOrder.Derives.context_weaken
                (Γ := []) (Δ := Δ) (by simp [Δ]) <|
                standard_sequence_weaken_successor <|
                  mem_successor_of_mem
                    (graph ·ₘ numₘ(index + 1))
                    right
                    (hGraphAt (index + 1))
                    hRight)
              hPrevious
          have hNextStep :=
            hStepAt (index + 1) hIndex
          simpa [Nat.succ_eq_add_one,
            Nat.add_assoc] using
            (FirstOrder.Derives.iffElimLeft
              (membership_right_iff_of_equality
                right
                (graph ·ₘ numₘ((index + 1) + 1))
                (Sₘ(graph ·ₘ numₘ(index + 1)))
                hRight
                (hGraphAt ((index + 1) + 1))
                (successor_term_admissible
                  (graph ·ₘ numₘ(index + 1))
                  (hGraphAt (index + 1)))
                hNextStep)
              hPreviousInSuccessor)
    have hRightInTerminal :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          right ∈ₘ (graph ·ₘ numₘ(count)) := by
      have hAt :=
        hRightInGraphSuccessor left (by
          simp [count])
      simpa [count] using hAt
    have hRightInResult :
        Δ ⊢ₘ[standard_sequence_semantics_theory]
          right ∈ₘ result :=
      FirstOrder.Derives.iffElimRight
        (membership_right_iff_of_equality
          right
          (graph ·ₘ numₘ(count))
          result
          hRight
          (hGraphAt count)
          hResult
          hTerminal)
        hRightInTerminal
    simpa [conclusion] using hRightInResult

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
