import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ArithmeticEvaluation
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FiniteSequenceMappingSemantics
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.IntrinsicQuantifier

/-!
# 内在有限算术轨迹

本模块提供标准有限图的值域反演与算术轨迹计算。所有递归均在外部列表或
`Nat` 上进行；对象层只消费类型化的图成员和定义合同。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

private def standard_addition_trace_elements
    {free : SetContext} (left right : Nat) :
    List (SetOpenTerm free) :=
  (List.range (left + 1)).map (fun index => numₘ(right + index))

private theorem standard_addition_trace_elements_get
    {free : SetContext} (left right index : Nat)
    (hIndex : index ≤ left) :
    (standard_addition_trace_elements (free := free) left right)[index]? =
      some (numₘ(right + index) : SetOpenTerm free) := by
  have hIndex' : index < left + 1 := Nat.lt_succ_iff.mpr hIndex
  simp [standard_addition_trace_elements, hIndex']

private theorem standard_addition_trace_step
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right index : Nat) (hIndex : index < left) :
    Γ ⊢ₘ[T]
      (standard_sequence_from 0
          (standard_addition_trace_elements left right) ·ₘ
        Sₘ(numₘ(index))) ≐ₘ
      Sₘ(standard_sequence_from 0
          (standard_addition_trace_elements left right) ·ₘ
        numₘ(index)) := by
  let trace : SetOpenTerm free :=
    standard_sequence_from 0
      (standard_addition_trace_elements left right)
  have hCurrent :=
    standard_sequence_from_getElem?_apply_eq
      (Γ := Γ) S.toFiniteSequenceEvaluationSupport 0
      (standard_addition_trace_elements_get
        (free := free) left right index (Nat.le_of_lt hIndex))
  have hCurrent' : Γ ⊢ₘ[T]
      (trace ·ₘ numₘ(index)) ≐ₘ numₘ(right + index) := by
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace] using hCurrent
  have hSuccessor :=
    successor_term_congr_of_equality
      (trace ·ₘ numₘ(index)) (numₘ(right + index)) hCurrent'
  have hNext :=
    standard_sequence_from_getElem?_apply_eq
      (Γ := Γ) S.toFiniteSequenceEvaluationSupport 0
      (standard_addition_trace_elements_get
        (free := free) left right (index + 1) (Nat.succ_le_iff.mpr hIndex))
  have hNext' : Γ ⊢ₘ[T]
      (trace ·ₘ numₘ(index + 1)) ≐ₘ
        Sₘ(numₘ(right + index)) := by
    have hNextSymm := Metatheory.Derives.equality_symm hNext
    simpa [trace, standard_addition_trace_elements,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using! hNextSymm
  have hResult := Metatheory.Derives.equality_trans
    hNext' (Metatheory.Derives.equality_symm hSuccessor)
  simpa [trace, finite_numeral_term] using hResult

private theorem standard_addition_trace_step_of_numeral_member
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (left right : Nat) (point : SetOpenTerm free)
    (hPoint : Γ ⊢ₘ[T] point ∈ₘ numₘ(left)) :
    Γ ⊢ₘ[T]
      (standard_sequence_from 0
          (standard_addition_trace_elements left right) ·ₘ
        Sₘ(point)) ≐ₘ
      Sₘ(standard_sequence_from 0
          (standard_addition_trace_elements left right) ·ₘ point) := by
  let trace : SetOpenTerm free :=
    standard_sequence_from 0
      (standard_addition_trace_elements left right)
  let conclusion : SetOpenFormula free :=
    (trace ·ₘ Sₘ(point)) ≐ₘ Sₘ(trace ·ₘ point)
  apply (ArithmeticSupport.finite_core
    S.toFiniteSequenceEvaluationSupport.toArithmeticSupport).member_elim
    left point conclusion hPoint
  intro index hIndex
  let equality : SetOpenFormula free := point ≐ₘ numₘ(index)
  let Δ : Context signature free := equality :: Γ
  have hEquality : Δ ⊢ₘ[T] point ≐ₘ numₘ(index) :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hStep : Δ ⊢ₘ[T]
      (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
        Sₘ(trace ·ₘ numₘ(index)) := by
    simpa [trace, equality, Δ] using
      (standard_addition_trace_step
        (Γ := Δ) S left right index hIndex)
  have hSuccessorArgument : Δ ⊢ₘ[T]
      Sₘ(point) ≐ₘ Sₘ(numₘ(index)) :=
    successor_term_congr_of_equality point (numₘ(index)) hEquality
  have hApplicationArgument : Δ ⊢ₘ[T]
      (trace ·ₘ Sₘ(point)) ≐ₘ
        (trace ·ₘ Sₘ(numₘ(index))) :=
    function_application_term_congr_argument_of_equality
      trace (Sₘ(point)) (Sₘ(numₘ(index))) hSuccessorArgument
  have hApplicationPoint : Δ ⊢ₘ[T]
      (trace ·ₘ point) ≐ₘ (trace ·ₘ numₘ(index)) :=
    function_application_term_congr_argument_of_equality
      trace point (numₘ(index)) hEquality
  have hSuccessorValue : Δ ⊢ₘ[T]
      Sₘ(trace ·ₘ point) ≐ₘ Sₘ(trace ·ₘ numₘ(index)) :=
    successor_term_congr_of_equality
      (trace ·ₘ point) (trace ·ₘ numₘ(index)) hApplicationPoint
  have hResult := Metatheory.Derives.equality_trans
    hApplicationArgument (Metatheory.Derives.equality_trans
      hStep (Metatheory.Derives.equality_symm hSuccessorValue))
  simpa [conclusion, trace, equality, Δ] using hResult

private theorem standard_addition_trace_elements_weaken
    (left right : Nat) :
    (standard_addition_trace_elements (free := []) left right).map
        (fun element => element.weakenFree SetSort.set) =
      standard_addition_trace_elements (free := [SetSort.set]) left right := by
  simp [standard_addition_trace_elements, Function.comp_def]

private def standard_addition_trace_step_formula
    (left right : Nat) : SetSentence :=
  let point : SetOpenTerm [SetSort.set] := .fvar .here
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0
      (standard_addition_trace_elements (free := []) left right)
  ((point ∈ₘ (numₘ(left) : SetOpenTerm []).weakenFree SetSort.set) ⟶ₘ
      ((trace.weakenFree SetSort.set ·ₘ Sₘ(point)) ≐ₘ
        Sₘ(trace.weakenFree SetSort.set ·ₘ point))).forallFreeTop SetSort.set

private theorem standard_addition_trace_step_forall
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (left right : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      standard_addition_trace_step_formula left right := by
  let point : SetOpenTerm [SetSort.set] := .fvar .here
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0
      (standard_addition_trace_elements (free := []) left right)
  let traceOpen : SetOpenTerm [SetSort.set] :=
    trace.weakenFree SetSort.set
  let leftOpen : SetOpenTerm [SetSort.set] :=
    (numₘ(left) : SetOpenTerm []).weakenFree SetSort.set
  have hBody :
      FreshVariable.extendContext SetSort.set
          ([] : Context signature []) ⊢ₘ[T]
        (point ∈ₘ leftOpen) ⟶ₘ
          ((traceOpen ·ₘ Sₘ(point)) ≐ₘ Sₘ(traceOpen ·ₘ point)) := by
    apply FirstOrder.Derives.imp_intro
    let membership : SetOpenFormula [SetSort.set] :=
      point ∈ₘ leftOpen
    let Δ : Context signature [SetSort.set] := membership :: []
    have hMembership : Δ ⊢ₘ[T] membership :=
      FirstOrder.Derives.assumption List.mem_cons_self
    simpa [point, trace, traceOpen, leftOpen, membership, Δ,
      standard_sequence_from_weakenFree, standard_addition_trace_elements,
      finite_numeral_term_weakenFree, Function.comp_def,
      standard_addition_trace_elements_weaken, FreshVariable.extendContext] using
      (standard_addition_trace_step_of_numeral_member
        (Γ := Δ) S left right point (by
          simpa [membership, leftOpen] using hMembership))
  simpa [standard_addition_trace_step_formula, point, trace, traceOpen, leftOpen,
    standard_sequence_from_weakenFree] using
    (FirstOrder.Derives.forall_intro hBody)

theorem standard_sequence_finite_numeral_addition
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (left right : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      numₘ(left + right) ≐ₘ
        (numₘ(left) +ₘ numₘ(right)) := by
  let elements : List (SetOpenTerm []) :=
    standard_addition_trace_elements (free := []) left right
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0 elements
  let result : SetOpenTerm [] := numₘ(left + right)
  have hLeftOmega : ([] : Context signature []) ⊢ₘ[T]
      (numₘ(left) : SetOpenTerm []) ∈ₘ ωₘ :=
    S.finite_numeral_mem_omega left
  have hRightOmega : ([] : Context signature []) ⊢ₘ[T]
      (numₘ(right) : SetOpenTerm []) ∈ₘ ωₘ :=
    S.finite_numeral_mem_omega right
  have hDomain :=
    standard_sequence_domain_eq
      (Γ := ([] : Context signature []))
      S.toFiniteSequenceGraphSupport (elements := elements)
  have hTraceMapping : ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(left))) ωₘ := by
    have hDomain' : ([] : Context signature []) ⊢ₘ[T]
        Sₘ(numₘ(left)) ≐ₘ domₘ(trace) := by
      simpa [trace, elements, standard_addition_trace_elements,
        finite_numeral_term] using
        (Metatheory.Derives.equality_symm hDomain)
    simpa [trace, elements] using
      (standard_sequence_from_is_mapping
        (Γ := ([] : Context signature []))
        S.toFiniteSequenceEvaluationSupport 0
        (elements := elements) (Sₘ(numₘ(left))) ωₘ hDomain'
        (fun element hElement => by
          rcases List.mem_map.mp hElement with ⟨index, _, rfl⟩
          exact S.finite_numeral_mem_omega (right + index)))
  have hInitial : ([] : Context signature []) ⊢ₘ[T]
      (trace ·ₘ ∅ₘ) ≐ₘ (numₘ(right) : SetOpenTerm []) := by
    have hGet : elements[0]? =
        some (numₘ(right) : SetOpenTerm []) := by
      simp [elements, standard_addition_trace_elements]
    have hApply :=
      standard_sequence_from_getElem?_apply_eq
        (Γ := ([] : Context signature []))
        S.toFiniteSequenceEvaluationSupport 0 hGet
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace, elements] using! hApply
  have hStep : ([] : Context signature []) ⊢ₘ[T]
      standard_addition_trace_step_formula left right :=
    standard_addition_trace_step_forall S left right
  have hTerminal : ([] : Context signature []) ⊢ₘ[T]
      trace ·ₘ numₘ(left) ≐ₘ result := by
    have hGet : elements[left]? =
        some (numₘ(right + left) : SetOpenTerm []) := by
      simp [elements, standard_addition_trace_elements]
    have hApply :=
      standard_sequence_from_getElem?_apply_eq
        (Γ := ([] : Context signature []))
        S.toFiniteSequenceEvaluationSupport 0 hGet
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace, elements, result, Nat.add_comm] using hApply
  have hGraph : ([] : Context signature []) ⊢ₘ[T]
      natural_addition_graph_condition
        (numₘ(left) : SetOpenTerm [])
        (numₘ(right) : SetOpenTerm []) result trace := by
    change ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(left))) ωₘ ∧ₘ
        ((trace ·ₘ ∅ₘ ≐ₘ (numₘ(right) : SetOpenTerm [])) ∧ₘ
          (standard_addition_trace_step_formula left right ∧ₘ
            (trace ·ₘ (numₘ(left) : SetOpenTerm []) ≐ₘ result)))
    exact FirstOrder.Derives.conj_intro hTraceMapping <|
      FirstOrder.Derives.conj_intro hInitial <|
        FirstOrder.Derives.conj_intro hStep hTerminal
  have hResultOmega : ([] : Context signature []) ⊢ₘ[T]
      result ∈ₘ ωₘ := by
    simpa [result] using S.finite_numeral_mem_omega (left + right)
  have hSpec : ([] : Context signature []) ⊢ₘ[T]
      natural_addition_spec
        (numₘ(left) : SetOpenTerm [])
        (numₘ(right) : SetOpenTerm []) result := by
    apply FirstOrder.Derives.conj_intro hResultOmega
    apply FirstOrder.Derives.exists_intro trace
    change ([] : Context signature []) ⊢ₘ[T]
      ((natural_addition_graph_condition
        ((numₘ(left) : SetOpenTerm []).weakenFree SetSort.set)
        ((numₘ(right) : SetOpenTerm []).weakenFree SetSort.set)
        (result.weakenFree SetSort.set)
        (.fvar .here : SetOpenTerm [SetSort.set])).abstractFreeTop).instantiateTop
          trace
    rw [Formula.instantiateTop_abstractFreeTop]
    have hFormula :
        Formula.instantiateFreeTop trace
            (natural_addition_graph_condition
              ((numₘ(left) : SetOpenTerm []).weakenFree SetSort.set)
              ((numₘ(right) : SetOpenTerm []).weakenFree SetSort.set)
              (result.weakenFree SetSort.set)
              (.fvar .here : SetOpenTerm [SetSort.set])) =
          natural_addition_graph_condition
            (numₘ(left) : SetOpenTerm [])
            (numₘ(right) : SetOpenTerm []) result trace := by
      unfold natural_addition_graph_condition
      simp [Formula.instantiateFreeTop_forallFreeTop,
        Formula.substituteFree, Substitution.free_map,
        Formula.substitute, Formula.substituteMapped,
        Term.substituteMapped, Arguments.substituteMapped,
        Term.instantiateFreeTop, Term.substitute,
        Substitution.instantiateFreeTop,
        VariableSubstitution.liftFree,
        VariableSubstitution.instantiateFreeTop,
        finite_numeral_term_weakenFree, result]
    rw [hFormula]
    exact hGraph
  have hDefinition : ([] : Context signature []) ⊢ₘ[T]
      natural_addition_definition_instance
        (numₘ(left) : SetOpenTerm [])
        (numₘ(right) : SetOpenTerm []) result :=
    S.addition_definition_instance_derives
      (Γ := ([] : Context signature []))
      (numₘ(left) : SetOpenTerm []) (numₘ(right) : SetOpenTerm []) result
  have hContract : ([] : Context signature []) ⊢ₘ[T]
      ((numₘ(left) ∈ₘ ωₘ) ∧ₘ (numₘ(right) ∈ₘ ωₘ)) ⟶ₘ
        (((result ≐ₘ (numₘ(left) +ₘ numₘ(right))) ↔ₘ
          natural_addition_spec
            (numₘ(left) : SetOpenTerm [])
            (numₘ(right) : SetOpenTerm []) result)) := by
    simpa [natural_addition_definition_instance] using hDefinition
  have hInstance := FirstOrder.Derives.imp_elim hContract <|
    FirstOrder.Derives.conj_intro hLeftOmega hRightOmega
  have hEquality := FirstOrder.Derives.iff_elim_right hInstance hSpec
  simpa [result] using hEquality

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC

