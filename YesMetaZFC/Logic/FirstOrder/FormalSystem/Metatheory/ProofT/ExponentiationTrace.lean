import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.MultiplicationTrace

/-!
# 内在有限幂轨迹

幂的递归步复用内在乘法的有限 numeral 求值；对象层只验证有限图满足幂定义合同。
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

private def standard_exponentiation_trace_elements
    {free : SetContext} (base exponent : Nat) :
    List (SetOpenTerm free) :=
  (List.range (exponent + 1)).map (fun index => numₘ(base ^ index))

private theorem standard_exponentiation_trace_elements_get
    {free : SetContext} (base exponent index : Nat)
    (hIndex : index ≤ exponent) :
    (standard_exponentiation_trace_elements
      (free := free) base exponent)[index]? =
      some (numₘ(base ^ index) : SetOpenTerm free) := by
  have hIndex' : index < exponent + 1 := Nat.lt_succ_iff.mpr hIndex
  simp [standard_exponentiation_trace_elements, hIndex']

private theorem standard_exponentiation_trace_step
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (base exponent index : Nat) (hIndex : index < exponent) :
    Γ ⊢ₘ[T]
      (standard_sequence_from 0
          (standard_exponentiation_trace_elements base exponent) ·ₘ
        Sₘ(numₘ(index))) ≐ₘ
      ((standard_sequence_from 0
          (standard_exponentiation_trace_elements base exponent) ·ₘ
        numₘ(index)) *ₘ numₘ(base)) := by
  let trace : SetOpenTerm free :=
    standard_sequence_from 0
      (standard_exponentiation_trace_elements base exponent)
  have hCurrent :=
    standard_sequence_from_getElem?_apply_eq
      (Γ := Γ) S.toFiniteSequenceEvaluationSupport 0
      (standard_exponentiation_trace_elements_get
        (free := free) base exponent index (Nat.le_of_lt hIndex))
  have hCurrent' : Γ ⊢ₘ[T]
      (trace ·ₘ numₘ(index)) ≐ₘ numₘ(base ^ index) := by
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace] using hCurrent
  have hNext :=
    standard_sequence_from_getElem?_apply_eq
      (Γ := Γ) S.toFiniteSequenceEvaluationSupport 0
      (standard_exponentiation_trace_elements_get
        (free := free) base exponent (index + 1)
        (Nat.succ_le_iff.mpr hIndex))
  have hNext' : Γ ⊢ₘ[T]
      (trace ·ₘ numₘ(index + 1)) ≐ₘ
        numₘ(base ^ (index + 1)) := by
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace, standard_exponentiation_trace_elements] using hNext
  have hMultiplicationClosed :=
    standard_sequence_finite_numeral_multiplication S (base ^ index) base
  have hMultiplicationFree := FirstOrder.Derives.free_renaming
    (T := T)
    (VariableRenaming.empty : VariableRenaming [] free)
    hMultiplicationClosed
  have hMultiplicationContext := FirstOrder.Derives.context_weaken
    (Γ := ([] : Context signature free))
    (Δ := Γ) (by simp) hMultiplicationFree
  have hMultiplication : Γ ⊢ₘ[T]
      numₘ(base ^ (index + 1)) ≐ₘ
        (numₘ(base ^ index) *ₘ numₘ(base)) := by
    simpa [Formula.renameFree, Formula.rename, Renaming.free,
      Formula.renameMapped, Term.renameMapped, Arguments.renameMapped,
      finite_numeral_term_renameMapped, Nat.pow_succ] using
      hMultiplicationContext
  have hCurrentMultiplication : Γ ⊢ₘ[T]
      ((trace ·ₘ numₘ(index)) *ₘ numₘ(base)) ≐ₘ
        (numₘ(base ^ index) *ₘ numₘ(base)) := by
    let context : SetTerm [SetSort.set] free :=
      (.bvar .here : SetTerm [SetSort.set] free) *ₘ
        (numₘ(base) : SetOpenTerm free).weakenBound SetSort.set
    simpa only [context,
      Term.instantiateTop_app,
      Arguments.instantiateTop_cons,
      Arguments.instantiateTop_nil,
      Term.instantiateTop_weakenBound,
      Term.instantiateTop_bvar_here] using!
      Metatheory.Derives.term_context_congr_of_equality
        (T := T) (Γ := Γ) context hCurrent'
  have hResult := Metatheory.Derives.equality_trans hNext' <|
    Metatheory.Derives.equality_trans hMultiplication
      (Metatheory.Derives.equality_symm hCurrentMultiplication)
  simpa [trace, finite_numeral_term] using hResult

private theorem standard_exponentiation_trace_step_of_numeral_member
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    {free : SetContext} {Γ : Context signature free}
    (base exponent : Nat) (point : SetOpenTerm free)
    (hPoint : Γ ⊢ₘ[T] point ∈ₘ numₘ(exponent)) :
    Γ ⊢ₘ[T]
      (standard_sequence_from 0
          (standard_exponentiation_trace_elements base exponent) ·ₘ
        Sₘ(point)) ≐ₘ
      ((standard_sequence_from 0
          (standard_exponentiation_trace_elements base exponent) ·ₘ
        point) *ₘ numₘ(base)) := by
  let trace : SetOpenTerm free :=
    standard_sequence_from 0
      (standard_exponentiation_trace_elements base exponent)
  let conclusion : SetOpenFormula free :=
    (trace ·ₘ Sₘ(point)) ≐ₘ ((trace ·ₘ point) *ₘ numₘ(base))
  apply (ArithmeticSupport.finite_core
    S.toFiniteSequenceEvaluationSupport.toArithmeticSupport).member_elim
    exponent point conclusion hPoint
  intro index hIndex
  let equality : SetOpenFormula free := point ≐ₘ numₘ(index)
  let Δ : Context signature free := equality :: Γ
  have hEquality : Δ ⊢ₘ[T] point ≐ₘ numₘ(index) :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hStep : Δ ⊢ₘ[T]
      (trace ·ₘ Sₘ(numₘ(index))) ≐ₘ
        ((trace ·ₘ numₘ(index)) *ₘ numₘ(base)) := by
    simpa [trace, equality, Δ] using
      (standard_exponentiation_trace_step
        (Γ := Δ) S base exponent index hIndex)
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
  have hMultiplicationArgument : Δ ⊢ₘ[T]
      ((trace ·ₘ point) *ₘ numₘ(base)) ≐ₘ
        ((trace ·ₘ numₘ(index)) *ₘ numₘ(base)) := by
    let context : SetTerm [SetSort.set] free :=
      (.bvar .here : SetTerm [SetSort.set] free) *ₘ
        (numₘ(base) : SetOpenTerm free).weakenBound SetSort.set
    simpa only [context,
      Term.instantiateTop_app,
      Arguments.instantiateTop_cons,
      Arguments.instantiateTop_nil,
      Term.instantiateTop_weakenBound,
      Term.instantiateTop_bvar_here] using!
      Metatheory.Derives.term_context_congr_of_equality
        (T := T) (Γ := Δ) context hApplicationPoint
  have hResult := Metatheory.Derives.equality_trans
    hApplicationArgument (Metatheory.Derives.equality_trans
      hStep (Metatheory.Derives.equality_symm hMultiplicationArgument))
  simpa [conclusion, trace, equality, Δ] using hResult

private theorem standard_exponentiation_trace_elements_weaken
    (base exponent : Nat) :
    (standard_exponentiation_trace_elements
      (free := []) base exponent).map
        (fun element => element.weakenFree SetSort.set) =
      standard_exponentiation_trace_elements
        (free := [SetSort.set]) base exponent := by
  simp [standard_exponentiation_trace_elements, Function.comp_def]

private def standard_exponentiation_trace_step_formula
    (base exponent : Nat) : SetSentence :=
  let point : SetOpenTerm [SetSort.set] := .fvar .here
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0
      (standard_exponentiation_trace_elements
        (free := []) base exponent)
  ((point ∈ₘ (numₘ(exponent) : SetOpenTerm []).weakenFree SetSort.set) ⟶ₘ
      ((trace.weakenFree SetSort.set ·ₘ Sₘ(point)) ≐ₘ
        ((trace.weakenFree SetSort.set ·ₘ point) *ₘ
          (numₘ(base) : SetOpenTerm []).weakenFree SetSort.set))).forallFreeTop SetSort.set

private theorem standard_exponentiation_trace_step_forall
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (base exponent : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      standard_exponentiation_trace_step_formula base exponent := by
  let point : SetOpenTerm [SetSort.set] := .fvar .here
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0
      (standard_exponentiation_trace_elements
        (free := []) base exponent)
  let traceOpen : SetOpenTerm [SetSort.set] :=
    trace.weakenFree SetSort.set
  let baseOpen : SetOpenTerm [SetSort.set] :=
    (numₘ(base) : SetOpenTerm []).weakenFree SetSort.set
  let exponentOpen : SetOpenTerm [SetSort.set] :=
    (numₘ(exponent) : SetOpenTerm []).weakenFree SetSort.set
  have hBody :
      FreshVariable.extendContext SetSort.set
          ([] : Context signature []) ⊢ₘ[T]
        (point ∈ₘ exponentOpen) ⟶ₘ
          ((traceOpen ·ₘ Sₘ(point)) ≐ₘ
            ((traceOpen ·ₘ point) *ₘ baseOpen)) := by
    apply FirstOrder.Derives.imp_intro
    let membership : SetOpenFormula [SetSort.set] :=
      point ∈ₘ exponentOpen
    let Δ : Context signature [SetSort.set] := membership :: []
    have hMembership : Δ ⊢ₘ[T] membership :=
      FirstOrder.Derives.assumption List.mem_cons_self
    simpa [point, trace, traceOpen, baseOpen, exponentOpen, membership, Δ,
      standard_sequence_from_weakenFree,
      standard_exponentiation_trace_elements,
      finite_numeral_term_weakenFree, Function.comp_def,
      standard_exponentiation_trace_elements_weaken,
      FreshVariable.extendContext] using
      (standard_exponentiation_trace_step_of_numeral_member
        (Γ := Δ) S base exponent point (by
          simpa [membership, exponentOpen] using hMembership))
  simpa [standard_exponentiation_trace_step_formula, point, trace, traceOpen,
    baseOpen, exponentOpen, standard_sequence_from_weakenFree] using
    (FirstOrder.Derives.forall_intro hBody)

/-- 对象层幂在任意外部有限 numeral 上还原为自然数幂。 -/
theorem standard_sequence_finite_numeral_exponentiation
    {T : SetTheory} (S : ArithmeticEvaluationSupport T)
    (base exponent : Nat) :
    ([] : Context signature []) ⊢ₘ[T]
      numₘ(base ^ exponent) ≐ₘ
        (numₘ(base) ^ₘ numₘ(exponent)) := by
  let elements : List (SetOpenTerm []) :=
    standard_exponentiation_trace_elements
      (free := []) base exponent
  let trace : SetOpenTerm [] :=
    standard_sequence_from 0 elements
  let result : SetOpenTerm [] := numₘ(base ^ exponent)
  have hBaseOmega : ([] : Context signature []) ⊢ₘ[T]
      (numₘ(base) : SetOpenTerm []) ∈ₘ ωₘ :=
    S.finite_numeral_mem_omega base
  have hExponentOmega : ([] : Context signature []) ⊢ₘ[T]
      (numₘ(exponent) : SetOpenTerm []) ∈ₘ ωₘ :=
    S.finite_numeral_mem_omega exponent
  have hDomain :=
    standard_sequence_domain_eq
      (Γ := ([] : Context signature []))
      S.toFiniteSequenceGraphSupport (elements := elements)
  have hTraceMapping : ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(exponent))) ωₘ := by
    have hDomain' : ([] : Context signature []) ⊢ₘ[T]
        Sₘ(numₘ(exponent)) ≐ₘ domₘ(trace) := by
      simpa [trace, elements, standard_exponentiation_trace_elements,
        finite_numeral_term] using
        (Metatheory.Derives.equality_symm hDomain)
    simpa [trace, elements] using
      (standard_sequence_from_is_mapping
        (Γ := ([] : Context signature []))
        S.toFiniteSequenceEvaluationSupport 0
        (elements := elements) (Sₘ(numₘ(exponent))) ωₘ hDomain'
        (fun element hElement => by
          rcases List.mem_map.mp hElement with ⟨index, _, rfl⟩
          exact S.finite_numeral_mem_omega (base ^ index)))
  have hInitial : ([] : Context signature []) ⊢ₘ[T]
      (trace ·ₘ ∅ₘ) ≐ₘ Sₘ(∅ₘ) := by
    have hGet : elements[0]? =
        some (numₘ(base ^ 0) : SetOpenTerm []) := by
      simp [elements, standard_exponentiation_trace_elements]
    have hApply :=
      standard_sequence_from_getElem?_apply_eq
        (Γ := ([] : Context signature []))
        S.toFiniteSequenceEvaluationSupport 0 hGet
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace, elements, finite_numeral_term, Nat.pow_zero] using hApply
  have hStep : ([] : Context signature []) ⊢ₘ[T]
      standard_exponentiation_trace_step_formula base exponent :=
    standard_exponentiation_trace_step_forall S base exponent
  have hTerminal : ([] : Context signature []) ⊢ₘ[T]
      trace ·ₘ numₘ(exponent) ≐ₘ result := by
    have hGet : elements[exponent]? =
        some (numₘ(base ^ exponent) : SetOpenTerm []) := by
      simp [elements, standard_exponentiation_trace_elements]
    have hApply :=
      standard_sequence_from_getElem?_apply_eq
        (Γ := ([] : Context signature []))
        S.toFiniteSequenceEvaluationSupport 0 hGet
    exact Metatheory.Derives.equality_symm <| by
      simpa [trace, elements, result] using hApply
  have hGraph : ([] : Context signature []) ⊢ₘ[T]
      natural_exponentiation_graph_condition
        (numₘ(base) : SetOpenTerm [])
        (numₘ(exponent) : SetOpenTerm []) result trace := by
    change ([] : Context signature []) ⊢ₘ[T]
      is_mapping_formula trace (Sₘ(numₘ(exponent))) ωₘ ∧ₘ
        ((trace ·ₘ ∅ₘ ≐ₘ Sₘ(∅ₘ)) ∧ₘ
          (standard_exponentiation_trace_step_formula base exponent ∧ₘ
            (trace ·ₘ (numₘ(exponent) : SetOpenTerm []) ≐ₘ result)))
    exact FirstOrder.Derives.conj_intro hTraceMapping <|
      FirstOrder.Derives.conj_intro hInitial <|
        FirstOrder.Derives.conj_intro hStep hTerminal
  have hResultOmega : ([] : Context signature []) ⊢ₘ[T]
      result ∈ₘ ωₘ := by
    simpa [result] using S.finite_numeral_mem_omega (base ^ exponent)
  have hSpec : ([] : Context signature []) ⊢ₘ[T]
      natural_exponentiation_spec
        (numₘ(base) : SetOpenTerm [])
        (numₘ(exponent) : SetOpenTerm []) result := by
    apply FirstOrder.Derives.conj_intro hResultOmega
    apply FirstOrder.Derives.exists_intro trace
    change ([] : Context signature []) ⊢ₘ[T]
      ((natural_exponentiation_graph_condition
        ((numₘ(base) : SetOpenTerm []).weakenFree SetSort.set)
        ((numₘ(exponent) : SetOpenTerm []).weakenFree SetSort.set)
        (result.weakenFree SetSort.set)
        (.fvar .here : SetOpenTerm [SetSort.set])).abstractFreeTop).instantiateTop
          trace
    rw [Formula.instantiateTop_abstractFreeTop]
    have hFormula :
        Formula.instantiateFreeTop trace
            (natural_exponentiation_graph_condition
              ((numₘ(base) : SetOpenTerm []).weakenFree SetSort.set)
              ((numₘ(exponent) : SetOpenTerm []).weakenFree SetSort.set)
              (result.weakenFree SetSort.set)
              (.fvar .here : SetOpenTerm [SetSort.set])) =
          natural_exponentiation_graph_condition
            (numₘ(base) : SetOpenTerm [])
            (numₘ(exponent) : SetOpenTerm []) result trace := by
      unfold natural_exponentiation_graph_condition
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
      natural_exponentiation_definition_instance
        (numₘ(base) : SetOpenTerm [])
        (numₘ(exponent) : SetOpenTerm []) result :=
    S.exponentiation_definition_instance_derives
      (Γ := ([] : Context signature []))
      (numₘ(base) : SetOpenTerm []) (numₘ(exponent) : SetOpenTerm []) result
  have hContract : ([] : Context signature []) ⊢ₘ[T]
      ((numₘ(base) ∈ₘ ωₘ) ∧ₘ (numₘ(exponent) ∈ₘ ωₘ)) ⟶ₘ
        (((result ≐ₘ (numₘ(base) ^ₘ numₘ(exponent))) ↔ₘ
          natural_exponentiation_spec
            (numₘ(base) : SetOpenTerm [])
            (numₘ(exponent) : SetOpenTerm []) result)) := by
    simpa [natural_exponentiation_definition_instance] using hDefinition
  have hInstance := FirstOrder.Derives.imp_elim hContract <|
    FirstOrder.Derives.conj_intro hBaseOmega hExponentOmega
  have hEquality := FirstOrder.Derives.iff_elim_right hInstance hSpec
  simpa [result] using hEquality

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
