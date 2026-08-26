import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SingletonOpening

/-!
# 动态变量符号编码构造

本模块证明任意对象自然数下标经 `var_codeₘ` 编码后属于变量符号集合。
证明只使用对象算术闭包、长度一符号码构造和变量符号集合的定义合同。
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

private theorem
    gq_variable_construction_infinity_subset_natural_exponentiation
    {formula : SetFormula}
    (hFormula : infinity_theory formula) :
    natural_exponentiation_theory formula :=
  natural_multiplication_theory_subset_natural_exponentiation_theory <|
    natural_addition_theory_subset_natural_multiplication_theory <|
      natural_set_theory_subset_natural_addition_theory <|
        natural_order_type_theory_subset_natural_subset_type_theory <|
          bounded_subset_theory_subset_natural_order_type_theory <|
            unbounded_subset_theory_subset_bounded_subset_theory <|
              infinity_theory_subset_unbounded_subset_theory hFormula

private theorem gq_variable_construction_finite_numeral_open
    (value depth : Nat)
    (replacement : SetTerm) :
    Term.openAt SetSort.set depth replacement
        (numₘ(value)) =
      numₘ(value) :=
  Term.openAt_eq_self_of_boundClosed
    SetSort.set depth replacement (numₘ(value))
    (finite_numeral_term_admissible value).2

private theorem gq_variable_construction_finite_numeral_close
    (value : Nat)
    (id : FreeVarId)
    (depth : Nat) :
    Term.closeFreeAt SetSort.set id depth
        (numₘ(value)) =
      numₘ(value) :=
  Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    SetSort.set id depth (numₘ(value))
    (finite_numeral_term_admissible value).2 <| by
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil

/--
自由变量 `x#700` 处的动态变量符号构造。

该证明体保留完整对象推导，后续公共接口只对它作全称化和实例化。
-/
private theorem gq_variable_code_mem_variable_symbols_at_700 :
    ⊢ₘ[godel_quotation_theory]
      ((x#700 ∈ₘ ωₘ) ⟶ₘ
        (var_codeₘ(x#700) ∈ₘ VarSymₘ)) := by
  let index : SetTerm := x#700
  let exponent : SetTerm := Sₘ(index)
  let number : SetTerm :=
    variable_symbol_number_term index
  let rawCode : SetTerm :=
    variable_symbol_code_term index
  let variableCode : SetTerm := var_codeₘ(index)
  let membership : SetFormula := index ∈ₘ ωₘ
  let Γ : Context signature := [membership]
  have hIndex :
      Term.Admissible index SetSort.set := by
    simpa [index] using set_variable_admissible 700
  have hExponent :
      Term.Admissible exponent SetSort.set := by
    exact successor_term_admissible index hIndex
  have hNumber :
      Term.Admissible number SetSort.set := by
    exact indexed_prime_power_code_term_admissible
      3 index hIndex
  have hRawCode :
      Term.Admissible rawCode SetSort.set := by
    exact variable_symbol_code_term_admissible
      index hIndex
  have hVariableCode :
      Term.Admissible variableCode SetSort.set := by
    exact variable_code_term_admissible index hIndex
  have hMembership :
      Formula.Admissible membership := by
    exact membership_formula_admissible
      hIndex omega_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  have hIndexMem :
      Γ ⊢ₘ[godel_quotation_theory]
        index ∈ₘ ωₘ := by
    simpa [Γ, membership] using
      (FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ) (φ := membership)
        (by simp [Γ]))
  have hIndexMemInfinity :
      Γ ⊢ₘ[infinity_theory]
        index ∈ₘ ωₘ := by
    simpa [Γ, membership] using
      (FirstOrder.Derives.assumption
        (T := infinity_theory)
        (Γ := Γ) (φ := membership)
        (by simp [Γ]))
  have hExponentMemInfinity :
      Γ ⊢ₘ[infinity_theory]
        exponent ∈ₘ ωₘ := by
    simpa [exponent] using
      infinity_successor_term_mem_omega
        index hIndex hIndexMemInfinity
  have hExponentMemNatural :
      Γ ⊢ₘ[natural_exponentiation_theory]
        exponent ∈ₘ ωₘ :=
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        gq_variable_construction_infinity_subset_natural_exponentiation
          hFormula)
      hExponentMemInfinity
  have hBaseMemNatural :
      Γ ⊢ₘ[natural_exponentiation_theory]
        numₘ(3) ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        FirstOrder.Derives.theory_weaken
          (fun _ hFormula =>
            gq_variable_construction_infinity_subset_natural_exponentiation
              hFormula)
          (infinity_finite_numeral_mem_omega 3)
  have hNumberMemNatural :
      Γ ⊢ₘ[natural_exponentiation_theory]
        number ∈ₘ ωₘ := by
    simpa [number, variable_symbol_number_term,
      indexed_prime_power_code_term,
      prime_power_code_term, exponent] using
      natural_exponentiation_term_mem_omega
        (numₘ(3)) exponent
        (finite_numeral_term_admissible 3)
        hExponent hBaseMemNatural hExponentMemNatural
  have hNumberMem :
      Γ ⊢ₘ[godel_quotation_theory]
        number ∈ₘ ωₘ :=
    gq_weaken_standard_sequence <|
      standard_sequence_weaken_natural_exponentiation
        hNumberMemNatural
  have hNumberFresh :
      ReservedIdsFresh [0, 1, 2] [number] := by
    intro term hTerm id hId
    rcases List.mem_singleton.mp hTerm with rfl
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hId
    rcases hId with rfl | rfl | rfl <;> (
      simp only [number, index, Term.freeSupport,
        Term.freeSupportList]
      rw [finite_numeral_term_freeSupport]
      decide)
  have hRawCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        rawCode ∈ₘ CodeStrₘ := by
    have hImplication :=
      FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_singleton_symbol_code_mem_code_string_of_omega
            number hNumber hNumberFresh
    simpa [rawCode, variable_symbol_code_term] using
      FirstOrder.Derives.impElim
        hImplication hNumberMem
  have hOperatorDefinition :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        gq_weaken_symbol_operator <|
          variable_code_definition_instance_derives
            index variableCode hIndex hVariableCode
  have hVariableReflexive :
      Γ ⊢ₘ[godel_quotation_theory]
        variableCode ≐ₘ var_codeₘ(index) := by
    simpa [variableCode] using
      (FirstOrder.Derives.eq_refl_m
        (T := godel_quotation_theory)
        (Γ := Γ) (sort := SetSort.set)
        variableCode)
  have hVariableRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        variableCode ≐ₘ rawCode := by
    simpa [variableCode, rawCode] using
      FirstOrder.Derives.iffElimRight
        hOperatorDefinition hVariableReflexive
  have hVariableCodeString :
      Γ ⊢ₘ[godel_quotation_theory]
        variableCode ∈ₘ CodeStrₘ :=
    FirstOrder.Derives.iffElimLeft
      (membership_left_iff_of_equality
        variableCode rawCode CodeStrₘ
        hVariableCode hRawCode
        code_string_space_term_admissible
        hVariableRaw)
      hRawCodeString
  have hVariableFresh :
      (SetSort.set, 200) ∉
        Term.freeSupport variableCode := by
    simp only [variableCode, index,
      Term.freeSupport, Term.freeSupportList]
    decide
  have hDefinition :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        gq_variable_symbol_definition_instance
          variableCode hVariableCode hVariableFresh
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        variable_symbol_condition variableCode := by
    apply FirstOrder.Derives.conjIntro
      hVariableCodeString
    nd_apply FirstOrder.Derives.exists_intro
      (term := index)
    have hVariableOpen :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 index variableCode
        hVariableCode.2
    have hVariableClose (depth : Nat) :
        Term.closeFreeAt SetSort.set 200 depth
            variableCode =
          variableCode :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 200 depth variableCode
        hVariableCode.2 hVariableFresh
    simpa [variable_symbol_condition,
      variableCode, rawCode, index,
      Formula.openAt_closeFreeAt_eq_substituteFree,
      Formula.openAt, Formula.closeFreeAt,
      Formula.next_depth, Formula.substituteFree,
      Term.openAt, Term.closeFreeAt,
      Term.substituteFree, set_variable,
      set_bound_variable, hVariableOpen,
      hVariableClose,
      gq_variable_construction_finite_numeral_open,
      gq_variable_construction_finite_numeral_close] using
      FirstOrder.Derives.conjIntro
        hIndexMem hVariableRaw
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hCondition

/-- 任意对象自然数下标的变量编码属于变量符号集合。 -/
theorem gq_variable_code_mem_variable_symbols_universal :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 700],
        ((x#700 ∈ₘ ωₘ) ⟶ₘ
          (var_codeₘ(x#700) ∈ₘ VarSymₘ)) := by
  simpa using
    FirstOrder.Derives.forall_intro
      (T := godel_quotation_theory)
      (Γ := []) (sort := SetSort.set)
      (eigen := 700)
      (by
        intro formula hFormula
        rw [(godel_quotation_theory_sentence hFormula).2]
        exact List.not_mem_nil)
      (by
        intro formula hFormula
        cases hFormula)
      gq_variable_code_mem_variable_symbols_at_700

/-- 任意 admissible 对象下标处的变量符号构造蕴含。 -/
theorem gq_variable_code_mem_variable_symbols
    (index : SetTerm)
    (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[godel_quotation_theory]
      (index ∈ₘ ωₘ) ⟶ₘ
        (var_codeₘ(index) ∈ₘ VarSymₘ) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := index)
      gq_variable_code_mem_variable_symbols_universal
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree,
    set_variable] using hAt

/-- 任意上下文中的对象自然数下标可直接构造变量符号编码。 -/
theorem gq_variable_code_mem_variable_symbols_of_omega
    {Γ : Context signature}
    (index : SetTerm)
    (hIndex : Term.Admissible index SetSort.set)
    (hIndexMem :
      Γ ⊢ₘ[godel_quotation_theory]
        index ∈ₘ ωₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      var_codeₘ(index) ∈ₘ VarSymₘ :=
  FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_variable_code_mem_variable_symbols
          index hIndex)
    hIndexMem

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
