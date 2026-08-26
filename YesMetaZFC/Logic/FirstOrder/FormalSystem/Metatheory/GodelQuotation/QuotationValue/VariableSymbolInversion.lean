import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.SingletonOpening

/-!
# 变量符号 quotation 反演

本模块只恢复变量符号码的有限结构，不把对象层自然数见证提升为 Lean 自然数。
这正是有限 token replay 所需的边界：对象层负责证明符号码是长度一函数，
外部 decoder 只处理已经出现在有限输入行中的具体 token。
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
任意变量编码运算结果都是定义域为 `1` 的有限序列。

这里不要求 `index ∈ ωₘ`：有限结构只来自 `var_codeₘ` 的定义合同。自然数前提
只在需要进一步证明该编码属于 `VarSymₘ` 时才应加入。
-/
theorem gq_variable_code_finite_domain_one
    {Γ : Context signature}
    (index : SetTerm)
    (hIndex : Term.Admissible index SetSort.set)
    (hFresh :
      ReservedIdsFresh [0, 1, 2]
        [variable_symbol_number_term index]) :
    Γ ⊢ₘ[godel_quotation_theory]
      (finite_sequence_condition (var_codeₘ(index)) ∧ₘ
        (domₘ(var_codeₘ(index)) ≐ₘ numₘ(1))) := by
  let code : SetTerm := var_codeₘ(index)
  let rawCode : SetTerm :=
    variable_symbol_code_term index
  let number : SetTerm :=
    variable_symbol_number_term index
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      variable_code_term_admissible index hIndex
  have hRawCode :
      Term.Admissible rawCode SetSort.set := by
    simpa [rawCode] using
      variable_symbol_code_term_admissible index hIndex
  have hNumber :
      Term.Admissible number SetSort.set := by
    simpa [number, variable_symbol_number_term] using
      indexed_prime_power_code_term_admissible
        3 index hIndex
  have hDefinition :
      Γ ⊢ₘ[godel_quotation_theory]
        variable_code_definition_instance
          index code :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_symbol_operator <|
          variable_code_definition_instance_derives
            index code hIndex hCode
  have hCodeRaw :
      Γ ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    have hReflexive :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ var_codeₘ(index) := by
      simpa [code] using
        (FirstOrder.Derives.eq_refl_m
          (T := godel_quotation_theory)
          (Γ := Γ) (sort := SetSort.set) code)
    simpa [code, rawCode,
      variable_code_definition_instance] using
      FirstOrder.Derives.iffElimRight
        hDefinition hReflexive
  have hRawOpening :
      Γ ⊢ₘ[godel_quotation_theory]
        (finite_sequence_condition rawCode ∧ₘ
          ((domₘ(rawCode) ≐ₘ numₘ(1)) ∧ₘ
            ((numₘ(0) ∈ₘ domₘ(rawCode)) ∧ₘ
              ((rawCode ·ₘ numₘ(0)) ≐ₘ number)))) := by
    simpa [rawCode, number,
      variable_symbol_code_term] using
      gq_singleton_symbol_code_opening
        (Γ := Γ) number hNumber hFresh
  have hFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition code :=
    FirstOrder.Derives.iffElimLeft
      (finite_sequence_condition_iff_of_equality
        code rawCode hCode hRawCode hCodeRaw)
      (FirstOrder.Derives.conjElimLeft
        hRawOpening)
  have hDomain :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(code) ≐ₘ numₘ(1) :=
    Metatheory.Derives.equality_trans
      (domain_term_congr_of_equality
        code rawCode hCode hRawCode hCodeRaw)
      (FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight
          hRawOpening)
  simpa [code] using
    FirstOrder.Derives.conjIntro
      hFinite hDomain

/--
任意变量符号成员都是定义域为 `1` 的有限序列。

证明保留 `VarSymₘ` 定义中的对象自然数见证，仅用该见证构造动态 singleton；
结论不产生 Lean 层变量名。
-/
theorem gq_variable_symbol_member_implies_finite_domain_one_of_fresh
    (symbol : SetTerm)
    (hSymbol : Term.Admissible symbol SetSort.set)
    (hFresh :
      (SetSort.set, 200) ∉ Term.freeSupport symbol) :
    ⊢ₘ[godel_quotation_theory]
      (symbol ∈ₘ VarSymₘ) ⟶ₘ
        (finite_sequence_condition symbol ∧ₘ
          (domₘ(symbol) ≐ₘ numₘ(1))) := by
  let membership : SetFormula := symbol ∈ₘ VarSymₘ
  let witness : SetTerm := x#200
  let rawCode : SetTerm :=
    variable_symbol_code_term witness
  let number : SetTerm :=
    variable_symbol_number_term witness
  let witnessCondition : SetFormula :=
    (witness ∈ₘ ωₘ) ∧ₘ
      (symbol ≐ₘ rawCode)
  let conclusion : SetFormula :=
    finite_sequence_condition symbol ∧ₘ
      (domₘ(symbol) ≐ₘ numₘ(1))
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hSymbol variable_symbol_set_term_admissible
  have hWitness :
      Term.Admissible witness SetSort.set := by
    simpa [witness] using
      set_variable_admissible 200
  have hNumber :
      Term.Admissible number SetSort.set := by
    simpa [number, variable_symbol_number_term] using
      indexed_prime_power_code_term_admissible
        3 witness hWitness
  have hRawCode :
      Term.Admissible rawCode SetSort.set := by
    simpa [rawCode] using
      variable_symbol_code_term_admissible
        witness hWitness
  have hWitnessConditionAdmissible :
      Formula.Admissible witnessCondition := by
    dsimp only [witnessCondition]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hWitness omega_term_admissible)
      (Formula.Admissible.equal
        hSymbol hRawCode)
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        witnessCondition ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [witnessCondition]
    have hCondition :
        Γ ⊢ₘ[godel_quotation_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hWitnessConditionAdmissible)
    have hEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          symbol ≐ₘ rawCode := by
      simpa [witnessCondition] using
        FirstOrder.Derives.conjElimRight hCondition
    have hOpening :
        Γ ⊢ₘ[godel_quotation_theory]
          (finite_sequence_condition rawCode ∧ₘ
            ((domₘ(rawCode) ≐ₘ numₘ(1)) ∧ₘ
              ((numₘ(0) ∈ₘ domₘ(rawCode)) ∧ₘ
                ((rawCode ·ₘ numₘ(0)) ≐ₘ
                  number)))) := by
      simpa [rawCode, number,
        variable_symbol_code_term] using
        gq_singleton_symbol_code_opening
          (Γ := Γ) number hNumber
          (by
            intro term hTerm id hId
            rw [List.mem_singleton] at hTerm
            subst term
            have hIdNe : id ≠ 200 := by
              simp only [List.mem_cons,
                List.not_mem_nil, or_false] at hId
              rcases hId with rfl | rfl | rfl <;>
                decide
            simp only [number, witness,
              Term.freeSupport, Term.freeSupportList,
              finite_numeral_term_freeSupport]
            intro hMember
            exact hIdNe <|
              congrArg Prod.snd <|
                List.mem_singleton.mp hMember)
    have hFinite :
        Γ ⊢ₘ[godel_quotation_theory]
          finite_sequence_condition symbol :=
      FirstOrder.Derives.iffElimLeft
        (finite_sequence_condition_iff_of_equality
          symbol rawCode hSymbol hRawCode hEquality)
        (FirstOrder.Derives.conjElimLeft hOpening)
    have hDomain :
        Γ ⊢ₘ[godel_quotation_theory]
          domₘ(symbol) ≐ₘ numₘ(1) :=
      Metatheory.Derives.equality_trans
        (domain_term_congr_of_equality
          symbol rawCode hSymbol hRawCode hEquality)
        (FirstOrder.Derives.conjElimLeft <|
          FirstOrder.Derives.conjElimRight hOpening)
    simpa [conclusion] using
      FirstOrder.Derives.conjIntro hFinite hDomain
  have hConclusionFresh :
      (SetSort.set, 200) ∉
        Formula.freeSupport conclusion := by
    simp only [conclusion, finite_sequence_condition,
      Formula.freeSupport,
      Term.freeSupport, Term.freeSupportList,
      finite_numeral_term_freeSupport,
      List.append_nil]
    intro hMember
    rcases List.mem_append.mp hMember with
      hMember | hMember
    · rcases List.mem_append.mp hMember with
        hMember | hMember <;>
        exact hFresh hMember
    · exact hFresh hMember
  have hExistsImp :
      ⊢ₘ[godel_quotation_theory]
        (∃ₘ[SetSort.set, 200], witnessCondition) ⟶ₘ
          conclusion :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 200)
      (by
        intro formula hFormula
        rw [(godel_quotation_theory_sentence hFormula).2]
        exact List.not_mem_nil)
      (by
        intro formula hFormula
        cases hFormula)
      hConclusionFresh hPoint
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        symbol ∈ₘ VarSymₘ :=
    FirstOrder.Derives.assumption
      (by simp [Γ, membership])
      (Formula.check_admissible_complete
        hMembershipAdmissible)
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        variable_symbol_condition symbol :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_variable_symbol_definition_instance
          symbol hSymbol hFresh))
      hMember
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 200], witnessCondition := by
    simpa [variable_symbol_condition,
      witnessCondition, witness, rawCode,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable] using
      FirstOrder.Derives.conjElimRight hCondition
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp [Γ])
      hExistsImp)
    hExists

/-- 对象层全称化后的变量符号有限结构定理。 -/
theorem gq_variable_symbol_finite_domain_one_universal :
    ⊢ₘ[godel_quotation_theory]
      ∀ₘ[SetSort.set, 700],
        ((x#700 ∈ₘ VarSymₘ) ⟶ₘ
          (finite_sequence_condition (x#700) ∧ₘ
            (domₘ(x#700) ≐ₘ numₘ(1)))) := by
  let symbol : SetTerm := x#700
  have hSymbol :
      Term.Admissible symbol SetSort.set := by
    simpa [symbol] using set_variable_admissible 700
  have hFresh :
      (SetSort.set, 200) ∉
        Term.freeSupport symbol := by
    simp only [symbol, Term.freeSupport
      ]
    decide
  have hPoint :=
    gq_variable_symbol_member_implies_finite_domain_one_of_fresh
      symbol hSymbol hFresh
  simpa [symbol] using
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
      hPoint

/-- 任意 admissible 变量符号成员都是定义域为 `1` 的有限序列。 -/
theorem gq_variable_symbol_member_implies_finite_domain_one
    (symbol : SetTerm)
    (hSymbol : Term.Admissible symbol SetSort.set) :
    ⊢ₘ[godel_quotation_theory]
      (symbol ∈ₘ VarSymₘ) ⟶ₘ
        (finite_sequence_condition symbol ∧ₘ
          (domₘ(symbol) ≐ₘ numₘ(1))) := by
  have hAt :=
    FirstOrder.Derives.forall_elim
      (term := symbol)
      gq_variable_symbol_finite_domain_one_universal
  have hOneFixed :
      Term.substituteFree SetSort.set 700 symbol
          (numₘ(1)) =
        numₘ(1) :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set 700 symbol (numₘ(1)) <| by
        rw [finite_numeral_term_freeSupport]
        exact List.not_mem_nil
  simpa [finite_sequence_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hOneFixed] using hAt

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
