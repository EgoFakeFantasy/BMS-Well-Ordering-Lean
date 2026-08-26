import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.VariableSymbolInversion

/-!
# FormalSystem 符号见证的对象算术上界

本模块把一般自然幂索引界接到变量与常元符号码。核心结论保持纯对象层：
标准 singleton token 若属于无限符号族，则其内部自然数见证已经落在该 token
给出的有限初段中。整个过程不把对象自然数反演为 Lean 自然数。
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

/-! ## 一般素数幂界 -/

/--
若标准底数严格大于 `1`，则任意对象自然数 `index` 严格小于
`base ^ S(index)`。

这里只实例化对象算术扩展中的一般增长律；`base` 仍是任意外部自然数，不绑定
Gödel 编码使用的 `3` 或 `5`。
-/
theorem gq_index_mem_indexed_prime_power_of_theory
    {T : SetTheory}
    {Γ : Context signature}
    (hQuotation :
      ∀ formula, godel_quotation_theory formula → T formula)
    (base : Nat)
    (index : SetTerm)
    (hBase : 1 < base)
    (hIndex : Term.Admissible index SetSort.set)
    (hIndexOmega :
      Γ ⊢ₘ[T]
        index ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      index ∈ₘ
        indexed_prime_power_code_term base index := by
  have hInstance :
      Γ ⊢ₘ[T]
        natural_exponentiation_index_bound_instance
          (numₘ(base)) index := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    apply FirstOrder.Derives.theory_weaken hQuotation
    apply gq_weaken_standard_sequence
    apply
      standard_sequence_weaken_natural_exponentiation_bound
    exact
      natural_exponentiation_index_bound_instance_derives
        (numₘ(base)) index
        (finite_numeral_term_admissible base)
        hIndex
  have hBaseOmega :
      Γ ⊢ₘ[T]
        numₘ(base) ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hQuotation <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_omega base
  have hOneBase :
      Γ ⊢ₘ[T]
        numₘ(1) ∈ₘ numₘ(base) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hQuotation <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_of_lt
              1 base hBase
  simpa [natural_exponentiation_index_bound_instance,
    indexed_prime_power_code_term,
    prime_power_code_term] using
    FirstOrder.Derives.impElim hInstance <|
      FirstOrder.Derives.conjIntro hBaseOmega <|
        FirstOrder.Derives.conjIntro
          hIndexOmega hOneBase

/-- Gödel quotation 理论中的单素数幂索引界。 -/
theorem gq_index_mem_indexed_prime_power
    {Γ : Context signature}
    (base : Nat)
    (index : SetTerm)
    (hBase : 1 < base)
    (hIndex : Term.Admissible index SetSort.set)
    (hIndexOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        index ∈ₘ ωₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      index ∈ₘ
        indexed_prime_power_code_term base index :=
  gq_index_mem_indexed_prime_power_of_theory
    (T := godel_quotation_theory)
    (fun _ hFormula => hFormula)
    base index hBase hIndex hIndexOmega

/-! ## 幂乘积的双索引界 -/

/--
两个标准底数都严格大于 `1` 时，左右对象索引同时落在对应幂乘积内。

该接口只把对象算术扩展实例化到外部给定底数；函数和谓词编码分别取
`(3, 5)` 与 `(3, 7)`。
-/
theorem gq_indices_mem_indexed_prime_power_product_of_theory
    {T : SetTheory}
    {Γ : Context signature}
    (hQuotation :
      ∀ formula, godel_quotation_theory formula → T formula)
    (leftBase rightBase : Nat)
    (leftIndex rightIndex : SetTerm)
    (hLeftBase : 1 < leftBase)
    (hRightBase : 1 < rightBase)
    (hLeftIndex :
      Term.Admissible leftIndex SetSort.set)
    (hRightIndex :
      Term.Admissible rightIndex SetSort.set)
    (hLeftOmega :
      Γ ⊢ₘ[T]
        leftIndex ∈ₘ ωₘ)
    (hRightOmega :
      Γ ⊢ₘ[T]
        rightIndex ∈ₘ ωₘ) :
    Γ ⊢ₘ[T]
      ((leftIndex ∈ₘ
          ((indexed_prime_power_code_term
              leftBase leftIndex) *ₘ
            (indexed_prime_power_code_term
              rightBase rightIndex))) ∧ₘ
        (rightIndex ∈ₘ
          ((indexed_prime_power_code_term
              leftBase leftIndex) *ₘ
            (indexed_prime_power_code_term
              rightBase rightIndex)))) := by
  have hInstance :
      Γ ⊢ₘ[T]
        natural_exponent_product_index_bound_instance
          (numₘ(leftBase)) leftIndex
          (numₘ(rightBase)) rightIndex := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    apply FirstOrder.Derives.theory_weaken hQuotation
    apply gq_weaken_standard_sequence
    apply
      standard_sequence_weaken_natural_exponentiation_bound
    exact
      natural_exponent_product_index_bound_instance_derives
        (numₘ(leftBase)) leftIndex
        (numₘ(rightBase)) rightIndex
        (finite_numeral_term_admissible leftBase)
        hLeftIndex
        (finite_numeral_term_admissible rightBase)
        hRightIndex
  have hLeftBaseOmega :
      Γ ⊢ₘ[T]
        numₘ(leftBase) ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hQuotation <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_omega
              leftBase
  have hRightBaseOmega :
      Γ ⊢ₘ[T]
        numₘ(rightBase) ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hQuotation <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_omega
              rightBase
  have hOneLeft :
      Γ ⊢ₘ[T]
        numₘ(1) ∈ₘ numₘ(leftBase) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hQuotation <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_of_lt
              1 leftBase hLeftBase
  have hOneRight :
      Γ ⊢ₘ[T]
        numₘ(1) ∈ₘ numₘ(rightBase) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken hQuotation <|
          gq_weaken_standard_sequence <|
            standard_sequence_finite_numeral_mem_of_lt
              1 rightBase hRightBase
  simpa [natural_exponent_product_index_bound_instance,
    indexed_prime_power_code_term,
    prime_power_code_term] using
    FirstOrder.Derives.impElim hInstance <|
      FirstOrder.Derives.conjIntro hLeftBaseOmega <|
        FirstOrder.Derives.conjIntro hLeftOmega <|
          FirstOrder.Derives.conjIntro hOneLeft <|
            FirstOrder.Derives.conjIntro
              hRightBaseOmega <|
                FirstOrder.Derives.conjIntro
                  hRightOmega hOneRight

/-- Gödel quotation 理论中的双素数幂乘积索引界。 -/
theorem gq_indices_mem_indexed_prime_power_product
    {Γ : Context signature}
    (leftBase rightBase : Nat)
    (leftIndex rightIndex : SetTerm)
    (hLeftBase : 1 < leftBase)
    (hRightBase : 1 < rightBase)
    (hLeftIndex :
      Term.Admissible leftIndex SetSort.set)
    (hRightIndex :
      Term.Admissible rightIndex SetSort.set)
    (hLeftOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        leftIndex ∈ₘ ωₘ)
    (hRightOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        rightIndex ∈ₘ ωₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      ((leftIndex ∈ₘ
          ((indexed_prime_power_code_term
              leftBase leftIndex) *ₘ
            (indexed_prime_power_code_term
              rightBase rightIndex))) ∧ₘ
        (rightIndex ∈ₘ
          ((indexed_prime_power_code_term
              leftBase leftIndex) *ₘ
            (indexed_prime_power_code_term
              rightBase rightIndex)))) :=
  gq_indices_mem_indexed_prime_power_product_of_theory
    (T := godel_quotation_theory)
    (fun _ hFormula => hFormula)
    leftBase rightBase leftIndex rightIndex
    hLeftBase hRightBase hLeftIndex hRightIndex
    hLeftOmega hRightOmega

/-! ## 标准 singleton 的有限见证反演 -/

/--
标准 singleton token 若属于变量符号集合，则满足有限变量 token 条件。

对象见证先由 `3^(index+1)` 的一般增长律压入 `token`，再注入 `S(token)`；
证明只依赖对象算术增长律和有限标准序列事实。
-/
theorem gq_variable_symbol_member_implies_token_condition
    (token : Nat) :
    ⊢ₘ[godel_quotation_theory]
      (sym_codeₘ(numₘ(token)) ∈ₘ VarSymₘ) ⟶ₘ
        fs_variable_token_condition
          (numₘ(token)) := by
  let symbol : SetTerm :=
    sym_codeₘ(numₘ(token))
  let membership : SetFormula :=
    symbol ∈ₘ VarSymₘ
  let conclusion : SetFormula :=
    fs_variable_token_condition (numₘ(token))
  have hSymbol :
      Term.Admissible symbol SetSort.set := by
    simpa [symbol] using
      singleton_symbol_code_term_admissible
        (numₘ(token))
        (finite_numeral_term_admissible token)
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hSymbol variable_symbol_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [membership]
  have hMembership :
      Γ ⊢ₘ[godel_quotation_theory]
        symbol ∈ₘ VarSymₘ := by
    simpa [Γ, membership] using
      (FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ) (φ := membership)
        (by simp [Γ]))
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        variable_symbol_condition symbol :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_variable_symbol_definition_instance
            symbol hSymbol (by
              simp only [symbol, Term.freeSupport,
                Term.freeSupportList,
                finite_numeral_term_freeSupport]
              exact List.not_mem_nil))
      hMembership
  let witness : SetTerm := x#200
  let witnessCondition : SetFormula :=
    (witness ∈ₘ ωₘ) ∧ₘ
      (symbol ≐ₘ
        variable_symbol_code_term witness)
  have hWitnessConditionAdmissible :
      Formula.Admissible witnessCondition := by
    dsimp [witnessCondition, witness]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        (set_variable_admissible 200)
        omega_term_admissible)
      (Formula.Admissible.equal hSymbol
        (variable_symbol_code_term_admissible
          (x#200)
          (set_variable_admissible 200)))
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 200],
          witnessCondition := by
    simpa [variable_symbol_condition,
      witnessCondition, witness,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable] using
      FirstOrder.Derives.conjElimRight hCondition
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 200)
    (body := witnessCondition)
    (conclusion := conclusion)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hWitnessConditionAdmissible)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simp [membership, symbol,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport]
  · simp [conclusion,
      fs_variable_token_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport]
  · exact hExists
  · let Δ : Context signature :=
      witnessCondition :: Γ
    have hWitness :
        Term.Admissible witness SetSort.set := by
      simpa [witness] using
        set_variable_admissible 200
    have hWitnessCondition :
        Δ ⊢ₘ[godel_quotation_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hWitnessOmega :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ ωₘ :=
      FirstOrder.Derives.conjElimLeft
        hWitnessCondition
    have hCodeEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          symbol ≐ₘ
            variable_symbol_code_term witness := by
      simpa [witnessCondition] using
        FirstOrder.Derives.conjElimRight
          hWitnessCondition
    have hValueEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          numₘ(token) ≐ₘ
            variable_symbol_number_term witness := by
      simpa [symbol,
        variable_symbol_code_term] using
        gq_singleton_symbol_code_value_eq_of_equality
          (numₘ(token))
          (variable_symbol_number_term witness)
          (finite_numeral_term_admissible token)
          (by
            simpa [variable_symbol_number_term] using
              indexed_prime_power_code_term_admissible
                3 witness hWitness)
          (by
            intro term hTerm id hId
            simp only [List.mem_cons] at hTerm
            rcases hTerm with rfl | hTerm
            · simp only [finite_numeral_term_freeSupport]
              exact List.not_mem_nil
            · rcases hTerm with rfl | hTerm
              · have hIdNe : id ≠ 200 := by
                  simp only [List.mem_cons,
                    List.not_mem_nil, or_false] at hId
                  rcases hId with rfl | rfl | rfl <;>
                    decide
                simp only [witness, Term.freeSupport,
                  Term.freeSupportList,
                  finite_numeral_term_freeSupport]
                intro hMember
                exact hIdNe <|
                  congrArg Prod.snd <|
                    List.mem_singleton.mp hMember
              · exact False.elim
                  (List.not_mem_nil hTerm))
          hCodeEquality
    have hWitnessPower :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ
            variable_symbol_number_term witness := by
      simpa [variable_symbol_number_term] using
        gq_index_mem_indexed_prime_power
          (Γ := Δ) 3 witness (by omega)
          hWitness hWitnessOmega
    have hWitnessToken :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ numₘ(token) :=
      FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          witness (numₘ(token))
          (variable_symbol_number_term witness)
          hWitness
          (finite_numeral_term_admissible token)
          (by
            simpa [variable_symbol_number_term] using
              indexed_prime_power_code_term_admissible
                3 witness hWitness)
          hValueEquality)
        hWitnessPower
    have hWitnessBound :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ Sₘ(numₘ(token)) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_weaken_standard_sequence <|
              standard_sequence_weaken_successor <|
                mem_successor_of_mem
                  (numₘ(token)) witness
                  (finite_numeral_term_admissible token)
                  hWitness)
        hWitnessToken
    unfold conclusion fs_variable_token_condition
    nd_apply FirstOrder.Derives.exists_intro
      (term := witness)
    have hNumeralOpen
        (number : Nat) :
        Term.openAt SetSort.set 0 witness
            (numₘ(number)) =
          numₘ(number) :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 witness (numₘ(number))
        (finite_numeral_term_admissible number).2
    simpa [Formula.openAt, Term.openAt,
      symbol, hNumeralOpen] using
      FirstOrder.Derives.conjIntro
        hWitnessBound hCodeEquality

/-!
任意变量符号码的零位若等于具体 token，则该 token 满足变量条件。
这里把对象层 `VarSymₘ` 成员先压到长度一标准 singleton，再运输到
`sym_codeₘ(numₘ(token))`；因此调用方不需要反演对象自然数见证。
-/
theorem gq_variable_symbol_zero_value_implies_token_condition_of_theory
    {T : SetTheory} {Γ : Context signature}
    (hQuotation :
      ∀ formula, godel_quotation_theory formula → T formula)
    (hStandardTheory :
      ∀ formula, standard_sequence_semantics_theory formula → T formula)
    (hSentence :
      ∀ formula, T formula → Formula.Sentence formula)
    (symbol : SetTerm) (token : Nat)
    (hSymbol : Term.Admissible symbol SetSort.set)
    (hMember :
      Γ ⊢ₘ[T]
        symbol ∈ₘ VarSymₘ)
    (hValue :
      Γ ⊢ₘ[T]
        (symbol ·ₘ numₘ(0)) ≐ₘ numₘ(token)) :
    Γ ⊢ₘ[T]
      fs_variable_token_condition (numₘ(token)) := by
  have hFiniteDomain :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
        FirstOrder.Derives.theory_weaken
          hQuotation
          (gq_variable_symbol_member_implies_finite_domain_one
            symbol hSymbol))
      hMember
  have hFinite :
      Γ ⊢ₘ[T]
        finite_sequence_condition symbol :=
    FirstOrder.Derives.conjElimLeft hFiniteDomain
  have hDomain :
      Γ ⊢ₘ[T]
        domₘ(symbol) ≐ₘ numₘ(1) :=
    FirstOrder.Derives.conjElimRight hFiniteDomain
  have hStandard :
      Γ ⊢ₘ[T]
        symbol ≐ₘ standard_token_sequence [token] := by
    apply
      gq_standard_token_sequence_eq_of_function_domain_pointwise_of_theory
        (T := T)
        (Γ := Γ)
        hStandardTheory hSentence
        symbol [token]
    · simpa [finite_sequence_condition] using
        FirstOrder.Derives.conjElimLeft hFinite
    · simpa using hDomain
    · intro index value hGet
      have hIndex : index < [token].length :=
        (List.getElem?_eq_some_iff.mp hGet).1
      have hIndexZero : index = 0 := by
        simpa using hIndex
      subst index
      have hValueToken : value = token := by
        simpa using hGet.symm
      subst value
      exact hValue
  have hStandardToSymbol :
      Γ ⊢ₘ[T]
        standard_token_sequence [token] ≐ₘ
          sym_codeₘ(numₘ(token)) := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    apply FirstOrder.Derives.theory_weaken hStandardTheory
    simpa [standard_token_sequence] using
      standard_singleton_sequence_eq_symbol_code
        (numₘ(token))
        (finite_numeral_term_admissible token)
  have hToSymbol :
      Γ ⊢ₘ[T]
        symbol ≐ₘ sym_codeₘ(numₘ(token)) :=
    Metatheory.Derives.equality_trans
      hStandard hStandardToSymbol
  have hTokenMember :
      Γ ⊢ₘ[T]
        sym_codeₘ(numₘ(token)) ∈ₘ VarSymₘ :=
    FirstOrder.Derives.iffElimRight
      (membership_left_iff_of_equality
        symbol
        (sym_codeₘ(numₘ(token)))
        VarSymₘ
        hSymbol
        (singleton_symbol_code_term_admissible
          (numₘ(token))
          (finite_numeral_term_admissible token))
        variable_symbol_set_term_admissible
        hToSymbol)
      hMember
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (FirstOrder.Derives.theory_weaken
        hQuotation
        (gq_variable_symbol_member_implies_token_condition token)))
    hTokenMember

/-- Gödel quotation 理论中的特例。 -/
theorem gq_variable_symbol_zero_value_implies_token_condition
    {Γ : Context signature}
    (symbol : SetTerm) (token : Nat)
    (hSymbol : Term.Admissible symbol SetSort.set)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        symbol ∈ₘ VarSymₘ)
    (hValue :
      Γ ⊢ₘ[godel_quotation_theory]
        (symbol ·ₘ numₘ(0)) ≐ₘ numₘ(token)) :
    Γ ⊢ₘ[godel_quotation_theory]
      fs_variable_token_condition (numₘ(token)) :=
  gq_variable_symbol_zero_value_implies_token_condition_of_theory
    (T := godel_quotation_theory)
    (fun _ hFormula => hFormula)
    (fun _ hFormula => Or.inl hFormula)
    (fun _ hFormula => godel_quotation_theory_sentence hFormula)
    symbol token hSymbol hMember hValue

/--
标准 singleton token 若属于常元符号集合，则其对象索引见证也落在
`S(token)` 中。

该结论为后续有限签名常元反演保留原始符号码等式，不提前选择 Lean 层常元。
-/
theorem gq_constant_symbol_member_implies_bounded_witness
    (token : Nat) :
    ⊢ₘ[godel_quotation_theory]
      (sym_codeₘ(numₘ(token)) ∈ₘ ConstSymₘ) ⟶ₘ
        (∃ₘ[SetSort.set],
          (((bₛ#0 ∈ₘ Sₘ(numₘ(token))) ∧ₘ
            (sym_codeₘ(numₘ(token)) ≐ₘ
              constant_symbol_code_term
                (bₛ#0))))) := by
  let symbol : SetTerm :=
    sym_codeₘ(numₘ(token))
  let membership : SetFormula :=
    symbol ∈ₘ ConstSymₘ
  let conclusion : SetFormula :=
    ∃ₘ[SetSort.set],
      ((bₛ#0 ∈ₘ Sₘ(numₘ(token))) ∧ₘ
        (symbol ≐ₘ
          constant_symbol_code_term (bₛ#0)))
  have hSymbol :
      Term.Admissible symbol SetSort.set := by
    simpa [symbol] using
      singleton_symbol_code_term_admissible
        (numₘ(token))
        (finite_numeral_term_admissible token)
  have hMembershipAdmissible :
      Formula.Admissible membership := by
    simpa [membership] using
      membership_formula_admissible
        hSymbol constant_symbol_set_term_admissible
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature := [membership]
  have hMembership :
      Γ ⊢ₘ[godel_quotation_theory]
        symbol ∈ₘ ConstSymₘ := by
    simpa [Γ, membership] using
      (FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ) (φ := membership)
        (by simp [Γ]))
  have hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        constant_symbol_condition symbol :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          gq_constant_symbol_definition_instance
            symbol hSymbol (by
              simp only [symbol, Term.freeSupport,
                Term.freeSupportList,
                finite_numeral_term_freeSupport]
              exact List.not_mem_nil))
      hMembership
  let witness : SetTerm := x#201
  let witnessCondition : SetFormula :=
    (witness ∈ₘ ωₘ) ∧ₘ
      (symbol ≐ₘ
        constant_symbol_code_term witness)
  have hWitnessConditionAdmissible :
      Formula.Admissible witnessCondition := by
    dsimp [witnessCondition, witness]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        (set_variable_admissible 201)
        omega_term_admissible)
      (Formula.Admissible.equal hSymbol
        (constant_symbol_code_term_admissible
          (x#201)
          (set_variable_admissible 201)))
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 201],
          witnessCondition := by
    simpa [constant_symbol_condition,
      witnessCondition, witness,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable] using
      FirstOrder.Derives.conjElimRight hCondition
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 201)
    (body := witnessCondition)
    (conclusion := conclusion)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hWitnessConditionAdmissible)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simp [membership, symbol,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport]
  · simp [conclusion, symbol,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport]
  · exact hExists
  · let Δ : Context signature :=
      witnessCondition :: Γ
    have hWitness :
        Term.Admissible witness SetSort.set := by
      simpa [witness] using
        set_variable_admissible 201
    have hWitnessCondition :
        Δ ⊢ₘ[godel_quotation_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hWitnessOmega :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ ωₘ :=
      FirstOrder.Derives.conjElimLeft
        hWitnessCondition
    have hCodeEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          symbol ≐ₘ
            constant_symbol_code_term witness := by
      simpa [witnessCondition] using
        FirstOrder.Derives.conjElimRight
          hWitnessCondition
    have hValueEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          numₘ(token) ≐ₘ
            constant_symbol_number_term witness := by
      simpa [symbol,
        constant_symbol_code_term] using
        gq_singleton_symbol_code_value_eq_of_equality
          (numₘ(token))
          (constant_symbol_number_term witness)
          (finite_numeral_term_admissible token)
          (by
            simpa [constant_symbol_number_term] using
              indexed_prime_power_code_term_admissible
                5 witness hWitness)
          (by
            intro term hTerm id hId
            simp only [List.mem_cons] at hTerm
            rcases hTerm with rfl | hTerm
            · simp only [finite_numeral_term_freeSupport]
              exact List.not_mem_nil
            · rcases hTerm with rfl | hTerm
              · have hIdNe : id ≠ 201 := by
                  simp only [List.mem_cons,
                    List.not_mem_nil, or_false] at hId
                  rcases hId with rfl | rfl | rfl <;>
                    decide
                simp only [witness, Term.freeSupport,
                  Term.freeSupportList,
                  finite_numeral_term_freeSupport]
                intro hMember
                exact hIdNe <|
                  congrArg Prod.snd <|
                    List.mem_singleton.mp hMember
              · exact False.elim
                  (List.not_mem_nil hTerm))
          hCodeEquality
    have hWitnessPower :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ
            constant_symbol_number_term witness := by
      simpa [constant_symbol_number_term] using
        gq_index_mem_indexed_prime_power
          (Γ := Δ) 5 witness (by omega)
          hWitness hWitnessOmega
    have hWitnessToken :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ numₘ(token) :=
      FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          witness (numₘ(token))
          (constant_symbol_number_term witness)
          hWitness
          (finite_numeral_term_admissible token)
          (by
            simpa [constant_symbol_number_term] using
              indexed_prime_power_code_term_admissible
                5 witness hWitness)
          hValueEquality)
        hWitnessPower
    have hWitnessBound :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ Sₘ(numₘ(token)) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ]) <|
            gq_weaken_standard_sequence <|
              standard_sequence_weaken_successor <|
                mem_successor_of_mem
                  (numₘ(token)) witness
                  (finite_numeral_term_admissible token)
                  hWitness)
        hWitnessToken
    unfold conclusion
    nd_apply FirstOrder.Derives.exists_intro
      (term := witness)
    have hNumeralOpen
        (number : Nat) :
        Term.openAt SetSort.set 0 witness
            (numₘ(number)) =
          numₘ(number) :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 witness (numₘ(number))
        (finite_numeral_term_admissible number).2
    simpa [Formula.openAt, Term.openAt,
      symbol, hNumeralOpen] using
      FirstOrder.Derives.conjIntro
        hWitnessBound hCodeEquality

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
