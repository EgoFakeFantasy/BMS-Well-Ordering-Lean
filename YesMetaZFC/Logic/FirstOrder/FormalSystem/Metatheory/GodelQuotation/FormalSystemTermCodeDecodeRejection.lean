import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemNamedTermDecoderComposition
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemFormulaCodeRejection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormalSystemSymbolWitnessBound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.TermCodeInversion.StandardOpening

/-!
# FormalSystem 项码的 checked 解码拒绝

本模块把宿主项 decoder 的具体失败翻译为对象层 `TermCodeₘ` 成员否定。当前先闭合
singleton 基础分支：变量分支由有界变量 token 条件排除，常元分支由对象算术给出
有限索引见证后逐项排除。
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

private theorem fs_finite_numeral_open
    (value depth : Nat) (replacement : SetTerm) :
    Term.openAt SetSort.set depth replacement
        (numₘ(value)) =
      numₘ(value) :=
  Term.openAt_eq_self_of_boundClosed
    SetSort.set depth replacement
    (numₘ(value))
    (finite_numeral_term_admissible value).2

private theorem fs_finite_numeral_close
    (value : Nat) (id : FreeVarId) (depth : Nat) :
    Term.closeFreeAt SetSort.set id depth
        (numₘ(value)) =
      numₘ(value) :=
  Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
    SetSort.set id depth
    (numₘ(value))
    (finite_numeral_term_admissible value).2
    (by
      rw [finite_numeral_term_freeSupport]
      exact List.not_mem_nil)

/-! ## 宿主 singleton 失败分解 -/

private theorem fs_logical_token_ne_constant_token
    (symbol : LogicalSymbolKind) (index : Nat) :
    Numbered.logical_token symbol ≠
      Numbered.constant_token index := by
  intro hEquality
  have hParity :=
    congrArg (fun token => token % 2) hEquality
  cases symbol <;>
    simp [Numbered.logical_token,
      logical_symbol_exponent,
      Numbered.constant_token, Nat.pow_mod] at hParity

private theorem fs_membership_token_ne_constant_token
    (index : Nat) :
    Numbered.membership_token ≠
      Numbered.constant_token index := by
  intro hEquality
  have hParity :=
    congrArg (fun token => token % 2) hEquality
  simp [Numbered.membership_token,
    Numbered.constant_token, Nat.pow_mod] at hParity

private theorem fs_function_token_ne_constant_token
    (arityPredecessor symbolIndex constantIndex : Nat) :
    Numbered.function_token arityPredecessor symbolIndex ≠
      Numbered.constant_token constantIndex := by
  intro hEquality
  have hCoprime :
      Nat.Coprime
        (3 ^ (arityPredecessor + 1))
        (5 ^ (constantIndex + 1)) :=
    Nat.Coprime.pow
      (arityPredecessor + 1)
      (constantIndex + 1)
      (by decide)
  have hDiv :
      3 ^ (arityPredecessor + 1) ∣
        5 ^ (constantIndex + 1) := by
    refine ⟨5 ^ (symbolIndex + 1), ?_⟩
    simpa [Numbered.function_token,
      Numbered.constant_token] using hEquality.symm
  have hOne := hCoprime.eq_one_of_dvd hDiv
  simp at hOne

private theorem fs_predicate_token_ne_constant_token
    (arityPredecessor symbolIndex constantIndex : Nat) :
    Numbered.predicate_token arityPredecessor symbolIndex ≠
      Numbered.constant_token constantIndex := by
  intro hEquality
  have hCoprime :
      Nat.Coprime
        (3 ^ (arityPredecessor + 1))
        (5 ^ (constantIndex + 1)) :=
    Nat.Coprime.pow
      (arityPredecessor + 1)
      (constantIndex + 1)
      (by decide)
  have hDiv :
      3 ^ (arityPredecessor + 1) ∣
        5 ^ (constantIndex + 1) := by
    refine ⟨7 ^ (symbolIndex + 1), ?_⟩
    simpa [Numbered.predicate_token,
      Numbered.constant_token] using hEquality.symm
  have hOne := hCoprime.eq_one_of_dvd hDiv
  simp at hOne

/-- singleton 项解码失败时，其 token 不能是变量 token。 -/
theorem fs_named_term_singleton_decode_variable_none
    (freeBase : Nat) (boundNames : List Nat)
    (token : Nat)
    (hDecode :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames [token] =
        none) :
    fs_variable_name_decode token = none := by
  cases hVariable :
      fs_variable_name_decode token with
  | none =>
      rfl
  | some name =>
      have hToken :
          Numbered.variable_token name = token :=
        fs_variable_name_decode_value_of_some
          hVariable
      have hSuccess :=
        fs_named_term_tokens_decode_with_env_variable
          freeBase boundNames name
      rw [← hToken] at hDecode
      rw [hSuccess] at hDecode
      contradiction

/--
合法公式签名中的 singleton token 若项解码失败，就不可能是任意常元 token。

当前函数符号分支中，零元符号会被 decoder 直接接受；正元函数和一般谓词则由
素因子编码互斥排除。
-/
theorem fs_formula_token_ne_constant_of_term_singleton_decode_none
    (freeBase : Nat) (boundNames : List Nat)
    (token : Nat)
    (hToken : FSFormulaToken token)
    (hDecode :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames [token] =
        none) :
    ∀ index, token ≠ Numbered.constant_token index := by
  intro index hEquality
  cases hToken with
  | logical symbol =>
      exact
        fs_logical_token_ne_constant_token
          symbol index hEquality
  | membership =>
      exact
        fs_membership_token_ne_constant_token
          index hEquality
  | var name =>
      exact
        token_reflection_constant_token_ne_variable_token
          index name hEquality.symm
  | func symbol =>
      cases hDomain : signature.funcDomain symbol with
      | nil =>
          have hCodeEquality :
              Numbered.constant_token symbol.ctorIdx =
                Numbered.constant_token index := by
            simpa [fs_function_symbol_token,
              hDomain] using hEquality
          have hIndex :
              symbol.ctorIdx = index :=
            token_reflection_constant_token_injective
              hCodeEquality
          subst index
          have hSuccess :=
            fs_named_term_tokens_decode_with_env_constant
              freeBase boundNames symbol hDomain
          have hFailure :
              fs_named_term_tokens_decode_with_env
                  freeBase boundNames
                  [Numbered.constant_token
                    symbol.ctorIdx] =
                none := by
            simpa [fs_function_symbol_token,
              hDomain] using hDecode
          rw [hSuccess] at hFailure
          contradiction
      | cons head tail =>
          exact
            fs_function_token_ne_constant_token
              tail.length symbol.ctorIdx index <| by
                simpa [fs_function_symbol_token,
                  hDomain] using hEquality
  | pred symbol hSymbol =>
      exact
        fs_predicate_token_ne_constant_token
          (signature.relDomain symbol).length.pred
          symbol.ctorIdx index <| by
            simpa [fs_predicate_symbol_token] using
              hEquality

/-! ## 正元函数应用根的有限证书 -/

/--
一个具体 token 的有界正元函数符号条件。

两个见证分别是元数前驱与函数编号；它们都被 token 后继界住，并保留完整
singleton 符号码等式。
-/
def fs_bounded_function_symbol_condition
    (token : SetTerm) : SetFormula :=
  ∃ₘ[SetSort.set],
    ((bₛ#0 ∈ₘ Sₘ(token)) ∧ₘ
      (∃ₘ[SetSort.set],
        ((bₛ#0 ∈ₘ Sₘ(token)) ∧ₘ
          (sym_codeₘ(token) ≐ₘ
            coded_function_symbol_code_term
              (bₛ#1) (bₛ#0)))))

theorem fs_bounded_function_symbol_condition_admissible
    (token : SetTerm)
    (hToken : Term.Admissible token SetSort.set) :
    Formula.Admissible
      (fs_bounded_function_symbol_condition token) := by
  unfold fs_bounded_function_symbol_condition
  prove_admissible

/--
标准 token 串若满足一次正元函数应用生成条件，则第零位 token 给出一个有界
函数符号证书。

对象算术只把动态元数前驱和函数编号压入首 token 的有限初段；参数列与逐项项码
条件不参与该根证书。
-/
theorem
    gq_term_application_from_condition_implies_bounded_function_symbol
    (tokens : List Nat) (token : Nat)
    (hGet : tokens[0]? = some token) :
    ⊢ₘ[godel_quotation_theory]
      term_application_from_condition
          TermCodeₘ
          (standard_token_sequence tokens) ⟶ₘ
        fs_bounded_function_symbol_condition
          (numₘ(token)) := by
  let code : SetTerm :=
    standard_token_sequence tokens
  let arity : SetTerm := x#210
  let symbolIndex : SetTerm := x#211
  let arguments : SetTerm := x#212
  let header : SetFormula :=
    (arity ∈ₘ ωₘ) ∧ₘ
      ((symbolIndex ∈ₘ ωₘ) ∧ₘ
        ((arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ)) ∧ₘ
          (domₘ(arguments) ≐ₘ Sₘ(arity))))
  let values : SetFormula :=
    ∀ₘ[SetSort.set, 213],
      (x#213 ∈ₘ domₘ(arguments)) ⟶ₘ
        ((arguments ·ₘ x#213) ∈ₘ TermCodeₘ)
  let equality : SetFormula :=
    code ≐ₘ
      term_application_code_term
        arity symbolIndex arguments
  let body : SetFormula :=
    header ∧ₘ (values ∧ₘ equality)
  let conclusion : SetFormula :=
    fs_bounded_function_symbol_condition
      (numₘ(token))
  have hCode :
      Term.Admissible code SetSort.set := by
    simpa [code] using
      standard_token_sequence_admissible tokens
  have hArity :
      Term.Admissible arity SetSort.set := by
    simpa [arity] using
      set_variable_admissible 210
  have hIndex :
      Term.Admissible symbolIndex SetSort.set := by
    simpa [symbolIndex] using
      set_variable_admissible 211
  have hArguments :
      Term.Admissible arguments SetSort.set := by
    simpa [arguments] using
      set_variable_admissible 212
  have hBodyAdmissible :
      Formula.Admissible body := by
    dsimp only [body, header, values, equality]
    prove_admissible
  have hConclusionAdmissible :
      Formula.Admissible conclusion := by
    simpa [conclusion] using
      fs_bounded_function_symbol_condition_admissible
        (numₘ(token))
        (finite_numeral_term_admissible token)
  have hPoint :
      ⊢ₘ[godel_quotation_theory]
        body ⟶ₘ conclusion := by
    nd_apply FirstOrder.Derives.impIntro
    let Γ : Context signature := [body]
    have hBody :
        Γ ⊢ₘ[godel_quotation_theory] body :=
      FirstOrder.Derives.assumption
        (by simp [Γ])
        (Formula.check_admissible_complete
          hBodyAdmissible)
    have hHeader :
        Γ ⊢ₘ[godel_quotation_theory] header :=
      FirstOrder.Derives.conjElimLeft hBody
    have hArityOmega :
        Γ ⊢ₘ[godel_quotation_theory]
          arity ∈ₘ ωₘ :=
      FirstOrder.Derives.conjElimLeft hHeader
    have hIndexOmega :
        Γ ⊢ₘ[godel_quotation_theory]
          symbolIndex ∈ₘ ωₘ :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight
          hHeader
    have hPositive :
        Γ ⊢ₘ[godel_quotation_theory]
          arguments ∈ₘ seq₊_spaceₘ(CodeStrₘ) :=
      FirstOrder.Derives.conjElimLeft <|
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight
            hHeader
    have hEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          code ≐ₘ
            term_application_code_term
              arity symbolIndex arguments := by
      simpa [equality] using
        FirstOrder.Derives.conjElimRight <|
          FirstOrder.Derives.conjElimRight
            hBody
    have hOpening :=
      FirstOrder.Derives.impElim
        (gq_term_application_code_opening
          (Γ := Γ)
          arity symbolIndex arguments
          hArity hIndex hArguments
          (reserved_ids_fresh_cons_variable
            210
            (by
              intro id hId
              simp only [List.mem_cons,
                List.not_mem_nil, or_false] at hId
              rcases hId with
                rfl | rfl | rfl <;> decide)
            (reserved_ids_fresh_cons_variable
              211
              (by
                intro id hId
                simp only [List.mem_cons,
                  List.not_mem_nil, or_false] at hId
                rcases hId with
                  rfl | rfl | rfl <;> decide)
              (reserved_ids_fresh_nil [0, 1, 2]))))
        hPositive
    have hCodePoint :=
      gq_point_inversion_of_equality
        code
        (term_application_code_term
          arity symbolIndex arguments)
        (numₘ(0))
        (coded_function_symbol_number_term
          arity symbolIndex)
        hEquality
        (FirstOrder.Derives.conjElimLeft
          hOpening)
    have hStandardPoint :
        Γ ⊢ₘ[godel_quotation_theory]
          ((numₘ(0) ∈ₘ domₘ(code)) ∧ₘ
            ((code ·ₘ numₘ(0)) ≐ₘ
              numₘ(token))) := by
      simpa [code] using
        gq_standard_token_sequence_point_inversion
          code tokens
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := Γ) (by simp)
            (FirstOrder.Derives.eq_refl_m
              (sort := SetSort.set) code))
          hGet
    have hValueEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          numₘ(token) ≐ₘ
            coded_function_symbol_number_term
              arity symbolIndex :=
      Metatheory.Derives.equality_trans
        (Metatheory.Derives.equality_symm
          (FirstOrder.Derives.conjElimRight
            hStandardPoint))
        (FirstOrder.Derives.conjElimRight
          hCodePoint)
    have hSymbolEquality :
        Γ ⊢ₘ[godel_quotation_theory]
          sym_codeₘ(numₘ(token)) ≐ₘ
            coded_function_symbol_code_term
              arity symbolIndex := by
      simpa [coded_function_symbol_code_term] using
        gq_singleton_symbol_code_congr_of_equality
          (numₘ(token))
          (coded_function_symbol_number_term
            arity symbolIndex)
          hValueEquality
    have hRawBounds :
        Γ ⊢ₘ[godel_quotation_theory]
          ((arity ∈ₘ
              coded_function_symbol_number_term
                arity symbolIndex) ∧ₘ
            (symbolIndex ∈ₘ
              coded_function_symbol_number_term
                arity symbolIndex)) := by
      simpa [coded_function_symbol_number_term] using
        gq_indices_mem_indexed_prime_power_product
          (Γ := Γ)
          3 5 arity symbolIndex
          (by omega) (by omega)
          hArity hIndex
          hArityOmega hIndexOmega
    have hArityToken :
        Γ ⊢ₘ[godel_quotation_theory]
          arity ∈ₘ numₘ(token) :=
      FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          arity
          (numₘ(token))
          (coded_function_symbol_number_term
            arity symbolIndex)
          hArity
          (finite_numeral_term_admissible token)
          (coded_function_symbol_number_term_admissible
            arity symbolIndex hArity hIndex)
          hValueEquality)
        (FirstOrder.Derives.conjElimLeft
          hRawBounds)
    have hIndexToken :
        Γ ⊢ₘ[godel_quotation_theory]
          symbolIndex ∈ₘ numₘ(token) :=
      FirstOrder.Derives.iffElimLeft
        (membership_right_iff_of_equality
          symbolIndex
          (numₘ(token))
          (coded_function_symbol_number_term
            arity symbolIndex)
          hIndex
          (finite_numeral_term_admissible token)
          (coded_function_symbol_number_term_admissible
            arity symbolIndex hArity hIndex)
          hValueEquality)
        (FirstOrder.Derives.conjElimRight
          hRawBounds)
    have hArityBound :
        Γ ⊢ₘ[godel_quotation_theory]
          arity ∈ₘ Sₘ(numₘ(token)) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            gq_weaken_standard_sequence <|
              standard_sequence_weaken_successor <|
                mem_successor_of_mem
                  (numₘ(token)) arity
                  (finite_numeral_term_admissible token)
                  hArity)
        hArityToken
    have hIndexBound :
        Γ ⊢ₘ[godel_quotation_theory]
          symbolIndex ∈ₘ Sₘ(numₘ(token)) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) <|
            gq_weaken_standard_sequence <|
              standard_sequence_weaken_successor <|
                mem_successor_of_mem
                  (numₘ(token)) symbolIndex
                  (finite_numeral_term_admissible token)
                  hIndex)
        hIndexToken
    have hInner :
        Γ ⊢ₘ[godel_quotation_theory]
          ∃ₘ[SetSort.set],
            ((bₛ#0 ∈ₘ Sₘ(numₘ(token))) ∧ₘ
              (sym_codeₘ(numₘ(token)) ≐ₘ
                coded_function_symbol_code_term
                  arity (bₛ#0))) := by
      nd_apply FirstOrder.Derives.exists_intro
        (term := symbolIndex)
      simpa [arity, Formula.openAt, Formula.next_depth,
        Term.openAt, set_variable, set_bound_variable,
        fs_finite_numeral_open] using
        FirstOrder.Derives.conjIntro
          hIndexBound hSymbolEquality
    unfold conclusion
    unfold fs_bounded_function_symbol_condition
    nd_apply FirstOrder.Derives.exists_intro
      (term := arity)
    simpa [Formula.openAt, Formula.next_depth,
      Term.openAt, set_variable, set_bound_variable,
      fs_finite_numeral_open] using
      FirstOrder.Derives.conjIntro
        hArityBound hInner
  have hConclusionFresh
      (id : FreeVarId) :
      (SetSort.set, id) ∉
        Formula.freeSupport conclusion := by
    simp only [conclusion,
      fs_bounded_function_symbol_condition,
      Formula.freeSupport, Term.freeSupport,
      Term.freeSupportList,
      finite_numeral_term_freeSupport]
    exact List.not_mem_nil
  have hAt212 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 212)
      (by
        intro formula hFormula
        rw [(godel_quotation_theory_sentence
          hFormula).2]
        exact List.not_mem_nil)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 212)
      hPoint
  have hAt211 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 211)
      (by
        intro formula hFormula
        rw [(godel_quotation_theory_sentence
          hFormula).2]
        exact List.not_mem_nil)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 211)
      hAt212
  have hAt210 :=
    Metatheory.Derives.exists_imp_of_imp
      (T := godel_quotation_theory)
      (Γ := [])
      (sort := SetSort.set)
      (eigen := 210)
      (by
        intro formula hFormula
        rw [(godel_quotation_theory_sentence
          hFormula).2]
        exact List.not_mem_nil)
      (by
        intro formula hFormula
        cases hFormula)
      (hConclusionFresh 210)
      hAt211
  simpa [term_application_from_condition,
    body, header, values, equality,
    arity, symbolIndex, arguments,
    code, conclusion] using hAt210

/--
在闭合局部上下文中消去一个有界函数符号证书。

两个对象见证分别经有限 numeral 成员消去变成宿主自然数分支；分支只接收具体
singleton 函数符号码等式，不需要保留量词见证及其相等式。
-/
theorem gq_bounded_function_symbol_condition_elim_context
    {Γ : Context signature}
    (token : Nat)
    (conclusion : SetFormula)
    (hConclusionAdmissible :
      Formula.Admissible conclusion)
    (hContextClosed :
      ∀ formula, formula ∈ Γ →
        Formula.freeSupport formula = [])
    (hConclusionClosed :
      Formula.freeSupport conclusion = [])
    (hCondition :
      Γ ⊢ₘ[godel_quotation_theory]
        fs_bounded_function_symbol_condition
          (numₘ(token)))
    (hBranch :
      ∀ arity index,
        arity < token + 1 →
        index < token + 1 →
        (sym_codeₘ(numₘ(token)) ≐ₘ
          coded_function_symbol_code_term
            (numₘ(arity)) (numₘ(index))) :: Γ
          ⊢ₘ[godel_quotation_theory]
            conclusion) :
    Γ ⊢ₘ[godel_quotation_theory]
      conclusion := by
  let arityWitness : SetTerm := x#703
  let indexWitness : SetTerm := x#704
  let innerCondition : SetFormula :=
    (indexWitness ∈ₘ Sₘ(numₘ(token))) ∧ₘ
      (sym_codeₘ(numₘ(token)) ≐ₘ
        coded_function_symbol_code_term
          arityWitness indexWitness)
  let outerCondition : SetFormula :=
    (arityWitness ∈ₘ Sₘ(numₘ(token))) ∧ₘ
      (∃ₘ[SetSort.set, 704], innerCondition)
  have hArityWitness :
      Term.Admissible arityWitness SetSort.set := by
    simpa [arityWitness] using
      set_variable_admissible 703
  have hIndexWitness :
      Term.Admissible indexWitness SetSort.set := by
    simpa [indexWitness] using
      set_variable_admissible 704
  have hInnerAdmissible :
      Formula.Admissible innerCondition := by
    dsimp only [innerCondition]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hIndexWitness
        (successor_term_admissible
          (numₘ(token))
          (finite_numeral_term_admissible token)))
      (Formula.Admissible.equal
        (singleton_symbol_code_term_admissible
          (numₘ(token))
          (finite_numeral_term_admissible token))
        (coded_function_symbol_code_term_admissible
          arityWitness indexWitness
          hArityWitness hIndexWitness))
  have hOuterAdmissible :
      Formula.Admissible outerCondition := by
    dsimp only [outerCondition]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        hArityWitness
        (successor_term_admissible
          (numₘ(token))
          (finite_numeral_term_admissible token)))
      (Formula.Admissible.exists_closeFreeAt
        SetSort.set 704 hInnerAdmissible)
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 703],
          outerCondition := by
    simpa [fs_bounded_function_symbol_condition,
      outerCondition, innerCondition,
      arityWitness, indexWitness,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable,
      fs_finite_numeral_close] using
      hCondition
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 703)
    (body := outerCondition)
    (conclusion := conclusion)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hOuterAdmissible)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rw [hContextClosed formula hFormula]
    exact List.not_mem_nil
  · rw [hConclusionClosed]
    exact List.not_mem_nil
  · exact hExists
  · let Δ : Context signature :=
      outerCondition :: Γ
    have hOuter :
        Δ ⊢ₘ[godel_quotation_theory]
          outerCondition :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
        (Formula.check_admissible_complete
          hOuterAdmissible)
    have hArityMember :
        Δ ⊢ₘ[godel_quotation_theory]
          arityWitness ∈ₘ
            numₘ(token + 1) := by
      simpa [outerCondition,
        finite_numeral_term] using
        FirstOrder.Derives.conjElimLeft hOuter
    have hInnerExists :
        Δ ⊢ₘ[godel_quotation_theory]
          ∃ₘ[SetSort.set, 704],
            innerCondition := by
      simpa [outerCondition] using
        FirstOrder.Derives.conjElimRight hOuter
    have hOuterIndexFresh :
        (SetSort.set, 704) ∉
          Formula.freeSupport outerCondition := by
      simp only [outerCondition, arityWitness,
        Formula.freeSupport, Term.freeSupport,
        Term.freeSupportList,
        finite_numeral_term_freeSupport]
      intro hMember
      rcases List.mem_cons.mp hMember with
        hMember | hMember
      · exact
          (by decide :
            (SetSort.set, (704 : FreeVarId)) ≠
              (SetSort.set, (703 : FreeVarId)))
            hMember
      · exact
          Formula.not_mem_freeSupport_closeFreeAt
            SetSort.set 704 0 innerCondition
            hMember
    apply FirstOrder.Derives.exists_elim
      (T := godel_quotation_theory)
      (Γ := Δ)
      (sort := SetSort.set)
      (eigen := 704)
      (body := innerCondition)
      (conclusion := conclusion)
      (hBodyCheck :=
        Formula.check_admissible_complete
          hInnerAdmissible)
    · intro formula hFormula
      rw [(godel_quotation_theory_sentence
        hFormula).2]
      exact List.not_mem_nil
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · exact hOuterIndexFresh
      · rw [hContextClosed formula hFormula]
        exact List.not_mem_nil
    · rw [hConclusionClosed]
      exact List.not_mem_nil
    · exact hInnerExists
    · let Ε : Context signature :=
        innerCondition :: Δ
      have hInner :
          Ε ⊢ₘ[godel_quotation_theory]
            innerCondition :=
        FirstOrder.Derives.assumption
          (by simp [Ε])
          (Formula.check_admissible_complete
            hInnerAdmissible)
      have hIndexMember :
          Ε ⊢ₘ[godel_quotation_theory]
            indexWitness ∈ₘ
              numₘ(token + 1) := by
        simpa [innerCondition,
          finite_numeral_term] using
          FirstOrder.Derives.conjElimLeft hInner
      have hSymbolEquality :
          Ε ⊢ₘ[godel_quotation_theory]
            sym_codeₘ(numₘ(token)) ≐ₘ
              coded_function_symbol_code_term
                arityWitness indexWitness := by
        simpa [innerCondition] using
          FirstOrder.Derives.conjElimRight hInner
      have hArityMember' :
          Ε ⊢ₘ[godel_quotation_theory]
            arityWitness ∈ₘ
              numₘ(token + 1) :=
        FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Ε)
          (by
            intro formula hFormula
            exact List.mem_cons_of_mem
              innerCondition hFormula)
          hArityMember
      apply gq_finite_numeral_member_elim_context
        (Γ := Ε)
        (token + 1)
        arityWitness conclusion
        hArityWitness
        hConclusionAdmissible
        hArityMember'
      intro arity hArity
      let Ζ : Context signature :=
        (arityWitness ≐ₘ numₘ(arity)) :: Ε
      have hArityEquality :
          Ζ ⊢ₘ[godel_quotation_theory]
            arityWitness ≐ₘ numₘ(arity) :=
        FirstOrder.Derives.assumption
          (by simp [Ζ])
      have hIndexMember' :
          Ζ ⊢ₘ[godel_quotation_theory]
            indexWitness ∈ₘ
              numₘ(token + 1) :=
        FirstOrder.Derives.context_weaken
          (Γ := Ε) (Δ := Ζ)
          (by
            intro formula hFormula
            exact List.mem_cons_of_mem
              (arityWitness ≐ₘ numₘ(arity))
              hFormula)
          hIndexMember
      have hSymbolEquality' :
          Ζ ⊢ₘ[godel_quotation_theory]
            sym_codeₘ(numₘ(token)) ≐ₘ
              coded_function_symbol_code_term
                arityWitness indexWitness :=
        FirstOrder.Derives.context_weaken
          (Γ := Ε) (Δ := Ζ)
          (by
            intro formula hFormula
            exact List.mem_cons_of_mem
              (arityWitness ≐ₘ numₘ(arity))
              hFormula)
          hSymbolEquality
      apply gq_finite_numeral_member_elim_context
        (Γ := Ζ)
        (token + 1)
        indexWitness conclusion
        hIndexWitness
        hConclusionAdmissible
        hIndexMember'
      intro index hIndex
      let Η : Context signature :=
        (indexWitness ≐ₘ numₘ(index)) :: Ζ
      have hIndexEquality :
          Η ⊢ₘ[godel_quotation_theory]
            indexWitness ≐ₘ numₘ(index) :=
        FirstOrder.Derives.assumption
          (by simp [Η])
      have hArityEquality' :
          Η ⊢ₘ[godel_quotation_theory]
            arityWitness ≐ₘ numₘ(arity) :=
        FirstOrder.Derives.context_weaken
          (Γ := Ζ) (Δ := Η)
          (by
            intro formula hFormula
            exact List.mem_cons_of_mem
              (indexWitness ≐ₘ numₘ(index))
              hFormula)
          hArityEquality
      have hSymbolEquality'' :
          Η ⊢ₘ[godel_quotation_theory]
            sym_codeₘ(numₘ(token)) ≐ₘ
              coded_function_symbol_code_term
                arityWitness indexWitness :=
        FirstOrder.Derives.context_weaken
          (Γ := Ζ) (Δ := Η)
          (by
            intro formula hFormula
            exact List.mem_cons_of_mem
              (indexWitness ≐ₘ numₘ(index))
              hFormula)
          hSymbolEquality'
      have hCodeEquality :
          Η ⊢ₘ[godel_quotation_theory]
            coded_function_symbol_code_term
                arityWitness indexWitness ≐ₘ
              coded_function_symbol_code_term
                (numₘ(arity)) (numₘ(index)) :=
        gq_coded_function_symbol_code_term_congr_of_equalities
          arityWitness (numₘ(arity))
          indexWitness (numₘ(index))
          hArityWitness
          (finite_numeral_term_admissible arity)
          hIndexWitness
          (finite_numeral_term_admissible index)
          hArityEquality'
          hIndexEquality
      have hConcreteEquality :
          Η ⊢ₘ[godel_quotation_theory]
            sym_codeₘ(numₘ(token)) ≐ₘ
              coded_function_symbol_code_term
                (numₘ(arity)) (numₘ(index)) :=
        Metatheory.Derives.equality_trans
          hSymbolEquality'' hCodeEquality
      apply FirstOrder.Derives.cut
        hConcreteEquality
      exact FirstOrder.Derives.context_weaken
        (Γ :=
          (sym_codeₘ(numₘ(token)) ≐ₘ
            coded_function_symbol_code_term
              (numₘ(arity)) (numₘ(index))) :: Γ)
        (Δ :=
          (sym_codeₘ(numₘ(token)) ≐ₘ
            coded_function_symbol_code_term
              (numₘ(arity)) (numₘ(index))) :: Η)
        (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · simp
          · simp [Η, Ζ, Ε, Δ, hFormula])
        (hBranch arity index hArity hIndex)

/--
标准 token 串的首 token 若不是任何正元函数 token，则它不可能满足项应用生成条件。

证明先提取有界双索引证书，再在每个有限分支用 singleton 符号码的不等式回放排除。
-/
theorem
    gq_term_application_from_condition_falsum_of_head_not_function
    {Γ : Context signature}
    (tokens : List Nat) (token : Nat)
    (hGet : tokens[0]? = some token)
    (hToken :
      ∀ arity index,
        token ≠
          Numbered.function_token arity index)
    (hContextClosed :
      ∀ formula, formula ∈ Γ →
        Formula.freeSupport formula = [])
    (hApplication :
      Γ ⊢ₘ[godel_quotation_theory]
        term_application_from_condition
          TermCodeₘ
          (standard_token_sequence tokens)) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hBounded :
      Γ ⊢ₘ[godel_quotation_theory]
        fs_bounded_function_symbol_condition
          (numₘ(token)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) <|
          gq_term_application_from_condition_implies_bounded_function_symbol
            tokens token hGet)
      hApplication
  apply gq_bounded_function_symbol_condition_elim_context
    (Γ := Γ)
    token Formula.falsum
    Formula.Admissible.falsum
    hContextClosed
    (by simp [Formula.freeSupport])
    hBounded
  intro arity index _ _
  let Δ : Context signature :=
    (sym_codeₘ(numₘ(token)) ≐ₘ
      coded_function_symbol_code_term
        (numₘ(arity)) (numₘ(index))) :: Γ
  have hEquality :
      Δ ⊢ₘ[godel_quotation_theory]
        sym_codeₘ(numₘ(token)) ≐ₘ
          coded_function_symbol_code_term
            (numₘ(arity)) (numₘ(index)) :=
    FirstOrder.Derives.assumption
      (by simp [Δ])
  exact FirstOrder.Derives.negElim
    hEquality
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Δ) (by simp [Δ]) <|
        gq_symbol_code_ne_of_token_ne
          (coded_function_symbol_code_term
            (numₘ(arity)) (numₘ(index)))
          token
          (Numbered.function_token arity index)
          (coded_function_symbol_code_term_admissible
            (numₘ(arity)) (numₘ(index))
            (finite_numeral_term_admissible arity)
            (finite_numeral_term_admissible index))
          (coded_function_symbol_code_eq_standard_token_sequence
            arity index)
          (hToken arity index))

/-! ## 对象 singleton 基础分支 -/

private theorem gq_standard_singleton_symbol_member
    {Γ : Context signature}
    (token : Nat) (space : SetTerm)
    (hSpace : Term.Admissible space SetSort.set)
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence [token] ∈ₘ space) :
    Γ ⊢ₘ[godel_quotation_theory]
      sym_codeₘ(numₘ(token)) ∈ₘ space := by
  exact FirstOrder.Derives.iffElimRight
    (membership_left_iff_of_equality
      (standard_token_sequence [token])
      (sym_codeₘ(numₘ(token)))
      space
      (standard_token_sequence_admissible [token])
      (singleton_symbol_code_term_admissible
        (numₘ(token))
        (finite_numeral_term_admissible token))
      hSpace
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_standard_token_singleton_eq_symbol_code
          token)))
    hMember

private theorem gq_constant_symbol_code_term_congr_of_equality
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        left ≐ₘ right) :
    Γ ⊢ₘ[godel_quotation_theory]
      constant_symbol_code_term left ≐ₘ
        constant_symbol_code_term right := by
  let parameter :=
    FreshVariable.fresh_id SetSort.set
      [left ≐ₘ right]
  let context :=
    constant_symbol_code_term (x#parameter)
  have hRaw :=
    gq_term_context_congr_of_equality
      parameter left right context
      (Term.check_admissible_complete hLeft)
      (Term.check_admissible_complete hRight)
      (by prove_term_check)
      (by
        have hFormulaFresh :
            (SetSort.set, parameter) ∉
              Formula.freeSupport
                (left ≐ₘ right) := by
          dsimp [parameter]
          exact FreshVariable.fresh_id_not_mem_m
            (sort := SetSort.set)
            (formulas := [left ≐ₘ right])
            (formula := left ≐ₘ right)
            (by simp)
        intro hMember
        apply hFormulaFresh
        exact List.mem_append_left
          (Term.freeSupport right) hMember)
      hEquality
  have hZeroFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter
          replacement (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hFiveFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter
          replacement (numₘ(5)) =
        numₘ(5) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  simpa [context, constant_symbol_code_term,
    constant_symbol_number_term,
    indexed_prime_power_code_term,
    prime_power_code_term,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hZeroFixed, hFiveFixed] using hRaw

private theorem
    gq_standard_singleton_constant_falsum_of_token_ne
    {Γ : Context signature}
    (token : Nat)
    (hToken :
      ∀ index,
        token ≠ Numbered.constant_token index)
    (hContextClosed :
      ∀ formula, formula ∈ Γ →
        Formula.freeSupport formula = [])
    (hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence [token] ∈ₘ
          ConstSymₘ) :
    Γ ⊢ₘ[godel_quotation_theory]
      Formula.falsum := by
  have hSymbolMember :=
    gq_standard_singleton_symbol_member
      token ConstSymₘ
      constant_symbol_set_term_admissible
      hMember
  have hBounded :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set],
          (((bₛ#0 ∈ₘ Sₘ(numₘ(token))) ∧ₘ
            (sym_codeₘ(numₘ(token)) ≐ₘ
              constant_symbol_code_term
                (bₛ#0)))) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (gq_constant_symbol_member_implies_bounded_witness
          token))
      hSymbolMember
  let witness : SetTerm := x#702
  let witnessCondition : SetFormula :=
    (witness ∈ₘ Sₘ(numₘ(token))) ∧ₘ
      (sym_codeₘ(numₘ(token)) ≐ₘ
        constant_symbol_code_term witness)
  have hWitnessConditionAdmissible :
      Formula.Admissible witnessCondition := by
    dsimp [witnessCondition, witness]
    exact Formula.Admissible.conj
      (membership_formula_admissible
        (set_variable_admissible 702)
        (successor_term_admissible
          (numₘ(token))
          (finite_numeral_term_admissible token)))
      (Formula.Admissible.equal
        (singleton_symbol_code_term_admissible
          (numₘ(token))
          (finite_numeral_term_admissible token))
        (constant_symbol_code_term_admissible
          (x#702) (set_variable_admissible 702)))
  have hExists :
      Γ ⊢ₘ[godel_quotation_theory]
        ∃ₘ[SetSort.set, 702],
          witnessCondition := by
    have hTokenClose :
        Term.closeFreeAt SetSort.set 702 0
            (numₘ(token)) =
          numₘ(token) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 702 0 (numₘ(token))
        (finite_numeral_term_admissible token).2
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    have hZeroClose :
        Term.closeFreeAt SetSort.set 702 0
            (numₘ(0)) =
          numₘ(0) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 702 0 (numₘ(0))
        (finite_numeral_term_admissible 0).2
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    have hFiveClose :
        Term.closeFreeAt SetSort.set 702 0
            (numₘ(5)) =
          numₘ(5) :=
      Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
        SetSort.set 702 0 (numₘ(5))
        (finite_numeral_term_admissible 5).2
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    simpa [witnessCondition, witness,
      Formula.closeFreeAt, Term.closeFreeAt,
      set_variable, set_bound_variable,
      hTokenClose, hZeroClose, hFiveClose] using
      hBounded
  apply FirstOrder.Derives.exists_elim
    (T := godel_quotation_theory)
    (Γ := Γ)
    (sort := SetSort.set)
    (eigen := 702)
    (body := witnessCondition)
    (conclusion := Formula.falsum)
    (hBodyCheck :=
      Formula.check_admissible_complete
        hWitnessConditionAdmissible)
  · intro formula hFormula
    rw [(godel_quotation_theory_sentence
      hFormula).2]
    exact List.not_mem_nil
  · intro formula hFormula
    rw [hContextClosed formula hFormula]
    exact List.not_mem_nil
  · simp [Formula.freeSupport]
  · exact hExists
  · let Δ : Context signature :=
      witnessCondition :: Γ
    have hWitness :
        Term.Admissible witness SetSort.set := by
      simpa [witness] using
        set_variable_admissible 702
    have hCondition :
        Δ ⊢ₘ[godel_quotation_theory]
          witnessCondition :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hWitnessMember :
        Δ ⊢ₘ[godel_quotation_theory]
          witness ∈ₘ numₘ(token + 1) := by
      simpa [witnessCondition,
        finite_numeral_term] using
        FirstOrder.Derives.conjElimLeft
          hCondition
    have hSymbolEquality :
        Δ ⊢ₘ[godel_quotation_theory]
          sym_codeₘ(numₘ(token)) ≐ₘ
            constant_symbol_code_term witness := by
      simpa [witnessCondition] using
        FirstOrder.Derives.conjElimRight
          hCondition
    apply gq_finite_numeral_member_elim_context
      (Γ := Δ)
      (token + 1) witness Formula.falsum
      hWitness Formula.Admissible.falsum
      hWitnessMember
    intro index hIndex
    let Ε : Context signature :=
      (witness ≐ₘ numₘ(index)) :: Δ
    have hWitnessEquality :
        Ε ⊢ₘ[godel_quotation_theory]
          witness ≐ₘ numₘ(index) :=
      FirstOrder.Derives.assumption
        (by simp [Ε])
    have hCodeEquality :
        Ε ⊢ₘ[godel_quotation_theory]
          constant_symbol_code_term witness ≐ₘ
            constant_symbol_code_term
              (numₘ(index)) :=
      gq_constant_symbol_code_term_congr_of_equality
        witness (numₘ(index))
        hWitness
        (finite_numeral_term_admissible index)
        hWitnessEquality
    have hConcreteEquality :
        Ε ⊢ₘ[godel_quotation_theory]
          sym_codeₘ(numₘ(token)) ≐ₘ
            constant_symbol_code_term
              (numₘ(index)) :=
      Metatheory.Derives.equality_trans
        (FirstOrder.Derives.context_weaken
          (Γ := Δ) (Δ := Ε)
          (by
            intro formula hFormula
            simpa [Ε] using
              List.mem_cons_of_mem
                (witness ≐ₘ numₘ(index))
                hFormula)
          hSymbolEquality)
        hCodeEquality
    exact FirstOrder.Derives.negElim
      hConcreteEquality
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Ε) (by simp)
        (gq_symbol_code_ne_of_token_ne
          (constant_symbol_code_term
            (numₘ(index)))
          token
          (Numbered.constant_token index)
          (constant_symbol_code_term_admissible
            (numₘ(index))
            (finite_numeral_term_admissible index))
          (constant_symbol_code_eq_standard_token_sequence
            index)
          (hToken index)))

/--
合法公式签名中的 singleton token 若具名项 decoder 失败，则其标准序列不是项码。

这是项码 checked 拒绝的基础情形；证明完全停留在对象语法与有限宿主计算之间。
-/
theorem gq_standard_token_singleton_term_code_not_of_decode_none
    (freeBase : Nat) (boundNames : List Nat)
    (token : Nat)
    (hToken : FSFormulaToken token)
    (hDecode :
      fs_named_term_tokens_decode_with_env
          freeBase boundNames [token] =
        none) :
    ⊢ₘ[godel_quotation_theory]
      ¬ₘ (standard_token_sequence [token] ∈ₘ
        TermCodeₘ) := by
  let membership : SetFormula :=
    standard_token_sequence [token] ∈ₘ TermCodeₘ
  nd_apply FirstOrder.Derives.negIntro
  let Γ : Context signature := [membership]
  have hMember :
      Γ ⊢ₘ[godel_quotation_theory]
        standard_token_sequence [token] ∈ₘ
          TermCodeₘ := by
    simpa [Γ, membership] using
      FirstOrder.Derives.assumption
        (T := godel_quotation_theory)
        (Γ := Γ)
        (φ := membership)
        (by simp [Γ])
  have hBase :
      Γ ⊢ₘ[godel_quotation_theory]
        ((standard_token_sequence [token] ∈ₘ
            VarSymₘ) ∨ₘ
          (standard_token_sequence [token] ∈ₘ
            ConstSymₘ)) :=
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp [Γ])
        (gq_standard_token_sequence_term_code_implies_base_symbol_of_second_not_left
          [token] (by simp)))
      hMember
  apply FirstOrder.Derives.disjElim hBase
  · let Δ : Context signature :=
      (standard_token_sequence [token] ∈ₘ
        VarSymₘ) :: Γ
    have hVariable :
        Δ ⊢ₘ[godel_quotation_theory]
          standard_token_sequence [token] ∈ₘ
            VarSymₘ :=
      FirstOrder.Derives.assumption
        (by simp [Δ])
    have hSymbolVariable :=
      gq_standard_singleton_symbol_member
        token VarSymₘ
        variable_symbol_set_term_admissible
        hVariable
    have hCondition :
        Δ ⊢ₘ[godel_quotation_theory]
          fs_variable_token_condition
            (numₘ(token)) :=
      FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Δ) (by simp [Δ])
          (gq_variable_symbol_member_implies_token_condition
            token))
        hSymbolVariable
    exact FirstOrder.Derives.negElim
      hCondition
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Δ) (by simp [Δ])
        (gq_fs_variable_token_condition_not
          token
          (fs_named_term_singleton_decode_variable_none
            freeBase boundNames token hDecode)))
  · let Δ : Context signature :=
      (standard_token_sequence [token] ∈ₘ
        ConstSymₘ) :: Γ
    exact
      gq_standard_singleton_constant_falsum_of_token_ne
        token
        (fs_formula_token_ne_constant_of_term_singleton_decode_none
          freeBase boundNames token hToken hDecode)
        (by
          intro formula hFormula
          simp only [Γ, membership,
            List.mem_cons] at hFormula
          rcases hFormula with
            rfl | rfl | hFormula
          · simp [Formula.freeSupport,
              Term.freeSupport,
              Term.freeSupportList]
          · simp [Formula.freeSupport,
              Term.freeSupport,
              Term.freeSupportList]
          · exact False.elim
              (List.not_mem_nil hFormula))
        (FirstOrder.Derives.assumption
          (by simp))

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
