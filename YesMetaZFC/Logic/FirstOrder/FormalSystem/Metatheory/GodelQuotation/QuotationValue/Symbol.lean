import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.FormulaCode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.StandardTokenSequenceFlatten
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.Token
import YesMetaZFC.Logic.FirstOrder.Hilbert.Substitution
/-!
# Gödel quotation 的符号值
本模块证明数值标签、变量、常元及正元符号的对象编码等于对应标准 singleton
token 序列。对象函数符号的计算只经由已证明合同完成。
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
universe u v w
/-- 长度一符号编码在任意对象理论与上下文中尊重其值的已证等式。 -/
theorem gq_singleton_symbol_code_congr_of_equality
    {T : SetTheory} {Γ : Context signature}
    (left right : SetTerm)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right)
    (hLeftCheck : Term.CheckCertificate left SetSort.set := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right SetSort.set := by
      prove_term_check) :
    Γ ⊢ₘ[T]
      sym_codeₘ(left) ≐ₘ sym_codeₘ(right) := by
  let leftCode := sym_codeₘ(left)
  let parameter := FreshVariable.fresh_id SetSort.set
    [leftCode ≐ₘ leftCode]
  let body : SetFormula :=
    leftCode ≐ₘ sym_codeₘ(x#parameter)
  have hLeftCode :
      Term.CheckCertificate leftCode SetSort.set := by
    prove_term_check
  have hLeftCodeFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement leftCode =
        leftCode := by
    apply Term.substituteFree_eq_self_of_not_mem
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m SetSort.set leftCode
  have hZeroFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set parameter replacement (numₘ(0)) =
        numₘ(0) := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [finite_numeral_term_freeSupport]
    simp
  have hReflexive :
      Γ ⊢ₘ[T]
        body⟪SetSort.set, parameter ↦ left⟫ₘ := by
    simpa [body, leftCode,
      Formula.substituteFree, Term.substituteFree,
      set_variable, hLeftCodeFixed, hZeroFixed] using
      (FirstOrder.Derives.eq_refl_m leftCode)
  have hTransport :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := SetSort.set) (eigen := parameter) (left := left) (right := right) (body := body)
      hEquality hReflexive
  simpa [body, leftCode,
    Formula.substituteFree, Term.substituteFree,
    set_variable, hLeftCodeFixed, hZeroFixed] using hTransport
/-- 已证明等式可在 quotation 理论中穿过任意对象项上下文。 -/
theorem gq_term_context_congr_of_equality
    {Γ : Context signature}
    (parameter : FreeVarId) (left right context : SetTerm)
    (hLeft : Term.CheckCertificate left SetSort.set)
    (hRight : Term.CheckCertificate right SetSort.set)
    (hContext : Term.CheckCertificate context SetSort.set) (hLeftFresh :
      (SetSort.set, parameter) ∉ Term.freeSupport left) (hEquality :
      Γ ⊢ₘ[godel_quotation_theory] left ≐ₘ right) :
    Γ ⊢ₘ[godel_quotation_theory]
      Term.substituteFree SetSort.set parameter left context ≐ₘ
        Term.substituteFree SetSort.set parameter right context := by
  exact
    Metatheory.Derives.term_substituteFree_congr_of_equality
      SetSort.set parameter left right context
      hLeft.admissible hRight.admissible hContext.admissible
      hLeftFresh hEquality
/--
若一个闭自然数项已经证明取值为外部自然数 `value`，其长度一符号编码就等于相应
标准 singleton token 序列。
-/
private theorem gq_singleton_symbol_code_eq_standard_of_value
    (number : SetTerm) (value : Nat)
    (hValue : ⊢ₘ[godel_quotation_theory] number ≐ₘ numₘ(value))
    (hNumber : Term.CheckCertificate number SetSort.set := by
      prove_term_check) :
    ⊢ₘ[godel_quotation_theory]
      sym_codeₘ(number) ≐ₘ standard_token_sequence [value] := by
  let numeral := numₘ(value)
  have hNumeral : Term.CheckCertificate numeral SetSort.set := by
    prove_term_check
  have hCodeNumeral :=
    gq_singleton_symbol_code_congr_of_equality
      number numeral hValue
  have hStandard :
      ⊢ₘ[godel_quotation_theory]
        standard_token_sequence [value] ≐ₘ sym_codeₘ(numeral) :=
    gq_weaken_standard_sequence <| by
      simpa [standard_token_sequence, numeral] using
        standard_singleton_sequence_eq_symbol_code
          numeral hNumeral.admissible
  have hStandardBack :
      ⊢ₘ[godel_quotation_theory]
        sym_codeₘ(numeral) ≐ₘ standard_token_sequence [value] :=
    Metatheory.Derives.equality_symm hStandard
  exact Metatheory.Derives.equality_trans
    hCodeNumeral hStandardBack
/--
对象幂项形成的长度一符号编码，等于相应外部幂值的标准 singleton token 序列。
-/
theorem prime_power_symbol_code_eq_standard_token_sequence (prime exponent : Nat) :
    ⊢ₘ[godel_quotation_theory]
      sym_codeₘ(prime_power_code_term prime (numₘ(exponent))) ≐ₘ
        standard_token_sequence [prime ^ exponent] := by
  let number := prime_power_code_term prime (numₘ(exponent))
  let numeral := numₘ(prime ^ exponent)
  have hNumber : Term.CheckCertificate number SetSort.set := by
    prove_term_check
  have hNumeral : Term.CheckCertificate numeral SetSort.set := by
    prove_term_check
  have hNumeralNumber :
      ⊢ₘ[godel_quotation_theory]
        numeral ≐ₘ number :=
    gq_weaken_standard_sequence <| by
      simpa [number, numeral, prime_power_code_term] using
        standard_token_sequence_finite_numeral_exponentiation
          prime exponent
  have hNumberNumeral :
      ⊢ₘ[godel_quotation_theory]
        number ≐ₘ numeral :=
    Metatheory.Derives.equality_symm hNumeralNumber
  have hCodeNumeral :=
    gq_singleton_symbol_code_congr_of_equality
      number numeral hNumberNumeral
  have hStandard :
      ⊢ₘ[godel_quotation_theory]
        standard_token_sequence [prime ^ exponent] ≐ₘ
          sym_codeₘ(numeral) :=
    gq_weaken_standard_sequence <| by
      simpa [standard_token_sequence, numeral] using
        standard_singleton_sequence_eq_symbol_code (numₘ(prime ^ exponent))
          hNumeral.admissible
  have hStandardBack :
      ⊢ₘ[godel_quotation_theory]
        sym_codeₘ(numeral) ≐ₘ
          standard_token_sequence [prime ^ exponent] :=
    Metatheory.Derives.equality_symm hStandard
  exact Metatheory.Derives.equality_trans
    hCodeNumeral hStandardBack
/-- 逻辑符号对象编码等于它的标准 singleton token 序列。 -/
theorem logical_symbol_code_eq_standard_token_sequence (symbol : LogicalSymbolKind) :
    ⊢ₘ[godel_quotation_theory]
      logical_symbol_code_term symbol ≐ₘ
        standard_token_sequence [logical_token symbol] := by
  simpa [logical_symbol_number_term, Numbered.logical_token] using
    prime_power_symbol_code_eq_standard_token_sequence
      2 (logical_symbol_exponent symbol)
/-- 隶属符号对象编码等于它的标准 singleton token 序列。 -/
theorem membership_symbol_code_eq_standard_token_sequence :
    ⊢ₘ[godel_quotation_theory]
      membership_symbol_code_term ≐ₘ
        standard_token_sequence [membership_token] := by
  simpa [membership_symbol_number_term, Numbered.membership_token] using
    prime_power_symbol_code_eq_standard_token_sequence 2 7
/-- 具名变量编码等于 `3^(name+1)` 的标准 singleton token 序列。 -/
theorem named_variable_code_eq_standard_token_sequence (name : Nat) :
    ⊢ₘ[godel_quotation_theory]
      named_variable_code name ≐ₘ
        standard_token_sequence [variable_token name] := by
  let index := numₘ(name)
  let variableCode := named_variable_code name
  let rawCode := variable_symbol_code_term index
  have hIndex : Term.CheckCertificate index SetSort.set := by
    prove_term_check
  have hVariableCode :
      Term.CheckCertificate variableCode SetSort.set := by
    prove_term_check
  have hRawCode : Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hDefinition :=
    gq_weaken_symbol_operator <|
      variable_code_definition_instance_derives
        index variableCode hIndex.admissible hVariableCode.admissible
  have hReflexive :
      ⊢ₘ[godel_quotation_theory]
        variableCode ≐ₘ var_codeₘ(index) := by
    simpa [variableCode, named_variable_code, index] using
      (FirstOrder.Derives.eq_refl_m variableCode)
  have hVariableRaw :
      ⊢ₘ[godel_quotation_theory]
        variableCode ≐ₘ rawCode := by
    simpa [variableCode, rawCode, index,
      variable_code_definition_instance] using
      FirstOrder.Derives.iffElimRight hDefinition hReflexive
  have hRawStandard :
      ⊢ₘ[godel_quotation_theory]
        rawCode ≐ₘ
          standard_token_sequence [variable_token name] := by
    simpa [rawCode, index, variable_symbol_code_term,
      variable_symbol_number_term, indexed_prime_power_code_term,
      Numbered.variable_token, finite_numeral_term] using
      prime_power_symbol_code_eq_standard_token_sequence
        3 (name + 1)
  exact Metatheory.Derives.equality_trans
    hVariableRaw hRawStandard
/-- 常元符号对象编码等于 `5^(index+1)` 的标准 singleton token 序列。 -/
theorem constant_symbol_code_eq_standard_token_sequence (index : Nat) :
    ⊢ₘ[godel_quotation_theory]
      constant_symbol_code_term (numₘ(index)) ≐ₘ
        standard_token_sequence [Numbered.constant_token index] := by
  simpa [constant_symbol_code_term, constant_symbol_number_term,
    indexed_prime_power_code_term, Numbered.constant_token,
    finite_numeral_term] using
    prime_power_symbol_code_eq_standard_token_sequence 5 (index + 1)
/-- 常元编码运算的 quotation 值等于相应标准 singleton token 序列。 -/
theorem constant_code_eq_standard_token_sequence (index : Nat) :
    ⊢ₘ[godel_quotation_theory]
      const_codeₘ(numₘ(index)) ≐ₘ
        standard_token_sequence [Numbered.constant_token index] := by
  let indexTerm := numₘ(index)
  let code := const_codeₘ(indexTerm)
  let rawCode := constant_symbol_code_term indexTerm
  have hIndex : Term.CheckCertificate indexTerm SetSort.set := by
    prove_term_check
  have hCode : Term.CheckCertificate code SetSort.set := by
    prove_term_check
  have hRawCode : Term.CheckCertificate rawCode SetSort.set := by
    prove_term_check
  have hDefinition :=
    gq_weaken_symbol_operator <|
      constant_code_definition_instance_derives
        indexTerm code hIndex.admissible hCode.admissible
  have hReflexive :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ const_codeₘ(indexTerm) := by
    simpa [code] using (FirstOrder.Derives.eq_refl_m code)
  have hCodeRaw :
      ⊢ₘ[godel_quotation_theory]
        code ≐ₘ rawCode := by
    simpa [code, rawCode,
      constant_code_definition_instance] using
      FirstOrder.Derives.iffElimRight hDefinition hReflexive
  have hRawStandard :
      ⊢ₘ[godel_quotation_theory]
        rawCode ≐ₘ
          standard_token_sequence [Numbered.constant_token index] := by
    simpa [rawCode, indexTerm] using
      constant_symbol_code_eq_standard_token_sequence index
  exact Metatheory.Derives.equality_trans
    hCodeRaw hRawStandard
/--
两个素数幂乘积形成的长度一符号编码，等于其外部自然数乘积的标准 singleton 序列。
-/
theorem prime_power_product_symbol_code_eq_standard_token_sequence (leftPrime leftExponent rightPrime rightExponent : Nat) :
    ⊢ₘ[godel_quotation_theory]
      sym_codeₘ( (prime_power_code_term leftPrime (numₘ(leftExponent))) *ₘ
          prime_power_code_term rightPrime (numₘ(rightExponent))) ≐ₘ
        standard_token_sequence
          [leftPrime ^ leftExponent * rightPrime ^ rightExponent] := by
  let leftPower :=
    prime_power_code_term leftPrime (numₘ(leftExponent))
  let rightPower :=
    prime_power_code_term rightPrime (numₘ(rightExponent))
  let leftNumeral := numₘ(leftPrime ^ leftExponent)
  let rightNumeral := numₘ(rightPrime ^ rightExponent)
  let product := leftPower *ₘ rightPower
  let productNumeral :=
    numₘ(leftPrime ^ leftExponent * rightPrime ^ rightExponent)
  have hLeftPower :
      Term.CheckCertificate leftPower SetSort.set := by
    prove_term_check
  have hRightPower :
      Term.CheckCertificate rightPower SetSort.set := by
    prove_term_check
  have hLeftNumeral :
      Term.CheckCertificate leftNumeral SetSort.set := by
    prove_term_check
  have hRightNumeral :
      Term.CheckCertificate rightNumeral SetSort.set := by
    prove_term_check
  have hProduct : Term.CheckCertificate product SetSort.set := by
    prove_term_check
  have hProductNumeral :
      Term.CheckCertificate productNumeral SetSort.set := by
    prove_term_check
  have hLeftNumeralPower :
      ⊢ₘ[godel_quotation_theory] leftNumeral ≐ₘ leftPower :=
    gq_weaken_standard_sequence <| by
      simpa [leftNumeral, leftPower, prime_power_code_term] using
        standard_token_sequence_finite_numeral_exponentiation
          leftPrime leftExponent
  have hLeftValue :
      ⊢ₘ[godel_quotation_theory] leftPower ≐ₘ leftNumeral :=
    Metatheory.Derives.equality_symm hLeftNumeralPower
  have hRightNumeralPower :
      ⊢ₘ[godel_quotation_theory] rightNumeral ≐ₘ rightPower :=
    gq_weaken_standard_sequence <| by
      simpa [rightNumeral, rightPower, prime_power_code_term] using
        standard_token_sequence_finite_numeral_exponentiation
          rightPrime rightExponent
  have hRightValue :
      ⊢ₘ[godel_quotation_theory] rightPower ≐ₘ rightNumeral :=
    Metatheory.Derives.equality_symm hRightNumeralPower
  let leftParameter :=
    FreshVariable.fresh_id SetSort.set [leftPower ≐ₘ leftPower]
  let leftContext := (x#leftParameter) *ₘ rightPower
  have hLeftContext :
      Term.CheckCertificate leftContext SetSort.set := by
    prove_term_check
  have hRightPowerFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set leftParameter replacement rightPower =
        rightPower := by
    apply Term.substituteFree_eq_self_of_not_mem
    simp [rightPower,  Term.freeSupport,
      Term.freeSupportList, finite_numeral_term_freeSupport]
  have hLeftProductRaw :=
    gq_term_context_congr_of_equality
      leftParameter leftPower leftNumeral leftContext
      hLeftPower hLeftNumeral hLeftContext (by
        dsimp [leftParameter]
        exact FreshVariable.fresh_term_not_mem_m
          SetSort.set leftPower)
      hLeftValue
  have hLeftProduct :
      ⊢ₘ[godel_quotation_theory]
        product ≐ₘ (leftNumeral *ₘ rightPower) := by
    simpa [product, leftContext, leftParameter,
      natural_multiplication_term, Term.substituteFree,
      set_variable, hRightPowerFixed] using hLeftProductRaw
  let rightParameter :=
    FreshVariable.fresh_id SetSort.set [rightPower ≐ₘ rightPower]
  let rightContext := leftNumeral *ₘ (x#rightParameter)
  have hRightContext :
      Term.CheckCertificate rightContext SetSort.set := by
    prove_term_check
  have hLeftNumeralFixed (replacement : SetTerm) :
      Term.substituteFree SetSort.set rightParameter replacement leftNumeral =
        leftNumeral := by
    apply Term.substituteFree_eq_self_of_not_mem
    rw [show Term.freeSupport leftNumeral = [] by
      simpa [leftNumeral] using
        finite_numeral_term_freeSupport (leftPrime ^ leftExponent)]
    simp
  have hRightProductRaw :=
    gq_term_context_congr_of_equality
      rightParameter rightPower rightNumeral rightContext
      hRightPower hRightNumeral hRightContext (by
        dsimp [rightParameter]
        exact FreshVariable.fresh_term_not_mem_m
          SetSort.set rightPower)
      hRightValue
  have hRightProduct :
      ⊢ₘ[godel_quotation_theory] (leftNumeral *ₘ rightPower) ≐ₘ (leftNumeral *ₘ rightNumeral) := by
    simpa [rightContext, rightParameter,
      natural_multiplication_term, Term.substituteFree,
      set_variable, hLeftNumeralFixed] using hRightProductRaw
  have hMiddleProduct :
      Term.CheckCertificate
        (leftNumeral *ₘ rightPower) SetSort.set := by
    prove_term_check
  have hNumeralProductTerm :
      Term.CheckCertificate
        (leftNumeral *ₘ rightNumeral) SetSort.set := by
    prove_term_check
  have hProductToNumeralProduct :
      ⊢ₘ[godel_quotation_theory]
        product ≐ₘ (leftNumeral *ₘ rightNumeral) :=
    Metatheory.Derives.equality_trans hLeftProduct hRightProduct
  have hNumeralProduct :
      ⊢ₘ[godel_quotation_theory]
        productNumeral ≐ₘ (leftNumeral *ₘ rightNumeral) :=
    gq_weaken_standard_sequence <| by
      simpa [productNumeral, leftNumeral, rightNumeral] using
        standard_token_sequence_finite_numeral_multiplication (leftPrime ^ leftExponent) (rightPrime ^ rightExponent)
  have hNumeralProductBack :
      ⊢ₘ[godel_quotation_theory] (leftNumeral *ₘ rightNumeral) ≐ₘ productNumeral :=
    Metatheory.Derives.equality_symm hNumeralProduct
  have hProductValue :
      ⊢ₘ[godel_quotation_theory] product ≐ₘ productNumeral :=
    Metatheory.Derives.equality_trans
      hProductToNumeralProduct hNumeralProductBack
  simpa [product, productNumeral] using
    gq_singleton_symbol_code_eq_standard_of_value
      product (leftPrime ^ leftExponent * rightPrime ^ rightExponent)
      hProductValue
/--
正元函数符号码同时尊重元数前驱与函数编号的已证等式。

该接口把双索引编码视为一个二元对象项构造子，不暴露其素数幂乘积实现。
-/
theorem gq_coded_function_symbol_code_term_congr_of_equalities
    {Γ : Context signature}
    (leftArity rightArity leftIndex rightIndex : SetTerm)
    (hLeftArity : Term.Admissible leftArity SetSort.set)
    (hRightArity : Term.Admissible rightArity SetSort.set)
    (hLeftIndex : Term.Admissible leftIndex SetSort.set)
    (hRightIndex : Term.Admissible rightIndex SetSort.set)
    (hArityEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftArity ≐ₘ rightArity)
    (hIndexEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftIndex ≐ₘ rightIndex) :
    Γ ⊢ₘ[godel_quotation_theory]
      coded_function_symbol_code_term
          leftArity leftIndex ≐ₘ
        coded_function_symbol_code_term
          rightArity rightIndex := by
  apply
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      coded_function_symbol_code_term
  · exact coded_function_symbol_code_term_admissible
  · intro parameter replacement arity index
    have hNumeralFixed (value : Nat) :
        Term.substituteFree SetSort.set parameter
            replacement (numₘ(value)) =
          numₘ(value) :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set parameter replacement
        (numₘ(value))
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    simp [coded_function_symbol_code_term,
      coded_function_symbol_number_term,
      indexed_prime_power_code_term,
      prime_power_code_term,
      singleton_symbol_code_term,
      Term.substituteFree, hNumeralFixed]
  · exact hLeftArity
  · exact hRightArity
  · exact hLeftIndex
  · exact hRightIndex
  · exact hArityEquality
  · exact hIndexEquality

/--
正元谓词符号码同时尊重元数前驱与谓词编号的已证等式。

该接口与函数符号版本保持同一强度，只暴露二元对象项构造子的合同性质。
-/
theorem gq_coded_predicate_symbol_code_term_congr_of_equalities
    {Γ : Context signature}
    (leftArity rightArity leftIndex rightIndex : SetTerm)
    (hLeftArity : Term.Admissible leftArity SetSort.set)
    (hRightArity : Term.Admissible rightArity SetSort.set)
    (hLeftIndex : Term.Admissible leftIndex SetSort.set)
    (hRightIndex : Term.Admissible rightIndex SetSort.set)
    (hArityEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftArity ≐ₘ rightArity)
    (hIndexEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        leftIndex ≐ₘ rightIndex) :
    Γ ⊢ₘ[godel_quotation_theory]
      coded_predicate_symbol_code_term
          leftArity leftIndex ≐ₘ
        coded_predicate_symbol_code_term
          rightArity rightIndex := by
  apply
    Metatheory.Derives.binary_term_constructor_congr_of_equalities
      coded_predicate_symbol_code_term
  · exact coded_predicate_symbol_code_term_admissible
  · intro parameter replacement arity index
    have hNumeralFixed (value : Nat) :
        Term.substituteFree SetSort.set parameter
            replacement (numₘ(value)) =
          numₘ(value) :=
      Term.substituteFree_eq_self_of_not_mem
        SetSort.set parameter replacement
        (numₘ(value))
        (by
          rw [finite_numeral_term_freeSupport]
          exact List.not_mem_nil)
    simp [coded_predicate_symbol_code_term,
      coded_predicate_symbol_number_term,
      indexed_prime_power_code_term,
      prime_power_code_term,
      singleton_symbol_code_term,
      Term.substituteFree, hNumeralFixed]
  · exact hLeftArity
  · exact hRightArity
  · exact hLeftIndex
  · exact hRightIndex
  · exact hArityEquality
  · exact hIndexEquality

/-- 正元函数符号对象编码等于其标准 singleton token 序列。 -/
theorem coded_function_symbol_code_eq_standard_token_sequence (arityPredecessor index : Nat) :
    ⊢ₘ[godel_quotation_theory]
      coded_function_symbol_code_term (numₘ(arityPredecessor)) (numₘ(index)) ≐ₘ
        standard_token_sequence
          [Numbered.function_token arityPredecessor index] := by
  simpa [coded_function_symbol_code_term,
    coded_function_symbol_number_term,
    indexed_prime_power_code_term, Numbered.function_token,
    finite_numeral_term] using
    prime_power_product_symbol_code_eq_standard_token_sequence
      3 (arityPredecessor + 1) 5 (index + 1)
/-- 正元谓词符号对象编码等于其标准 singleton token 序列。 -/
theorem coded_predicate_symbol_code_eq_standard_token_sequence (arityPredecessor index : Nat) :
    ⊢ₘ[godel_quotation_theory]
      coded_predicate_symbol_code_term (numₘ(arityPredecessor)) (numₘ(index)) ≐ₘ
        standard_token_sequence
          [Numbered.predicate_token arityPredecessor index] := by
  simpa [coded_predicate_symbol_code_term,
    coded_predicate_symbol_number_term,
    indexed_prime_power_code_term, Numbered.predicate_token,
    finite_numeral_term] using
    prime_power_product_symbol_code_eq_standard_token_sequence
      3 (arityPredecessor + 1) 7 (index + 1)
end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
