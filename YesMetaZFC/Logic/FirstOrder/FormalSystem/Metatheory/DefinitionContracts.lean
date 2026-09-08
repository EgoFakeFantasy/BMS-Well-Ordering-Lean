import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure

/-!
# 结构化编码的对象理论定义合同

本模块把结构语法、结构变换与逻辑规则的闭定义公理实例化为可直接消费的对象逻辑
定理。全部实参均是内在良构的开放项；排序、作用域、bound 闭性和变量新鲜性由类型
直接保证，不再携带 `Admissible`、自由支撑或保留自然数编号条件。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

private theorem structural_syntax_axiom_derives :
    ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
      Formula.fromSentence structural_syntax_definition_axiom :=
  FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)

/-! ## 结构语法递归方程 -/

/-- 项码递归方程可在任意开放上下文中直接实例化。 -/
theorem term_code_at_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (depth code : SetOpenTerm free) :
    Γ ⊢ₘ[formal_language_encoding_theory]
      term_code_at_definition_instance depth code := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    term_code_at_definition_instance
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons code
      (VariableSubstitution.cons depth VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    simpa [structural_syntax_definition_axiom, body] using!
      FirstOrder.Derives.conj_elim_left
        (FirstOrder.Derives.conj_elim_left structural_syntax_axiom_derives)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, Term.substituteFree, Substitution.free_map,
    Term.substitute, Term.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-- 参数列码递归方程可在任意开放上下文中直接实例化。 -/
theorem term_list_code_at_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (depth length code : SetOpenTerm free) :
    Γ ⊢ₘ[formal_language_encoding_theory]
      term_list_code_at_definition_instance depth length code := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    term_list_code_at_definition_instance
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons code
      (VariableSubstitution.cons length
        (VariableSubstitution.cons depth VariableSubstitution.empty))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    simpa [structural_syntax_definition_axiom, body] using!
      FirstOrder.Derives.conj_elim_right
        (FirstOrder.Derives.conj_elim_left structural_syntax_axiom_derives)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, Term.substituteFree, Substitution.free_map,
    Term.substitute, Term.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-- 公式码递归方程可在任意开放上下文中直接实例化。 -/
theorem formula_code_at_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (depth code : SetOpenTerm free) :
    Γ ⊢ₘ[formal_language_encoding_theory]
      formula_code_at_definition_instance depth code := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    formula_code_at_definition_instance
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons code
      (VariableSubstitution.cons depth VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[formal_language_encoding_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    simpa [structural_syntax_definition_axiom, body] using!
      FirstOrder.Derives.conj_elim_right structural_syntax_axiom_derives
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, Term.substituteFree, Substitution.free_map,
    Term.substitute, Term.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-! ## 结构变换与自由变量出现 -/

/-- 统一结构变换图可在任意开放上下文中直接实例化。 -/
theorem syntax_transform_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (kind operation depth variableIndex replacement source target :
      SetOpenTerm free) :
    Γ ⊢ₘ[expression_encoding_theory]
      syntax_transform_definition_instance
        kind operation depth variableIndex replacement source target := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
        SetSort.set, SetSort.set, SetSort.set] :=
    syntax_transform_definition_instance
      (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set, SetSort.set,
        SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons target
      (VariableSubstitution.cons source
        (VariableSubstitution.cons replacement
          (VariableSubstitution.cons variableIndex
            (VariableSubstitution.cons depth
              (VariableSubstitution.cons operation
                (VariableSubstitution.cons kind
                  VariableSubstitution.empty))))))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    have hAxiom :
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          Formula.fromSentence syntax_transform_definition_axiom :=
      FirstOrder.Derives.theory_axiom
        (by exact Or.inr (Or.inl (Or.inr (Or.inl rfl))))
    simpa [syntax_transform_definition_axiom, body] using hAxiom
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, Term.substituteFree, Substitution.free_map,
    Term.substitute, Term.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-- 自由变量出现递归方程可在任意开放上下文中直接实例化。 -/
theorem free_variable_occurs_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (kind variableIndex code : SetOpenTerm free) :
    Γ ⊢ₘ[expression_encoding_theory]
      free_variable_occurs_definition_instance kind variableIndex code := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    free_variable_occurs_definition_instance
      (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons code
      (VariableSubstitution.cons variableIndex
        (VariableSubstitution.cons kind VariableSubstitution.empty))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    have hAxiom :
        ([] : Context signature []) ⊢ₘ[expression_encoding_theory]
          Formula.fromSentence free_variable_occurs_definition_axiom :=
      FirstOrder.Derives.theory_axiom
        (by exact Or.inr (Or.inl (Or.inl rfl)))
    simpa [free_variable_occurs_definition_axiom, body] using hAxiom
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, Term.substituteFree, Substitution.free_map,
    Term.substitute, Term.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.boundId] using hInstance

/-! ## 逻辑公理闭包与 modus ponens -/

private theorem logical_axiom_code_axiom_derives :
    ([] : Context signature []) ⊢ₘ[logical_axiom_code_theory]
      Formula.fromSentence logical_axiom_code_definition_axiom :=
  FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)

/-- 基础逻辑公理集合的成员关系等价于十二个结构化公理族的析取。 -/
theorem base_logical_axiom_set_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (code : SetOpenTerm free) :
    Γ ⊢ₘ[logical_axiom_code_theory]
      ((code ∈ₘ BaseLogicAxiomsₘ) ↔ₘ
        base_logical_axiom_condition code) := by
  let body : SetOpenFormula [SetSort.set] :=
    ((.fvar .here ∈ₘ BaseLogicAxiomsₘ) ↔ₘ
      base_logical_axiom_condition (.fvar .here))
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons code VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[logical_axiom_code_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    simpa [logical_axiom_code_definition_axiom,
      base_logical_axiom_set_definition_axiom, body] using!
      FirstOrder.Derives.conj_elim_left logical_axiom_code_axiom_derives
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId] using! hInstance

/-- 逻辑公理码谓词等价于逻辑公理闭包集合的成员关系。 -/
theorem logical_axiom_code_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (code : SetOpenTerm free) :
    Γ ⊢ₘ[logical_axiom_code_theory]
      (logical_axiom_codeₘ(code) ↔ₘ code ∈ₘ LogicAxiomsₘ) := by
  let body : SetOpenFormula [SetSort.set] :=
    (logical_axiom_codeₘ(.fvar .here) ↔ₘ
      (.fvar .here ∈ₘ LogicAxiomsₘ))
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons code VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[logical_axiom_code_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    simpa [logical_axiom_code_definition_axiom,
      is_logical_axiom_code_definition_axiom, body] using!
      FirstOrder.Derives.conj_elim_right
        (FirstOrder.Derives.conj_elim_right logical_axiom_code_axiom_derives)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId] using hInstance

/-- `modus_ponensₘ` 等价于结构化公式码与蕴含码条件。 -/
theorem modus_ponens_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (premise implication conclusion : SetOpenTerm free) :
    Γ ⊢ₘ[logical_rule_encoding_theory]
      (modus_ponensₘ(premise, implication, conclusion) ↔ₘ
        modus_ponens_condition premise implication conclusion) := by
  let body : SetOpenFormula
      [SetSort.set, SetSort.set, SetSort.set] :=
    (modus_ponensₘ(
        .fvar (.there (.there .here)), .fvar (.there .here), .fvar .here) ↔ₘ
      modus_ponens_condition
        (.fvar (.there (.there .here)))
        (.fvar (.there .here)) (.fvar .here))
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons conclusion
      (VariableSubstitution.cons implication
        (VariableSubstitution.cons premise VariableSubstitution.empty))
  have hClosed :
      ([] : Context signature []) ⊢ₘ[logical_rule_encoding_theory]
        Formula.fromSentence (Metatheory.Formula.forall_close body) := by
    have hAxiom :
        ([] : Context signature []) ⊢ₘ[logical_rule_encoding_theory]
          Formula.fromSentence modus_ponens_definition_axiom :=
      FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
    simpa [modus_ponens_definition_axiom, body] using hAxiom
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree, VariableSubstitution.weakenBound,
    VariableSubstitution.boundId, VariableSubstitution.freeId] using! hInstance

/-- 三条公式码证书和蕴含码等式足以推出一次对象化 modus ponens。 -/
theorem modus_ponens_derives_of_condition
    {free : SetContext} {T : SetTheory} {Γ : Context signature free}
    (hLogicalRules :
      ∀ sentence : SetSentence,
        logical_rule_encoding_theory sentence → T sentence)
    (premise implication conclusion : SetOpenTerm free)
    (hPremiseFormulaCode : Γ ⊢ₘ[T] formula_codeₘ(premise))
    (hImplicationFormulaCode : Γ ⊢ₘ[T] formula_codeₘ(implication))
    (hConclusionFormulaCode : Γ ⊢ₘ[T] formula_codeₘ(conclusion))
    (hImplicationCode :
      Γ ⊢ₘ[T] implication ≐ₘ imp_codeₘ(premise, conclusion)) :
    Γ ⊢ₘ[T] modus_ponensₘ(premise, implication, conclusion) := by
  have hIff :
      Γ ⊢ₘ[T]
        (modus_ponensₘ(premise, implication, conclusion) ↔ₘ
          modus_ponens_condition premise implication conclusion) :=
    FirstOrder.Derives.theory_weaken
      (by
        intro sentence hSentence
        exact hLogicalRules sentence hSentence)
      (modus_ponens_definition_instance_derives
        (Γ := Γ) premise implication conclusion)
  apply FirstOrder.Derives.iff_elim_right hIff
  exact FirstOrder.Derives.conj_intro
    (FirstOrder.Derives.conj_intro
      (FirstOrder.Derives.conj_intro
        hPremiseFormulaCode hImplicationFormulaCode)
      hConclusionFormulaCode)
    hImplicationCode

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
