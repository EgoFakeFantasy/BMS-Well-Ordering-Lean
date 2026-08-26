import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationComposition
/-!
# 等价关系、函数与映射
本模块建立关系代数之上的函数层。文献中的 `DJGX`、`HanS`、`InSh` 与 `rng`
只在注释中作为索引；公共接口统一使用 `is_equivalence_relation`、`is_function`、
`is_mapping` 与 `range`。
定义采用现代直接规格：
* 等价关系由非空载体上的自反、对称、传递关系刻画；
* 函数是单值关系，不重复加入可由关系性与图成员推出的值域限制；
* 映射记录精确定义域和值域上界；
* 求值函数只在函数及定义域成员这一自然 guard 下与图成员关系等价。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-! ## 等价关系 -/
/-- 关系在其定义域上自反。 -/
def relation_reflexive_on_domain_condition (relation : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ domₘ(relation)) ⟶ₘ (⟨bₛ#0, bₛ#0⟩ₘ ∈ₘ relation)
/-- 关系在其定义域上对称。 -/
def relation_symmetric_on_domain_condition (relation : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set],
    ∀ₘ[SetSort.set], ((bₛ#1 ∈ₘ domₘ(relation)) ∧ₘ (bₛ#0 ∈ₘ domₘ(relation))) ⟶ₘ (⟨bₛ#1, bₛ#0⟩ₘ ∈ₘ relation) ⟶ₘ (⟨bₛ#0, bₛ#1⟩ₘ ∈ₘ relation)
/-- 关系在其定义域上传递。 -/
def relation_transitive_on_domain_condition (relation : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set],
    ∀ₘ[SetSort.set],
      ∀ₘ[SetSort.set], ((bₛ#2 ∈ₘ domₘ(relation)) ∧ₘ ((bₛ#1 ∈ₘ domₘ(relation)) ∧ₘ (bₛ#0 ∈ₘ domₘ(relation)))) ⟶ₘ ((⟨bₛ#2, bₛ#1⟩ₘ ∈ₘ relation) ∧ₘ
              (⟨bₛ#1, bₛ#0⟩ₘ ∈ₘ relation)) ⟶ₘ (⟨bₛ#2, bₛ#0⟩ₘ ∈ₘ relation)
/--
等价关系的现代条件。
文献以 `¬(dom(R) = ∅)` 表示非空；核心改用存在成员，避免把空集描述符合同
传播到只需要非空性的定义中。
-/
def is_equivalence_relation_condition (relation : SetTerm) :
    SetFormula :=
  is_relation_formula relation ∧ₘ ((domₘ(relation) ≐ₘ ranₘ(relation)) ∧ₘ (set_has_member (domₘ(relation)) ∧ₘ (relation_reflexive_on_domain_condition relation ∧ₘ
          (relation_symmetric_on_domain_condition relation ∧ₘ
            relation_transitive_on_domain_condition relation))))
/-- 等价关系谓词的开放定义实例。文献索引为 `DJGX`。 -/
def is_equivalence_relation_definition_instance (relation : SetTerm) :
    SetFormula :=
  is_equivalence_relation_formula relation ↔ₘ
    is_equivalence_relation_condition relation
/-- 等价关系谓词定义公理。 -/
def is_equivalence_relation_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_equivalence_relation_definition_instance (x#0)
/-! ## 函数与映射 -/
/-- 一个关系是单值的。 -/
def function_single_valued_condition (function : SetTerm) :
    SetFormula :=
  ∀ₘ[SetSort.set],
    ∀ₘ[SetSort.set],
      ∀ₘ[SetSort.set], ((⟨bₛ#2, bₛ#1⟩ₘ ∈ₘ function) ∧ₘ (⟨bₛ#2, bₛ#0⟩ₘ ∈ₘ function)) ⟶ₘ (bₛ#1 ≐ₘ bₛ#0)
/-- 集合编码函数是单值关系。 -/
def is_function_condition (function : SetTerm) :
    SetFormula :=
  is_relation_formula function ∧ₘ
    function_single_valued_condition function
/-- 函数谓词的开放定义实例。文献索引为 `HanS`。 -/
def is_function_definition_instance (function : SetTerm) :
    SetFormula :=
  is_function_formula function ↔ₘ
    is_function_condition function
/-- 函数谓词定义公理。 -/
def is_function_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    is_function_definition_instance (x#0)
/-- `function` 是从 `source` 映入 `target` 的映射。 -/
def is_mapping_condition (function source target : SetTerm) :
    SetFormula :=
  is_function_formula function ∧ₘ ((source ≐ₘ domₘ(function)) ∧ₘ (ranₘ(function) ⊆ₘ target))
/-- 映射谓词的开放定义实例。文献索引为 `InSh`。 -/
def is_mapping_definition_instance (function source target : SetTerm) :
    SetFormula :=
  is_mapping_formula function source target ↔ₘ
    is_mapping_condition function source target
/-- 映射谓词定义公理。 -/
def is_mapping_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        is_mapping_definition_instance (x#0) (x#1) (x#2)
/-! ## 函数求值 -/
/-- 求值函数符号的开放图合同。 -/
def function_application_definition_instance (function argument value : SetTerm) :
    SetFormula := (is_function_formula function ∧ₘ (argument ∈ₘ domₘ(function))) ⟶ₘ ((value ≐ₘ (function ·ₘ argument)) ↔ₘ (⟨argument, value⟩ₘ ∈ₘ function))
/-- 求值函数符号定义公理。 -/
def function_application_definition_axiom :
    SetFormula :=
  ∀ₘ[SetSort.set, 0],
    ∀ₘ[SetSort.set, 1],
      ∀ₘ[SetSort.set, 2],
        function_application_definition_instance (x#0) (x#1) (x#2)
/--
函数图成员的规范坐标条件。
该条件把文献中反复展开的有序对见证压缩为投影、定义域与求值三个稳定接口。
-/
def function_graph_member_condition (function member : SetTerm) :
    SetFormula :=
  is_ordered_pair_formula member ∧ₘ (((member)₀ₘ ∈ₘ domₘ(function)) ∧ₘ ((member)₁ₘ ≐ₘ (function ·ₘ (member)₀ₘ)))
/-- 两个函数图具有相同定义域，并在该定义域上逐点相等。 -/
def function_extensional_agreement (left right : SetTerm) :
    SetFormula := (domₘ(left) ≐ₘ domₘ(right)) ∧ₘ (∀ₘ[SetSort.set], (bₛ#0 ∈ₘ domₘ(left)) ⟶ₘ ((left ·ₘ bₛ#0) ≐ₘ (right ·ₘ bₛ#0)))
/-! ## 理论边界 -/
/-- 在关系复合层上加入等价关系谓词。 -/
def equivalence_relation_theory : SetTheory :=
  Theory.insert
    is_equivalence_relation_definition_axiom
    relation_composition_operator_theory
/-- 加入函数谓词。 -/
def function_predicate_theory : SetTheory :=
  Theory.insert
    is_function_definition_axiom
    equivalence_relation_theory
/-- 加入映射谓词。 -/
def mapping_predicate_theory : SetTheory :=
  Theory.insert
    is_mapping_definition_axiom
    function_predicate_theory
/-- 加入函数求值符号。 -/
def function_application_theory : SetTheory :=
  Theory.insert
    function_application_definition_axiom
    mapping_predicate_theory
/-! ## proof-carrying 良构性 -/
/-- 函数求值项满足 proof-carrying 项边界。 -/
theorem function_application_term_admissible (function argument : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hArgument : Term.Admissible argument SetSort.set) :
    Term.Admissible (function ·ₘ argument)
      SetSort.set := by
  simpa using
    set_function_application_admissible
      .application [⟨function, by assumption⟩, ⟨argument, by assumption⟩]
      (by rfl) (by rfl)
/-- 函数求值项的合法性由函数项与参数项证书计算。 -/
@[term_check] theorem function_application_term_check {function argument : SetTerm}
    (hFunction : Term.CheckCertificate function SetSort.set) (hArgument : Term.CheckCertificate argument SetSort.set) :
    Term.CheckCertificate (function ·ₘ argument) SetSort.set :=
  Term.check_admissible_complete <| function_application_term_admissible function argument hFunction.admissible hArgument.admissible
/-- 等价关系谓词原子保持公式 admissibility。 -/
theorem is_equivalence_relation_formula_admissible
    {relation : SetTerm} (hRelation : Term.Admissible
      relation SetSort.set) :
    Formula.Admissible (is_equivalence_relation_formula relation) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hRelation
      ArgsAdmissible.nil)
/-- 函数谓词原子保持公式 admissibility。 -/
theorem is_function_formula_admissible
    {function : SetTerm} (hFunction : Term.Admissible
      function SetSort.set) :
    Formula.Admissible (is_function_formula function) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hFunction
      ArgsAdmissible.nil)
/-- 函数谓词原子的合法性由函数项证书计算。 -/
@[formula_check] theorem is_function_formula_check {function : SetTerm}
    (hFunction : Term.CheckCertificate function SetSort.set) :
    Formula.CheckCertificate (is_function_formula function) :=
  Formula.check_admissible_complete <| is_function_formula_admissible hFunction.admissible
/-- 映射谓词原子保持公式 admissibility。 -/
theorem is_mapping_formula_admissible
    {function source target : SetTerm} (hFunction : Term.Admissible
      function SetSort.set) (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set) :
    Formula.Admissible (is_mapping_formula
        function source target) := by
  apply Formula.Admissible.rel
  simpa [signature] using (ArgsAdmissible.cons hFunction <|
      ArgsAdmissible.cons hSource <|
        ArgsAdmissible.cons hTarget
          ArgsAdmissible.nil)
/-- 映射谓词原子的合法性由三个参数项证书计算。 -/
@[formula_check] theorem is_mapping_formula_check {function source target : SetTerm}
    (hFunction : Term.CheckCertificate function SetSort.set) (hSource : Term.CheckCertificate source SetSort.set)
    (hTarget : Term.CheckCertificate target SetSort.set) : Formula.CheckCertificate (is_mapping_formula function source target) :=
  Formula.check_admissible_complete <| is_mapping_formula_admissible hFunction.admissible hSource.admissible hTarget.admissible
/-- 函数图成员的规范坐标条件保持公式 admissibility。 -/
theorem function_graph_member_condition_admissible
    {function member : SetTerm} (hFunction : Term.Admissible
      function SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    Formula.Admissible (function_graph_member_condition
        function member) := by
  have hLeft :
      Term.Admissible (member)₀ₘ
        SetSort.set :=
    left_projection_term_admissible
      member hMember
  have hRight :
      Term.Admissible (member)₁ₘ
        SetSort.set :=
    right_projection_term_admissible
      member hMember
  exact Formula.Admissible.conj (is_ordered_pair_formula_admissible
      hMember) (Formula.Admissible.conj (membership_formula_admissible
        hLeft (domain_term_admissible
          function hFunction)) (Formula.Admissible.equal
        hRight (function_application_term_admissible
          function (member)₀ₘ
          hFunction hLeft)))
/-- 函数图成员条件的合法性由函数项与成员项证书计算。 -/
@[formula_check] theorem function_graph_member_condition_check {function member : SetTerm}
    (hFunction : Term.CheckCertificate function SetSort.set) (hMember : Term.CheckCertificate member SetSort.set) :
    Formula.CheckCertificate (function_graph_member_condition function member) :=
  Formula.check_admissible_complete <| function_graph_member_condition_admissible hFunction.admissible hMember.admissible
/-- 函数外延协议保持公式 admissibility。 -/
theorem function_extensional_agreement_admissible
    {left right : SetTerm} (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    Formula.Admissible (function_extensional_agreement
        left right) := by
  prove_admissible
/-- 函数外延协议的合法性由两个函数项证书计算。 -/
@[formula_check] theorem function_extensional_agreement_check {left right : SetTerm}
    (hLeft : Term.CheckCertificate left SetSort.set) (hRight : Term.CheckCertificate right SetSort.set) :
    Formula.CheckCertificate (function_extensional_agreement left right) :=
  Formula.check_admissible_complete <| function_extensional_agreement_admissible hLeft.admissible hRight.admissible
/-- 求值函数符号的开放图合同保持公式 admissibility。 -/
theorem function_application_definition_instance_admissible
    {function argument value : SetTerm} (hFunction : Term.Admissible
      function SetSort.set) (hArgument : Term.Admissible
      argument SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    Formula.Admissible (function_application_definition_instance
        function argument value) :=
  Formula.Admissible.imp (Formula.Admissible.conj (is_function_formula_admissible hFunction) (membership_formula_admissible
        hArgument (domain_term_admissible
          function hFunction))) (Formula.Admissible.iff (Formula.Admissible.equal
        hValue (function_application_term_admissible
          function argument hFunction hArgument)) (membership_formula_admissible (ordered_pair_term_admissible
          argument value hArgument hValue)
        hFunction))
theorem is_equivalence_relation_definition_axiom_admissible :
    Formula.Admissible
      is_equivalence_relation_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_function_definition_axiom_admissible :
    Formula.Admissible
      is_function_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem is_mapping_definition_axiom_admissible :
    Formula.Admissible
      is_mapping_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem function_application_definition_axiom_admissible :
    Formula.Admissible
      function_application_definition_axiom := by
  apply Formula.check_admissible_sound
  native_decide
theorem equivalence_relation_theory_admissible :
    Theory.Admissible equivalence_relation_theory :=
  Theory.admissible_insert
    is_equivalence_relation_definition_axiom_admissible
    relation_composition_operator_theory_admissible
theorem function_predicate_theory_admissible :
    Theory.Admissible function_predicate_theory :=
  Theory.admissible_insert
    is_function_definition_axiom_admissible
    equivalence_relation_theory_admissible
theorem mapping_predicate_theory_admissible :
    Theory.Admissible mapping_predicate_theory :=
  Theory.admissible_insert
    is_mapping_definition_axiom_admissible
    function_predicate_theory_admissible
theorem function_application_theory_admissible :
    Theory.Admissible function_application_theory :=
  Theory.admissible_insert
    function_application_definition_axiom_admissible
    mapping_predicate_theory_admissible
/-! ## 闭理论边界 -/
@[derive_close_sentence]
theorem equivalence_relation_theory_sentence
    {formula : SetFormula} (hFormula : equivalence_relation_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_equivalence_relation_definition_axiom_admissible
    · native_decide
  · exact relation_composition_operator_theory_sentence
      hFormula
@[derive_close_sentence]
theorem function_predicate_theory_sentence
    {formula : SetFormula} (hFormula : function_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_function_definition_axiom_admissible
    · native_decide
  · exact equivalence_relation_theory_sentence hFormula
@[derive_close_sentence]
theorem mapping_predicate_theory_sentence
    {formula : SetFormula} (hFormula : mapping_predicate_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact is_mapping_definition_axiom_admissible
    · native_decide
  · exact function_predicate_theory_sentence hFormula
@[derive_close_sentence]
theorem function_application_theory_sentence
    {formula : SetFormula} (hFormula : function_application_theory formula) :
    Formula.Sentence formula := by
  rcases hFormula with rfl | hFormula
  · constructor
    · exact function_application_definition_axiom_admissible
    · native_decide
  · exact mapping_predicate_theory_sentence hFormula
/-! ## 理论嵌入 -/
theorem relation_composition_operator_theory_subset_equivalence_relation_theory
    {formula : SetFormula} (hFormula : relation_composition_operator_theory formula) :
    equivalence_relation_theory formula :=
  Or.inr hFormula
theorem equivalence_relation_theory_subset_function_predicate_theory
    {formula : SetFormula} (hFormula : equivalence_relation_theory formula) :
    function_predicate_theory formula :=
  Or.inr hFormula
theorem function_predicate_theory_subset_mapping_predicate_theory
    {formula : SetFormula} (hFormula : function_predicate_theory formula) :
    mapping_predicate_theory formula :=
  Or.inr hFormula
theorem mapping_predicate_theory_subset_function_application_theory
    {formula : SetFormula} (hFormula : mapping_predicate_theory formula) :
    function_application_theory formula :=
  Or.inr hFormula
theorem relation_composition_operator_theory_subset_function_application_theory
    {formula : SetFormula} (hFormula : relation_composition_operator_theory formula) :
    function_application_theory formula :=
  mapping_predicate_theory_subset_function_application_theory (function_predicate_theory_subset_mapping_predicate_theory
      (equivalence_relation_theory_subset_function_predicate_theory (relation_composition_operator_theory_subset_equivalence_relation_theory
          hFormula)))
/-! ## 定义公理实例化 -/
/-- 等价关系谓词定义公理可在任意 admissible 集合项处实例化。 -/
theorem is_equivalence_relation_definition_instance_derives (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[equivalence_relation_theory]
      is_equivalence_relation_definition_instance
        relation := by
  have hAxiom :
      ⊢ₘ[equivalence_relation_theory]
        is_equivalence_relation_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim (term := relation) hAxiom
  have hOpenZero :
      Term.openAt SetSort.set 0 relation relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 relation relation hRelation.2
  have hOpenOne :
      Term.openAt SetSort.set 1 relation relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 relation relation hRelation.2
  have hOpenTwo :
      Term.openAt SetSort.set 2 relation relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 relation relation hRelation.2
  have hOpenThree :
      Term.openAt SetSort.set 3 relation relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 3 relation relation hRelation.2
  simpa [is_equivalence_relation_definition_axiom,
    is_equivalence_relation_definition_instance,
    is_equivalence_relation_condition,
    relation_reflexive_on_domain_condition,
    relation_symmetric_on_domain_condition,
    relation_transitive_on_domain_condition,
    set_has_member,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, domain_term, range_term,
    ordered_pair_term,
    hOpenZero, hOpenOne, hOpenTwo,
    hOpenThree] using hInstance
/-- 函数谓词定义公理可在任意 admissible 集合项处实例化。 -/
theorem is_function_definition_instance_derives (function : SetTerm) (hFunction : Term.Admissible function SetSort.set) :
    ⊢ₘ[function_predicate_theory]
      is_function_definition_instance function := by
  have hAxiom :
      ⊢ₘ[function_predicate_theory]
        is_function_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hInstance :=
    FirstOrder.Derives.forall_elim (term := function) hAxiom
  have hOpenZero :
      Term.openAt SetSort.set 0 function function =
        function :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 function function hFunction.2
  have hOpenOne :
      Term.openAt SetSort.set 1 function function =
        function :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 function function hFunction.2
  have hOpenTwo :
      Term.openAt SetSort.set 2 function function =
        function :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 function function hFunction.2
  simpa [is_function_definition_axiom,
    is_function_definition_instance,
    is_function_condition,
    function_single_valued_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, ordered_pair_term,
    hOpenZero, hOpenOne, hOpenTwo] using
    hInstance
/-- 映射谓词定义公理可在任意 admissible 集合项处实例化。 -/
theorem is_mapping_definition_instance_derives (function source target : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set) :
    ⊢ₘ[mapping_predicate_theory]
      is_mapping_definition_instance
        function source target := by
  have hAxiom :
      ⊢ₘ[mapping_predicate_theory]
        is_mapping_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hFunctionInstance :=
    FirstOrder.Derives.forall_elim (term := function) hAxiom
  have hSourceInstance :=
    FirstOrder.Derives.forall_elim (term := source) hFunctionInstance
  have hTargetInstance :=
    FirstOrder.Derives.forall_elim (term := target) hSourceInstance
  have hFunctionOpenZero :
      Term.openAt SetSort.set 0 target function =
        function :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 target function hFunction.2
  have hFunctionOpenOneSource :
      Term.openAt SetSort.set 1 source function =
        function :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 source function hFunction.2
  have hFunctionOpenOne :
      Term.openAt SetSort.set 1 target function =
        function :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 target function hFunction.2
  have hSourceOpenZero :
      Term.openAt SetSort.set 0 target source =
        source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 target source hSource.2
  simpa [is_mapping_definition_axiom,
    is_mapping_definition_instance,
    is_mapping_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, domain_term, range_term,
    hFunctionOpenZero, hFunctionOpenOne,
    hFunctionOpenOneSource,
    hSourceOpenZero] using hTargetInstance
/-- 求值定义公理可在任意三个 admissible 集合项处实例化。 -/
theorem function_application_definition_instance_derives (function argument value : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hArgument : Term.Admissible argument SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    ⊢ₘ[function_application_theory]
      function_application_definition_instance
        function argument value := by
  have hAxiom :
      ⊢ₘ[function_application_theory]
        function_application_definition_axiom :=
    FirstOrder.Derives.theory_mem (by
      exact Or.inl rfl)
  have hFunctionInstance :=
    FirstOrder.Derives.forall_elim (term := function) hAxiom
  have hArgumentInstance :=
    FirstOrder.Derives.forall_elim (term := argument) hFunctionInstance
  have hValueInstance :=
    FirstOrder.Derives.forall_elim (term := value) hArgumentInstance
  have hFunctionOpenZero :
      Term.openAt SetSort.set 0 value function =
        function :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 value function hFunction.2
  have hFunctionOpenOneArgument :
      Term.openAt SetSort.set 1 argument function =
        function :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 argument function hFunction.2
  have hFunctionOpenOne :
      Term.openAt SetSort.set 1 value function =
        function :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 value function hFunction.2
  have hArgumentOpenZero :
      Term.openAt SetSort.set 0 value argument =
        argument :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 value argument hArgument.2
  simpa [function_application_definition_axiom,
    function_application_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, domain_term,
    function_application_term, ordered_pair_term,
    hFunctionOpenZero, hFunctionOpenOne,
    hFunctionOpenOneArgument,
    hArgumentOpenZero] using hValueInstance
/-! ## 公开定义合同 -/
theorem is_equivalence_relation_iff_condition (relation : SetTerm) (hRelation : Term.Admissible relation SetSort.set) :
    ⊢ₘ[equivalence_relation_theory]
      is_equivalence_relation_formula relation ↔ₘ
        is_equivalence_relation_condition relation :=
  is_equivalence_relation_definition_instance_derives
    relation hRelation
theorem is_function_iff_condition (function : SetTerm) (hFunction : Term.Admissible function SetSort.set) :
    ⊢ₘ[function_predicate_theory]
      is_function_formula function ↔ₘ
        is_function_condition function :=
  is_function_definition_instance_derives
    function hFunction
theorem is_mapping_iff_condition (function source target : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set) :
    ⊢ₘ[mapping_predicate_theory]
      is_mapping_formula function source target ↔ₘ
        is_mapping_condition function source target :=
  is_mapping_definition_instance_derives
    function source target
    hFunction hSource hTarget
/-- 映射谓词蕴含其现代定义条件。 -/
theorem is_mapping_implies_condition (function source target : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set) :
    ⊢ₘ[mapping_predicate_theory]
      is_mapping_formula function source target ⟶ₘ
        is_mapping_condition
          function source target := by
  nd_apply FirstOrder.Derives.impIntro
  let predicate :=
    is_mapping_formula function source target
  have hDefinition :
      [predicate] ⊢ₘ[mapping_predicate_theory]
        is_mapping_formula function source target ↔ₘ
          is_mapping_condition
            function source target :=
    FirstOrder.Derives.context_weaken_cons (assumption := predicate) (is_mapping_iff_condition
        function source target
        hFunction hSource hTarget)
  exact FirstOrder.Derives.iffElimRight
    hDefinition (show [predicate] ⊢ₘ[mapping_predicate_theory]
        predicate from
      .assumption (by simp))
theorem function_application_eq_iff_graph (function argument value : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hArgument : Term.Admissible argument SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    ⊢ₘ[function_application_theory] (is_function_formula function ∧ₘ (argument ∈ₘ domₘ(function))) ⟶ₘ ((value ≐ₘ (function ·ₘ argument)) ↔ₘ
          (⟨argument, value⟩ₘ ∈ₘ function)) :=
  function_application_definition_instance_derives
    function argument value
    hFunction hArgument hValue
/-! ## 函数项合同 -/
/-- 已证明的集合等式可提升为定义域函数项等式。 -/
theorem domain_term_congr_of_equality
    {T : SetTheory} {Γ : Context signature} (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] domₘ(left) ≐ₘ domₘ(right) := by
  exact Metatheory.Derives.unary_term_constructor_congr_of_equality
    domain_term
    domain_term_admissible
    (by intros; simp [Term.substituteFree])
    left right hLeft hRight hEquality
/-- 两组参数等式可同时提升为函数求值项等式。 -/
theorem function_application_term_congr_of_equalities
    {T : SetTheory} {Γ : Context signature}
    (function₁ function₂ argument₁ argument₂ : SetTerm)
    (hFunction₁ : Term.Admissible function₁ SetSort.set)
    (hFunction₂ : Term.Admissible function₂ SetSort.set)
    (hArgument₁ : Term.Admissible argument₁ SetSort.set)
    (hArgument₂ : Term.Admissible argument₂ SetSort.set)
    (hFunctionEquality : Γ ⊢ₘ[T] function₁ ≐ₘ function₂)
    (hArgumentEquality : Γ ⊢ₘ[T] argument₁ ≐ₘ argument₂) :
    Γ ⊢ₘ[T]
      (function₁ ·ₘ argument₁) ≐ₘ
        (function₂ ·ₘ argument₂) := by
  exact Metatheory.Derives.binary_term_constructor_congr_of_equalities
    function_application_term
    function_application_term_admissible
    (by intros; simp [Term.substituteFree])
    function₁ function₂ argument₁ argument₂
    hFunction₁ hFunction₂ hArgument₁ hArgument₂
    hFunctionEquality hArgumentEquality
/-- 已证明的函数项等式可在固定参数处提升为求值项等式。 -/
theorem function_application_term_congr_function_of_equality
    {T : SetTheory} {Γ : Context signature} (left right argument : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hArgument : Term.Admissible argument SetSort.set) (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (left ·ₘ argument) ≐ₘ (right ·ₘ argument) := by
  exact function_application_term_congr_of_equalities
    left right argument argument
    hLeft hRight hArgument hArgument
    hEquality
    (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) argument)
/-- 已证明的参数等式可在固定函数处提升为求值项等式。 -/
theorem function_application_term_congr_argument_of_equality
    {T : SetTheory} {Γ : Context signature} (function left right : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] (function ·ₘ left) ≐ₘ (function ·ₘ right) := by
  exact function_application_term_congr_of_equalities
    function function left right
    hFunction hFunction hLeft hRight
    (FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) function)
    hEquality
/-! ## 函数图的基础合同 -/
theorem relation_composition_operator_theory_subset_function_predicate_theory
    {formula : SetFormula} (hFormula : relation_composition_operator_theory formula) :
    function_predicate_theory formula :=
  Or.inr (Or.inr hFormula)
theorem relation_plane_theory_subset_function_predicate_theory
    {formula : SetFormula} (hFormula : relation_plane_theory formula) :
    function_predicate_theory formula :=
  relation_composition_operator_theory_subset_function_predicate_theory (relation_plane_theory_subset_relation_composition_operator_theory
      hFormula)
theorem relation_domain_operator_theory_subset_function_predicate_theory
    {formula : SetFormula} (hFormula : relation_domain_operator_theory formula) :
    function_predicate_theory formula :=
  relation_plane_theory_subset_function_predicate_theory (relation_range_operator_theory_subset_relation_plane_theory
      (relation_range_theory_subset_relation_range_operator_theory (relation_domain_operator_theory_subset_relation_range_theory
          hFormula)))
/-- 函数谓词理论嵌入函数求值理论。 -/
theorem function_predicate_theory_subset_function_application_theory
    {formula : SetFormula} (hFormula : function_predicate_theory formula) :
    function_application_theory formula :=
  mapping_predicate_theory_subset_function_application_theory (function_predicate_theory_subset_mapping_predicate_theory
      hFormula)
/-- 关系平面理论嵌入函数求值理论。 -/
theorem relation_plane_theory_subset_function_application_theory
    {formula : SetFormula} (hFormula : relation_plane_theory formula) :
    function_application_theory formula :=
  relation_composition_operator_theory_subset_function_application_theory (relation_plane_theory_subset_relation_composition_operator_theory
      hFormula)
/-- 定义域算子理论嵌入函数求值理论。 -/
theorem relation_domain_operator_theory_subset_function_application_theory
    {formula : SetFormula} (hFormula : relation_domain_operator_theory formula) :
    function_application_theory formula :=
  function_predicate_theory_subset_function_application_theory (relation_domain_operator_theory_subset_function_predicate_theory
      hFormula)
/-- 外延理论嵌入函数求值理论。 -/
theorem extensionality_theory_subset_function_application_theory
    {formula : SetFormula} (hFormula : extensionality_theory formula) :
    function_application_theory formula :=
  relation_plane_theory_subset_function_application_theory (relation_predicate_theory_subset_relation_plane_theory
      (relation_base_theory_subset_relation_predicate_theory (extensionality_theory_subset_relation_base_theory
          hFormula)))
/-- 左投影算子理论嵌入函数谓词理论。 -/
theorem left_projection_operator_theory_subset_function_predicate_theory
    {formula : SetFormula} (hFormula : left_projection_operator_theory formula) :
    function_predicate_theory formula :=
  relation_plane_theory_subset_function_predicate_theory (ordered_pair_reverse_operator_theory_subset_relation_plane_theory
      (right_projection_operator_theory_subset_ordered_pair_reverse_operator_theory (left_projection_operator_theory_subset_right_projection_operator_theory
          hFormula)))
/-- 左投影算子理论嵌入函数求值理论。 -/
theorem left_projection_operator_theory_subset_function_application_theory
    {formula : SetFormula} (hFormula : left_projection_operator_theory formula) :
    function_application_theory formula :=
  function_predicate_theory_subset_function_application_theory (left_projection_operator_theory_subset_function_predicate_theory
      hFormula)
/-- 函数谓词蕴含关系谓词。 -/
theorem is_function_implies_is_relation (function : SetTerm) (hFunction : Term.Admissible function SetSort.set) :
    ⊢ₘ[function_predicate_theory]
      is_function_formula function ⟶ₘ
        is_relation_formula function := by
  nd_apply FirstOrder.Derives.impIntro
  have hDefinition :=
    FirstOrder.Derives.context_weaken_cons (assumption := is_function_formula function) (is_function_definition_instance_derives
        function hFunction)
  have hFunctionAssumption :
      [is_function_formula function] ⊢ₘ[function_predicate_theory]
        is_function_formula function :=
    .assumption (by simp)
  have hCondition :
      [is_function_formula function] ⊢ₘ[function_predicate_theory]
        is_function_condition function := by
    exact FirstOrder.Derives.iffElimRight
      hDefinition
      hFunctionAssumption
  exact FirstOrder.Derives.conjElimLeft hCondition
/-- 函数图在同一输入处至多有一个输出。 -/
theorem is_function_single_valued (function input left right : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hInput : Term.Admissible input SetSort.set) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[function_predicate_theory]
      is_function_formula function ⟶ₘ (⟨input, left⟩ₘ ∈ₘ function) ⟶ₘ (⟨input, right⟩ₘ ∈ₘ function) ⟶ₘ (left ≐ₘ right) := by
  have hLeftPair :
      Term.Admissible (⟨input, left⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible
      input left hInput hLeft
  have hRightPair :
      Term.Admissible (⟨input, right⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible
      input right hInput hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [⟨input, right⟩ₘ ∈ₘ function,
      ⟨input, left⟩ₘ ∈ₘ function,
      is_function_formula function]
  have hDefinition :=
    FirstOrder.Derives.context_weaken_cons (assumption := ⟨input, right⟩ₘ ∈ₘ function) <|
      FirstOrder.Derives.context_weaken_cons (assumption := ⟨input, left⟩ₘ ∈ₘ function) <|
        FirstOrder.Derives.context_weaken_cons (assumption := is_function_formula function) <|
          is_function_definition_instance_derives
            function hFunction
  have hFunctionAssumption :
      Γ ⊢ₘ[function_predicate_theory]
        is_function_formula function := by
    exact .assumption (by simp [Γ])
  have hCondition :
      Γ ⊢ₘ[function_predicate_theory]
        is_function_condition function := by
    exact FirstOrder.Derives.iffElimRight
      hDefinition
      hFunctionAssumption
  have hSingle :
      Γ ⊢ₘ[function_predicate_theory]
        function_single_valued_condition function :=
    FirstOrder.Derives.conjElimRight hCondition
  have hAtInput :=
    FirstOrder.Derives.forall_elim (term := input) hSingle
  have hAtLeft :=
    FirstOrder.Derives.forall_elim (term := left) hAtInput
  have hAtRight :=
    FirstOrder.Derives.forall_elim (term := right) hAtLeft
  have hFunctionOpenThree :
      Term.openAt SetSort.set 0
          right (Term.openAt SetSort.set 1
            left (Term.openAt SetSort.set 2
              input function)) =
        function := by
    rw [Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 input function hFunction.2]
    rw [Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 left function hFunction.2]
    exact Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right function hFunction.2
  have hInputOpenOne :
      Term.openAt SetSort.set 1 left input =
        input :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 left input hInput.2
  have hInputOpenZero :
      Term.openAt SetSort.set 0 right input =
        input :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right input hInput.2
  have hLeftOpenZero :
      Term.openAt SetSort.set 0 right left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right left hLeft.2
  have hRightOpenZero :
      Term.openAt SetSort.set 0 right right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 right right hRight.2
  have hAtRight' :
      Γ ⊢ₘ[function_predicate_theory] (⟨input, left⟩ₘ ∈ₘ function ∧ₘ (⟨input, right⟩ₘ ∈ₘ function)) ⟶ₘ (left ≐ₘ right) := by
    simpa [function_single_valued_condition,
      Formula.openAt, Formula.next_depth, Term.openAt,
      ordered_pair_term, hFunctionOpenThree,
      hInputOpenOne, hInputOpenZero,
      hLeftOpenZero, hRightOpenZero] using
      hAtRight
  exact FirstOrder.Derives.impElim
    hAtRight' (FirstOrder.Derives.conjIntro
      (.assumption (by simp)) (.assumption (by simp)))
/-- 关系图中的有序对，其第一坐标属于关系定义域。 -/
theorem relation_member_left_coordinate_mem_domain (relation input value : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hInput : Term.Admissible input SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    ⊢ₘ[function_predicate_theory]
      is_relation_formula relation ⟶ₘ (⟨input, value⟩ₘ ∈ₘ relation) ⟶ₘ (input ∈ₘ domₘ(relation)) := by
  have hPair :
      Term.Admissible (⟨input, value⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible
      input value hInput hValue
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let pair := ⟨input, value⟩ₘ
  let relation_formula := is_relation_formula relation
  let membership := pair ∈ₘ relation
  let Γ : Context signature :=
    [membership, relation_formula]
  have hRelationOpen :
      Term.openAt SetSort.set 0 pair relation =
        relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 pair relation hRelation.2
  have hInputOpen :
      Term.openAt SetSort.set 0 pair input =
        input :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 pair input hInput.2
  have hRelationFormula :
      Γ ⊢ₘ[function_predicate_theory]
        is_relation_formula relation := by
    simpa [Γ, relation_formula] using (show Γ ⊢ₘ[function_predicate_theory]
        relation_formula from
        .assumption (by simp [Γ]))
  have hMembership :
      Γ ⊢ₘ[function_predicate_theory]
        pair ∈ₘ relation := by
    simpa [Γ, membership] using (show Γ ⊢ₘ[function_predicate_theory]
        membership from
        .assumption (by simp [Γ]))
  have hDomainIff :
      Γ ⊢ₘ[function_predicate_theory] (input ∈ₘ domₘ(relation)) ↔ₘ ((input ∈ₘ double_union_term relation) ∧ₘ
            relation_domain_member_condition
              relation input) := by
    have hIff :=
      is_relation_domain_member_iff
        relation input hRelation hInput
    have hIff' :=
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          relation_domain_operator_theory_subset_function_predicate_theory
            hFormula)
        hIff
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons
          hIff'))
      hRelationFormula
  have hCoordinates :
      Γ ⊢ₘ[function_predicate_theory]
        input ∈ₘ double_union_term relation := by
    have hCoordinateIff :=
      ordered_pair_coordinates_mem_double_union
        relation pair input value
        hRelation hPair hInput hValue
    have hCoordinateIff' :=
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          relation_plane_theory_subset_function_predicate_theory
            hFormula)
        hCoordinateIff
    have hRepresentation :
        Γ ⊢ₘ[function_predicate_theory]
          pair ≐ₘ ⟨input, value⟩ₘ :=
      FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) pair))
    have hCoordinates' :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons
              hCoordinateIff'))
          hMembership)
        hRepresentation
    exact FirstOrder.Derives.conjElimLeft hCoordinates'
  have hDomainCondition :
      Γ ⊢ₘ[function_predicate_theory]
        relation_domain_member_condition
          relation input := by
    have hConditionAdmissible :
        Formula.Admissible (relation_domain_member_condition
            relation input) :=
      relation_coordinate_member_condition_admissible
        hRelation hInput
    unfold relation_domain_member_condition
      relation_coordinate_member_condition
    nd_apply FirstOrder.Derives.exists_intro (term := pair)
    apply FirstOrder.Derives.conjIntro
    · simpa [pair, Formula.openAt, Term.openAt,
        hRelationOpen] using hMembership
    · have hProjection :=
        FirstOrder.Derives.context_weaken_cons (assumption := membership) <|
          FirstOrder.Derives.context_weaken_cons (assumption := relation_formula) <|
            FirstOrder.Derives.theory_weaken (fun _ hFormula =>
                left_projection_operator_theory_subset_function_predicate_theory
                  hFormula) (ordered_pair_term_left_projection_eq
                input value hInput hValue)
      have hProjectionSymm :=
        FirstOrder.Metatheory.Derives.equality_symm
          hProjection
      simpa [Formula.openAt, Term.openAt,
        pair, relation_coordinate_projection_term,
        hRelationOpen, hInputOpen] using hProjectionSymm
  have hResult :
      Γ ⊢ₘ[function_predicate_theory]
        input ∈ₘ domₘ(relation) :=
    FirstOrder.Derives.iffElimLeft
      hDomainIff (FirstOrder.Derives.conjIntro
        hCoordinates hDomainCondition)
  exact hResult
/--
关系图中的有序对，其第二坐标属于关系值域。
这是定义域坐标定理的严格对偶；后续映射求值的目标集闭性统一经该合同取得，
不再在有限序列与证明码层重复展开值域分离定义。
-/
theorem relation_member_right_coordinate_mem_range (relation input value : SetTerm) (hRelation : Term.Admissible relation SetSort.set)
    (hInput : Term.Admissible input SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    ⊢ₘ[function_predicate_theory]
      is_relation_formula relation ⟶ₘ (⟨input, value⟩ₘ ∈ₘ relation) ⟶ₘ (value ∈ₘ ranₘ(relation)) := by
  have hPair :
      Term.Admissible (⟨input, value⟩ₘ) SetSort.set :=
    ordered_pair_term_admissible
      input value hInput hValue
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let pair := ⟨input, value⟩ₘ
  let relationFormula := is_relation_formula relation
  let membership := pair ∈ₘ relation
  let Γ : Context signature := [membership, relationFormula]
  have hRelationOpen :
      Term.openAt SetSort.set 0 pair relation = relation :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 pair relation hRelation.2
  have hValueOpen :
      Term.openAt SetSort.set 0 pair value = value :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 pair value hValue.2
  have hRelationFormula :
      Γ ⊢ₘ[function_predicate_theory]
        is_relation_formula relation := by
    simpa [Γ, relationFormula] using (show Γ ⊢ₘ[function_predicate_theory]
          relationFormula from
        .assumption (by simp [Γ]))
  have hMembership :
      Γ ⊢ₘ[function_predicate_theory]
        pair ∈ₘ relation := by
    simpa [Γ, membership] using (show Γ ⊢ₘ[function_predicate_theory]
          membership from
        .assumption (by simp [Γ]))
  have hRangeIff :
      Γ ⊢ₘ[function_predicate_theory] (value ∈ₘ ranₘ(relation)) ↔ₘ ((value ∈ₘ double_union_term relation) ∧ₘ
            relation_range_member_condition
              relation value) := by
    have hIff :=
      is_relation_range_member_iff
        relation value hRelation hValue
    have hIff' :=
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          relation_plane_theory_subset_function_predicate_theory (relation_range_operator_theory_subset_relation_plane_theory
              hFormula))
        hIff
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons hIff'))
      hRelationFormula
  have hCoordinates :
      Γ ⊢ₘ[function_predicate_theory]
        value ∈ₘ double_union_term relation := by
    have hCoordinateIff :=
      ordered_pair_coordinates_mem_double_union
        relation pair input value
        hRelation hPair hInput hValue
    have hCoordinateIff' :=
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          relation_plane_theory_subset_function_predicate_theory
            hFormula)
        hCoordinateIff
    have hRepresentation :
        Γ ⊢ₘ[function_predicate_theory]
          pair ≐ₘ ⟨input, value⟩ₘ :=
      FirstOrder.Derives.context_weaken_cons
        (FirstOrder.Derives.context_weaken_cons
          (FirstOrder.Derives.eq_refl_m
            (sort := SetSort.set) pair))
    have hCoordinates' :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (FirstOrder.Derives.context_weaken_cons
              hCoordinateIff'))
          hMembership)
        hRepresentation
    exact FirstOrder.Derives.conjElimRight hCoordinates'
  have hRangeCondition :
      Γ ⊢ₘ[function_predicate_theory]
        relation_range_member_condition
          relation value := by
    have hConditionAdmissible :
        Formula.Admissible (relation_range_member_condition
            relation value) :=
      relation_coordinate_member_condition_admissible
        hRelation hValue
    unfold relation_range_member_condition
      relation_coordinate_member_condition
    nd_apply FirstOrder.Derives.exists_intro (term := pair)
    apply FirstOrder.Derives.conjIntro
    · simpa [pair, Formula.openAt, Term.openAt,
        hRelationOpen] using hMembership
    · have hProjection :=
        FirstOrder.Derives.context_weaken_cons (assumption := membership) <|
          FirstOrder.Derives.context_weaken_cons (assumption := relationFormula) <|
            FirstOrder.Derives.theory_weaken (fun _ hFormula =>
                relation_plane_theory_subset_function_predicate_theory (ordered_pair_reverse_operator_theory_subset_relation_plane_theory
                    (right_projection_operator_theory_subset_ordered_pair_reverse_operator_theory
                      hFormula))) (ordered_pair_term_right_projection_eq
                input value hInput hValue)
      have hProjectionSymm :=
        FirstOrder.Metatheory.Derives.equality_symm
          hProjection
      simpa [Formula.openAt, Term.openAt,
        pair, relation_coordinate_projection_term,
        hRelationOpen, hValueOpen] using hProjectionSymm
  exact FirstOrder.Derives.iffElimLeft
    hRangeIff (FirstOrder.Derives.conjIntro
      hCoordinates hRangeCondition)
/-! ## 求值图合同 -/
/-- 函数及定义域 guard 下，规范求值有序对属于函数图。 -/
theorem function_application_graph_mem (function argument : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hArgument : Term.Admissible argument SetSort.set) :
    ⊢ₘ[function_application_theory] (is_function_formula function ∧ₘ (argument ∈ₘ domₘ(function))) ⟶ₘ (⟨argument, function ·ₘ argument⟩ₘ ∈ₘ function) := by
  have hContract :=
    function_application_eq_iff_graph
      function argument (function ·ₘ argument)
      hFunction hArgument (function_application_term_admissible
        function argument hFunction hArgument)
  have hReflexive :
      ⊢ₘ[function_application_theory] (function ·ₘ argument) ≐ₘ (function ·ₘ argument) :=
    FirstOrder.Derives.eq_refl_m
      (sort := SetSort.set) (function ·ₘ argument)
  derive_prop
/--
映射在源集内的规范求值属于目标集。
该合同完整消费映射定义中的三个组成部分：函数性、定义域等于源集、值域包含于
目标集。有限序列空间与后续证明轨迹只需使用这一公开接口，无需自行展开函数图、
值域分离和子集定义。
-/
theorem is_mapping_application_mem_target (function source target argument : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set) (hArgument : Term.Admissible argument SetSort.set) :
    ⊢ₘ[function_application_theory]
      is_mapping_formula function source target ⟶ₘ (argument ∈ₘ source) ⟶ₘ ((function ·ₘ argument) ∈ₘ target) := by
  let mappingFormula : SetFormula :=
    is_mapping_formula function source target
  let sourceMembership : SetFormula :=
    argument ∈ₘ source
  let value : SetTerm := function ·ₘ argument
  let Γ : Context signature :=
    [sourceMembership, mappingFormula]
  have hMappingAdmissible :
      Formula.Admissible mappingFormula := by
    simpa [mappingFormula] using
      is_mapping_formula_admissible
        hFunction hSource hTarget
  have hSourceMembershipAdmissible :
      Formula.Admissible sourceMembership := by
    simpa [sourceMembership] using
      membership_formula_admissible hArgument hSource
  have hValue :
      Term.Admissible value SetSort.set := by
    simpa [value] using
      function_application_term_admissible
        function argument hFunction hArgument
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hMapping :
      Γ ⊢ₘ[function_application_theory]
        is_mapping_formula function source target := by
    simpa [Γ, mappingFormula] using (show Γ ⊢ₘ[function_application_theory]
          mappingFormula from
        .assumption (by simp [Γ]))
  have hSourceMember :
      Γ ⊢ₘ[function_application_theory]
        argument ∈ₘ source := by
    simpa [Γ, sourceMembership] using (show Γ ⊢ₘ[function_application_theory]
          sourceMembership from
        .assumption (by simp [Γ]))
  have hMappingCondition :
      Γ ⊢ₘ[function_application_theory]
        is_mapping_condition function source target :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            mapping_predicate_theory_subset_function_application_theory
              hFormula) (is_mapping_implies_condition
            function source target
            hFunction hSource hTarget))
      hMapping
  have hFunctionFormula :
      Γ ⊢ₘ[function_application_theory]
        is_function_formula function :=
    FirstOrder.Derives.conjElimLeft hMappingCondition
  have hSourceEquality :
      Γ ⊢ₘ[function_application_theory]
        source ≐ₘ domₘ(function) :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hMappingCondition
  have hRangeSubset :
      Γ ⊢ₘ[function_application_theory]
        ranₘ(function) ⊆ₘ target :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight hMappingCondition
  have hDomainMembership :
      Γ ⊢ₘ[function_application_theory]
        argument ∈ₘ domₘ(function) :=
    FirstOrder.Derives.iffElimRight (membership_right_iff_of_equality
        argument source (domₘ(function))
        hArgument hSource (domain_term_admissible function hFunction)
        hSourceEquality)
      hSourceMember
  have hGraphMembership :
      Γ ⊢ₘ[function_application_theory]
        ⟨argument, value⟩ₘ ∈ₘ function := by
    have hGraph :=
      function_application_graph_mem
        function argument hFunction hArgument
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) (by simpa [value] using hGraph))
      (FirstOrder.Derives.conjIntro
        hFunctionFormula hDomainMembership)
  have hRelation :
      Γ ⊢ₘ[function_application_theory]
        is_relation_formula function :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            function_predicate_theory_subset_function_application_theory
              hFormula) (is_function_implies_is_relation
            function hFunction))
      hFunctionFormula
  have hRangeMembership :
      Γ ⊢ₘ[function_application_theory]
        value ∈ₘ ranₘ(function) := by
    have hRange :=
      relation_member_right_coordinate_mem_range
        function argument value
        hFunction hArgument hValue
    exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <|
          FirstOrder.Derives.theory_weaken (fun _ hFormula =>
              function_predicate_theory_subset_function_application_theory
                hFormula)
            hRange)
        hRelation)
      hGraphMembership
  have hSubsetDefinition :
      Γ ⊢ₘ[function_application_theory]
        subset_definition_instance (ranₘ(function)) target :=
    FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          relation_plane_theory_subset_function_application_theory (subset_theory_subset_relation_plane_theory
              hFormula)) (subset_definition_instance_derives_of_admissible (ranₘ(function)) target (range_term_admissible function hFunction)
          hTarget)
  have hSubsetCondition :
      Γ ⊢ₘ[function_application_theory]
        subset_condition (ranₘ(function)) target :=
    FirstOrder.Derives.iffElimRight
      hSubsetDefinition hRangeSubset
  have hAtRaw :=
    FirstOrder.Derives.forall_elim (term := value) hSubsetCondition
  have hRangeOpen :
      Term.openAt SetSort.set 0 value (ranₘ(function)) =
        ranₘ(function) :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 value (ranₘ(function)) (range_term_admissible function hFunction).2
  have hTargetOpen :
      Term.openAt SetSort.set 0 value target = target :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 value target hTarget.2
  have hAt :
      Γ ⊢ₘ[function_application_theory] (value ∈ₘ ranₘ(function)) ⟶ₘ (value ∈ₘ target) := by
    simpa [subset_condition, Formula.openAt,
      Term.openAt, hRangeOpen, hTargetOpen] using hAtRaw
  simpa [value] using (FirstOrder.Derives.impElim hAt hRangeMembership)
/-- 函数及定义域 guard 下，图成员的值等于规范求值项。 -/
theorem function_application_eq_of_graph (function argument value : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hArgument : Term.Admissible argument SetSort.set) (hValue : Term.Admissible value SetSort.set) :
    ⊢ₘ[function_application_theory] (is_function_formula function ∧ₘ (argument ∈ₘ domₘ(function))) ⟶ₘ (⟨argument, value⟩ₘ ∈ₘ function) ⟶ₘ
          (value ≐ₘ (function ·ₘ argument)) := by
  have hContract :=
    function_application_eq_iff_graph
      function argument value
      hFunction hArgument hValue
  derive_prop
/--
函数成员的规范坐标刻画。
这一定理是函数外延性与映射赋值规则的公共图合同，避免后续证明重复维护
“成员是有序对、第一坐标在定义域中、第二坐标等于函数值”三段推导。
-/
theorem is_function_member_iff_coordinates (function member : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[function_application_theory]
      is_function_formula function ⟶ₘ ((member ∈ₘ function) ↔ₘ
          function_graph_member_condition
            function member) := by
  let left_coordinate := (member)₀ₘ
  let right_coordinate := (member)₁ₘ
  let represented :=
    ⟨left_coordinate, right_coordinate⟩ₘ
  have hLeftCoordinate :
      Term.Admissible left_coordinate SetSort.set :=
    left_projection_term_admissible member hMember
  have hRightCoordinate :
      Term.Admissible right_coordinate SetSort.set :=
    right_projection_term_admissible member hMember
  have hRepresented :
      Term.Admissible represented SetSort.set :=
    ordered_pair_term_admissible
      left_coordinate right_coordinate
      hLeftCoordinate hRightCoordinate
  nd_apply FirstOrder.Derives.impIntro
  apply FirstOrder.Derives.iffIntro
  · let Γ : Context signature :=
      [member ∈ₘ function,
        is_function_formula function]
    have hFunctionFormula :
        Γ ⊢ₘ[function_application_theory]
          is_function_formula function :=
      .assumption (by simp [Γ])
    have hMembership :
        Γ ⊢ₘ[function_application_theory]
          member ∈ₘ function :=
      .assumption (by simp [Γ])
    have hRelation :
        Γ ⊢ₘ[function_application_theory]
          is_relation_formula function :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := member ∈ₘ function) <|
          FirstOrder.Derives.context_weaken_cons (assumption := is_function_formula function) <|
            FirstOrder.Derives.theory_weaken (fun _ hFormula =>
                function_predicate_theory_subset_function_application_theory
                  hFormula) (is_function_implies_is_relation
                function hFunction))
        hFunctionFormula
    have hOrdered :
        Γ ⊢ₘ[function_application_theory]
          is_ordered_pair_formula member :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := member ∈ₘ function) <|
            FirstOrder.Derives.context_weaken_cons (assumption := is_function_formula function) <|
              FirstOrder.Derives.theory_weaken (fun _ hFormula =>
                  relation_plane_theory_subset_function_application_theory (relation_predicate_theory_subset_relation_plane_theory
                      hFormula)) (is_relation_member_is_ordered_pair
                  function member hFunction hMember))
          hRelation)
        hMembership
    have hRepresentation :
        Γ ⊢ₘ[function_application_theory]
          member ≐ₘ represented := by
      simpa [represented, left_coordinate,
        right_coordinate] using (FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons
              (assumption := member ∈ₘ function) <|
              FirstOrder.Derives.context_weaken_cons (assumption := is_function_formula function) <|
                FirstOrder.Derives.theory_weaken (fun _ hFormula =>
                    relation_plane_theory_subset_function_application_theory
                      hFormula) (is_relation_member_eq_ordered_pair_projections
                    function member hFunction hMember))
            hRelation)
          hMembership)
    have hRepresentedMembership :
        Γ ⊢ₘ[function_application_theory]
          represented ∈ₘ function := by
      exact FirstOrder.Derives.iffElimRight (membership_left_iff_of_equality
          member represented function
          hMember hRepresented hFunction
          hRepresentation)
        hMembership
    have hDomain :
        Γ ⊢ₘ[function_application_theory]
          left_coordinate ∈ₘ domₘ(function) := by
      exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := member ∈ₘ function) <|
            FirstOrder.Derives.context_weaken_cons (assumption := is_function_formula function) <|
              FirstOrder.Derives.theory_weaken (fun _ hFormula =>
                  function_predicate_theory_subset_function_application_theory
                    hFormula) (relation_member_left_coordinate_mem_domain
                  function left_coordinate right_coordinate
                  hFunction hLeftCoordinate hRightCoordinate))
          hRelation) (by
          simpa [represented] using hRepresentedMembership)
    have hValue :
        Γ ⊢ₘ[function_application_theory]
          right_coordinate ≐ₘ (function ·ₘ left_coordinate) :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := member ∈ₘ function) <|
            FirstOrder.Derives.context_weaken_cons (assumption := is_function_formula function) <|
              function_application_eq_of_graph
                function left_coordinate right_coordinate
                hFunction hLeftCoordinate hRightCoordinate) (FirstOrder.Derives.conjIntro
            hFunctionFormula hDomain)) (by
          simpa [represented] using hRepresentedMembership)
    simpa [function_graph_member_condition,
      left_coordinate, right_coordinate] using (FirstOrder.Derives.conjIntro
        hOrdered (FirstOrder.Derives.conjIntro
          hDomain hValue))
  · let condition :=
      function_graph_member_condition function member
    let Γ : Context signature :=
      [condition, is_function_formula function]
    have hFunctionFormula :
        Γ ⊢ₘ[function_application_theory]
          is_function_formula function :=
      .assumption (by simp [Γ])
    have hCondition :
        Γ ⊢ₘ[function_application_theory]
          function_graph_member_condition
            function member := by
      simpa [condition] using (show Γ ⊢ₘ[function_application_theory]
            condition from
          .assumption (by simp [Γ]))
    have hOrdered :
        Γ ⊢ₘ[function_application_theory]
          is_ordered_pair_formula member :=
      FirstOrder.Derives.conjElimLeft hCondition
    have hDomain :
        Γ ⊢ₘ[function_application_theory]
          left_coordinate ∈ₘ domₘ(function) := by
      simpa [function_graph_member_condition,
        left_coordinate] using (FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight
            hCondition))
    have hValue :
        Γ ⊢ₘ[function_application_theory]
          right_coordinate ≐ₘ (function ·ₘ left_coordinate) := by
      simpa [function_graph_member_condition,
        left_coordinate, right_coordinate] using (FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight
            hCondition))
    have hRepresentation :
        Γ ⊢ₘ[function_application_theory]
          member ≐ₘ represented := by
      have hRepresentationImp :=
        FirstOrder.Derives.context_weaken_cons (assumption := condition) <|
          FirstOrder.Derives.context_weaken_cons (assumption := is_function_formula function) <|
            FirstOrder.Derives.theory_weaken (fun _ hFormula =>
                relation_plane_theory_subset_function_application_theory (right_projection_operator_theory_subset_relation_plane_theory
                    hFormula)) (is_ordered_pair_eq_ordered_pair_projections
                member hMember)
      simpa [represented, left_coordinate,
        right_coordinate] using (FirstOrder.Derives.impElim
          hRepresentationImp hOrdered)
    have hRepresentedMembership :
        Γ ⊢ₘ[function_application_theory]
          represented ∈ₘ function := by
      have hContract :=
        FirstOrder.Derives.context_weaken_cons (assumption := condition) <|
          FirstOrder.Derives.context_weaken_cons (assumption := is_function_formula function) <|
            function_application_eq_iff_graph
              function left_coordinate right_coordinate
              hFunction hLeftCoordinate hRightCoordinate
      have hGraph :=
        FirstOrder.Derives.impElim
          hContract (FirstOrder.Derives.conjIntro
            hFunctionFormula hDomain)
      simpa [represented] using (FirstOrder.Derives.iffElimRight
          hGraph hValue)
    exact FirstOrder.Derives.iffElimLeft (membership_left_iff_of_equality
        member represented function
        hMember hRepresented hFunction
        hRepresentation)
      hRepresentedMembership
/--
定义域相等且逐点相等时，两个函数图的规范成员条件等价。
该引理只处理坐标规格，不假设两端已经是函数；函数性在最终外延定理中单独消费。
-/
theorem function_graph_member_condition_iff_of_agreement (left right member : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hMember : Term.Admissible member SetSort.set) :
    ⊢ₘ[function_application_theory]
      function_extensional_agreement left right ⟶ₘ (function_graph_member_condition left member ↔ₘ
          function_graph_member_condition right member) := by
  let coordinate := (member)₀ₘ
  let value := (member)₁ₘ
  let agreement :=
    function_extensional_agreement left right
  let Γ : Context signature := [agreement]
  have hCoordinate :
      Term.Admissible coordinate SetSort.set :=
    left_projection_term_admissible member hMember
  have hValue :
      Term.Admissible value SetSort.set :=
    right_projection_term_admissible member hMember
  have hLeftDomain :
      Term.Admissible (domₘ(left)) SetSort.set :=
    domain_term_admissible left hLeft
  have hRightDomain :
      Term.Admissible (domₘ(right)) SetSort.set :=
    domain_term_admissible right hRight
  have hLeftApplication :
      Term.Admissible (left ·ₘ coordinate) SetSort.set :=
    function_application_term_admissible
      left coordinate hLeft hCoordinate
  have hRightApplication :
      Term.Admissible (right ·ₘ coordinate) SetSort.set :=
    function_application_term_admissible
      right coordinate hRight hCoordinate
  nd_apply FirstOrder.Derives.impIntro
  have hAgreement :
      Γ ⊢ₘ[function_application_theory]
        function_extensional_agreement left right := by
    simpa [Γ, agreement] using (show Γ ⊢ₘ[function_application_theory]
          agreement from
        .assumption (by simp [Γ]))
  have hDomainEquality :
      Γ ⊢ₘ[function_application_theory]
        domₘ(left) ≐ₘ domₘ(right) := by
    simpa [function_extensional_agreement] using (FirstOrder.Derives.conjElimLeft
        hAgreement)
  have hPointwise :
      Γ ⊢ₘ[function_application_theory]
        ∀ₘ[SetSort.set], (bₛ#0 ∈ₘ domₘ(left)) ⟶ₘ ((left ·ₘ bₛ#0) ≐ₘ (right ·ₘ bₛ#0)) := by
    simpa [function_extensional_agreement] using (FirstOrder.Derives.conjElimRight
        hAgreement)
  have hPointwiseRaw :=
    FirstOrder.Derives.forall_elim
      (term := coordinate) hPointwise
  have hLeftOpen :
      Term.openAt SetSort.set 0 coordinate left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 coordinate left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 coordinate right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 coordinate right hRight.2
  have hPointwiseAt :
      Γ ⊢ₘ[function_application_theory] (coordinate ∈ₘ domₘ(left)) ⟶ₘ ((left ·ₘ coordinate) ≐ₘ (right ·ₘ coordinate)) := by
    simpa [Formula.openAt, Formula.next_depth,
      Term.openAt, domain_term,
      function_application_term,
      hLeftOpen, hRightOpen] using
      hPointwiseRaw
  have hDomainMembership :=
    membership_right_iff_of_equality
      coordinate (domₘ(left)) (domₘ(right))
      hCoordinate hLeftDomain hRightDomain
      hDomainEquality
  apply FirstOrder.Derives.iffIntro
  · let left_condition :=
      function_graph_member_condition left member
    let ΓLeft : Context signature :=
      [left_condition, agreement]
    have hCondition :
        ΓLeft ⊢ₘ[function_application_theory]
          function_graph_member_condition left member := by
      simpa [left_condition] using (show ΓLeft ⊢ₘ[function_application_theory]
            left_condition from
          .assumption (by simp [ΓLeft]))
    have hOrdered :
        ΓLeft ⊢ₘ[function_application_theory]
          is_ordered_pair_formula member :=
      FirstOrder.Derives.conjElimLeft hCondition
    have hCoordinateLeft :
        ΓLeft ⊢ₘ[function_application_theory]
          coordinate ∈ₘ domₘ(left) := by
      simpa [function_graph_member_condition,
        coordinate] using (FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight
            hCondition))
    have hValueLeft :
        ΓLeft ⊢ₘ[function_application_theory]
          value ≐ₘ (left ·ₘ coordinate) := by
      simpa [function_graph_member_condition,
        coordinate, value] using (FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight
            hCondition))
    have hCoordinateRight :
        ΓLeft ⊢ₘ[function_application_theory]
          coordinate ∈ₘ domₘ(right) :=
      FirstOrder.Derives.iffElimRight (FirstOrder.Derives.context_weaken_cons (assumption := left_condition)
          hDomainMembership)
        hCoordinateLeft
    have hApplicationEquality :
        ΓLeft ⊢ₘ[function_application_theory] (left ·ₘ coordinate) ≐ₘ (right ·ₘ coordinate) :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := left_condition)
          hPointwiseAt)
        hCoordinateLeft
    have hValueRight :
        ΓLeft ⊢ₘ[function_application_theory]
          value ≐ₘ (right ·ₘ coordinate) :=
      FirstOrder.Metatheory.Derives.equality_trans
        hValueLeft hApplicationEquality
    simpa [function_graph_member_condition,
      coordinate, value] using (FirstOrder.Derives.conjIntro
        hOrdered (FirstOrder.Derives.conjIntro
          hCoordinateRight hValueRight))
  · let right_condition :=
      function_graph_member_condition right member
    let ΓRight : Context signature :=
      [right_condition, agreement]
    have hCondition :
        ΓRight ⊢ₘ[function_application_theory]
          function_graph_member_condition right member := by
      simpa [right_condition] using (show ΓRight ⊢ₘ[function_application_theory]
            right_condition from
          .assumption (by simp [ΓRight]))
    have hOrdered :
        ΓRight ⊢ₘ[function_application_theory]
          is_ordered_pair_formula member :=
      FirstOrder.Derives.conjElimLeft hCondition
    have hCoordinateRight :
        ΓRight ⊢ₘ[function_application_theory]
          coordinate ∈ₘ domₘ(right) := by
      simpa [function_graph_member_condition,
        coordinate] using (FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight
            hCondition))
    have hValueRight :
        ΓRight ⊢ₘ[function_application_theory]
          value ≐ₘ (right ·ₘ coordinate) := by
      simpa [function_graph_member_condition,
        coordinate, value] using (FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight
            hCondition))
    have hCoordinateLeft :
        ΓRight ⊢ₘ[function_application_theory]
          coordinate ∈ₘ domₘ(left) :=
      FirstOrder.Derives.iffElimLeft (FirstOrder.Derives.context_weaken_cons (assumption := right_condition)
          hDomainMembership)
        hCoordinateRight
    have hApplicationEquality :
        ΓRight ⊢ₘ[function_application_theory] (left ·ₘ coordinate) ≐ₘ (right ·ₘ coordinate) :=
      FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := right_condition)
          hPointwiseAt)
        hCoordinateLeft
    have hApplicationEqualitySymm :
        ΓRight ⊢ₘ[function_application_theory] (right ·ₘ coordinate) ≐ₘ (left ·ₘ coordinate) :=
      FirstOrder.Metatheory.Derives.equality_symm
        hApplicationEquality
    have hValueLeft :
        ΓRight ⊢ₘ[function_application_theory]
          value ≐ₘ (left ·ₘ coordinate) :=
      FirstOrder.Metatheory.Derives.equality_trans
        hValueRight hApplicationEqualitySymm
    simpa [function_graph_member_condition,
      coordinate, value] using (FirstOrder.Derives.conjIntro
        hOrdered (FirstOrder.Derives.conjIntro
          hCoordinateLeft hValueLeft))
/-! ## 函数外延性 -/
/-- 集合等式推出定义域相等与逐点相等。 -/
theorem function_extensional_agreement_of_equality (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[function_application_theory] (left ≐ₘ right) ⟶ₘ
        function_extensional_agreement
          left right := by
  let equality : SetFormula := left ≐ₘ right
  let point_body : SetFormula := (bₛ#0 ∈ₘ domₘ(left)) ⟶ₘ ((left ·ₘ bₛ#0) ≐ₘ (right ·ₘ bₛ#0))
  let argument :=
    FreshVariable.fresh_id SetSort.set
      [equality, point_body]
  let Γ : Context signature := [equality]
  have hArgumentFreshEquality : (SetSort.set, argument) freshForₘ
        equality := by
    dsimp [argument]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hArgumentFreshBody : (SetSort.set, argument) freshForₘ
        point_body := by
    dsimp [argument]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  nd_apply FirstOrder.Derives.impIntro
  have hEquality :
      Γ ⊢ₘ[function_application_theory]
        left ≐ₘ right := by
    simpa [Γ, equality] using (show Γ ⊢ₘ[function_application_theory]
          equality from
        .assumption (by simp [Γ]))
  have hDomainEquality :
      Γ ⊢ₘ[function_application_theory]
        domₘ(left) ≐ₘ domₘ(right) :=
    domain_term_congr_of_equality
      left right hLeft hRight hEquality
  have hApplicationEquality :
      Γ ⊢ₘ[function_application_theory] (left ·ₘ x#argument) ≐ₘ (right ·ₘ x#argument) :=
    function_application_term_congr_function_of_equality
      left right (x#argument)
      hLeft hRight (set_variable_admissible argument)
      hEquality
  have hPoint :
      Γ ⊢ₘ[function_application_theory] (x#argument ∈ₘ domₘ(left)) ⟶ₘ ((left ·ₘ x#argument) ≐ₘ (right ·ₘ x#argument)) := by
    nd_apply FirstOrder.Derives.impIntro
    exact FirstOrder.Derives.context_weaken_cons (assumption := x#argument ∈ₘ domₘ(left))
      hApplicationEquality
  have hLeftOpen :
      Term.openAt SetSort.set 0 (x#argument) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#argument) left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 (x#argument) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#argument) right hRight.2
  have hPointOpened :
      Γ ⊢ₘ[function_application_theory]
        Formula.openAt SetSort.set 0 (x#argument) point_body := by
    simpa [point_body, Formula.openAt,
      Formula.next_depth, Term.openAt,
      domain_term, function_application_term,
      hLeftOpen, hRightOpen] using hPoint
  have hPointwise :
      Γ ⊢ₘ[function_application_theory]
        ∀ₘ[SetSort.set], point_body := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := function_application_theory) (Γ := Γ) (sort := SetSort.set) (eigen := argument) (body :=
          Formula.openAt SetSort.set 0 (x#argument) point_body) (by
          intro formula hFormula
          have hSentence :=
            function_application_theory_sentence hFormula
          rw [hSentence.2]
          simp) (by
          intro formula hFormula
          rcases List.mem_singleton.mp hFormula with rfl
          exact hArgumentFreshEquality)
        hPointOpened
    simpa [Formula.closeFreeAt_openAt
      SetSort.set argument 0 point_body
      hArgumentFreshBody] using hGeneralized
  simpa [function_extensional_agreement,
    point_body] using (FirstOrder.Derives.conjIntro
      hDomainEquality hPointwise)
/-- 两个函数满足定义域相等与逐点相等时，其函数图相等。 -/
theorem functions_equal_of_extensional_agreement (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[function_application_theory] (is_function_formula left ∧ₘ
          is_function_formula right) ⟶ₘ
        function_extensional_agreement
            left right ⟶ₘ (left ≐ₘ right) := by
  let functions : SetFormula :=
    is_function_formula left ∧ₘ
      is_function_formula right
  let agreement :=
    function_extensional_agreement left right
  let agreement_body : SetFormula := (bₛ#0 ∈ₘ left) ↔ₘ (bₛ#0 ∈ₘ right)
  let member :=
    FreshVariable.fresh_id SetSort.set
      [functions, agreement, agreement_body]
  let Γ : Context signature :=
    [agreement, functions]
  have hMemberFreshFunctions : (SetSort.set, member) freshForₘ
        functions := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshAgreement : (SetSort.set, member) freshForₘ
        agreement := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hMemberFreshBody : (SetSort.set, member) freshForₘ
        agreement_body := by
    dsimp [member]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hFunctionsAdmissible :
      Formula.Admissible functions := by
    dsimp [functions]
    exact Formula.Admissible.conj (is_function_formula_admissible hLeft) (is_function_formula_admissible hRight)
  have hAgreementAdmissible :
      Formula.Admissible agreement := by
    dsimp [agreement]
    exact function_extensional_agreement_admissible
      hLeft hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hFunctions :
      Γ ⊢ₘ[function_application_theory]
        is_function_formula left ∧ₘ
          is_function_formula right := by
    simpa [Γ, functions] using (show Γ ⊢ₘ[function_application_theory]
          functions from
        .assumption (by simp [Γ]))
  have hAgreement :
      Γ ⊢ₘ[function_application_theory]
        function_extensional_agreement
          left right := by
    simpa [Γ, agreement] using (show Γ ⊢ₘ[function_application_theory]
          agreement from
        .assumption (by simp [Γ]))
  have hLeftFunction :
      Γ ⊢ₘ[function_application_theory]
        is_function_formula left :=
    FirstOrder.Derives.conjElimLeft hFunctions
  have hRightFunction :
      Γ ⊢ₘ[function_application_theory]
        is_function_formula right :=
    FirstOrder.Derives.conjElimRight hFunctions
  have hLeftGraph :
      Γ ⊢ₘ[function_application_theory] ((x#member ∈ₘ left) ↔ₘ
          function_graph_member_condition
            left (x#member)) :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := agreement) <|
        FirstOrder.Derives.context_weaken_cons (assumption := functions) <|
          is_function_member_iff_coordinates
            left (x#member)
            hLeft (set_variable_admissible member))
      hLeftFunction
  have hRightGraph :
      Γ ⊢ₘ[function_application_theory] ((x#member ∈ₘ right) ↔ₘ
          function_graph_member_condition
            right (x#member)) :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := agreement) <|
        FirstOrder.Derives.context_weaken_cons (assumption := functions) <|
          is_function_member_iff_coordinates
            right (x#member)
            hRight (set_variable_admissible member))
      hRightFunction
  have hConditionIff :
      Γ ⊢ₘ[function_application_theory] (function_graph_member_condition
            left (x#member) ↔ₘ
          function_graph_member_condition
            right (x#member)) :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := agreement) <|
        FirstOrder.Derives.context_weaken_cons (assumption := functions) <|
          function_graph_member_condition_iff_of_agreement
            left right (x#member)
            hLeft hRight (set_variable_admissible member))
      hAgreement
  have hMembershipIff :
      Γ ⊢ₘ[function_application_theory] (x#member ∈ₘ left) ↔ₘ (x#member ∈ₘ right) := by
    derive_prop
  have hLeftOpen :
      Term.openAt SetSort.set 0 (x#member) left =
        left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) left hLeft.2
  have hRightOpen :
      Term.openAt SetSort.set 0 (x#member) right =
        right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 (x#member) right hRight.2
  have hMembershipIffOpened :
      Γ ⊢ₘ[function_application_theory]
        Formula.openAt SetSort.set 0 (x#member) agreement_body := by
    simpa [agreement_body, Formula.openAt,
      Term.openAt, hLeftOpen, hRightOpen] using
      hMembershipIff
  have hMembershipAgreement :
      Γ ⊢ₘ[function_application_theory]
        membership_agreement left right := by
    have hGeneralized :=
      FirstOrder.Derives.forall_intro (T := function_application_theory) (Γ := Γ) (sort := SetSort.set) (eigen := member) (body :=
          Formula.openAt SetSort.set 0 (x#member) agreement_body) (by
          intro formula hFormula
          have hSentence :=
            function_application_theory_sentence hFormula
          rw [hSentence.2]
          simp) (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · exact hMemberFreshAgreement
          · rcases List.mem_singleton.mp hFormula with rfl
            exact hMemberFreshFunctions)
        hMembershipIffOpened
    simpa [membership_agreement,
      Formula.closeFreeAt_openAt
        SetSort.set member 0 agreement_body
        hMemberFreshBody] using hGeneralized
  have hExtensionality :
      Γ ⊢ₘ[function_application_theory]
        extensionality_instance left right :=
    FirstOrder.Derives.context_weaken_cons (assumption := agreement) <|
      FirstOrder.Derives.context_weaken_cons (assumption := functions) <|
        FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            extensionality_theory_subset_function_application_theory
              hFormula) (extensionality_instance_derives_of_admissible
            left right hLeft hRight)
  exact FirstOrder.Derives.impElim
    hExtensionality hMembershipAgreement
/--
文献定理 2.40 的现代形式：两个函数相等，当且仅当它们定义域相等并逐点相等。
-/
theorem function_eq_iff_domain_eq_and_pointwise (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[function_application_theory] (is_function_formula left ∧ₘ
          is_function_formula right) ⟶ₘ ((left ≐ₘ right) ↔ₘ
          function_extensional_agreement
            left right) := by
  have hForward :=
    function_extensional_agreement_of_equality
      left right hLeft hRight
  have hBackward :=
    functions_equal_of_extensional_agreement
      left right hLeft hRight
  derive_prop
/-! ## 映射赋值合同 -/
/--
映射的参数属于源集时，求值等式与图成员关系等价。
目标集约束已经由映射谓词中的值域包含条件记录，因此求值图合同本身无需重复要求
候选值属于目标集。
-/
theorem is_mapping_application_eq_iff_graph (function source target argument value : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set) (hArgument : Term.Admissible argument SetSort.set)
    (hValue : Term.Admissible value SetSort.set) :
    ⊢ₘ[function_application_theory]
      is_mapping_formula function source target ⟶ₘ (argument ∈ₘ source) ⟶ₘ ((value ≐ₘ (function ·ₘ argument)) ↔ₘ (⟨argument, value⟩ₘ ∈ₘ function)) := by
  let mapping_formula :=
    is_mapping_formula function source target
  let source_membership := argument ∈ₘ source
  let Γ : Context signature :=
    [source_membership, mapping_formula]
  have hDomain :
      Term.Admissible (domₘ(function)) SetSort.set :=
    domain_term_admissible function hFunction
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hMapping :
      Γ ⊢ₘ[function_application_theory]
        is_mapping_formula function source target := by
    simpa [Γ, mapping_formula] using (show Γ ⊢ₘ[function_application_theory]
          mapping_formula from
        .assumption (by simp [Γ]))
  have hSourceMembership :
      Γ ⊢ₘ[function_application_theory]
        argument ∈ₘ source := by
    simpa [Γ, source_membership] using (show Γ ⊢ₘ[function_application_theory]
          source_membership from
        .assumption (by simp [Γ]))
  have hMappingCondition :
      Γ ⊢ₘ[function_application_theory]
        is_mapping_condition
          function source target :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := source_membership) <|
        FirstOrder.Derives.context_weaken_cons (assumption := mapping_formula) <|
          FirstOrder.Derives.theory_weaken (fun _ hFormula =>
              mapping_predicate_theory_subset_function_application_theory
                hFormula) (is_mapping_implies_condition
              function source target
              hFunction hSource hTarget))
      hMapping
  have hFunctionFormula :
      Γ ⊢ₘ[function_application_theory]
        is_function_formula function :=
    FirstOrder.Derives.conjElimLeft
      hMappingCondition
  have hSourceEquality :
      Γ ⊢ₘ[function_application_theory]
        source ≐ₘ domₘ(function) :=
    FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight
        hMappingCondition)
  have hDomainMembership :
      Γ ⊢ₘ[function_application_theory]
        argument ∈ₘ domₘ(function) :=
    FirstOrder.Derives.iffElimRight (membership_right_iff_of_equality
        argument source (domₘ(function))
        hArgument hSource hDomain
        hSourceEquality)
      hSourceMembership
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := source_membership) <|
      FirstOrder.Derives.context_weaken_cons (assumption := mapping_formula) <|
        function_application_eq_iff_graph
          function argument value
          hFunction hArgument hValue) (FirstOrder.Derives.conjIntro
      hFunctionFormula hDomainMembership)
/--
文献定义 2.30 的原始 guard 形式；候选值属于目标集这一前提在现代核心中是冗余的。
-/
theorem is_mapping_application_eq_iff_graph_with_target (function source target argument value : SetTerm) (hFunction : Term.Admissible function SetSort.set)
    (hSource : Term.Admissible source SetSort.set) (hTarget : Term.Admissible target SetSort.set) (hArgument : Term.Admissible argument SetSort.set)
    (hValue : Term.Admissible value SetSort.set) :
    ⊢ₘ[function_application_theory]
      is_mapping_formula function source target ⟶ₘ ((argument ∈ₘ source) ∧ₘ (value ∈ₘ target)) ⟶ₘ ((value ≐ₘ (function ·ₘ argument)) ↔ₘ
            (⟨argument, value⟩ₘ ∈ₘ function)) := by
  have hCore :=
    is_mapping_application_eq_iff_graph
      function source target argument value
      hFunction hSource hTarget hArgument hValue
  let mapping_formula :=
    is_mapping_formula function source target
  let guarded_membership := (argument ∈ₘ source) ∧ₘ (value ∈ₘ target)
  let Γ : Context signature :=
    [guarded_membership, mapping_formula]
  have hMappingAdmissible :
      Formula.Admissible mapping_formula := by
    simpa [mapping_formula] using
      is_mapping_formula_admissible
        hFunction hSource hTarget
  have hGuardAdmissible :
      Formula.Admissible guarded_membership := by
    simpa [guarded_membership] using
      Formula.Admissible.conj (membership_formula_admissible
          hArgument hSource) (membership_formula_admissible
          hValue hTarget)
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hMapping :
      Γ ⊢ₘ[function_application_theory]
        mapping_formula :=
    .assumption (by simp [Γ])
  have hGuard :
      Γ ⊢ₘ[function_application_theory]
        guarded_membership :=
    .assumption (by simp [Γ])
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons (assumption := guarded_membership) <|
        FirstOrder.Derives.context_weaken_cons (assumption := mapping_formula) hCore)
      hMapping) (FirstOrder.Derives.conjElimLeft hGuard)
/-! ## 全称闭包接口 -/
/-- 等价关系谓词定义的单变量全称闭包。 -/
theorem is_equivalence_relation_iff_condition_forall (relation : FreeVarId) :
    ⊢ₘ[equivalence_relation_theory]
      ∀ₘ[SetSort.set, relation],
        is_equivalence_relation_formula (x#relation) ↔ₘ
          is_equivalence_relation_condition (x#relation) := by
  derive_close (relation) using
    is_equivalence_relation_iff_condition (x#relation) (set_variable_admissible relation)
/-- 函数谓词定义的单变量全称闭包。 -/
theorem is_function_iff_condition_forall (function : FreeVarId) :
    ⊢ₘ[function_predicate_theory]
      ∀ₘ[SetSort.set, function],
        is_function_formula (x#function) ↔ₘ
          is_function_condition (x#function) := by
  derive_close (function) using
    is_function_iff_condition (x#function) (set_variable_admissible function)
/-- 映射谓词定义的三变量全称闭包。 -/
theorem is_mapping_iff_condition_forall (function source target : FreeVarId) :
    ⊢ₘ[mapping_predicate_theory]
      ∀ₘ[SetSort.set, function],
        ∀ₘ[SetSort.set, source],
          ∀ₘ[SetSort.set, target],
            is_mapping_formula (x#function) (x#source) (x#target) ↔ₘ
              is_mapping_condition (x#function) (x#source) (x#target) := by
  derive_close (function, source, target) using
    is_mapping_iff_condition (x#function) (x#source) (x#target) (set_variable_admissible function) (set_variable_admissible source)
      (set_variable_admissible target)
/-- 函数求值图合同的三变量全称闭包。 -/
theorem function_application_eq_iff_graph_forall (function argument value : FreeVarId) :
    ⊢ₘ[function_application_theory]
      ∀ₘ[SetSort.set, function],
        ∀ₘ[SetSort.set, argument],
          ∀ₘ[SetSort.set, value], (is_function_formula (x#function) ∧ₘ (x#argument ∈ₘ domₘ(x#function))) ⟶ₘ (((x#value) ≐ₘ ((x#function) ·ₘ (x#argument))) ↔ₘ
                (⟨x#argument, x#value⟩ₘ ∈ₘ
                  x#function)) := by
  derive_close (function, argument, value) using
    function_application_eq_iff_graph (x#function) (x#argument) (x#value) (set_variable_admissible function) (set_variable_admissible argument)
      (set_variable_admissible value)
/-- 函数成员坐标刻画的双变量全称闭包。 -/
theorem is_function_member_iff_coordinates_forall (function member : FreeVarId) :
    ⊢ₘ[function_application_theory]
      ∀ₘ[SetSort.set, function],
        ∀ₘ[SetSort.set, member],
          is_function_formula (x#function) ⟶ₘ (((x#member) ∈ₘ x#function) ↔ₘ
              function_graph_member_condition (x#function) (x#member)) := by
  derive_close (function, member) using
    is_function_member_iff_coordinates (x#function) (x#member) (set_variable_admissible function) (set_variable_admissible member)
/-- 文献定理 2.40 的双变量全称闭包。 -/
theorem function_eq_iff_domain_eq_and_pointwise_forall (left right : FreeVarId) :
    ⊢ₘ[function_application_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right], (is_function_formula (x#left) ∧ₘ
              is_function_formula (x#right)) ⟶ₘ (((x#left) ≐ₘ (x#right)) ↔ₘ
              function_extensional_agreement (x#left) (x#right)) := by
  derive_close (left, right) using
    function_eq_iff_domain_eq_and_pointwise (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)
/-- 文献定义 2.30 的五变量全称闭包。 -/
theorem is_mapping_application_eq_iff_graph_with_target_forall (function source target argument value : FreeVarId) :
    ⊢ₘ[function_application_theory]
      ∀ₘ[SetSort.set, function],
        ∀ₘ[SetSort.set, source],
          ∀ₘ[SetSort.set, target],
            ∀ₘ[SetSort.set, argument],
              ∀ₘ[SetSort.set, value],
                is_mapping_formula (x#function) (x#source) (x#target) ⟶ₘ (((x#argument ∈ₘ x#source) ∧ₘ (x#value ∈ₘ x#target)) ⟶ₘ (((x#value) ≐ₘ
                        ((x#function) ·ₘ (x#argument))) ↔ₘ (⟨x#argument, x#value⟩ₘ ∈ₘ
                        x#function))) := by
  derive_close (function, source, target, argument, value) using
    is_mapping_application_eq_iff_graph_with_target (x#function) (x#source) (x#target) (x#argument) (x#value) (set_variable_admissible function)
      (set_variable_admissible source) (set_variable_admissible target) (set_variable_admissible argument) (set_variable_admissible value)
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
