import YesMetaZFC.Logic.FirstOrder.FormalSystem.LogicalRuleEncoding
import YesMetaZFC.Logic.FirstOrder.Hilbert.Substitution
/-!
# 形式系统编码的对象理论定义合同
本模块把编码层的闭定义公理实例化为可直接消费的对象逻辑定理。实例化只使用
`Derives` 的理论成员与全称消去规则；字符串规格本身仍保留为对象公式。
若规格内部使用具名 free-variable 编号来构造量词，实参必须对这些保留编号新鲜。
该条件在接口中显式出现，防止实例化时悄悄捕获调用方的自由变量。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
/-- 一组对象项对定义内部保留的 free-variable 编号同时新鲜。 -/
def ReservedIdsFresh (ids : List FreeVarId) (terms : List SetTerm) : Prop :=
  ∀ term, term ∈ terms → ∀ id, id ∈ ids → (SetSort.set, id) ∉ Term.freeSupport term
/-- 空项列对任意保留编号都新鲜。 -/
theorem reserved_ids_fresh_nil (ids : List FreeVarId) :
    ReservedIdsFresh ids [] := by
  intro term hTerm
  cases hTerm
/-- 自由支撑为空的闭项可以前接到新鲜项列。 -/
theorem reserved_ids_fresh_cons_closed
    {ids : List FreeVarId} {terms : List SetTerm} {term : SetTerm}
    (hTerm : Term.freeSupport term = [])
    (hTerms : ReservedIdsFresh ids terms) :
    ReservedIdsFresh ids (term :: terms) := by
  intro candidate hCandidate id hId
  rcases List.mem_cons.mp hCandidate with rfl | hCandidate
  · rw [hTerm]
    exact List.not_mem_nil
  · exact hTerms candidate hCandidate id hId
/-- 与全部保留编号不同的自由变量项可以前接到新鲜项列。 -/
theorem reserved_ids_fresh_cons_variable
    {ids : List FreeVarId} {terms : List SetTerm}
    (variableId : FreeVarId)
    (hVariable : ∀ id, id ∈ ids → variableId ≠ id)
    (hTerms : ReservedIdsFresh ids terms) :
    ReservedIdsFresh ids (x#variableId :: terms) := by
  intro candidate hCandidate id hId
  rcases List.mem_cons.mp hCandidate with rfl | hCandidate
  · intro hMember
    change (SetSort.set, id) ∈ [(SetSort.set, variableId)] at hMember
    exact hVariable id hId
      (congrArg Prod.snd (List.mem_singleton.mp hMember)).symm
  · exact hTerms candidate hCandidate id hId
/-! ## 有限序列与基础编码构造 -/
/-- 有限序列合并定义公理可在三个 admissible 项处安全实例化。 -/
theorem finite_sequence_concatenation_definition_instance_derives (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[finite_sequence_concatenation_theory]
      finite_sequence_concatenation_definition_instance
        left right candidate := by
  have hAxiom :
      ⊢ₘ[finite_sequence_concatenation_theory]
        finite_sequence_concatenation_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hLeftInstance := FirstOrder.Derives.forall_elim
    (term := left) hAxiom
  have hRightInstance := FirstOrder.Derives.forall_elim
    (term := right) hLeftInstance
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hRightInstance
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  simpa [finite_sequence_concatenation_definition_axiom,
    finite_sequence_concatenation_definition_instance,
    finite_sequence_concatenation_spec,
    finite_sequence_concatenation_left_condition,
    finite_sequence_concatenation_right_condition,
    finite_sequence_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hLeftOpen, hRightOpen] using
      hCandidateInstance
/--
两个有限序列的规范合并项满足完整合并规格。
该定理把定义合同中的候选等式固定为自反等式；后续前缀反演只需消费它的定义域与
左右点态投影，不再重复展开定义公理。
-/
theorem finite_sequence_concatenation_self_spec_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[finite_sequence_concatenation_theory] (finite_sequence_condition left ∧ₘ
          finite_sequence_condition right) ⟶ₘ
        finite_sequence_concatenation_spec
          left right (left ⌢ₘ right) := by
  let precondition : SetFormula :=
    finite_sequence_condition left ∧ₘ
      finite_sequence_condition right
  have hCandidate :
      Term.Admissible (left ⌢ₘ right) SetSort.set :=
    finite_sequence_concatenation_term_admissible
      left right hLeft hRight
  have hContract :=
    finite_sequence_concatenation_definition_instance_derives
      left right (left ⌢ₘ right)
      hLeft hRight hCandidate
  nd_apply FirstOrder.Derives.impIntro
  have hPrecondition :
      [precondition] ⊢ₘ[finite_sequence_concatenation_theory]
        precondition :=
    FirstOrder.Derives.assumption (by simp)
  have hIff :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons hContract)
      hPrecondition
  have hReflexive :
      [precondition] ⊢ₘ[finite_sequence_concatenation_theory] (left ⌢ₘ right) ≐ₘ (left ⌢ₘ right) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) (left ⌢ₘ right)
  simpa [precondition] using
    FirstOrder.Derives.iffElimRight hIff hReflexive
/-- 合并结果仍是有限序列。 -/
theorem finite_sequence_concatenation_finite_derives (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[finite_sequence_concatenation_theory] (finite_sequence_condition left ∧ₘ
          finite_sequence_condition right) ⟶ₘ
        finite_sequence_condition (left ⌢ₘ right) := by
  have hSpec :=
    finite_sequence_concatenation_self_spec_derives
      left right hLeft hRight
  derive_prop
/-- 合并结果在左段定义域上同时保留定义域成员与逐点值。 -/
theorem finite_sequence_concatenation_left_point_derives (left right index : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[finite_sequence_concatenation_theory] (finite_sequence_condition left ∧ₘ
          finite_sequence_condition right) ⟶ₘ (index ∈ₘ domₘ(left)) ⟶ₘ ((index ∈ₘ domₘ(left ⌢ₘ right)) ∧ₘ (((left ⌢ₘ right) ·ₘ index) ≐ₘ (left ·ₘ index))) := by
  let precondition : SetFormula :=
    finite_sequence_condition left ∧ₘ
      finite_sequence_condition right
  let membership : SetFormula := index ∈ₘ domₘ(left)
  let Γ : Context signature := [membership, precondition]
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hPrecondition :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        precondition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hMembership :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        membership :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hSpec :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        finite_sequence_concatenation_spec
          left right (left ⌢ₘ right) :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        finite_sequence_concatenation_self_spec_derives
          left right hLeft hRight)
      hPrecondition
  have hPointwise :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        ∀ₘ[SetSort.set],
          finite_sequence_concatenation_left_condition
            left (left ⌢ₘ right) bₛ#0 :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hSpec
  have hAtIndex :=
    FirstOrder.Derives.forall_elim
      (term := index) hPointwise
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  have hAtIndex' :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        membership ⟶ₘ ((index ∈ₘ domₘ(left ⌢ₘ right)) ∧ₘ (((left ⌢ₘ right) ·ₘ index) ≐ₘ (left ·ₘ index))) := by
    simpa [membership,
      finite_sequence_concatenation_left_condition,
      Formula.openAt, Term.openAt,
      hLeftOpen, hRightOpen] using hAtIndex
  exact FirstOrder.Derives.impElim hAtIndex' hMembership
/-- 合并结果的定义域包含左段定义域。 -/
theorem finite_sequence_concatenation_left_domain_derives (left right index : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[finite_sequence_concatenation_theory] (finite_sequence_condition left ∧ₘ
          finite_sequence_condition right) ⟶ₘ (index ∈ₘ domₘ(left)) ⟶ₘ (index ∈ₘ domₘ(left ⌢ₘ right)) := by
  have hPoint :=
    finite_sequence_concatenation_left_point_derives
      left right index hLeft hRight hIndex
  derive_prop
/-- 合并结果在左段定义域上逐点保留左序列。 -/
theorem finite_sequence_concatenation_left_value_derives (left right index : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[finite_sequence_concatenation_theory] (finite_sequence_condition left ∧ₘ
          finite_sequence_condition right) ⟶ₘ (index ∈ₘ domₘ(left)) ⟶ₘ (((left ⌢ₘ right) ·ₘ index) ≐ₘ (left ·ₘ index)) := by
  have hPoint :=
    finite_sequence_concatenation_left_point_derives
      left right index hLeft hRight hIndex
  derive_prop
/-- 合并结果在右段平移位置上同时记录定义域成员与逐点值。 -/
theorem finite_sequence_concatenation_right_point_derives (left right index : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[finite_sequence_concatenation_theory] (finite_sequence_condition left ∧ₘ
          finite_sequence_condition right) ⟶ₘ (index ∈ₘ domₘ(right)) ⟶ₘ ((((domₘ(left) +ₘ index) ∈ₘ
              domₘ(left ⌢ₘ right))) ∧ₘ (((left ⌢ₘ right) ·ₘ (domₘ(left) +ₘ index)) ≐ₘ (right ·ₘ index))) := by
  let precondition : SetFormula :=
    finite_sequence_condition left ∧ₘ
      finite_sequence_condition right
  let membership : SetFormula := index ∈ₘ domₘ(right)
  let Γ : Context signature := [membership, precondition]
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hPrecondition :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        precondition :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hMembership :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        membership :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hSpec :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        finite_sequence_concatenation_spec
          left right (left ⌢ₘ right) :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken (Γ := []) (Δ := Γ) (by simp [Γ]) <|
        finite_sequence_concatenation_self_spec_derives
          left right hLeft hRight)
      hPrecondition
  have hPointwise :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        ∀ₘ[SetSort.set],
          finite_sequence_concatenation_right_condition
            left right (left ⌢ₘ right) bₛ#0 :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight <|
        FirstOrder.Derives.conjElimRight hSpec
  have hAtIndex :=
    FirstOrder.Derives.forall_elim
      (term := index) hPointwise
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  have hAtIndex' :
      Γ ⊢ₘ[finite_sequence_concatenation_theory]
        membership ⟶ₘ ((((domₘ(left) +ₘ index) ∈ₘ
              domₘ(left ⌢ₘ right))) ∧ₘ (((left ⌢ₘ right) ·ₘ (domₘ(left) +ₘ index)) ≐ₘ (right ·ₘ index))) := by
    simpa [membership,
      finite_sequence_concatenation_right_condition,
      Formula.openAt, Term.openAt,
      hLeftOpen, hRightOpen] using hAtIndex
  exact FirstOrder.Derives.impElim hAtIndex' hMembership
/-- 合并结果的定义域包含右段定义域的平移像。 -/
theorem finite_sequence_concatenation_right_domain_derives (left right index : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[finite_sequence_concatenation_theory] (finite_sequence_condition left ∧ₘ
          finite_sequence_condition right) ⟶ₘ (index ∈ₘ domₘ(right)) ⟶ₘ ((domₘ(left) +ₘ index) ∈ₘ
            domₘ(left ⌢ₘ right)) := by
  have hPoint :=
    finite_sequence_concatenation_right_point_derives
      left right index hLeft hRight hIndex
  derive_prop
/-- 合并结果在右段平移位置上逐点读取右序列。 -/
theorem finite_sequence_concatenation_right_value_derives (left right index : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hIndex : Term.Admissible index SetSort.set) :
    ⊢ₘ[finite_sequence_concatenation_theory] (finite_sequence_condition left ∧ₘ
          finite_sequence_condition right) ⟶ₘ (index ∈ₘ domₘ(right)) ⟶ₘ (((left ⌢ₘ right) ·ₘ (domₘ(left) +ₘ index)) ≐ₘ (right ·ₘ index)) := by
  have hPoint :=
    finite_sequence_concatenation_right_point_derives
      left right index hLeft hRight hIndex
  derive_prop
/-- 有限序列空间定义公理可在两个 admissible 项处直接实例化。 -/
theorem finite_sequence_space_definition_instance_derives (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[finite_sequence_space_theory]
      finite_sequence_space_definition_instance source candidate := by
  have hAxiom :
      ⊢ₘ[finite_sequence_space_theory]
        finite_sequence_space_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hSourceInstance := FirstOrder.Derives.forall_elim
    (term := source) hAxiom
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hSourceInstance
  have hSourceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term source hSource.2
  simpa [finite_sequence_space_definition_axiom,
    finite_sequence_space_definition_instance,
    finite_sequence_space_spec,
    finite_sequence_member_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hSourceOpen] using hCandidateInstance
/-- 非空有限序列空间定义公理可在两个 admissible 项处直接实例化。 -/
theorem nonempty_finite_sequence_space_definition_instance_derives (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[nonempty_finite_sequence_space_theory]
      nonempty_finite_sequence_space_definition_instance
        source candidate := by
  have hAxiom :
      ⊢ₘ[nonempty_finite_sequence_space_theory]
        nonempty_finite_sequence_space_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hSourceInstance := FirstOrder.Derives.forall_elim
    (term := source) hAxiom
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hSourceInstance
  have hSourceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term source hSource.2
  have hCandidateOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term candidate = candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term candidate hCandidate.2
  simpa [nonempty_finite_sequence_space_definition_axiom,
    nonempty_finite_sequence_space_definition_instance,
    nonempty_finite_sequence_space_spec,
    nonempty_finite_sequence_member_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, finite_numeral_term,
    hSourceOpen, hCandidateOpen] using
      hCandidateInstance
/-- 有限序列族折叠定义公理可在两个 admissible 项处直接实例化。 -/
theorem finite_sequence_flatten_definition_instance_derives (family result : SetTerm) (hFamily : Term.Admissible family SetSort.set)
    (hResult : Term.Admissible result SetSort.set) :
    ⊢ₘ[finite_sequence_flatten_theory]
      finite_sequence_flatten_definition_instance family result := by
  have hAxiom :
      ⊢ₘ[finite_sequence_flatten_theory]
        finite_sequence_flatten_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hFamilyInstance := FirstOrder.Derives.forall_elim
    (term := family) hAxiom
  have hResultInstance := FirstOrder.Derives.forall_elim
    (term := result) hFamilyInstance
  have hFamilyOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term family = family :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term family hFamily.2
  simpa [finite_sequence_flatten_definition_axiom,
    finite_sequence_flatten_definition_instance,
    finite_sequence_flatten_spec,
    finite_sequence_flatten_step_condition,
    finite_sequence_family_condition,
    finite_sequence_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, finite_numeral_term,
    hFamilyOpen] using hResultInstance
/-- 变量编码运算符的对象理论定义合同。 -/
theorem variable_code_definition_instance_derives (index candidate : SetTerm) (hIndex : Term.Admissible index SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[symbol_code_operator_theory]
      variable_code_definition_instance index candidate := by
  have hAxiom :
      ⊢ₘ[symbol_code_operator_theory]
        symbol_code_operator_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hVariableAxiom := FirstOrder.Derives.conjElimLeft hAxiom
  have hIndexInstance := FirstOrder.Derives.forall_elim
    (term := index) hVariableAxiom
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hIndexInstance
  have hIndexOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term index = index :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term index hIndex.2
  simpa [symbol_code_operator_definition_axiom,
    variable_code_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, finite_numeral_term,
    hIndexOpen] using hCandidateInstance
/-- 常元编码运算符的对象理论定义合同。 -/
theorem constant_code_definition_instance_derives (index candidate : SetTerm) (hIndex : Term.Admissible index SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[symbol_code_operator_theory]
      constant_code_definition_instance index candidate := by
  have hAxiom :
      ⊢ₘ[symbol_code_operator_theory]
        symbol_code_operator_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hConstantAxiom := FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight hAxiom)
  have hIndexInstance := FirstOrder.Derives.forall_elim
    (term := index) hConstantAxiom
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hIndexInstance
  have hIndexOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term index = index :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term index hIndex.2
  simpa [symbol_code_operator_definition_axiom,
    constant_code_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, finite_numeral_term,
    hIndexOpen] using hCandidateInstance
/-- 等式公式编码运算符的对象理论定义合同。 -/
theorem equality_formula_code_definition_instance_derives (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[formula_constructor_theory]
      equality_formula_code_definition_instance
        left right candidate := by
  have hAxiom :
      ⊢ₘ[formula_constructor_theory]
        formula_constructor_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hEqualityAxiom := FirstOrder.Derives.conjElimLeft hAxiom
  have hLeftInstance := FirstOrder.Derives.forall_elim
    (term := left) hEqualityAxiom
  have hRightInstance := FirstOrder.Derives.forall_elim
    (term := right) hLeftInstance
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hRightInstance
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  simpa [formula_constructor_definition_axiom,
    equality_formula_code_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, logical_symbol_exponent,
    finite_numeral_term, hLeftOpen, hRightOpen] using
      hCandidateInstance
/-- 否定公式编码运算符的对象理论定义合同。 -/
theorem negation_formula_code_definition_instance_derives (body candidate : SetTerm) (hBody : Term.Admissible body SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[formula_constructor_theory]
      negation_formula_code_definition_instance body candidate := by
  have hAxiom :
      ⊢ₘ[formula_constructor_theory]
        formula_constructor_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hNegationAxiom := FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight hAxiom))
  have hBodyInstance := FirstOrder.Derives.forall_elim
    (term := body) hNegationAxiom
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hBodyInstance
  have hBodyOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term body = body :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term body hBody.2
  simpa [formula_constructor_definition_axiom,
    negation_formula_code_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, logical_symbol_exponent,
    finite_numeral_term, hBodyOpen] using hCandidateInstance
/-- 蕴含公式编码运算符的对象理论定义合同。 -/
theorem implication_formula_code_definition_instance_derives (left right candidate : SetTerm) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[formula_constructor_theory]
      implication_formula_code_definition_instance
        left right candidate := by
  have hAxiom :
      ⊢ₘ[formula_constructor_theory]
        formula_constructor_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hImplicationAxiom := FirstOrder.Derives.conjElimLeft (FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimRight hAxiom)))
  have hLeftInstance := FirstOrder.Derives.forall_elim
    (term := left) hImplicationAxiom
  have hRightInstance := FirstOrder.Derives.forall_elim
    (term := right) hLeftInstance
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hRightInstance
  have hLeftOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term left = left :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term left hLeft.2
  have hRightOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term right hRight.2
  simpa [formula_constructor_definition_axiom,
    implication_formula_code_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, logical_symbol_exponent,
    finite_numeral_term, hLeftOpen, hRightOpen] using hCandidateInstance
/-- 全称公式编码运算符的对象理论定义合同。 -/
theorem universal_formula_code_definition_instance_derives (boundVariable body candidate : SetTerm) (hBoundVariable : Term.Admissible boundVariable SetSort.set)
    (hBody : Term.Admissible body SetSort.set) (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[formula_constructor_theory]
      universal_formula_code_definition_instance
        boundVariable body candidate := by
  have hAxiom :
      ⊢ₘ[formula_constructor_theory]
        formula_constructor_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hUniversalAxiom := FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight
        (FirstOrder.Derives.conjElimRight hAxiom)))
  have hVariableInstance := FirstOrder.Derives.forall_elim
    (term := boundVariable) hUniversalAxiom
  have hBodyInstance := FirstOrder.Derives.forall_elim
    (term := body) hVariableInstance
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hBodyInstance
  have hVariableOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term boundVariable = boundVariable :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term boundVariable hBoundVariable.2
  have hBodyOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term body = body :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term body hBody.2
  simpa [formula_constructor_definition_axiom,
    universal_formula_code_definition_instance,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, logical_symbol_exponent,
    finite_numeral_term, hVariableOpen, hBodyOpen] using
      hCandidateInstance
/-! ## 替换合同 -/
/--
编码级替换定义公理的安全实例：在前置编码条件下，函数项的值恰好满足逐位置替换
规格。`310`、`311` 是该规格内部的保留 binder 编号。
-/
theorem code_substitution_definition_instance_derives (source boundVariable replacement candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hBoundVariable : Term.Admissible boundVariable SetSort.set) (hReplacement : Term.Admissible replacement SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) (hFresh : ReservedIdsFresh [310, 311]
      [source, boundVariable, replacement, candidate]) :
    ⊢ₘ[substitution_variable_theory]
      code_substitution_definition_instance
        source boundVariable replacement candidate := by
  have hAxiom :
      ⊢ₘ[substitution_variable_theory]
        substitution_variable_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hSubstitutionAxiom := FirstOrder.Derives.conjElimLeft hAxiom
  have hSourceInstance := FirstOrder.Derives.forall_elim
    (term := source) hSubstitutionAxiom
  have hBoundVariableInstance := FirstOrder.Derives.forall_elim
    (term := boundVariable) hSourceInstance
  have hReplacementInstance := FirstOrder.Derives.forall_elim
    (term := replacement) hBoundVariableInstance
  have hCandidateInstance := FirstOrder.Derives.forall_elim
    (term := candidate) hReplacementInstance
  have hSourceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term source hSource.2
  have hBoundVariableOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term boundVariable = boundVariable :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term boundVariable hBoundVariable.2
  have hReplacementOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term replacement = replacement :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term replacement hReplacement.2
  have hSourceClose310 (depth : Nat) :
      Term.closeFreeAt SetSort.set 310 depth source = source :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 310 depth source hSource.2 (hFresh source (by simp) 310 (by simp))
  have hSourceClose311 (depth : Nat) :
      Term.closeFreeAt SetSort.set 311 depth source = source :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 311 depth source hSource.2 (hFresh source (by simp) 311 (by simp))
  have hBoundVariableClose310 (depth : Nat) :
      Term.closeFreeAt SetSort.set 310 depth boundVariable =
        boundVariable :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 310 depth boundVariable hBoundVariable.2 (hFresh boundVariable (by simp) 310 (by simp))
  have hBoundVariableClose311 (depth : Nat) :
      Term.closeFreeAt SetSort.set 311 depth boundVariable =
        boundVariable :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 311 depth boundVariable hBoundVariable.2 (hFresh boundVariable (by simp) 311 (by simp))
  have hReplacementClose310 (depth : Nat) :
      Term.closeFreeAt SetSort.set 310 depth replacement = replacement :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 310 depth replacement hReplacement.2 (hFresh replacement (by simp) 310 (by simp))
  have hReplacementClose311 (depth : Nat) :
      Term.closeFreeAt SetSort.set 311 depth replacement = replacement :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 311 depth replacement hReplacement.2 (hFresh replacement (by simp) 311 (by simp))
  have hCandidateClose310 (depth : Nat) :
      Term.closeFreeAt SetSort.set 310 depth candidate = candidate :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 310 depth candidate hCandidate.2 (hFresh candidate (by simp) 310 (by simp))
  simpa [substitution_variable_definition_axiom,
    code_substitution_definition_axiom,
    code_substitution_definition_instance,
    code_substitution_spec, substitution_piece_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, finite_numeral_term,
    hSourceOpen, hBoundVariableOpen, hReplacementOpen,
    hSourceClose310, hSourceClose311,
    hBoundVariableClose310, hBoundVariableClose311,
    hReplacementClose310, hReplacementClose311,
    hCandidateClose310] using hCandidateInstance
/--
变量收集定义公理的安全实例。`312` 是变量出现位置见证，`313` 是逐个考察变量符号
时使用的保留 binder 编号。
-/
theorem variable_collection_definition_instance_derives (source candidate : SetTerm) (hSource : Term.Admissible source SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) (hFresh : ReservedIdsFresh [312, 313] [source, candidate]) :
    ⊢ₘ[substitution_variable_theory]
      variable_collection_definition_instance source candidate := by
  have hAxiom :
      ⊢ₘ[substitution_variable_theory]
        substitution_variable_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hCollectionAxiom :=
    FirstOrder.Derives.conjElimRight hAxiom
  have hSourceInstance :=
    FirstOrder.Derives.forall_elim
      (term := source) hCollectionAxiom
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim
      (term := candidate) hSourceInstance
  have hSourceOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term source = source :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term source hSource.2
  have hCandidateOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term candidate = candidate :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term candidate hCandidate.2
  have hSourceClose313 (depth : Nat) :
      Term.closeFreeAt SetSort.set 313 depth source = source :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 313 depth source hSource.2 (hFresh source (by simp) 313 (by simp))
  have hSourceClose312 (depth : Nat) :
      Term.closeFreeAt SetSort.set 312 depth source = source :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 312 depth source hSource.2 (hFresh source (by simp) 312 (by simp))
  have hCandidateClose313 (depth : Nat) :
      Term.closeFreeAt SetSort.set 313 depth candidate = candidate :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set 313 depth candidate hCandidate.2 (hFresh candidate (by simp) 313 (by simp))
  simpa [substitution_variable_definition_axiom,
    variable_collection_definition_axiom,
    variable_collection_definition_instance,
    variable_collection_spec,
    variable_symbol_occurs_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, finite_numeral_term,
    hSourceOpen, hCandidateOpen,
    hSourceClose312, hSourceClose313,
    hCandidateClose313] using
      hCandidateInstance
/-! ## 逻辑规则合同 -/
/--
在任意闭对象项处，`logical_axiom_codeₘ` 与完整逻辑公理码集合成员关系等价。
这只展开逻辑公理谓词的定义公理；外部 Hilbert 公理的实际正向枚举由更外层的
`HilbertCodeRepresentation` 桥接理论提供，避免在这里假定尚未完成的句法反演。
-/
theorem logical_axiom_code_iff_logic_axiom_set_member (code : SetTerm) (hCode : Term.Admissible code SetSort.set) :
    ⊢ₘ[logical_axiom_code_theory]
      logical_axiom_codeₘ(code) ↔ₘ (code ∈ₘ LogicAxiomsₘ) := by
  have hAxiom :
      ⊢ₘ[logical_axiom_code_theory]
        logical_axiom_code_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hPredicateDefinition :=
    FirstOrder.Derives.conjElimRight (FirstOrder.Derives.conjElimRight hAxiom)
  have hInstance := FirstOrder.Derives.forall_elim
    (term := code) hPredicateDefinition
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  simpa [logical_axiom_code_definition_axiom,
    is_logical_axiom_code_definition_axiom,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hCodeOpen] using hInstance
/--
完整逻辑公理集合的成员关系可精确反演为十二类基础模式，或一次 canonical 全称闭包。
这是 `LogicAxiomsₘ` 最小固定点定义的公共消去接口。闭项条件保证实例化不会捕获生成
条件内部保留的 witness 编号；后续证书化对象表示只需继续反演右侧两个分支。
-/
theorem logical_axiom_set_member_iff_generation (code : SetTerm) (hCode : Term.Admissible code SetSort.set) (hClosed : Term.freeSupport code = []) :
    ⊢ₘ[logical_axiom_code_theory] (code ∈ₘ LogicAxiomsₘ) ↔ₘ
        logical_axiom_code_generation_condition
          LogicAxiomsₘ code := by
  have hAxiom :
      ⊢ₘ[logical_axiom_code_theory]
        logical_axiom_code_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hSetDefinition :=
    FirstOrder.Derives.conjElimLeft <|
      FirstOrder.Derives.conjElimRight hAxiom
  have hGenerated :=
    FirstOrder.Derives.conjElimRight <|
      FirstOrder.Derives.conjElimRight hSetDefinition
  have hInstance :=
    FirstOrder.Derives.forall_elim
      (term := code) hGenerated
  have hCodeOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term code = code :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term code hCode.2
  have hCodeClose (id : FreeVarId) (depth : Nat) :
      Term.closeFreeAt SetSort.set id depth code = code :=
    Term.closeFreeAt_eq_self_of_boundClosed_of_not_mem
      SetSort.set id depth code hCode.2 <| by
        rw [hClosed]
        exact List.not_mem_nil
  have hCodeFresh (id : FreeVarId) : (SetSort.set, id) ∉ Term.freeSupport code := by
    rw [hClosed]
    exact List.not_mem_nil
  have hCodeSubstitute (id : FreeVarId) (replacement : SetTerm) :
      Term.substituteFree SetSort.set id replacement code = code :=
    Term.substituteFree_eq_self_of_not_mem
      SetSort.set id replacement code <| by
      rw [hClosed]
      exact List.not_mem_nil
  have hFreeVariableConditionFixed :
      Formula.substituteFree SetSort.set 456 code (canonical_free_variable_code_condition_with_id (x#455) 470) =
        canonical_free_variable_code_condition_with_id (x#455) 470 := by
    apply Formula.substituteFree_eq_self_of_not_mem
    native_decide
  have hBinderShiftConditionFixed :
      Formula.substituteFree SetSort.set 456 code (canonical_binder_shift_code_condition_with_ids (x#454) (x#460)
            462 463 464 465 466 467 468 469) =
        canonical_binder_shift_code_condition_with_ids (x#454) (x#460)
          462 463 464 465 466 467 468 469 := by
    apply Formula.substituteFree_eq_self_of_not_mem
    native_decide
  have hCodeSubstitutionConditionFixed :
      Formula.substituteFree SetSort.set 456 code (code_substitution_spec (x#460) (x#455)
            canonical_outer_binder_variable_code_term (x#461)) =
        code_substitution_spec (x#460) (x#455)
          canonical_outer_binder_variable_code_term (x#461) := by
    apply Formula.substituteFree_eq_self_of_not_mem
    native_decide
  have hFormulaCodeConditionFixed :
      Formula.substituteFree SetSort.set 456 code (formula_codeₘ(x#461)) =
        formula_codeₘ(x#461) := by
    apply Formula.substituteFree_eq_self_of_not_mem
    native_decide
  have hOuterBinderCodeFixed :
      Term.substituteFree SetSort.set 456 code
          canonical_outer_binder_variable_code_term =
        canonical_outer_binder_variable_code_term := by
    apply Term.substituteFree_eq_self_of_not_mem
    native_decide
  have hClosureSubstitute :
      Formula.substituteFree SetSort.set 456 code (canonical_forall_closure_code_condition (x#454) (x#455) (x#456)) =
        canonical_forall_closure_code_condition (x#454) (x#455) code := by
    unfold canonical_forall_closure_code_condition
    unfold canonical_forall_closure_code_condition_with_ids
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 456 460 0 code _ (by native_decide) hCode.2 (hCodeFresh 460)]
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 456 461 0 code _ (by native_decide) hCode.2 (hCodeFresh 461)]
    simp [Formula.substituteFree, Term.substituteFree,
      set_variable,
      is_formula_code_formula,
      universal_formula_code_term,
      hFreeVariableConditionFixed,
      hBinderShiftConditionFixed,
      hCodeSubstitutionConditionFixed,
      hOuterBinderCodeFixed]
  have hClosedClosureSubstitute :
      Formula.substituteFree SetSort.set 456 code (Formula.closeFreeAt SetSort.set 454 1 (Formula.closeFreeAt SetSort.set 455 0
              (canonical_forall_closure_code_condition (x#454) (x#455) (x#456)))) =
        Formula.closeFreeAt SetSort.set 454 1 (Formula.closeFreeAt SetSort.set 455 0 (canonical_forall_closure_code_condition (x#454) (x#455) code)) := by
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 456 454 1 code _ (by native_decide) hCode.2 (hCodeFresh 454)]
    rw [← Formula.closeFreeAt_substituteFree_comm
      SetSort.set 456 455 0 code _ (by native_decide) hCode.2 (hCodeFresh 455)]
    exact congrArg (Formula.closeFreeAt SetSort.set 454 1) <|
        congrArg (Formula.closeFreeAt SetSort.set 455 0)
          hClosureSubstitute
  simpa [logical_axiom_code_definition_axiom,
    logical_axiom_set_definition_axiom,
    logical_axiom_set_spec,
    logical_axiom_code_generated_condition,
    logical_axiom_code_generation_condition,
    base_logical_axiom_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hCodeOpen, hCodeClose,
    hCodeSubstitute, hClosedClosureSubstitute] using hInstance
/--
`modus_ponensₘ` 在三个 admissible 实参处等价于其明示的公式码与蕴含码条件。
这条合同只展开 MP 的定义公理，不预设任何基础逻辑公理模式已经完成对象编码。
-/
theorem modus_ponens_iff_condition (premise implication conclusion : SetTerm) (hPremise : Term.Admissible premise SetSort.set)
    (hImplication : Term.Admissible implication SetSort.set) (hConclusion : Term.Admissible conclusion SetSort.set) :
    ⊢ₘ[logical_rule_encoding_theory]
      modus_ponensₘ(premise, implication, conclusion) ↔ₘ
        modus_ponens_condition premise implication conclusion := by
  have hAxiom :
      ⊢ₘ[logical_rule_encoding_theory]
        modus_ponens_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hPremiseInstance := FirstOrder.Derives.forall_elim
    (term := premise) hAxiom
  have hImplicationInstance := FirstOrder.Derives.forall_elim
    (term := implication) hPremiseInstance
  have hConclusionInstance := FirstOrder.Derives.forall_elim
    (term := conclusion) hImplicationInstance
  have hPremiseOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term premise = premise :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term premise hPremise.2
  have hImplicationOpen (depth : Nat) (term : SetTerm) :
      Term.openAt SetSort.set depth term implication = implication :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set depth term implication hImplication.2
  simpa [modus_ponens_definition_axiom,
    modus_ponens_condition,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, hPremiseOpen,
    hImplicationOpen] using hConclusionInstance
/--
在任意包含逻辑规则编码理论的对象理论中，三条公式码证书和蕴含码等式足以推出
一次对象化 modus ponens。
-/
theorem modus_ponens_derives_of_condition
    {T : SetTheory} (hLogicalRules :
      ∀ formula : SetFormula,
        logical_rule_encoding_theory formula → T formula) (premise implication conclusion : SetTerm) (hPremise : Term.Admissible premise SetSort.set)
    (hImplication : Term.Admissible implication SetSort.set) (hConclusion : Term.Admissible conclusion SetSort.set) (hPremiseFormulaCode :
      ⊢ₘ[T] formula_codeₘ(premise)) (hImplicationFormulaCode :
      ⊢ₘ[T] formula_codeₘ(implication)) (hConclusionFormulaCode :
      ⊢ₘ[T] formula_codeₘ(conclusion)) (hImplicationCode :
      ⊢ₘ[T] implication ≐ₘ imp_codeₘ(premise, conclusion)) :
    ⊢ₘ[T] modus_ponensₘ(premise, implication, conclusion) := by
  have hIff :
      ⊢ₘ[T]
        modus_ponensₘ(premise, implication, conclusion) ↔ₘ
          modus_ponens_condition premise implication conclusion :=
    FirstOrder.Derives.theory_weaken hLogicalRules (modus_ponens_iff_condition
        premise implication conclusion
        hPremise hImplication hConclusion)
  apply FirstOrder.Derives.iffElimLeft hIff
  apply FirstOrder.Derives.conjIntro
  · apply FirstOrder.Derives.conjIntro
    · exact FirstOrder.Derives.conjIntro
        hPremiseFormulaCode hConclusionFormulaCode
    · exact hImplicationFormulaCode
  · exact hImplicationCode
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
