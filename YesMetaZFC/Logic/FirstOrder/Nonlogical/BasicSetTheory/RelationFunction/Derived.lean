import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationFunction.Core
/-!
# 有序对投影与反转的派生理论
本模块建立投影函数、反转函数、唯一性及文献闭包接口。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory
open scoped Symbols
/-- “是有序对”谓词推出左投影存在。 -/
theorem is_ordered_pair_implies_left_projection_exists (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[relation_function_theory]
      is_ordered_pair_formula pair ⟶ₘ
        left_projection_exists pair := by
  have hPredicateAdmissible :
      Formula.Admissible (is_ordered_pair_formula pair) :=
    is_ordered_pair_formula_admissible hPair
  nd_apply FirstOrder.Derives.impIntro
  let predicate :=
    is_ordered_pair_formula pair
  have hDefinition :
      [predicate] ⊢ₘ[relation_function_theory]
        is_ordered_pair_definition_instance pair :=
    FirstOrder.Derives.context_weaken_cons (is_ordered_pair_definition_instance_derives
        pair hPair)
  have hPredicate :
      [predicate] ⊢ₘ[relation_function_theory]
        is_ordered_pair_formula pair := by
    simpa [predicate] using (show
        [predicate] ⊢ₘ[relation_function_theory]
          predicate from
        .assumption (by simp))
  have hCondition :
      [predicate] ⊢ₘ[relation_function_theory]
        is_ordered_pair_condition pair :=
    FirstOrder.Derives.iffElimRight
      hDefinition hPredicate
  have hBridge :
      [predicate] ⊢ₘ[relation_function_theory]
        is_ordered_pair_condition pair ⟶ₘ
          left_projection_exists pair :=
    FirstOrder.Derives.context_weaken_cons (is_ordered_pair_condition_implies_left_projection_exists
        pair hPair)
  exact FirstOrder.Derives.impElim
    hBridge hCondition
/-- 有序对谓词背景下，左投影规格仍保持唯一。 -/
theorem is_ordered_pair_left_projection_unique (pair left right : SetTerm) (hPair : Term.Admissible pair SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_function_theory]
      is_ordered_pair_formula pair ⟶ₘ
        left_projection_spec pair left ⟶ₘ
          left_projection_spec pair right ⟶ₘ (left ≐ₘ right) := by
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.context_weaken_cons <|
    FirstOrder.Derives.of_empty (left_projection_unique
        pair left right hPair hLeft hRight)
/-- 有序对谓词背景下，两个左投影规格的合取推出候选相等。 -/
theorem is_ordered_pair_left_projection_functional (pair left right : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_function_theory]
      is_ordered_pair_formula pair ⟶ₘ ((left_projection_spec pair left ∧ₘ
            left_projection_spec pair right) ⟶ₘ (left ≐ₘ right)) := by
  have hUnique :=
    is_ordered_pair_left_projection_unique
      pair left right hPair hLeft hRight
  have hPredicateAdmissible :=
    is_ordered_pair_formula_admissible hPair
  have hLeftSpecAdmissible :=
    left_projection_spec_admissible hPair hLeft
  have hRightSpecAdmissible :=
    left_projection_spec_admissible hPair hRight
  have hConjunctionAdmissible :
      Formula.Admissible (left_projection_spec pair left ∧ₘ
          left_projection_spec pair right) :=
    Formula.Admissible.conj
      hLeftSpecAdmissible hRightSpecAdmissible
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  have hUnique' :=
    FirstOrder.Derives.context_weaken_cons (assumption :=
        left_projection_spec pair left ∧ₘ
          left_projection_spec pair right) <|
      FirstOrder.Derives.context_weaken_cons (assumption := is_ordered_pair_formula pair)
        hUnique
  have hPredicate :
      [left_projection_spec pair left ∧ₘ
          left_projection_spec pair right,
        is_ordered_pair_formula pair]
        ⊢ₘ[relation_function_theory]
          is_ordered_pair_formula pair :=
    .assumption (by simp)
  have hConjunction :
      [left_projection_spec pair left ∧ₘ
          left_projection_spec pair right,
        is_ordered_pair_formula pair]
        ⊢ₘ[relation_function_theory]
          left_projection_spec pair left ∧ₘ
            left_projection_spec pair right :=
    .assumption (by simp)
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hUnique' hPredicate) (FirstOrder.Derives.conjElimLeft
        hConjunction)) (FirstOrder.Derives.conjElimRight
      hConjunction)
/-! ## 投影函数符号的实例化合同 -/
/-- 左投影定义公理可在任意 admissible 集合项处实例化。 -/
theorem left_projection_definition_instance_derives (pair candidate : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[left_projection_operator_theory]
      left_projection_definition_instance
        pair candidate := by
  have hAxiom :
      ⊢ₘ[left_projection_operator_theory]
        left_projection_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hPairInstance :=
    FirstOrder.Derives.forall_elim (term := pair) hAxiom
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim (term := candidate) hPairInstance
  have hPairOpenZeroCandidate :
      Term.openAt SetSort.set 0 candidate pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate pair hPair.2
  have hPairOpenOneCandidate :
      Term.openAt SetSort.set 1 candidate pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate pair hPair.2
  have hPairOpenTwoCandidate :
      Term.openAt SetSort.set 2 candidate pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 2 candidate pair hPair.2
  simpa [left_projection_definition_axiom,
    left_projection_definition_instance,
    left_projection_spec,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, left_projection_term,
    hPairOpenZeroCandidate, hPairOpenOneCandidate,
    hPairOpenTwoCandidate] using hCandidateInstance
/-- 右投影定义公理可在任意 admissible 集合项处实例化。 -/
theorem right_projection_definition_instance_derives (pair candidate : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[right_projection_operator_theory]
      right_projection_definition_instance
        pair candidate := by
  have hAxiom :
      ⊢ₘ[right_projection_operator_theory]
        right_projection_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hPairInstance :=
    FirstOrder.Derives.forall_elim (term := pair) hAxiom
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim (term := candidate) hPairInstance
  have hPairOpenZeroCandidate :
      Term.openAt SetSort.set 0 candidate pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate pair hPair.2
  have hPairOpenOneCandidate :
      Term.openAt SetSort.set 1 candidate pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate pair hPair.2
  simpa [right_projection_definition_axiom,
    right_projection_definition_instance,
    right_projection_spec,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, right_projection_term,
    ordered_pair_term, hPairOpenZeroCandidate,
    hPairOpenOneCandidate] using
    hCandidateInstance
/-- 有序对反转定义公理可在任意 admissible 集合项处实例化。 -/
theorem ordered_pair_reverse_definition_instance_derives (pair candidate : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[ordered_pair_reverse_operator_theory]
      ordered_pair_reverse_definition_instance
        pair candidate := by
  have hAxiom :
      ⊢ₘ[ordered_pair_reverse_operator_theory]
        ordered_pair_reverse_definition_axiom :=
    FirstOrder.Derives.theory_mem (by exact Or.inl rfl)
  have hPairInstance :=
    FirstOrder.Derives.forall_elim (term := pair) hAxiom
  have hCandidateInstance :=
    FirstOrder.Derives.forall_elim (term := candidate) hPairInstance
  have hPairOpenZeroCandidate :
      Term.openAt SetSort.set 0 candidate pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 candidate pair hPair.2
  have hPairOpenOneCandidate :
      Term.openAt SetSort.set 1 candidate pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 1 candidate pair hPair.2
  simpa [ordered_pair_reverse_definition_axiom,
    ordered_pair_reverse_definition_instance,
    ordered_pair_reverse_spec,
    Formula.openAt_closeFreeAt_eq_substituteFree,
    Formula.openAt, Formula.closeFreeAt,
    Formula.next_depth, Formula.substituteFree,
    Term.openAt, Term.closeFreeAt,
    Term.substituteFree, set_variable,
    set_bound_variable, left_projection_term,
    right_projection_term, ordered_pair_term,
    ordered_pair_reverse_term,
    hPairOpenZeroCandidate,
    hPairOpenOneCandidate] using hCandidateInstance
/-! ## 规范有序对上的投影 -/
/-- 左投影函数项在规范有序对上返回第一坐标。 -/
theorem ordered_pair_term_left_projection_eq (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[left_projection_operator_theory] (⟨left, right⟩ₘ)₀ₘ ≐ₘ left := by
  let pair := ordered_pair_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    ordered_pair_term_admissible
      left right hLeft hRight
  have hDefinition :
      ⊢ₘ[left_projection_operator_theory]
        left_projection_definition_instance
          pair left :=
    left_projection_definition_instance_derives
      pair left hPair hLeft
  have hIsOrdered :
      ⊢ₘ[left_projection_operator_theory]
        is_ordered_pair_formula pair :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_function_theory_subset_left_projection_operator_theory
          hFormula) (by
        simpa [pair] using
          ordered_pair_term_is_ordered_pair_derives
            left right hLeft hRight)
  have hSpec :
      ⊢ₘ[left_projection_operator_theory]
        left_projection_spec pair left :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_left_projection_operator_theory
          hFormula) (by
        simpa [pair] using
          ordered_pair_term_left_projection_spec
            left right hLeft hRight)
  have hGraph :
      ⊢ₘ[left_projection_operator_theory] ((pair)₀ₘ ≐ₘ left) ↔ₘ
          left_projection_spec pair left :=
    FirstOrder.Derives.impElim
      hDefinition hIsOrdered
  simpa [pair] using
    FirstOrder.Derives.iffElimLeft
      hGraph hSpec
/-- 规范有序对满足第二坐标的右投影规格。 -/
theorem ordered_pair_term_right_projection_spec (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[ordered_pair_operator_theory]
      right_projection_spec
        ⟨left, right⟩ₘ right := by
  let pair := ordered_pair_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    ordered_pair_term_admissible
      left right hLeft hRight
  unfold right_projection_spec
  nd_apply FirstOrder.Derives.exists_intro (term := left)
  have hPairOpenZero :
      Term.openAt SetSort.set 0 left pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 left pair hPair.2
  have hRightOpenZero :
      Term.openAt SetSort.set 0 left right = right :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 left right hRight.2
  simpa [pair, ordered_pair_term,
    Formula.openAt, Term.openAt,
    hPairOpenZero, hRightOpenZero] using
      (FirstOrder.Derives.eq_refl_m
        (T := ordered_pair_operator_theory) (Γ := [])
        (sort := SetSort.set) pair)
/-- 右投影函数项在规范有序对上返回第二坐标。 -/
theorem ordered_pair_term_right_projection_eq (left right : SetTerm) (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[right_projection_operator_theory] (⟨left, right⟩ₘ)₁ₘ ≐ₘ right := by
  let pair := ordered_pair_term left right
  have hPair :
      Term.Admissible pair SetSort.set :=
    ordered_pair_term_admissible
      left right hLeft hRight
  have hDefinition :
      ⊢ₘ[right_projection_operator_theory]
        right_projection_definition_instance
          pair right :=
    right_projection_definition_instance_derives
      pair right hPair hRight
  have hIsOrdered :
      ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula pair :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        relation_function_theory_subset_right_projection_operator_theory
          hFormula) (by
        simpa [pair] using
          ordered_pair_term_is_ordered_pair_derives
            left right hLeft hRight)
  have hSpec :
      ⊢ₘ[right_projection_operator_theory]
        right_projection_spec pair right :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_right_projection_operator_theory
          hFormula) (by
        simpa [pair] using
          ordered_pair_term_right_projection_spec
            left right hLeft hRight)
  have hGraph :
      ⊢ₘ[right_projection_operator_theory] ((pair)₁ₘ ≐ₘ right) ↔ₘ
          right_projection_spec pair right :=
    FirstOrder.Derives.impElim
      hDefinition hIsOrdered
  simpa [pair] using
    FirstOrder.Derives.iffElimLeft
      hGraph hSpec
/-! ## 右投影存在性与唯一性 -/
/-- 有序对条件中的两个坐标可以直接重排为右投影见证。 -/
theorem is_ordered_pair_condition_implies_right_projection_exists (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ
      is_ordered_pair_condition pair ⟶ₘ
        right_projection_exists pair := by
  let condition :=
    is_ordered_pair_condition pair
  let conclusion :=
    right_projection_exists pair
  let left :=
    FreshVariable.fresh_id SetSort.set
      [condition, conclusion]
  let left_point : SetFormula :=
    ∃ₘ[SetSort.set],
      pair ≐ₘ ⟨x#left, bₛ#0⟩ₘ
  let right :=
    FreshVariable.fresh_id SetSort.set
      [condition, conclusion, left_point]
  let body : SetFormula :=
    pair ≐ₘ ⟨x#left, x#right⟩ₘ
  have hLeftFreshPair : (SetSort.set, left) ∉
        Term.freeSupport pair := by
    dsimp [left]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [condition, conclusion]) (formula := condition) (by simp)
    have hFresh' : (SetSort.set,
            FreshVariable.fresh_id SetSort.set
              [condition, conclusion]) ∉
            Term.freeSupport pair ∧ (SetSort.set,
            FreshVariable.fresh_id SetSort.set
              [condition, conclusion]) ∉
            Term.freeSupport ⟨bₛ#1, bₛ#0⟩ₘ := by
      simpa [condition, is_ordered_pair_condition,
        Formula.freeSupport] using hFresh
    exact hFresh'.1
  have hRightFreshPair : (SetSort.set, right) ∉
        Term.freeSupport pair := by
    dsimp [right]
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [condition, conclusion, left_point]) (formula := condition) (by simp)
    have hFresh' : (SetSort.set,
            FreshVariable.fresh_id SetSort.set
              [condition, conclusion, left_point]) ∉
            Term.freeSupport pair ∧ (SetSort.set,
            FreshVariable.fresh_id SetSort.set
              [condition, conclusion, left_point]) ∉
            Term.freeSupport ⟨bₛ#1, bₛ#0⟩ₘ := by
      simpa [condition, is_ordered_pair_condition,
        Formula.freeSupport] using hFresh
    exact hFresh'.1
  have hRightNeLeft : right ≠ left := by
    intro hEqual
    have hFresh :=
      FreshVariable.fresh_id_not_mem_m (sort := SetSort.set) (formulas := [condition, conclusion, left_point]) (formula := left_point) (by simp)
    have hMember : (SetSort.set, left) ∈
          Formula.freeSupport left_point := by
      simp only [left_point, Formula.freeSupport,
        Term.freeSupportList, Term.freeSupport]
      exact List.mem_append_right _ (List.mem_append_left _ List.mem_cons_self)
    have hMemberRight : (SetSort.set, right) ∈
          Formula.freeSupport left_point := by
      rw [hEqual]
      exact hMember
    exact hFresh hMemberRight
  have hCloseLeftPair (depth : Nat) :
      Term.closeFreeAt SetSort.set left depth pair =
        pair := by
    calc
      Term.closeFreeAt SetSort.set left depth pair =
          Term.closeFreeAt SetSort.set left depth (Term.openAt SetSort.set depth (x#left) pair) := by
        rw [Term.openAt_eq_self_of_boundClosed
          SetSort.set depth (x#left) pair hPair.2]
      _ = pair :=
        Term.closeFreeAt_openAt
          SetSort.set left depth pair hLeftFreshPair
  have hCloseRightPair (depth : Nat) :
      Term.closeFreeAt SetSort.set right depth pair =
        pair := by
    calc
      Term.closeFreeAt SetSort.set right depth pair =
          Term.closeFreeAt SetSort.set right depth (Term.openAt SetSort.set depth (x#right) pair) := by
        rw [Term.openAt_eq_self_of_boundClosed
          SetSort.set depth (x#right) pair hPair.2]
      _ = pair :=
        Term.closeFreeAt_openAt
          SetSort.set right depth pair hRightFreshPair
  have hExchange :
      ⊢ₘ (∃ₘ[SetSort.set, left],
          ∃ₘ[SetSort.set, right], body) ⟶ₘ (∃ₘ[SetSort.set, right],
          ∃ₘ[SetSort.set, left], body) :=
    FirstOrder.Metatheory.Derives.exists_exchange_imp (firstSort := SetSort.set) (secondSort := SetSort.set) (first := left) (second := right) (body := body)
      (by
        dsimp [body]
        exact Formula.Admissible.equal
          hPair (ordered_pair_term_admissible (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right)))
  simpa [condition, conclusion,
    is_ordered_pair_condition,
    right_projection_exists, body,
    Formula.closeFreeAt, Formula.next_depth,
    Term.closeFreeAt, set_variable,
    set_bound_variable, ordered_pair_term,
    hCloseLeftPair, hCloseRightPair,
    hRightNeLeft, Ne.symm hRightNeLeft] using hExchange
/-- “是有序对”谓词推出右投影存在。 -/
theorem is_ordered_pair_implies_right_projection_exists (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[relation_function_theory]
      is_ordered_pair_formula pair ⟶ₘ
        right_projection_exists pair := by
  nd_apply FirstOrder.Derives.impIntro
  let predicate :=
    is_ordered_pair_formula pair
  have hDefinition :
      [predicate] ⊢ₘ[relation_function_theory]
        is_ordered_pair_definition_instance pair :=
    FirstOrder.Derives.context_weaken_cons (is_ordered_pair_definition_instance_derives
        pair hPair)
  have hPredicate :
      [predicate] ⊢ₘ[relation_function_theory]
        is_ordered_pair_formula pair := by
    simpa [predicate] using (show
        [predicate] ⊢ₘ[relation_function_theory]
          predicate from
        .assumption (by simp))
  have hCondition :
      [predicate] ⊢ₘ[relation_function_theory]
        is_ordered_pair_condition pair :=
    FirstOrder.Derives.iffElimRight
      hDefinition hPredicate
  have hBridge :
      [predicate] ⊢ₘ[relation_function_theory]
        is_ordered_pair_condition pair ⟶ₘ
          right_projection_exists pair :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.of_empty (is_ordered_pair_condition_implies_right_projection_exists
          pair hPair)
  exact FirstOrder.Derives.impElim
    hBridge hCondition
/-! ## 投影函数项的规范合同 -/
/-- 在有序对谓词前提下，左投影函数项满足左投影规格。 -/
theorem is_ordered_pair_left_projection_term_spec (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[left_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ
        left_projection_spec pair (pair)₀ₘ := by
  nd_apply FirstOrder.Derives.impIntro
  let predicate :=
    is_ordered_pair_formula pair
  have hProjection :
      Term.Admissible (pair)₀ₘ SetSort.set :=
    left_projection_term_admissible pair hPair
  have hDefinition :
      [predicate] ⊢ₘ[left_projection_operator_theory]
        left_projection_definition_instance
          pair (pair)₀ₘ :=
    FirstOrder.Derives.context_weaken_cons (left_projection_definition_instance_derives
        pair (pair)₀ₘ hPair hProjection)
  have hPredicate :
      [predicate] ⊢ₘ[left_projection_operator_theory]
        is_ordered_pair_formula pair := by
    simpa [predicate] using (show
        [predicate] ⊢ₘ[left_projection_operator_theory]
          predicate from
        .assumption (by simp))
  have hGraph :
      [predicate] ⊢ₘ[left_projection_operator_theory] (((pair)₀ₘ ≐ₘ (pair)₀ₘ) ↔ₘ
          left_projection_spec pair (pair)₀ₘ) :=
    FirstOrder.Derives.impElim
      hDefinition hPredicate
  exact FirstOrder.Derives.iffElimRight
    hGraph (FirstOrder.Derives.eq_refl_m
      (T := left_projection_operator_theory) (Γ := [predicate])
      (sort := SetSort.set) (pair)₀ₘ)
/-- 在有序对谓词前提下，右投影函数项满足右投影规格。 -/
theorem is_ordered_pair_right_projection_term_spec (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[right_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ
        right_projection_spec pair (pair)₁ₘ := by
  nd_apply FirstOrder.Derives.impIntro
  let predicate :=
    is_ordered_pair_formula pair
  have hProjection :
      Term.Admissible (pair)₁ₘ SetSort.set :=
    right_projection_term_admissible pair hPair
  have hDefinition :
      [predicate] ⊢ₘ[right_projection_operator_theory]
        right_projection_definition_instance
          pair (pair)₁ₘ :=
    FirstOrder.Derives.context_weaken_cons (right_projection_definition_instance_derives
        pair (pair)₁ₘ hPair hProjection)
  have hPredicate :
      [predicate] ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula pair := by
    simpa [predicate] using (show
        [predicate] ⊢ₘ[right_projection_operator_theory]
          predicate from
        .assumption (by simp))
  have hGraph :
      [predicate] ⊢ₘ[right_projection_operator_theory] (((pair)₁ₘ ≐ₘ (pair)₁ₘ) ↔ₘ
          right_projection_spec pair (pair)₁ₘ) :=
    FirstOrder.Derives.impElim
      hDefinition hPredicate
  exact FirstOrder.Derives.iffElimRight
    hGraph (FirstOrder.Derives.eq_refl_m
      (T := right_projection_operator_theory) (Γ := [predicate])
      (sort := SetSort.set) (pair)₁ₘ)
/-! ## 有序对反转 -/
/-- 反转函数项满足交换两个投影的规范规格。 -/
theorem ordered_pair_reverse_term_spec_derives (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[ordered_pair_reverse_operator_theory]
      ordered_pair_reverse_spec pair pair⁻¹ₘ := by
  have hReverse :
      Term.Admissible pair⁻¹ₘ SetSort.set :=
    ordered_pair_reverse_term_admissible
      pair hPair
  have hDefinition :=
    ordered_pair_reverse_definition_instance_derives
      pair pair⁻¹ₘ hPair hReverse
  exact FirstOrder.Derives.iffElimRight
    hDefinition (FirstOrder.Derives.eq_refl_m
      (T := ordered_pair_reverse_operator_theory) (Γ := [])
      (sort := SetSort.set) pair⁻¹ₘ)
/-- 同一个有序对的两个规范反转候选必相等。 -/
theorem ordered_pair_reverse_unique (pair first second : SetTerm) (hPair : Term.Admissible pair SetSort.set) (_hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ
      ordered_pair_reverse_spec pair first ⟶ₘ
        ordered_pair_reverse_spec pair second ⟶ₘ (first ≐ₘ second) := by
  let left_projection :=
    left_projection_term pair
  let right_projection :=
    right_projection_term pair
  let swapped :=
    ordered_pair_term right_projection left_projection
  have hLeftProjection :
      Term.Admissible left_projection SetSort.set :=
    left_projection_term_admissible pair hPair
  have hRightProjection :
      Term.Admissible right_projection SetSort.set :=
    right_projection_term_admissible pair hPair
  have hSwapped :
      Term.Admissible swapped SetSort.set :=
    ordered_pair_term_admissible
      right_projection left_projection
      hRightProjection hLeftProjection
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [ordered_pair_reverse_spec pair second,
      ordered_pair_reverse_spec pair first]
  have hFirstEquality :
      Γ ⊢ₘ first ≐ₘ swapped := by
    simpa [Γ, ordered_pair_reverse_spec,
      swapped, left_projection,
      right_projection] using (show
        Γ ⊢ₘ ordered_pair_reverse_spec pair first from
        .assumption (by simp [Γ]))
  have hSecondEquality :
      Γ ⊢ₘ second ≐ₘ swapped := by
    simpa [Γ, ordered_pair_reverse_spec,
      swapped, left_projection,
      right_projection] using (show
        Γ ⊢ₘ ordered_pair_reverse_spec pair second from
        .assumption (by simp [Γ]))
  have hSecondSymmetry :
      Γ ⊢ₘ swapped ≐ₘ second :=
    FirstOrder.Metatheory.Derives.equality_symm
      hSecondEquality
  exact FirstOrder.Metatheory.Derives.equality_trans
    hFirstEquality hSecondSymmetry
/--
每个有序对都有满足文献投影规格的反转候选。
见证直接取 `⟨pair₁, pair₀⟩`；因此该构造只依赖已经建立的投影描述符，
不需要文献中的分离绕行。
-/
theorem is_ordered_pair_implies_ordered_pair_reverse_exists (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[right_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ
        ordered_pair_reverse_exists pair := by
  let left_projection :=
    left_projection_term pair
  let right_projection :=
    right_projection_term pair
  let swapped :=
    ordered_pair_term right_projection left_projection
  have hLeftProjection :
      Term.Admissible left_projection SetSort.set :=
    left_projection_term_admissible pair hPair
  have hRightProjection :
      Term.Admissible right_projection SetSort.set :=
    right_projection_term_admissible pair hPair
  have hSwapped :
      Term.Admissible swapped SetSort.set :=
    ordered_pair_term_admissible
      right_projection left_projection
      hRightProjection hLeftProjection
  nd_apply FirstOrder.Derives.impIntro
  let predicate :=
    is_ordered_pair_formula pair
  unfold ordered_pair_reverse_exists
  nd_apply FirstOrder.Derives.exists_intro (term := swapped)
  have hSwappedIsOrdered :
      [predicate] ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula swapped :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          relation_function_theory_subset_right_projection_operator_theory
            hFormula) (by
          simpa [swapped, left_projection,
            right_projection] using
            ordered_pair_term_is_ordered_pair_derives
              right_projection left_projection
              hRightProjection hLeftProjection)
  have hSwappedLeft :
      [predicate] ⊢ₘ[right_projection_operator_theory] (swapped)₀ₘ ≐ₘ right_projection :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          left_projection_operator_theory_subset_right_projection_operator_theory
            hFormula) (by
          simpa [swapped, left_projection,
            right_projection] using
            ordered_pair_term_left_projection_eq
              right_projection left_projection
              hRightProjection hLeftProjection)
  have hSwappedRight :
      [predicate] ⊢ₘ[right_projection_operator_theory] (swapped)₁ₘ ≐ₘ left_projection :=
    FirstOrder.Derives.context_weaken_cons <| (by
        simpa [swapped, left_projection,
          right_projection] using
          ordered_pair_term_right_projection_eq
            right_projection left_projection
            hRightProjection hLeftProjection)
  have hPaper :
      [predicate] ⊢ₘ[right_projection_operator_theory]
        ordered_pair_reverse_paper_spec
          pair swapped := by
    unfold ordered_pair_reverse_paper_spec
    exact FirstOrder.Derives.conjIntro
      hSwappedIsOrdered (FirstOrder.Derives.conjIntro
        hSwappedLeft hSwappedRight)
  have hPairOpenZero :
      Term.openAt SetSort.set 0 swapped pair = pair :=
    Term.openAt_eq_self_of_boundClosed
      SetSort.set 0 swapped pair hPair.2
  simpa [ordered_pair_reverse_paper_spec,
    swapped, Formula.openAt, Term.openAt,
    hPairOpenZero] using hPaper
/-! ## 文献定理的全称闭包接口 -/
/-- 文献蕴含规格下，有序对存在性的双变量全称闭包。 -/
theorem ordered_pair_paper_exists_forall (left right : FreeVarId) :
    ⊢ₘ[singleton_operator_theory]
      ∀ₘ[SetSort.set, left],
        ∀ₘ[SetSort.set, right],
          ordered_pair_paper_exists (x#left) (x#right) := by
  have hOpen :
      ⊢ₘ[singleton_operator_theory]
        ordered_pair_paper_exists (x#left) (x#right) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        Or.inr (Or.inr hFormula)) (ordered_pair_paper_exists_derives (x#left) (x#right) (set_variable_admissible left) (set_variable_admissible right))
  derive_close (left, right) using hOpen
/-- 文献蕴含规格下，有序对唯一性的四变量全称闭包。 -/
theorem ordered_pair_paper_unique_forall (first second left right : FreeVarId) :
    ⊢ₘ[singleton_operator_theory]
      ∀ₘ[SetSort.set, first],
        ∀ₘ[SetSort.set, second],
          ∀ₘ[SetSort.set, left],
            ∀ₘ[SetSort.set, right],
              ordered_pair_paper_spec (x#first) (x#second) (x#left) ⟶ₘ
                ordered_pair_paper_spec (x#first) (x#second) (x#right) ⟶ₘ (x#left ≐ₘ x#right) := by
  have hOpen :
      ⊢ₘ[singleton_operator_theory]
        ordered_pair_paper_spec (x#first) (x#second) (x#left) ⟶ₘ
          ordered_pair_paper_spec (x#first) (x#second) (x#right) ⟶ₘ (x#left ≐ₘ x#right) :=
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        Or.inr (Or.inr (Or.inr hFormula))) (ordered_pair_paper_unique (x#first) (x#second) (x#left) (x#right) (set_variable_admissible first)
        (set_variable_admissible second) (set_variable_admissible left) (set_variable_admissible right))
  derive_close (first, second, left, right) using hOpen
/-- 有序对函数符号单一性的四变量全称闭包。 -/
theorem ordered_pair_term_eq_iff_coordinates_forall (left₁ right₁ left₂ right₂ : FreeVarId) :
    ⊢ₘ[ordered_pair_operator_theory]
      ∀ₘ[SetSort.set, left₁],
        ∀ₘ[SetSort.set, right₁],
          ∀ₘ[SetSort.set, left₂],
            ∀ₘ[SetSort.set, right₂], (⟨x#left₁, x#right₁⟩ₘ ≐ₘ
                  ⟨x#left₂, x#right₂⟩ₘ) ↔ₘ ((x#left₁ ≐ₘ x#left₂) ∧ₘ (x#right₁ ≐ₘ x#right₂)) := by
  derive_close (left₁, right₁, left₂, right₂) using
      ordered_pair_term_eq_iff_coordinates (x#left₁) (x#right₁) (x#left₂) (x#right₂) (set_variable_admissible left₁) (set_variable_admissible right₁)
        (set_variable_admissible left₂) (set_variable_admissible right₂)
/-- 同一个集合的两个右投影候选必相等。 -/
theorem right_projection_unique (pair left right : SetTerm) (hPair : Term.Admissible pair SetSort.set) (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[ordered_pair_operator_theory]
      right_projection_spec pair left ⟶ₘ
        right_projection_spec pair right ⟶ₘ (left ≐ₘ right) := by
  let left_spec :=
    right_projection_spec pair left
  let right_spec :=
    right_projection_spec pair right
  let conclusion :=
    left ≐ₘ right
  have hLeftSpecAdmissible :
      Formula.Admissible left_spec := by
    dsimp [left_spec]
    exact right_projection_spec_admissible
      hPair hLeft
  have hRightSpecAdmissible :
      Formula.Admissible right_spec := by
    dsimp [right_spec]
    exact right_projection_spec_admissible
      hPair hRight
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [right_spec, left_spec]
  let left_bound_body : SetFormula :=
    pair ≐ₘ ⟨bₛ#0, left⟩ₘ
  let first :=
    FreshVariable.fresh_id SetSort.set
      [left_spec, right_spec, conclusion,
        left_bound_body]
  let left_point :=
    Formula.openAt SetSort.set 0 (x#first) left_bound_body
  have hFirstFreshLeftSpec : (SetSort.set, first) freshForₘ
        left_spec := by
    dsimp [first]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hFirstFreshRightSpec : (SetSort.set, first) freshForₘ
        right_spec := by
    dsimp [first]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hFirstFreshConclusion : (SetSort.set, first) freshForₘ
        conclusion := by
    dsimp [first]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hFirstFreshBoundBody : (SetSort.set, first) freshForₘ
        left_bound_body := by
    dsimp [first]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hLeftPointAdmissible :
      Formula.Admissible left_point := by
    have hOpened :=
      Formula.Admissible.exists_openAt (σ := signature) (body := left_bound_body) (term := x#first)
        SetSort.set (by
          simpa [left_spec,
            right_projection_spec,
            left_bound_body] using
            hLeftSpecAdmissible) (set_variable_admissible first)
    simpa [left_point] using hOpened
  have hLeftExists :
      Γ ⊢ₘ[ordered_pair_operator_theory] (∃ₘ[SetSort.set, first],
          left_point) := by
    have hClosure :
        Formula.closeFreeAt SetSort.set first 0
            left_point =
          left_bound_body := by
      dsimp [left_point]
      exact Formula.closeFreeAt_openAt
        SetSort.set first 0 left_bound_body
        hFirstFreshBoundBody
    change
      Γ ⊢ₘ[ordered_pair_operator_theory]
        Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set
            first 0 left_point)
    rw [hClosure]
    simpa [Γ, left_spec, right_projection_spec,
      left_bound_body] using (show
        Γ ⊢ₘ[ordered_pair_operator_theory]
          left_spec from
        .assumption (by simp [Γ]))
  have hLeftCase :
      left_point :: Γ
        ⊢ₘ[ordered_pair_operator_theory]
          conclusion := by
    let right_bound_body : SetFormula :=
      pair ≐ₘ ⟨bₛ#0, right⟩ₘ
    let second :=
      FreshVariable.fresh_id SetSort.set
        [left_point, left_spec, right_spec,
          conclusion, right_bound_body]
    let right_point :=
      Formula.openAt SetSort.set 0 (x#second) right_bound_body
    have hSecondFreshLeftPoint : (SetSort.set, second) freshForₘ
          left_point := by
      dsimp [second]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hSecondFreshLeftSpec : (SetSort.set, second) freshForₘ
          left_spec := by
      dsimp [second]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hSecondFreshRightSpec : (SetSort.set, second) freshForₘ
          right_spec := by
      dsimp [second]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hSecondFreshConclusion : (SetSort.set, second) freshForₘ
          conclusion := by
      dsimp [second]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hSecondFreshBoundBody : (SetSort.set, second) freshForₘ
          right_bound_body := by
      dsimp [second]
      exact FreshVariable.fresh_id_not_mem_m (by simp)
    have hRightPointAdmissible :
        Formula.Admissible right_point := by
      have hOpened :=
        Formula.Admissible.exists_openAt (σ := signature) (body := right_bound_body) (term := x#second)
          SetSort.set (by
            simpa [right_spec,
              right_projection_spec,
              right_bound_body] using
              hRightSpecAdmissible) (set_variable_admissible second)
      simpa [right_point] using hOpened
    have hRightExists :
        left_point :: Γ
          ⊢ₘ[ordered_pair_operator_theory] (∃ₘ[SetSort.set, second],
              right_point) := by
      have hClosure :
          Formula.closeFreeAt SetSort.set second 0
              right_point =
            right_bound_body := by
        dsimp [right_point]
        exact Formula.closeFreeAt_openAt
          SetSort.set second 0 right_bound_body
          hSecondFreshBoundBody
      change
        left_point :: Γ
          ⊢ₘ[ordered_pair_operator_theory]
            Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set
                second 0 right_point)
      rw [hClosure]
      simpa [Γ, right_spec, right_projection_spec,
        right_bound_body] using (show
          left_point :: Γ
            ⊢ₘ[ordered_pair_operator_theory]
              right_spec from
          .assumption (by simp [Γ]))
    have hRightCase :
        right_point :: left_point :: Γ
          ⊢ₘ[ordered_pair_operator_theory]
            conclusion := by
      let first_pair :=
        ordered_pair_term (x#first) left
      let second_pair :=
        ordered_pair_term (x#second) right
      have hFirstPair :
          Term.Admissible first_pair SetSort.set :=
        ordered_pair_term_admissible (x#first) left (set_variable_admissible first) hLeft
      have hSecondPair :
          Term.Admissible second_pair SetSort.set :=
        ordered_pair_term_admissible (x#second) right (set_variable_admissible second) hRight
      have hPairOpenZeroFirst :
          Term.openAt SetSort.set 0 (x#first) pair =
            pair :=
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#first) pair hPair.2
      have hLeftOpenZeroFirst :
          Term.openAt SetSort.set 0 (x#first) left =
            left :=
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#first) left hLeft.2
      have hPairOpenZeroSecond :
          Term.openAt SetSort.set 0 (x#second) pair =
            pair :=
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#second) pair hPair.2
      have hRightOpenZeroSecond :
          Term.openAt SetSort.set 0 (x#second) right =
            right :=
        Term.openAt_eq_self_of_boundClosed
          SetSort.set 0 (x#second) right hRight.2
      have hFirstEquality :
          right_point :: left_point :: Γ
            ⊢ₘ[ordered_pair_operator_theory]
              pair ≐ₘ first_pair := by
        simpa [left_point, left_bound_body,
          first_pair, Formula.openAt,
          Term.openAt, hPairOpenZeroFirst,
          hLeftOpenZeroFirst] using (show
            right_point :: left_point :: Γ
              ⊢ₘ[ordered_pair_operator_theory]
                left_point from
            .assumption (by simp))
      have hSecondEquality :
          right_point :: left_point :: Γ
            ⊢ₘ[ordered_pair_operator_theory]
              pair ≐ₘ second_pair := by
        simpa [right_point, right_bound_body,
          second_pair, Formula.openAt,
          Term.openAt, hPairOpenZeroSecond,
          hRightOpenZeroSecond] using (show
            right_point :: left_point :: Γ
              ⊢ₘ[ordered_pair_operator_theory]
                right_point from
            .assumption (by simp))
      have hFirstSymmetry :
          right_point :: left_point :: Γ
            ⊢ₘ[ordered_pair_operator_theory]
              first_pair ≐ₘ pair :=
        FirstOrder.Metatheory.Derives.equality_symm
          hFirstEquality
      have hPairEquality :
          right_point :: left_point :: Γ
            ⊢ₘ[ordered_pair_operator_theory]
              first_pair ≐ₘ second_pair :=
        FirstOrder.Metatheory.Derives.equality_trans
          hFirstSymmetry hSecondEquality
      have hCoordinates :
          right_point :: left_point :: Γ
            ⊢ₘ[ordered_pair_operator_theory] (first_pair ≐ₘ second_pair) ↔ₘ (((x#first) ≐ₘ (x#second)) ∧ₘ (left ≐ₘ right)) :=
        FirstOrder.Derives.context_weaken (by
            intro formula hFormula
            exact False.elim (List.not_mem_nil hFormula)) (by
            simpa [first_pair, second_pair] using
              ordered_pair_term_eq_iff_coordinates (x#first) left (x#second) right (set_variable_admissible first)
                hLeft (set_variable_admissible second)
                hRight)
      have hCoordinateEqualities :=
        FirstOrder.Derives.iffElimRight
          hCoordinates hPairEquality
      simpa [conclusion] using
        FirstOrder.Derives.conjElimRight
          hCoordinateEqualities
    exact FirstOrder.Derives.exists_elim (by
        intro formula hFormula
        have hSentence :=
          ordered_pair_operator_theory_sentence
            hFormula
        rw [hSentence.2]
        simp) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with
          rfl | hFormula
        · exact hSecondFreshLeftPoint
        · rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · exact hSecondFreshRightSpec
          · rcases List.mem_singleton.mp hFormula with rfl
            exact hSecondFreshLeftSpec)
      hSecondFreshConclusion
      hRightExists hRightCase
  exact FirstOrder.Derives.exists_elim (by
      intro formula hFormula
      have hSentence :=
        ordered_pair_operator_theory_sentence
          hFormula
      rw [hSentence.2]
      simp) (by
      intro formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · exact hFirstFreshRightSpec
      · rcases List.mem_singleton.mp hFormula with rfl
        exact hFirstFreshLeftSpec)
    hFirstFreshConclusion
    hLeftExists hLeftCase
/-- 每个有序对都等于由自身两个投影组成的规范有序对。 -/
theorem is_ordered_pair_eq_ordered_pair_projections (pair : SetTerm) (hPair : Term.Admissible pair SetSort.set) :
    ⊢ₘ[right_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ (pair ≐ₘ ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ) := by
  let left_projection :=
    left_projection_term pair
  let right_projection :=
    right_projection_term pair
  let reconstructed :=
    ordered_pair_term left_projection right_projection
  have hLeftProjection :
      Term.Admissible left_projection SetSort.set :=
    left_projection_term_admissible pair hPair
  have hRightProjection :
      Term.Admissible right_projection SetSort.set :=
    right_projection_term_admissible pair hPair
  have hReconstructed :
      Term.Admissible reconstructed SetSort.set :=
    ordered_pair_term_admissible
      left_projection right_projection
      hLeftProjection hRightProjection
  nd_apply FirstOrder.Derives.impIntro
  let predicate :=
    is_ordered_pair_formula pair
  let right_spec :=
    right_projection_spec pair right_projection
  let conclusion :=
    pair ≐ₘ reconstructed
  have hPredicateAdmissible :
      Formula.Admissible predicate := by
    dsimp [predicate]
    exact is_ordered_pair_formula_admissible
      hPair
  have hRightSpecAdmissible :
      Formula.Admissible right_spec := by
    dsimp [right_spec]
    exact right_projection_spec_admissible
      hPair hRightProjection
  have hPredicate :
      [predicate] ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula pair := by
    simpa [predicate] using (show
        [predicate] ⊢ₘ[right_projection_operator_theory]
          predicate from
        .assumption (by simp))
  have hRightSpecImp :
      [predicate] ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula pair ⟶ₘ
          right_spec :=
    FirstOrder.Derives.context_weaken_cons <| by
      simpa [right_spec, right_projection] using
        is_ordered_pair_right_projection_term_spec
          pair hPair
  have hRightSpec :
      [predicate] ⊢ₘ[right_projection_operator_theory]
        right_spec :=
    FirstOrder.Derives.impElim
      hRightSpecImp hPredicate
  let bound_body : SetFormula :=
    pair ≐ₘ ⟨bₛ#0, right_projection⟩ₘ
  let coordinate :=
    FreshVariable.fresh_id SetSort.set
      [predicate, right_spec, conclusion,
        bound_body]
  let point :=
    Formula.openAt SetSort.set 0 (x#coordinate) bound_body
  have hCoordinateFreshPredicate : (SetSort.set, coordinate) freshForₘ
        predicate := by
    dsimp [coordinate]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hCoordinateFreshConclusion : (SetSort.set, coordinate) freshForₘ
        conclusion := by
    dsimp [coordinate]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hCoordinateFreshBoundBody : (SetSort.set, coordinate) freshForₘ
        bound_body := by
    dsimp [coordinate]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hPointAdmissible :
      Formula.Admissible point := by
    have hOpened :=
      Formula.Admissible.exists_openAt (σ := signature) (body := bound_body) (term := x#coordinate)
        SetSort.set (by
          simpa [right_spec,
            right_projection_spec,
            bound_body] using
            hRightSpecAdmissible) (set_variable_admissible coordinate)
    simpa [point] using hOpened
  have hExists :
      [predicate] ⊢ₘ[right_projection_operator_theory] (∃ₘ[SetSort.set, coordinate], point) := by
    have hClosure :
        Formula.closeFreeAt SetSort.set coordinate 0
            point =
          bound_body := by
      dsimp [point]
      exact Formula.closeFreeAt_openAt
        SetSort.set coordinate 0 bound_body
        hCoordinateFreshBoundBody
    change
      [predicate] ⊢ₘ[right_projection_operator_theory]
        Formula.existsE SetSort.set (Formula.closeFreeAt SetSort.set
            coordinate 0 point)
    rw [hClosure]
    simpa [right_spec, right_projection_spec,
      bound_body] using hRightSpec
  have hCase :
      point :: [predicate]
        ⊢ₘ[right_projection_operator_theory]
          conclusion := by
    let represented :=
      ordered_pair_term (x#coordinate)
        right_projection
    have hRepresented :
        Term.Admissible represented SetSort.set :=
      ordered_pair_term_admissible (x#coordinate) right_projection (set_variable_admissible coordinate)
        hRightProjection
    have hPairOpenZero :
        Term.openAt SetSort.set 0 (x#coordinate) pair =
          pair :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 (x#coordinate) pair hPair.2
    have hRightProjectionOpenZero :
        Term.openAt SetSort.set 0 (x#coordinate) right_projection =
          right_projection :=
      Term.openAt_eq_self_of_boundClosed
        SetSort.set 0 (x#coordinate)
        right_projection hRightProjection.2
    have hRepresentation :
        point :: [predicate]
          ⊢ₘ[right_projection_operator_theory]
            pair ≐ₘ represented := by
      simpa [point, bound_body, represented,
        Formula.openAt, Term.openAt,
        hPairOpenZero,
        hRightProjectionOpenZero] using (show
          point :: [predicate]
            ⊢ₘ[right_projection_operator_theory]
              point from
          .assumption (by simp))
    have hLeftSpecImp :
        point :: [predicate]
          ⊢ₘ[right_projection_operator_theory]
            is_ordered_pair_formula pair ⟶ₘ
              left_projection_spec
                pair left_projection :=
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.theory_weaken (fun _ hFormula =>
              left_projection_operator_theory_subset_right_projection_operator_theory
                hFormula) (by
              simpa [left_projection] using
                is_ordered_pair_left_projection_term_spec
                  pair hPair)
    have hLeftSpec :
        point :: [predicate]
          ⊢ₘ[right_projection_operator_theory]
            left_projection_spec
              pair left_projection :=
      FirstOrder.Derives.impElim
        hLeftSpecImp (by
          simpa [predicate] using (show
              point :: [predicate]
                ⊢ₘ[right_projection_operator_theory]
                  predicate from
              .assumption (by simp)))
    have hRepresentedLeftSpec :
        point :: [predicate]
          ⊢ₘ[right_projection_operator_theory]
            left_projection_spec
              represented (x#coordinate) :=
      FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.context_weaken_cons <|
          FirstOrder.Derives.theory_weaken (fun _ hFormula =>
              ordered_pair_operator_theory_subset_right_projection_operator_theory
                hFormula) (by
              simpa [represented] using
                ordered_pair_term_left_projection_spec (x#coordinate) right_projection (set_variable_admissible coordinate)
                  hRightProjection)
    have hProjectionEquality :
        point :: [predicate]
          ⊢ₘ[right_projection_operator_theory]
            left_projection ≐ₘ (x#coordinate) :=
      left_projection_unique_of_pair_equality
        pair represented
        left_projection (x#coordinate)
        hPair hRepresented hLeftProjection (set_variable_admissible coordinate)
        hRepresentation hLeftSpec
        hRepresentedLeftSpec
    have hProjectionSymmetry :
        point :: [predicate]
          ⊢ₘ[right_projection_operator_theory] (x#coordinate) ≐ₘ left_projection :=
      FirstOrder.Metatheory.Derives.equality_symm
        hProjectionEquality
    have hRightReflexive :
        point :: [predicate]
          ⊢ₘ[right_projection_operator_theory]
            right_projection ≐ₘ right_projection :=
      FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) right_projection
    have hCoordinates :
        point :: [predicate]
          ⊢ₘ[right_projection_operator_theory] (represented ≐ₘ reconstructed) ↔ₘ (((x#coordinate) ≐ₘ left_projection) ∧ₘ
                (right_projection ≐ₘ right_projection)) :=
      FirstOrder.Derives.context_weaken (by
          intro formula hFormula
          exact False.elim (List.not_mem_nil hFormula)) (FirstOrder.Derives.theory_weaken (fun _ hFormula =>
            ordered_pair_operator_theory_subset_right_projection_operator_theory
              hFormula) (by
            simpa [represented, reconstructed] using
              ordered_pair_term_eq_iff_coordinates (x#coordinate) right_projection
                left_projection right_projection (set_variable_admissible coordinate)
                hRightProjection
                hLeftProjection hRightProjection))
    have hRepresentedReconstructed :
        point :: [predicate]
          ⊢ₘ[right_projection_operator_theory]
            represented ≐ₘ reconstructed :=
      FirstOrder.Derives.iffElimLeft
        hCoordinates (FirstOrder.Derives.conjIntro
          hProjectionSymmetry hRightReflexive)
    simpa [conclusion] using
      FirstOrder.Metatheory.Derives.equality_trans
        hRepresentation
        hRepresentedReconstructed
  exact FirstOrder.Derives.exists_elim (by
      intro formula hFormula
      have hSentence :=
        right_projection_operator_theory_sentence
          hFormula
      rw [hSentence.2]
      simp) (by
      intro formula hFormula
      rcases List.mem_singleton.mp hFormula with rfl
      exact hCoordinateFreshPredicate)
    hCoordinateFreshConclusion
    hExists hCase
/-- 文献投影规格蕴含规范的反转等式规格。 -/
theorem ordered_pair_reverse_paper_spec_implies_spec (pair reverse : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hReverse : Term.Admissible reverse SetSort.set) :
    ⊢ₘ[right_projection_operator_theory]
      ordered_pair_reverse_paper_spec pair reverse ⟶ₘ
        ordered_pair_reverse_spec pair reverse := by
  let left_projection :=
    left_projection_term pair
  let right_projection :=
    right_projection_term pair
  let reverse_left :=
    left_projection_term reverse
  let reverse_right :=
    right_projection_term reverse
  let represented :=
    ordered_pair_term reverse_left reverse_right
  let swapped :=
    ordered_pair_term right_projection left_projection
  have hLeftProjection :
      Term.Admissible left_projection SetSort.set :=
    left_projection_term_admissible pair hPair
  have hRightProjection :
      Term.Admissible right_projection SetSort.set :=
    right_projection_term_admissible pair hPair
  have hReverseLeft :
      Term.Admissible reverse_left SetSort.set :=
    left_projection_term_admissible reverse hReverse
  have hReverseRight :
      Term.Admissible reverse_right SetSort.set :=
    right_projection_term_admissible reverse hReverse
  have hRepresented :
      Term.Admissible represented SetSort.set :=
    ordered_pair_term_admissible
      reverse_left reverse_right
      hReverseLeft hReverseRight
  have hSwapped :
      Term.Admissible swapped SetSort.set :=
    ordered_pair_term_admissible
      right_projection left_projection
      hRightProjection hLeftProjection
  nd_apply FirstOrder.Derives.impIntro
  let paper :=
    ordered_pair_reverse_paper_spec pair reverse
  have hPaperAdmissible :
      Formula.Admissible paper := by
    dsimp [paper]
    exact ordered_pair_reverse_paper_spec_admissible
      hPair hReverse
  have hPaper :
      [paper] ⊢ₘ[right_projection_operator_theory]
        paper :=
    .assumption (by simp)
  have hReverseOrdered :
      [paper] ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula reverse := by
    simpa [paper, ordered_pair_reverse_paper_spec] using
      FirstOrder.Derives.conjElimLeft hPaper
  have hProjectionEqualities :
      [paper] ⊢ₘ[right_projection_operator_theory] ((reverse_left ≐ₘ right_projection) ∧ₘ (reverse_right ≐ₘ left_projection)) := by
    simpa [paper, ordered_pair_reverse_paper_spec,
      reverse_left, reverse_right,
      left_projection, right_projection] using
      FirstOrder.Derives.conjElimRight hPaper
  have hRepresentationImp :
      [paper] ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula reverse ⟶ₘ (reverse ≐ₘ represented) :=
    FirstOrder.Derives.context_weaken_cons <| by
      simpa [represented, reverse_left,
        reverse_right] using
        is_ordered_pair_eq_ordered_pair_projections
          reverse hReverse
  have hRepresentation :
      [paper] ⊢ₘ[right_projection_operator_theory]
        reverse ≐ₘ represented :=
    FirstOrder.Derives.impElim
      hRepresentationImp hReverseOrdered
  have hCoordinates :
      [paper] ⊢ₘ[right_projection_operator_theory] (represented ≐ₘ swapped) ↔ₘ ((reverse_left ≐ₘ right_projection) ∧ₘ (reverse_right ≐ₘ left_projection)) :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          ordered_pair_operator_theory_subset_right_projection_operator_theory
            hFormula) (by
          simpa [represented, swapped,
            reverse_left, reverse_right,
            left_projection, right_projection] using
            ordered_pair_term_eq_iff_coordinates
              reverse_left reverse_right
              right_projection left_projection
              hReverseLeft hReverseRight
              hRightProjection hLeftProjection)
  have hRepresentedSwapped :
      [paper] ⊢ₘ[right_projection_operator_theory]
        represented ≐ₘ swapped :=
    FirstOrder.Derives.iffElimLeft
      hCoordinates hProjectionEqualities
  simpa [ordered_pair_reverse_spec,
    represented, swapped, reverse_left,
    reverse_right, left_projection,
    right_projection] using
    FirstOrder.Metatheory.Derives.equality_trans
      hRepresentation hRepresentedSwapped
/-- 文献投影规格下，有序对反转候选保持唯一。 -/
theorem ordered_pair_reverse_paper_unique (pair first second : SetTerm) (hPair : Term.Admissible pair SetSort.set) (hFirst : Term.Admissible first SetSort.set)
    (hSecond : Term.Admissible second SetSort.set) :
    ⊢ₘ[right_projection_operator_theory]
      ordered_pair_reverse_paper_spec pair first ⟶ₘ
        ordered_pair_reverse_paper_spec pair second ⟶ₘ (first ≐ₘ second) := by
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [ordered_pair_reverse_paper_spec pair second,
      ordered_pair_reverse_paper_spec pair first]
  have hFirstSpec :
      Γ ⊢ₘ[right_projection_operator_theory]
        ordered_pair_reverse_spec pair first :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.context_weaken_cons <|
          ordered_pair_reverse_paper_spec_implies_spec
            pair first hPair hFirst) (by
        simpa [Γ] using (show
            Γ ⊢ₘ[right_projection_operator_theory]
              ordered_pair_reverse_paper_spec pair first from
            .assumption (by simp [Γ])))
  have hSecondSpec :
      Γ ⊢ₘ[right_projection_operator_theory]
        ordered_pair_reverse_spec pair second :=
    FirstOrder.Derives.impElim (FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.context_weaken_cons <|
          ordered_pair_reverse_paper_spec_implies_spec
            pair second hPair hSecond) (by
        simpa [Γ] using (show
            Γ ⊢ₘ[right_projection_operator_theory]
              ordered_pair_reverse_paper_spec pair second from
            .assumption (by simp [Γ])))
  have hUnique :
      Γ ⊢ₘ[right_projection_operator_theory]
        ordered_pair_reverse_spec pair first ⟶ₘ
          ordered_pair_reverse_spec pair second ⟶ₘ (first ≐ₘ second) :=
    FirstOrder.Derives.context_weaken (by
        intro formula hFormula
        exact False.elim (List.not_mem_nil hFormula)) (FirstOrder.Derives.theory_weaken (fun _ hFormula => False.elim hFormula) (ordered_pair_reverse_unique
          pair first second hPair hFirst hSecond))
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
      hUnique hFirstSpec)
    hSecondSpec
/-- 文献投影规格把候选识别为定义扩张中的反转函数项。 -/
theorem ordered_pair_reverse_paper_spec_implies_eq_term (pair candidate : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hCandidate : Term.Admissible candidate SetSort.set) :
    ⊢ₘ[ordered_pair_reverse_operator_theory]
      ordered_pair_reverse_paper_spec pair candidate ⟶ₘ (candidate ≐ₘ pair⁻¹ₘ) := by
  nd_apply FirstOrder.Derives.impIntro
  let paper :=
    ordered_pair_reverse_paper_spec pair candidate
  have hPaperAdmissible :
      Formula.Admissible paper := by
    dsimp [paper]
    exact ordered_pair_reverse_paper_spec_admissible
      hPair hCandidate
  have hPaper :
      [paper] ⊢ₘ[ordered_pair_reverse_operator_theory]
        paper :=
    .assumption (by simp)
  have hPaperToSpec :
      [paper] ⊢ₘ[ordered_pair_reverse_operator_theory]
        paper ⟶ₘ
          ordered_pair_reverse_spec pair candidate :=
    FirstOrder.Derives.context_weaken_cons <|
      FirstOrder.Derives.theory_weaken (fun _ hFormula =>
          right_projection_operator_theory_subset_ordered_pair_reverse_operator_theory
            hFormula) (ordered_pair_reverse_paper_spec_implies_spec
          pair candidate hPair hCandidate)
  have hSpec :
      [paper] ⊢ₘ[ordered_pair_reverse_operator_theory]
        ordered_pair_reverse_spec pair candidate :=
    FirstOrder.Derives.impElim hPaperToSpec hPaper
  have hDefinition :
      [paper] ⊢ₘ[ordered_pair_reverse_operator_theory] (candidate ≐ₘ pair⁻¹ₘ) ↔ₘ
          ordered_pair_reverse_spec pair candidate :=
    FirstOrder.Derives.context_weaken_cons (ordered_pair_reverse_definition_instance_derives
        pair candidate hPair hCandidate)
  exact FirstOrder.Derives.iffElimLeft
    hDefinition hSpec
/-- 有序对谓词背景下，右投影规格保持唯一。 -/
theorem is_ordered_pair_right_projection_unique (pair left right : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_function_theory]
      is_ordered_pair_formula pair ⟶ₘ
        right_projection_spec pair left ⟶ₘ
          right_projection_spec pair right ⟶ₘ (left ≐ₘ right) := by
  nd_apply FirstOrder.Derives.impIntro
  exact FirstOrder.Derives.context_weaken_cons <|
    FirstOrder.Derives.theory_weaken (fun _ hFormula =>
        ordered_pair_operator_theory_subset_relation_function_theory
          hFormula) (right_projection_unique
        pair left right hPair hLeft hRight)
/-- 有序对谓词背景下，两个右投影规格的合取推出候选相等。 -/
theorem is_ordered_pair_right_projection_functional (pair left right : SetTerm) (hPair : Term.Admissible pair SetSort.set)
    (hLeft : Term.Admissible left SetSort.set) (hRight : Term.Admissible right SetSort.set) :
    ⊢ₘ[relation_function_theory]
      is_ordered_pair_formula pair ⟶ₘ ((right_projection_spec pair left ∧ₘ
            right_projection_spec pair right) ⟶ₘ (left ≐ₘ right)) := by
  let predicate :=
    is_ordered_pair_formula pair
  let specifications :=
    right_projection_spec pair left ∧ₘ
      right_projection_spec pair right
  have hPredicateAdmissible :
      Formula.Admissible predicate := by
    dsimp [predicate]
    exact is_ordered_pair_formula_admissible
      hPair
  have hLeftSpecAdmissible :
      Formula.Admissible (right_projection_spec pair left) :=
    right_projection_spec_admissible
      hPair hLeft
  have hRightSpecAdmissible :
      Formula.Admissible (right_projection_spec pair right) :=
    right_projection_spec_admissible
      hPair hRight
  have hSpecificationsAdmissible :
      Formula.Admissible specifications := by
    dsimp [specifications]
    exact Formula.Admissible.conj
      hLeftSpecAdmissible
      hRightSpecAdmissible
  have hUnique :=
    is_ordered_pair_right_projection_unique
      pair left right hPair hLeft hRight
  change
    ⊢ₘ[relation_function_theory]
      predicate ⟶ₘ
        specifications ⟶ₘ (left ≐ₘ right)
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.impIntro
  let Γ : Context signature :=
    [specifications, predicate]
  have hUniqueContext :
      Γ ⊢ₘ[relation_function_theory]
        predicate ⟶ₘ
          right_projection_spec pair left ⟶ₘ
            right_projection_spec pair right ⟶ₘ (left ≐ₘ right) := by
    simpa [Γ, predicate] using (FirstOrder.Derives.context_weaken_cons <|
        FirstOrder.Derives.context_weaken_cons <|
          hUnique)
  have hPredicate :
      Γ ⊢ₘ[relation_function_theory]
        predicate :=
    .assumption (by simp [Γ])
  have hSpecifications :
      Γ ⊢ₘ[relation_function_theory]
        specifications :=
    .assumption (by simp [Γ])
  have hLeftSpec :
      Γ ⊢ₘ[relation_function_theory]
        right_projection_spec pair left := by
    simpa [specifications] using
      FirstOrder.Derives.conjElimLeft
        hSpecifications
  have hRightSpec :
      Γ ⊢ₘ[relation_function_theory]
        right_projection_spec pair right := by
    simpa [specifications] using
      FirstOrder.Derives.conjElimRight
        hSpecifications
  exact FirstOrder.Derives.impElim (FirstOrder.Derives.impElim (FirstOrder.Derives.impElim
        hUniqueContext hPredicate)
      hLeftSpec)
    hRightSpec
/-- 左投影存在性的单变量全称闭包。 -/
theorem is_ordered_pair_left_projection_exists_forall (pair : FreeVarId) :
    ⊢ₘ[relation_function_theory]
      ∀ₘ[SetSort.set, pair],
        is_ordered_pair_formula (x#pair) ⟶ₘ
          left_projection_exists (x#pair) := by
  derive_close (pair) using
    is_ordered_pair_implies_left_projection_exists (x#pair) (set_variable_admissible pair)
/-- 左投影函数性的三变量全称闭包。 -/
theorem is_ordered_pair_left_projection_functional_forall (pair left right : FreeVarId) :
    ⊢ₘ[relation_function_theory]
      ∀ₘ[SetSort.set, pair],
        ∀ₘ[SetSort.set, left],
          ∀ₘ[SetSort.set, right],
            is_ordered_pair_formula (x#pair) ⟶ₘ ((left_projection_spec (x#pair) (x#left) ∧ₘ
                  left_projection_spec (x#pair) (x#right)) ⟶ₘ (x#left ≐ₘ x#right)) := by
  derive_close (pair, left, right) using
    is_ordered_pair_left_projection_functional (x#pair) (x#left) (x#right) (set_variable_admissible pair) (set_variable_admissible left)
      (set_variable_admissible right)
/-- 右投影存在性的单变量全称闭包。 -/
theorem is_ordered_pair_right_projection_exists_forall (pair : FreeVarId) :
    ⊢ₘ[relation_function_theory]
      ∀ₘ[SetSort.set, pair],
        is_ordered_pair_formula (x#pair) ⟶ₘ
          right_projection_exists (x#pair) := by
  derive_close (pair) using
    is_ordered_pair_implies_right_projection_exists (x#pair) (set_variable_admissible pair)
/-- 右投影函数性的三变量全称闭包。 -/
theorem is_ordered_pair_right_projection_functional_forall (pair left right : FreeVarId) :
    ⊢ₘ[relation_function_theory]
      ∀ₘ[SetSort.set, pair],
        ∀ₘ[SetSort.set, left],
          ∀ₘ[SetSort.set, right],
            is_ordered_pair_formula (x#pair) ⟶ₘ ((right_projection_spec (x#pair) (x#left) ∧ₘ
                  right_projection_spec (x#pair) (x#right)) ⟶ₘ (x#left ≐ₘ x#right)) := by
  derive_close (pair, left, right) using
    is_ordered_pair_right_projection_functional (x#pair) (x#left) (x#right) (set_variable_admissible pair) (set_variable_admissible left)
      (set_variable_admissible right)
/-- 有序对反转存在性的单变量全称闭包。 -/
theorem is_ordered_pair_reverse_exists_forall (pair : FreeVarId) :
    ⊢ₘ[right_projection_operator_theory]
      ∀ₘ[SetSort.set, pair],
        is_ordered_pair_formula (x#pair) ⟶ₘ
          ordered_pair_reverse_exists (x#pair) := by
  derive_close (pair) using
    is_ordered_pair_implies_ordered_pair_reverse_exists (x#pair) (set_variable_admissible pair)
/-- 文献反转规格唯一性的三变量全称闭包。 -/
theorem ordered_pair_reverse_paper_unique_forall (pair first second : FreeVarId) :
    ⊢ₘ[right_projection_operator_theory]
      ∀ₘ[SetSort.set, pair],
        ∀ₘ[SetSort.set, first],
          ∀ₘ[SetSort.set, second],
            ordered_pair_reverse_paper_spec (x#pair) (x#first) ⟶ₘ
              ordered_pair_reverse_paper_spec (x#pair) (x#second) ⟶ₘ (x#first ≐ₘ x#second) := by
  derive_close (pair, first, second) using
    ordered_pair_reverse_paper_unique (x#pair) (x#first) (x#second) (set_variable_admissible pair) (set_variable_admissible first)
      (set_variable_admissible second)
/-- 反转函数项规范规格的单变量全称闭包。 -/
theorem ordered_pair_reverse_term_spec_forall (pair : FreeVarId) :
    ⊢ₘ[ordered_pair_reverse_operator_theory]
      ∀ₘ[SetSort.set, pair],
        ordered_pair_reverse_spec (x#pair) (x#pair)⁻¹ₘ := by
  derive_close (pair) using
    ordered_pair_reverse_term_spec_derives (x#pair) (set_variable_admissible pair)
/-- 文献反转规格识别函数项的双变量全称闭包。 -/
theorem ordered_pair_reverse_paper_spec_implies_eq_term_forall (pair candidate : FreeVarId) :
    ⊢ₘ[ordered_pair_reverse_operator_theory]
      ∀ₘ[SetSort.set, pair],
        ∀ₘ[SetSort.set, candidate],
          ordered_pair_reverse_paper_spec (x#pair) (x#candidate) ⟶ₘ (x#candidate ≐ₘ (x#pair)⁻¹ₘ) := by
  derive_close (pair, candidate) using
    ordered_pair_reverse_paper_spec_implies_eq_term (x#pair) (x#candidate) (set_variable_admissible pair) (set_variable_admissible candidate)
end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
