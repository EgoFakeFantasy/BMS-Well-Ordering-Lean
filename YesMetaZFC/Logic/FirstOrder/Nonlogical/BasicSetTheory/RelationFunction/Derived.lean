import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.RelationFunction.Core

/-!
# 关系与函数基础：导出定理

本模块把 Core 中的构造接口提升为投影、重构与反转定理。所有存在量词均由类型化
见证引入或在规范 fresh 上下文中消去；不保留自由变量编号闭包、admissibility、
闭性证明或兼容包装。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-! ## 定义公理实例化 -/

theorem left_projection_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (pair candidate : SetOpenTerm free) :
    Γ ⊢ₘ[left_projection_operator_theory]
      left_projection_definition_instance pair candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    left_projection_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons pair VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[left_projection_operator_theory]
        Formula.fromSentence left_projection_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, left_projection_definition_axiom,
    left_projection_definition_instance, left_projection_spec,
    intersection_member_condition, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

theorem right_projection_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (pair candidate : SetOpenTerm free) :
    Γ ⊢ₘ[right_projection_operator_theory]
      right_projection_definition_instance pair candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    right_projection_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons pair VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[right_projection_operator_theory]
        Formula.fromSentence right_projection_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, right_projection_definition_axiom,
    right_projection_definition_instance, right_projection_spec,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

theorem ordered_pair_reverse_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (pair candidate : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_reverse_operator_theory]
      ordered_pair_reverse_definition_instance pair candidate := by
  let body : SetOpenFormula [SetSort.set, SetSort.set] :=
    ordered_pair_reverse_definition_instance
      (.fvar (.there .here) :
        SetOpenTerm [SetSort.set, SetSort.set])
      (.fvar .here :
        SetOpenTerm [SetSort.set, SetSort.set])
  let τ : VariableSubstitution signature
      [SetSort.set, SetSort.set] [] free :=
    VariableSubstitution.cons candidate
      (VariableSubstitution.cons pair VariableSubstitution.empty)
  have hClosed :
      ([] : Context signature []) ⊢ₘ[ordered_pair_reverse_operator_theory]
        Formula.fromSentence ordered_pair_reverse_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, ordered_pair_reverse_definition_axiom,
    ordered_pair_reverse_definition_instance,
    ordered_pair_reverse_spec, Formula.substituteFree,
    Substitution.free_map, Formula.substitute,
    Formula.substituteMapped, Term.substituteMapped,
    Arguments.substituteMapped, VariableSubstitution.cons,
    VariableSubstitution.empty, VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hInstance

/-! ## 有序对谓词 -/

/-- 一个具体表示直接给出“是有序对”条件。 -/
theorem is_ordered_pair_condition_intro
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (pair left right : SetOpenTerm free)
    (hRepresentation : Γ ⊢ₘ[T] pair ≐ₘ ⟨left, right⟩ₘ) :
    Γ ⊢ₘ[T] is_ordered_pair_condition pair := by
  unfold is_ordered_pair_condition
  apply FirstOrder.Derives.exists_intro left
  rw [Formula.instantiateTop_abstractFreeTop]
  rw [Formula.instantiateFreeTop_existsFreeTop]
  apply FirstOrder.Derives.exists_intro right
  rw [Formula.instantiateTop_abstractFreeTop]
  simpa [Formula.instantiateFreeTop, Formula.substituteFree,
    Substitution.free_map, Substitution.instantiateFreeTop,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.liftFree,
    VariableSubstitution.instantiateFreeTop,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using hRepresentation

/-- 每个规范构造的有序对都满足有序对谓词。 -/
theorem ordered_pair_term_is_ordered_pair_derives
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[relation_function_theory]
      is_ordered_pair_formula ⟨left, right⟩ₘ := by
  have hDefinition := is_ordered_pair_definition_instance_derives
    (Γ := Γ) ⟨left, right⟩ₘ
  have hCondition := is_ordered_pair_condition_intro
    (T := relation_function_theory) (Γ := Γ)
    ⟨left, right⟩ₘ left right
    (Metatheory.Derives.equality_refl
      (T := relation_function_theory) (Γ := Γ) ⟨left, right⟩ₘ)
  exact FirstOrder.Derives.iff_elim_right hDefinition hCondition

/-! ## 规范有序对上的投影 -/

/-- 规范有序对满足第二坐标的右投影规格。 -/
theorem ordered_pair_term_right_projection_spec
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_operator_theory]
      right_projection_spec ⟨left, right⟩ₘ right := by
  unfold right_projection_spec
  apply FirstOrder.Derives.exists_intro left
  simpa using!
    (Metatheory.Derives.equality_refl
      (T := ordered_pair_operator_theory) (Γ := Γ)
      ⟨left, right⟩ₘ)

/-- 左投影函数项在规范有序对上返回第一坐标。 -/
theorem ordered_pair_term_left_projection_eq
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[left_projection_operator_theory]
      (⟨left, right⟩ₘ)₀ₘ ≐ₘ left := by
  let pair : SetOpenTerm free := ⟨left, right⟩ₘ
  have hDefinition := left_projection_definition_instance_derives
    (Γ := Γ) pair left
  have hIsOrdered := FirstOrder.Derives.theory_weaken
    relation_function_theory_subset_left_projection_operator_theory
    (ordered_pair_term_is_ordered_pair_derives
      (Γ := Γ) left right)
  have hSpec := FirstOrder.Derives.theory_weaken
    ordered_pair_operator_theory_subset_left_projection_operator_theory
    (ordered_pair_term_left_projection_spec
      (Γ := Γ) left right)
  have hGraph := FirstOrder.Derives.imp_elim
    hDefinition hIsOrdered
  simpa [pair] using
    (FirstOrder.Derives.iff_elim_right hGraph hSpec)

/-- 右投影函数项在规范有序对上返回第二坐标。 -/
theorem ordered_pair_term_right_projection_eq
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[right_projection_operator_theory]
      (⟨left, right⟩ₘ)₁ₘ ≐ₘ right := by
  let pair : SetOpenTerm free := ⟨left, right⟩ₘ
  have hDefinition := right_projection_definition_instance_derives
    (Γ := Γ) pair right
  have hIsOrdered := FirstOrder.Derives.theory_weaken
    relation_function_theory_subset_right_projection_operator_theory
    (ordered_pair_term_is_ordered_pair_derives
      (Γ := Γ) left right)
  have hSpec := FirstOrder.Derives.theory_weaken
    ordered_pair_operator_theory_subset_right_projection_operator_theory
    (ordered_pair_term_right_projection_spec
      (Γ := Γ) left right)
  have hGraph := FirstOrder.Derives.imp_elim
    hDefinition hIsOrdered
  simpa [pair] using
    (FirstOrder.Derives.iff_elim_right hGraph hSpec)

/-! ## 谓词前提下的投影 -/

/-- 有序对谓词前提下，左投影函数项满足左投影规格。 -/
theorem is_ordered_pair_left_projection_term_spec
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[left_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ
        left_projection_spec pair (pair)₀ₘ := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_ordered_pair_formula pair :: Γ
  have hDefinition := FirstOrder.Derives.context_weaken_cons
    (assumption := is_ordered_pair_formula pair)
    (left_projection_definition_instance_derives
      (Γ := Γ) pair (pair)₀ₘ)
  have hGraph := FirstOrder.Derives.imp_elim hDefinition
    (FirstOrder.Derives.assumption List.mem_cons_self)
  exact FirstOrder.Derives.iff_elim_left hGraph
    (Metatheory.Derives.equality_refl
      (T := left_projection_operator_theory) (Γ := Δ) (pair)₀ₘ)

/-- 有序对谓词前提下，右投影函数项满足右投影规格。 -/
theorem is_ordered_pair_right_projection_term_spec
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[right_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ
        right_projection_spec pair (pair)₁ₘ := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_ordered_pair_formula pair :: Γ
  have hDefinition := FirstOrder.Derives.context_weaken_cons
    (assumption := is_ordered_pair_formula pair)
    (right_projection_definition_instance_derives
      (Γ := Γ) pair (pair)₁ₘ)
  have hGraph := FirstOrder.Derives.imp_elim hDefinition
    (FirstOrder.Derives.assumption List.mem_cons_self)
  exact FirstOrder.Derives.iff_elim_left hGraph
    (Metatheory.Derives.equality_refl
      (T := right_projection_operator_theory) (Γ := Δ) (pair)₁ₘ)

/-- 有序对谓词推出左投影存在。 -/
theorem is_ordered_pair_implies_left_projection_exists
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[left_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ left_projection_exists pair := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_ordered_pair_formula pair :: Γ
  have hSpec := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (assumption := is_ordered_pair_formula pair)
      (is_ordered_pair_left_projection_term_spec (Γ := Γ) pair))
    (FirstOrder.Derives.assumption List.mem_cons_self)
  unfold left_projection_exists
  apply FirstOrder.Derives.exists_intro (pair)₀ₘ
  rw [Formula.instantiateTop_abstractFreeTop,
    left_projection_spec_instantiateFreeTop_context]
  exact hSpec

/-- 有序对谓词推出右投影存在。 -/
theorem is_ordered_pair_implies_right_projection_exists
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[right_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ right_projection_exists pair := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_ordered_pair_formula pair :: Γ
  have hSpec := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (assumption := is_ordered_pair_formula pair)
      (is_ordered_pair_right_projection_term_spec (Γ := Γ) pair))
    (FirstOrder.Derives.assumption List.mem_cons_self)
  unfold right_projection_exists
  apply FirstOrder.Derives.exists_intro (pair)₁ₘ
  rw [Formula.instantiateTop_abstractFreeTop,
    right_projection_spec_instantiateFreeTop_context]
  exact hSpec

/-- 任意左投影规格都直接给出左投影存在。 -/
theorem left_projection_spec_implies_exists
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (pair candidate : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] left_projection_spec pair candidate) :
    Γ ⊢ₘ[T] left_projection_exists pair := by
  unfold left_projection_exists
  apply FirstOrder.Derives.exists_intro candidate
  rw [Formula.instantiateTop_abstractFreeTop,
    left_projection_spec_instantiateFreeTop_context]
  exact hSpec

/-- 任意右投影规格都直接给出右投影存在。 -/
theorem right_projection_spec_implies_exists
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (pair candidate : SetOpenTerm free)
    (hSpec : Γ ⊢ₘ[T] right_projection_spec pair candidate) :
    Γ ⊢ₘ[T] right_projection_exists pair := by
  unfold right_projection_exists
  apply FirstOrder.Derives.exists_intro candidate
  rw [Formula.instantiateTop_abstractFreeTop,
    right_projection_spec_instantiateFreeTop_context]
  exact hSpec

/-- 同一个集合的两个右投影候选必相等。 -/
theorem right_projection_unique
    {free : SetContext} {Γ : Context signature free}
    (pair left right : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_operator_theory]
      right_projection_spec pair left ⟶ₘ
        right_projection_spec pair right ⟶ₘ (left ≐ₘ right) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    right_projection_spec pair right ::
      right_projection_spec pair left :: Γ
  have hLeft : Δ ⊢ₘ[ordered_pair_operator_theory]
      right_projection_spec pair left :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hRight : Δ ⊢ₘ[ordered_pair_operator_theory]
      right_projection_spec pair right :=
    FirstOrder.Derives.assumption (by simp [Δ])
  unfold right_projection_spec at hLeft
  apply FirstOrder.Derives.exists_elim hLeft
  let first : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let firstBody : SetOpenFormula (SetSort.set :: free) :=
    pair.weakenFree SetSort.set ≐ₘ
      ⟨first, left.weakenFree SetSort.set⟩ₘ
  let Ξ : Context signature (SetSort.set :: free) :=
    firstBody :: FreshVariable.extendContext SetSort.set Δ
  change Ξ ⊢ₘ[ordered_pair_operator_theory]
    left.weakenFree SetSort.set ≐ₘ right.weakenFree SetSort.set
  have hRight' :
      Ξ ⊢ₘ[ordered_pair_operator_theory]
        right_projection_spec (pair.weakenFree SetSort.set)
          (right.weakenFree SetSort.set) :=
    FirstOrder.Derives.assumption (by
      simp [Ξ, Δ, firstBody, FreshVariable.extendContext])
  unfold right_projection_spec at hRight'
  apply FirstOrder.Derives.exists_elim hRight'
  let second : SetOpenTerm
      (SetSort.set :: SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := SetSort.set :: free) SetSort.set
  let first' : SetOpenTerm
      (SetSort.set :: SetSort.set :: free) :=
    first.weakenFree SetSort.set
  let pair' : SetOpenTerm
      (SetSort.set :: SetSort.set :: free) :=
    (pair.weakenFree SetSort.set).weakenFree SetSort.set
  let left' : SetOpenTerm
      (SetSort.set :: SetSort.set :: free) :=
    (left.weakenFree SetSort.set).weakenFree SetSort.set
  let right' : SetOpenTerm
      (SetSort.set :: SetSort.set :: free) :=
    (right.weakenFree SetSort.set).weakenFree SetSort.set
  let secondBody : SetOpenFormula
      (SetSort.set :: SetSort.set :: free) :=
    pair' ≐ₘ ⟨second, right'⟩ₘ
  let Ψ : Context signature
      (SetSort.set :: SetSort.set :: free) :=
    secondBody :: FreshVariable.extendContext SetSort.set Ξ
  change Ψ ⊢ₘ[ordered_pair_operator_theory] left' ≐ₘ right'
  have hFirstRepresentation :
      Ψ ⊢ₘ[ordered_pair_operator_theory]
        pair' ≐ₘ ⟨first', left'⟩ₘ :=
    FirstOrder.Derives.assumption (by
      simp [Ψ, Ξ, firstBody, secondBody, pair', first', left',
        FreshVariable.extendContext, first, second,
        FreshVariable.newest])
  have hSecondRepresentation :
      Ψ ⊢ₘ[ordered_pair_operator_theory]
        pair' ≐ₘ ⟨second, right'⟩ₘ :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hConstructorEquality :
      Ψ ⊢ₘ[ordered_pair_operator_theory]
        ⟨first', left'⟩ₘ ≐ₘ ⟨second, right'⟩ₘ :=
    Metatheory.Derives.equality_trans
      (Metatheory.Derives.equality_symm hFirstRepresentation)
      hSecondRepresentation
  have hCoordinates := FirstOrder.Derives.iff_elim_left
    (ordered_pair_term_eq_iff_coordinates
      (Γ := Ψ) first' left' second right')
    hConstructorEquality
  exact FirstOrder.Derives.conj_elim_right hCoordinates

/-- 任意满足有序对谓词的集合等于由自身两个投影重构的规范有序对。 -/
theorem is_ordered_pair_eq_ordered_pair_projections
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[right_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ
        (pair ≐ₘ ⟨(pair)₀ₘ, (pair)₁ₘ⟩ₘ) := by
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free := is_ordered_pair_formula pair :: Γ
  have hPredicate :
      Δ ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula pair :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hRightSpec := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (assumption := is_ordered_pair_formula pair)
      (is_ordered_pair_right_projection_term_spec (Γ := Γ) pair))
    hPredicate
  unfold right_projection_spec at hRightSpec
  apply FirstOrder.Derives.exists_elim hRightSpec
  let coordinate : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let pair' : SetOpenTerm (SetSort.set :: free) :=
    pair.weakenFree SetSort.set
  let leftProjection : SetOpenTerm (SetSort.set :: free) :=
    (pair')₀ₘ
  let rightProjection : SetOpenTerm (SetSort.set :: free) :=
    (pair')₁ₘ
  let represented : SetOpenTerm (SetSort.set :: free) :=
    ⟨coordinate, rightProjection⟩ₘ
  let reconstructed : SetOpenTerm (SetSort.set :: free) :=
    ⟨leftProjection, rightProjection⟩ₘ
  let body : SetOpenFormula (SetSort.set :: free) :=
    pair' ≐ₘ represented
  let Ξ : Context signature (SetSort.set :: free) :=
    body :: FreshVariable.extendContext SetSort.set Δ
  change Ξ ⊢ₘ[right_projection_operator_theory]
    pair' ≐ₘ reconstructed
  have hRepresentation :
      Ξ ⊢ₘ[right_projection_operator_theory]
        pair' ≐ₘ represented :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hPredicate' :
      Ξ ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula pair' :=
    FirstOrder.Derives.assumption (by
      simp [Ξ, Δ, body, pair', FreshVariable.extendContext])
  have hLeftSpec :
      Ξ ⊢ₘ[right_projection_operator_theory]
        left_projection_spec pair' leftProjection := by
    have hImp := FirstOrder.Derives.theory_weaken
      left_projection_operator_theory_subset_right_projection_operator_theory
      (is_ordered_pair_left_projection_term_spec (Γ := Ξ) pair')
    simpa [leftProjection] using
      (FirstOrder.Derives.imp_elim hImp hPredicate')
  have hRepresentedLeftSpec :
      Ξ ⊢ₘ[right_projection_operator_theory]
        left_projection_spec represented coordinate :=
    FirstOrder.Derives.theory_weaken
      ordered_pair_operator_theory_subset_right_projection_operator_theory
      (by simpa [represented] using
        (ordered_pair_term_left_projection_spec
          (Γ := Ξ) coordinate rightProjection))
  have hCoordinateSpec :
      Ξ ⊢ₘ[right_projection_operator_theory]
        left_projection_spec pair' coordinate :=
    left_projection_spec_transport_pair_of_equality
      pair' represented coordinate hRepresentation hRepresentedLeftSpec
  have hLeftEquality :
      Ξ ⊢ₘ[right_projection_operator_theory]
        leftProjection ≐ₘ coordinate :=
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim
        (left_projection_unique
          (T := right_projection_operator_theory) (Γ := Ξ)
          pair' leftProjection coordinate)
        hLeftSpec)
      hCoordinateSpec
  have hReconstructed :
      Ξ ⊢ₘ[right_projection_operator_theory]
        represented ≐ₘ reconstructed :=
    ordered_pair_term_congr_of_equalities
      coordinate leftProjection rightProjection rightProjection
      (Metatheory.Derives.equality_symm hLeftEquality)
      (Metatheory.Derives.equality_refl
        (T := right_projection_operator_theory) (Γ := Ξ)
        rightProjection)
  exact Metatheory.Derives.equality_trans
    hRepresentation hReconstructed

/-! ## 有序对反转 -/

/-- 反转函数项满足交换两个投影的规范规格。 -/
theorem ordered_pair_reverse_term_spec_derives
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_reverse_operator_theory]
      ordered_pair_reverse_spec pair pair⁻¹ₘ := by
  have hDefinition := ordered_pair_reverse_definition_instance_derives
    (Γ := Γ) pair pair⁻¹ₘ
  exact FirstOrder.Derives.iff_elim_left hDefinition
    (Metatheory.Derives.equality_refl
      (T := ordered_pair_reverse_operator_theory) (Γ := Γ) pair⁻¹ₘ)

/-- 同一个有序对的两个规范反转候选必相等。 -/
theorem ordered_pair_reverse_unique
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (pair first second : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      ordered_pair_reverse_spec pair first ⟶ₘ
        ordered_pair_reverse_spec pair second ⟶ₘ (first ≐ₘ second) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    ordered_pair_reverse_spec pair second ::
      ordered_pair_reverse_spec pair first :: Γ
  have hFirst :
      Δ ⊢ₘ[T] first ≐ₘ ⟨(pair)₁ₘ, (pair)₀ₘ⟩ₘ := by
    simpa [ordered_pair_reverse_spec] using
      (show Δ ⊢ₘ[T] ordered_pair_reverse_spec pair first from
        FirstOrder.Derives.assumption (by simp [Δ]))
  have hSecond :
      Δ ⊢ₘ[T] second ≐ₘ ⟨(pair)₁ₘ, (pair)₀ₘ⟩ₘ := by
    simpa [ordered_pair_reverse_spec] using
      (show Δ ⊢ₘ[T] ordered_pair_reverse_spec pair second from
        FirstOrder.Derives.assumption (by simp [Δ]))
  exact Metatheory.Derives.equality_trans hFirst
    (Metatheory.Derives.equality_symm hSecond)

/-- 文献投影规格蕴含规范的反转等式规格。 -/
theorem ordered_pair_reverse_paper_spec_implies_spec
    {free : SetContext} {Γ : Context signature free}
    (pair reverse : SetOpenTerm free) :
    Γ ⊢ₘ[right_projection_operator_theory]
      ordered_pair_reverse_paper_spec pair reverse ⟶ₘ
        ordered_pair_reverse_spec pair reverse := by
  apply FirstOrder.Derives.imp_intro
  let paper : SetOpenFormula free :=
    ordered_pair_reverse_paper_spec pair reverse
  let Δ : Context signature free := paper :: Γ
  have hPaper : Δ ⊢ₘ[right_projection_operator_theory] paper :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hReverseOrdered :
      Δ ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula reverse := by
    simpa [paper, ordered_pair_reverse_paper_spec] using
      (FirstOrder.Derives.conj_elim_left hPaper)
  have hProjectionEqualities :
      Δ ⊢ₘ[right_projection_operator_theory]
        (((reverse)₀ₘ ≐ₘ (pair)₁ₘ) ∧ₘ
          ((reverse)₁ₘ ≐ₘ (pair)₀ₘ)) := by
    simpa [paper, ordered_pair_reverse_paper_spec] using
      (FirstOrder.Derives.conj_elim_right hPaper)
  have hRepresentation := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (assumption := paper)
      (is_ordered_pair_eq_ordered_pair_projections
        (Γ := Γ) reverse))
    hReverseOrdered
  have hCoordinateEquality := ordered_pair_term_congr_of_equalities
    (reverse)₀ₘ (pair)₁ₘ (reverse)₁ₘ (pair)₀ₘ
    (FirstOrder.Derives.conj_elim_left hProjectionEqualities)
    (FirstOrder.Derives.conj_elim_right hProjectionEqualities)
  simpa [ordered_pair_reverse_spec] using
    (Metatheory.Derives.equality_trans
      hRepresentation hCoordinateEquality)

/-- 文献投影规格下，反转候选仍保持唯一。 -/
theorem ordered_pair_reverse_paper_unique
    {free : SetContext} {Γ : Context signature free}
    (pair first second : SetOpenTerm free) :
    Γ ⊢ₘ[right_projection_operator_theory]
      ordered_pair_reverse_paper_spec pair first ⟶ₘ
        ordered_pair_reverse_paper_spec pair second ⟶ₘ
          (first ≐ₘ second) := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.imp_intro
  let Δ : Context signature free :=
    ordered_pair_reverse_paper_spec pair second ::
      ordered_pair_reverse_paper_spec pair first :: Γ
  have hFirstPaper :
      Δ ⊢ₘ[right_projection_operator_theory]
        ordered_pair_reverse_paper_spec pair first :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hSecondPaper :
      Δ ⊢ₘ[right_projection_operator_theory]
        ordered_pair_reverse_paper_spec pair second :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hFirstSpec := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (assumption := ordered_pair_reverse_paper_spec pair second)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := ordered_pair_reverse_paper_spec pair first)
        (ordered_pair_reverse_paper_spec_implies_spec
          (Γ := Γ) pair first)))
    hFirstPaper
  have hSecondSpec := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (assumption := ordered_pair_reverse_paper_spec pair second)
      (FirstOrder.Derives.context_weaken_cons
        (assumption := ordered_pair_reverse_paper_spec pair first)
        (ordered_pair_reverse_paper_spec_implies_spec
          (Γ := Γ) pair second)))
    hSecondPaper
  exact FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.imp_elim
      (ordered_pair_reverse_unique
        (T := right_projection_operator_theory) (Γ := Δ)
        pair first second)
      hFirstSpec)
    hSecondSpec

/-- 文献投影规格把候选识别为反转函数项。 -/
theorem ordered_pair_reverse_paper_spec_implies_eq_term
    {free : SetContext} {Γ : Context signature free}
    (pair candidate : SetOpenTerm free) :
    Γ ⊢ₘ[ordered_pair_reverse_operator_theory]
      ordered_pair_reverse_paper_spec pair candidate ⟶ₘ
        (candidate ≐ₘ pair⁻¹ₘ) := by
  apply FirstOrder.Derives.imp_intro
  let paper : SetOpenFormula free :=
    ordered_pair_reverse_paper_spec pair candidate
  let Δ : Context signature free := paper :: Γ
  have hPaper : Δ ⊢ₘ[ordered_pair_reverse_operator_theory] paper :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hSpec := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (assumption := paper)
      (FirstOrder.Derives.theory_weaken
        right_projection_operator_theory_subset_ordered_pair_reverse_operator_theory
        (ordered_pair_reverse_paper_spec_implies_spec
          (Γ := Γ) pair candidate)))
    hPaper
  have hDefinition := FirstOrder.Derives.context_weaken_cons
    (assumption := paper)
    (ordered_pair_reverse_definition_instance_derives
      (Γ := Γ) pair candidate)
  exact FirstOrder.Derives.iff_elim_right hDefinition hSpec

/-- 每个有序对都有交换两投影得到的文献反转候选。 -/
theorem is_ordered_pair_implies_ordered_pair_reverse_exists
    {free : SetContext} {Γ : Context signature free}
    (pair : SetOpenTerm free) :
    Γ ⊢ₘ[right_projection_operator_theory]
      is_ordered_pair_formula pair ⟶ₘ
        ordered_pair_reverse_exists pair := by
  apply FirstOrder.Derives.imp_intro
  let predicate : SetOpenFormula free := is_ordered_pair_formula pair
  let Δ : Context signature free := predicate :: Γ
  let swapped : SetOpenTerm free := ⟨(pair)₁ₘ, (pair)₀ₘ⟩ₘ
  have hSwappedOrdered :
      Δ ⊢ₘ[right_projection_operator_theory]
        is_ordered_pair_formula swapped :=
    FirstOrder.Derives.theory_weaken
      relation_function_theory_subset_right_projection_operator_theory
      (by simpa [swapped] using
        (ordered_pair_term_is_ordered_pair_derives
          (Γ := Δ) (pair)₁ₘ (pair)₀ₘ))
  have hSwappedLeft :
      Δ ⊢ₘ[right_projection_operator_theory]
        (swapped)₀ₘ ≐ₘ (pair)₁ₘ :=
    FirstOrder.Derives.theory_weaken
      left_projection_operator_theory_subset_right_projection_operator_theory
      (by simpa [swapped] using
        (ordered_pair_term_left_projection_eq
          (Γ := Δ) (pair)₁ₘ (pair)₀ₘ))
  have hSwappedRight :
      Δ ⊢ₘ[right_projection_operator_theory]
        (swapped)₁ₘ ≐ₘ (pair)₀ₘ := by
    simpa [swapped] using
      (ordered_pair_term_right_projection_eq
        (Γ := Δ) (pair)₁ₘ (pair)₀ₘ)
  have hPaper :
      Δ ⊢ₘ[right_projection_operator_theory]
        ordered_pair_reverse_paper_spec pair swapped := by
    unfold ordered_pair_reverse_paper_spec
    exact FirstOrder.Derives.conj_intro hSwappedOrdered
      (FirstOrder.Derives.conj_intro hSwappedLeft hSwappedRight)
  unfold ordered_pair_reverse_exists
  apply FirstOrder.Derives.exists_intro swapped
  rw [Formula.instantiateTop_abstractFreeTop]
  simpa [ordered_pair_reverse_paper_spec, swapped] using! hPaper

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
