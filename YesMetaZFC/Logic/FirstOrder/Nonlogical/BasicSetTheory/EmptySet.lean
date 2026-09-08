import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity
import YesMetaZFC.Logic.FirstOrder.Nonlogical.BasicSetTheory.Separation

/-!
# 空集

空集由恒假谓词的分离实例构造。所有元素、母集与候选集合均由内在类型上下文
约束；本层只保留存在唯一性、常量定义合同以及“无元素/非空”的数学接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Nonlogical
namespace BasicSetTheory

open scoped Symbols

/-- 恒假分离谓词。 -/
def empty_predicate {free : SetContext} : SetPredicate free where
  body := ¬ₘ ((.bvar .here : SetTerm [SetSort.set] free) ≐ₘ .bvar .here)

/-- 规范新元素不等于自身的否定条件。 -/
def empty_condition {bound free : SetContext} :
    SetFormula bound (SetSort.set :: free) :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  ¬ₘ (element ≐ₘ element)

/-- 一个集合没有元素的成员规格。 -/
def empty_set_spec {bound free : SetContext}
    (empty : SetTerm bound free) : SetFormula bound free :=
  membership_specification empty empty_condition

/-- 空集存在性的闭句。 -/
def empty_set_exists : SetSentence :=
  let candidate : SetOpenTerm [SetSort.set] := .fvar .here
  (empty_set_spec candidate).existsFreeTop SetSort.set

/-- 一个集合至少含有一个元素。 -/
def set_has_member {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  (element ∈ₘ source.weakenFree SetSort.set).existsFreeTop SetSort.set

/-- 一个集合没有任何元素。 -/
def set_has_no_members {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  let element : SetTerm bound (SetSort.set :: free) := .fvar .here
  (¬ₘ (element ∈ₘ source.weakenFree SetSort.set)).forallFreeTop SetSort.set

/-- 一个集合不等于空集常量。 -/
def set_nonempty_condition {bound free : SetContext}
    (source : SetTerm bound free) : SetFormula bound free :=
  ¬ₘ (source ≐ₘ (∅ₘ : SetTerm bound free))

/-- 由恒假分离实例生成的空集理论。 -/
def empty_set_theory : SetTheory :=
  (empty_predicate (free := [])).separation_theory

/-- 空集常量的定义实例。 -/
def empty_set_definition_instance {bound free : SetContext}
    (candidate : SetTerm bound free) : SetFormula bound free :=
  (candidate ≐ₘ (∅ₘ : SetTerm bound free)) ↔ₘ empty_set_spec candidate

/-- 空集常量的闭定义公理。 -/
def empty_set_definition_axiom : SetSentence :=
  let candidate : SetOpenTerm [SetSort.set] := .fvar .here
  Metatheory.Formula.forall_close
    (empty_set_definition_instance candidate)

/-- 在空集存在理论上加入空集常量定义。 -/
def empty_set_symbol_theory : SetTheory :=
  Theory.insert empty_set_definition_axiom empty_set_theory

/-- 恒假分离规格等价于空集规格。 -/
theorem empty_separation_spec_iff
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (source empty : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (empty_predicate.separation_spec source empty) ↔ₘ
        empty_set_spec empty := by
  unfold SetPredicate.separation_spec empty_set_spec
  apply Metatheory.Derives.forall_iff_mono
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let member : SetOpenFormula (SetSort.set :: free) :=
    element ∈ₘ empty.weakenFree SetSort.set
  let sourceMember : SetOpenFormula (SetSort.set :: free) :=
    element ∈ₘ source.weakenFree SetSort.set
  let reflexive : SetOpenFormula (SetSort.set :: free) :=
    element ≐ₘ element
  have hReflexive :
      FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T] reflexive := by
    simpa [reflexive] using
      (Metatheory.Derives.equality_refl
        (T := T) (Γ := FreshVariable.extendContext SetSort.set Γ) element)
  have hSchema :
      FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
        reflexive ⟶ₘ
          ((member ↔ₘ (sourceMember ∧ₘ ¬ₘ reflexive)) ↔ₘ
            (member ↔ₘ ¬ₘ reflexive)) := by
    apply FirstOrder.Derives.imp_intro
    apply FirstOrder.Derives.iff_intro
    · apply FirstOrder.Derives.iff_intro
      · have hLeft := FirstOrder.Derives.iff_elim_left
          (FirstOrder.Derives.assumption (T := T) (by simp :
            (member ↔ₘ (sourceMember ∧ₘ ¬ₘ reflexive)) ∈
              (member ::
                (member ↔ₘ (sourceMember ∧ₘ ¬ₘ reflexive)) ::
                  reflexive :: FreshVariable.extendContext SetSort.set Γ)))
          (FirstOrder.Derives.assumption (T := T) List.mem_cons_self)
        exact FirstOrder.Derives.conj_elim_right hLeft
      · have hNotReflexive :
            (¬ₘ reflexive) ::
              (member ↔ₘ (sourceMember ∧ₘ ¬ₘ reflexive)) ::
                reflexive :: FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
              ¬ₘ reflexive :=
          FirstOrder.Derives.assumption (T := T) List.mem_cons_self
        have hSourceMember :
            (¬ₘ reflexive) ::
              (member ↔ₘ (sourceMember ∧ₘ ¬ₘ reflexive)) ::
                reflexive :: FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
              sourceMember :=
          FirstOrder.Derives.contradiction_elim
          (FirstOrder.Derives.assumption (T := T) (by simp : reflexive ∈
            ((¬ₘ reflexive) ::
              (member ↔ₘ (sourceMember ∧ₘ ¬ₘ reflexive)) ::
                reflexive :: FreshVariable.extendContext SetSort.set Γ)))
          hNotReflexive
        have hConjunction := FirstOrder.Derives.conj_intro
          hSourceMember hNotReflexive
        exact FirstOrder.Derives.iff_elim_right
          (FirstOrder.Derives.assumption (T := T) (by simp :
            (member ↔ₘ (sourceMember ∧ₘ ¬ₘ reflexive)) ∈
              ((¬ₘ reflexive) ::
                (member ↔ₘ (sourceMember ∧ₘ ¬ₘ reflexive)) ::
                  reflexive :: FreshVariable.extendContext SetSort.set Γ)))
          hConjunction
    · apply FirstOrder.Derives.iff_intro
      · have hNotReflexive := FirstOrder.Derives.iff_elim_left
          (FirstOrder.Derives.assumption (T := T) (by simp :
            (member ↔ₘ ¬ₘ reflexive) ∈
              (member :: (member ↔ₘ ¬ₘ reflexive) :: reflexive ::
                FreshVariable.extendContext SetSort.set Γ)))
          (FirstOrder.Derives.assumption (T := T) List.mem_cons_self)
        have hSourceMember :
            member :: (member ↔ₘ ¬ₘ reflexive) :: reflexive ::
              FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
                sourceMember :=
          FirstOrder.Derives.contradiction_elim
          (FirstOrder.Derives.assumption (T := T) (by simp : reflexive ∈
            (member :: (member ↔ₘ ¬ₘ reflexive) :: reflexive ::
              FreshVariable.extendContext SetSort.set Γ)))
          hNotReflexive
        exact FirstOrder.Derives.conj_intro hSourceMember hNotReflexive
      · have hConjunction :
            (sourceMember ∧ₘ ¬ₘ reflexive) ::
              (member ↔ₘ ¬ₘ reflexive) :: reflexive ::
                FreshVariable.extendContext SetSort.set Γ ⊢ₘ[T]
                  sourceMember ∧ₘ ¬ₘ reflexive :=
          FirstOrder.Derives.assumption (T := T) List.mem_cons_self
        exact FirstOrder.Derives.iff_elim_right
          (FirstOrder.Derives.assumption (T := T) (by simp :
            (member ↔ₘ ¬ₘ reflexive) ∈
              ((sourceMember ∧ₘ ¬ₘ reflexive) ::
                (member ↔ₘ ¬ₘ reflexive) :: reflexive ::
                  FreshVariable.extendContext SetSort.set Γ)))
          (FirstOrder.Derives.conj_elim_right hConjunction)
  simpa [SetPredicate.separation_condition, SetPredicate.atNewest,
    empty_condition, empty_predicate, element, member, sourceMember,
    reflexive, FreshVariable.newest] using!
    FirstOrder.Derives.imp_elim hSchema hReflexive

/-- 同一空集规格的两个候选相等。 -/
theorem empty_set_unique
    {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[extensionality_theory]
      empty_set_spec left ⟶ₘ empty_set_spec right ⟶ₘ (left ≐ₘ right) := by
  simpa [empty_set_spec] using
    (membership_specification_unique
      (Γ := Γ) left right (empty_condition (bound := []) (free := free)))

/-- 空集常量定义公理可在任意候选项处实例化。 -/
theorem empty_set_definition_instance_derives
    {free : SetContext} {Γ : Context signature free}
    (candidate : SetOpenTerm free) :
    Γ ⊢ₘ[empty_set_symbol_theory]
      empty_set_definition_instance candidate := by
  let body : SetOpenFormula [SetSort.set] :=
    empty_set_definition_instance
      (FreshVariable.newest (σ := signature) (free := []) SetSort.set)
  let τ : VariableSubstitution signature [SetSort.set] [] free :=
    VariableSubstitution.cons candidate VariableSubstitution.empty
  have hClosed :
      ([] : Context signature []) ⊢ₘ[empty_set_symbol_theory]
        Formula.fromSentence empty_set_definition_axiom :=
    FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
  have hInstance := Metatheory.Derives.forall_close_elim
    (Γ := Γ) body τ hClosed
  simpa [body, τ, empty_set_definition_axiom,
    empty_set_definition_instance, empty_set_spec, empty_condition,
    membership_specification, FreshVariable.newest,
    Formula.substituteFree, Substitution.free_map,
    Formula.substitute, Formula.substituteMapped,
    Term.substituteMapped, Arguments.substituteMapped,
    VariableSubstitution.cons, VariableSubstitution.empty,
    VariableSubstitution.liftFree,
    VariableSubstitution.weakenBound,
    VariableSubstitution.boundId,
    VariableSubstitution.freeId] using! hInstance

/-- 空集常量满足空集规格。 -/
theorem empty_set_term_spec_derives
    {free : SetContext} {Γ : Context signature free} :
    Γ ⊢ₘ[empty_set_symbol_theory]
      empty_set_spec (∅ₘ : SetOpenTerm free) := by
  have hDefinition := empty_set_definition_instance_derives
    (Γ := Γ) (∅ₘ : SetOpenTerm free)
  exact FirstOrder.Derives.iff_elim_left hDefinition
    (Metatheory.Derives.equality_refl
      (T := empty_set_symbol_theory) (Γ := Γ)
      (∅ₘ : SetOpenTerm free))

/-- 满足空集规格的候选等于空集常量。 -/
theorem empty_set_eq_term_of_spec
    {free : SetContext} {Γ : Context signature free}
    (candidate : SetOpenTerm free) :
    Γ ⊢ₘ[empty_set_symbol_theory]
      empty_set_spec candidate ⟶ₘ (candidate ≐ₘ ∅ₘ) := by
  apply FirstOrder.Derives.imp_intro
  have hDefinition := empty_set_definition_instance_derives
    (Γ := empty_set_spec candidate :: Γ) candidate
  exact FirstOrder.Derives.iff_elim_right hDefinition
    (FirstOrder.Derives.assumption List.mem_cons_self)

/-- 空集规格推出没有任何元素。 -/
theorem empty_set_has_no_members
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (empty : SetOpenTerm free) :
    Γ ⊢ₘ[T] empty_set_spec empty ⟶ₘ set_has_no_members empty := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.forall_intro
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let member : SetOpenFormula (SetSort.set :: free) :=
    element ∈ₘ empty.weakenFree SetSort.set
  let reflexive : SetOpenFormula (SetSort.set :: free) :=
    element ≐ₘ element
  have hSpecification :
      FreshVariable.extendContext SetSort.set (empty_set_spec empty :: Γ) ⊢ₘ[T]
        (empty_set_spec empty).weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [FreshVariable.extendContext])
  have hAt := FirstOrder.Derives.forall_elim_newest_weakened hSpecification
  have hReflexive := Metatheory.Derives.equality_refl
    (T := T)
    (Γ := FreshVariable.extendContext SetSort.set (empty_set_spec empty :: Γ))
    element
  have hSchema :
      FreshVariable.extendContext SetSort.set (empty_set_spec empty :: Γ) ⊢ₘ[T]
        (member ↔ₘ ¬ₘ reflexive) ⟶ₘ
          (reflexive ⟶ₘ ¬ₘ member) := by
    apply FirstOrder.Derives.imp_intro
    apply FirstOrder.Derives.imp_intro
    apply FirstOrder.Derives.neg_intro
    have hNotReflexive := FirstOrder.Derives.iff_elim_left
      (FirstOrder.Derives.assumption (T := T) (by simp :
        (member ↔ₘ ¬ₘ reflexive) ∈
          (member :: reflexive :: (member ↔ₘ ¬ₘ reflexive) ::
            FreshVariable.extendContext SetSort.set
              (empty_set_spec empty :: Γ))))
      (FirstOrder.Derives.assumption (T := T) List.mem_cons_self)
    exact FirstOrder.Derives.neg_elim
      (FirstOrder.Derives.assumption (T := T) (by simp : reflexive ∈
        (member :: reflexive :: (member ↔ₘ ¬ₘ reflexive) ::
          FreshVariable.extendContext SetSort.set
            (empty_set_spec empty :: Γ))))
      hNotReflexive
  simpa [empty_set_spec, empty_condition, set_has_no_members,
    membership_specification, element, member, reflexive,
    FreshVariable.newest] using!
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hSchema hAt) hReflexive

/-- 无元素的集合满足任意右端集合的子集条件。 -/
theorem no_members_implies_subset_condition
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (left right : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      set_has_no_members left ⟶ₘ subset_condition left right := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.forall_intro
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let leftMember : SetOpenFormula (SetSort.set :: free) :=
    element ∈ₘ left.weakenFree SetSort.set
  let rightMember : SetOpenFormula (SetSort.set :: free) :=
    element ∈ₘ right.weakenFree SetSort.set
  have hUniversal :
      FreshVariable.extendContext SetSort.set (set_has_no_members left :: Γ) ⊢ₘ[T]
        (set_has_no_members left).weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [FreshVariable.extendContext])
  have hNotMember := FirstOrder.Derives.forall_elim_newest_weakened hUniversal
  have hSchema :
      FreshVariable.extendContext SetSort.set (set_has_no_members left :: Γ) ⊢ₘ[T]
        (¬ₘ leftMember) ⟶ₘ (leftMember ⟶ₘ rightMember) := by
    apply FirstOrder.Derives.imp_intro
    apply FirstOrder.Derives.imp_intro
    exact FirstOrder.Derives.contradiction_elim
      (FirstOrder.Derives.assumption List.mem_cons_self)
      (FirstOrder.Derives.assumption (by simp))
  simpa [set_has_no_members, subset_condition,
    element, leftMember, rightMember, FreshVariable.newest] using!
    FirstOrder.Derives.imp_elim hSchema hNotMember

/-- 满足空集规格的集合是任意集合的子集。 -/
theorem empty_set_subset
    {free : SetContext} {Γ : Context signature free}
    (empty set : SetOpenTerm free) :
    Γ ⊢ₘ[subset_theory]
      empty_set_spec empty ⟶ₘ (empty ⊆ₘ set) := by
  apply FirstOrder.Derives.imp_intro
  have hNoMembers := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (empty_set_has_no_members (T := subset_theory) (Γ := Γ) empty))
    (FirstOrder.Derives.assumption List.mem_cons_self)
  have hCondition := FirstOrder.Derives.imp_elim
    (FirstOrder.Derives.context_weaken_cons
      (no_members_implies_subset_condition
        (T := subset_theory) (Γ := Γ) empty set))
    hNoMembers
  have hDefinition := subset_definition_instance_derives
    (Γ := empty_set_spec empty :: Γ) empty set
  exact FirstOrder.Derives.iff_elim_right hDefinition hCondition

/-- 空集常量没有任何给定元素。 -/
theorem empty_set_term_has_no_members
    {free : SetContext} {Γ : Context signature free}
    (element : SetOpenTerm free) :
    Γ ⊢ₘ[empty_set_symbol_theory]
      ¬ₘ (element ∈ₘ (∅ₘ : SetOpenTerm free)) := by
  have hNoMembers := FirstOrder.Derives.imp_elim
    (empty_set_has_no_members
      (T := empty_set_symbol_theory) (Γ := Γ)
      (∅ₘ : SetOpenTerm free))
    (empty_set_term_spec_derives (Γ := Γ))
  have hAt := FirstOrder.Derives.forall_elim element hNoMembers
  simpa [set_has_no_members] using! hAt

/-- 一个实际成员推出其容器不等于空集常量。 -/
theorem member_implies_set_nonempty
    {free : SetContext} {Γ : Context signature free}
    (element source : SetOpenTerm free) :
    Γ ⊢ₘ[empty_set_symbol_theory]
      (element ∈ₘ source) ⟶ₘ set_nonempty_condition source := by
  apply FirstOrder.Derives.imp_intro
  unfold set_nonempty_condition
  apply FirstOrder.Derives.neg_intro
  have hMember :
      ((source ≐ₘ ∅ₘ) :: (element ∈ₘ source) :: Γ) ⊢ₘ[empty_set_symbol_theory]
        element ∈ₘ source :=
    FirstOrder.Derives.assumption (by simp)
  have hEquality :
      ((source ≐ₘ ∅ₘ) :: (element ∈ₘ source) :: Γ) ⊢ₘ[empty_set_symbol_theory]
        source ≐ₘ ∅ₘ :=
    FirstOrder.Derives.assumption List.mem_cons_self
  have hTransport := membership_right_iff_of_equality
    (T := empty_set_symbol_theory)
    (Γ := (source ≐ₘ ∅ₘ) :: (element ∈ₘ source) :: Γ)
    element source (∅ₘ : SetOpenTerm free) hEquality
  have hEmptyMember := FirstOrder.Derives.iff_elim_left hTransport hMember
  exact FirstOrder.Derives.neg_elim hEmptyMember
    (empty_set_term_has_no_members
      (Γ := (source ≐ₘ ∅ₘ) :: (element ∈ₘ source) :: Γ) element)

/-- 若不存在成员，则该集合满足空集规格。 -/
theorem not_set_has_member_implies_empty_set_spec
    {T : SetTheory} {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[T]
      (¬ₘ set_has_member source) ⟶ₘ empty_set_spec source := by
  apply FirstOrder.Derives.imp_intro
  apply FirstOrder.Derives.forall_intro
  let element : SetOpenTerm (SetSort.set :: free) :=
    FreshVariable.newest
      (σ := signature) (free := free) SetSort.set
  let member : SetOpenFormula (SetSort.set :: free) :=
    element ∈ₘ source.weakenFree SetSort.set
  let reflexive : SetOpenFormula (SetSort.set :: free) :=
    element ≐ₘ element
  have hNoExistence :
      FreshVariable.extendContext SetSort.set ((¬ₘ set_has_member source) :: Γ) ⊢ₘ[T]
        (¬ₘ set_has_member source).weakenFree SetSort.set :=
    FirstOrder.Derives.assumption (by
      simp [FreshVariable.extendContext])
  have hNotMember :
      FreshVariable.extendContext SetSort.set ((¬ₘ set_has_member source) :: Γ) ⊢ₘ[T]
        ¬ₘ member := by
    apply FirstOrder.Derives.neg_intro
    have hMember :
        (member :: FreshVariable.extendContext SetSort.set
          ((¬ₘ set_has_member source) :: Γ)) ⊢ₘ[T] member :=
      FirstOrder.Derives.assumption List.mem_cons_self
    have hExists := FirstOrder.Derives.exists_intro_newest hMember
    have hExists' :
        (member :: FreshVariable.extendContext SetSort.set
          ((¬ₘ set_has_member source) :: Γ)) ⊢ₘ[T]
            (set_has_member source).weakenFree SetSort.set := by
      simpa [set_has_member, member, element, FreshVariable.newest] using! hExists
    have hNoExistence' :
        FreshVariable.extendContext SetSort.set
          ((¬ₘ set_has_member source) :: Γ) ⊢ₘ[T]
            ¬ₘ (set_has_member source).weakenFree SetSort.set := by
      simpa using hNoExistence
    exact FirstOrder.Derives.neg_elim hExists'
      (FirstOrder.Derives.context_weaken_cons
        (assumption := member) hNoExistence')
  have hReflexive := Metatheory.Derives.equality_refl
    (T := T)
    (Γ := FreshVariable.extendContext SetSort.set ((¬ₘ set_has_member source) :: Γ))
    element
  have hSchema :
      FreshVariable.extendContext SetSort.set ((¬ₘ set_has_member source) :: Γ) ⊢ₘ[T]
        (¬ₘ member) ⟶ₘ
          (reflexive ⟶ₘ (member ↔ₘ ¬ₘ reflexive)) := by
    apply FirstOrder.Derives.imp_intro
    apply FirstOrder.Derives.imp_intro
    apply FirstOrder.Derives.iff_intro
    · exact FirstOrder.Derives.contradiction_elim
        (FirstOrder.Derives.assumption List.mem_cons_self)
        (FirstOrder.Derives.assumption (by simp))
    · exact FirstOrder.Derives.contradiction_elim
        (FirstOrder.Derives.assumption (by simp))
        (FirstOrder.Derives.assumption List.mem_cons_self)
  simpa [set_has_member, empty_set_spec, empty_condition,
    membership_specification, element, member, reflexive,
    FreshVariable.newest] using!
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.imp_elim hSchema hNotMember) hReflexive

/-- 没有成员的集合等于空集常量。 -/
theorem not_set_has_member_implies_eq_empty
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[empty_set_symbol_theory]
      (¬ₘ set_has_member source) ⟶ₘ (source ≐ₘ ∅ₘ) := by
  exact Metatheory.Derives.imp_trans
    (not_set_has_member_implies_empty_set_spec
      (T := empty_set_symbol_theory) (Γ := Γ) source)
    (empty_set_eq_term_of_spec (Γ := Γ) source)

/-- 不等于空集常量的集合必有成员。 -/
theorem set_nonempty_implies_has_member
    {free : SetContext} {Γ : Context signature free}
    (source : SetOpenTerm free) :
    Γ ⊢ₘ[empty_set_symbol_theory]
      set_nonempty_condition source ⟶ₘ set_has_member source := by
  let hasMember : SetOpenFormula free := set_has_member source
  let equalEmpty : SetOpenFormula free := source ≐ₘ (∅ₘ : SetOpenTerm free)
  have hNoMember := not_set_has_member_implies_eq_empty
    (Γ := Γ) source
  apply FirstOrder.Derives.imp_intro
  apply Metatheory.Derives.of_neg_assumption_contradiction
      (φ := hasMember) (ψ := equalEmpty)
  · exact FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken_cons
        (assumption := ¬ₘ hasMember)
        (FirstOrder.Derives.context_weaken_cons
          (assumption := ¬ₘ equalEmpty) hNoMember))
      (FirstOrder.Derives.assumption List.mem_cons_self)
  · exact FirstOrder.Derives.assumption (by simp :
      (¬ₘ equalEmpty) ∈
        ((¬ₘ hasMember) :: (¬ₘ equalEmpty) :: Γ))

/-- 恒假分离公理推出空集存在。 -/
theorem empty_set_exists_derives :
    ([] : Context signature []) ⊢ₘ[empty_set_theory] empty_set_exists := by
  let predicate : SetPredicate [] := empty_predicate
  have hAxiom :
      ([] : Context signature []) ⊢ₘ[empty_set_theory]
        predicate.separation_open_axiom := by
    have hClosed :
        ([] : Context signature []) ⊢ₘ[empty_set_theory]
          Formula.fromSentence predicate.separation_axiom :=
      FirstOrder.Derives.theory_axiom (by exact Or.inl rfl)
    simpa [predicate, SetPredicate.separation_axiom,
      Metatheory.Formula.forall_close,
      Formula.fromSentence, Renaming.emptyFree] using hClosed
  have hSourceExists :
      ([] : Context signature []) ⊢ₘ[empty_set_theory]
        ((Term.newestFree (σ := signature) (bound := []) (free := [])
            SetSort.set ≐ₘ
          Term.newestFree (σ := signature) (bound := []) (free := [])
            SetSort.set).existsFreeTop SetSort.set) :=
    FirstOrder.Derives.of_empty first_existence
  apply FirstOrder.Derives.exists_elim hSourceExists
  let source : SetOpenTerm [SetSort.set] :=
    FreshVariable.newest
      (σ := signature) (free := []) SetSort.set
  let sourceReflexive : SetOpenFormula [SetSort.set] := source ≐ₘ source
  have hAxiomAt :
      (sourceReflexive :: ([] : Context signature [SetSort.set])) ⊢ₘ[empty_set_theory]
        predicate.separation_open_axiom.weakenFree SetSort.set := by
    have hWeak := FirstOrder.Derives.free_renaming
      (T := empty_set_theory) (VariableRenaming.weaken SetSort.set) hAxiom
    exact FirstOrder.Derives.context_weaken_cons
      (by simpa [predicate] using! hWeak)
  have hSeparation := FirstOrder.Derives.forall_elim_newest_weakened hAxiomAt
  have hMap :
      (sourceReflexive :: ([] : Context signature [SetSort.set])) ⊢ₘ[empty_set_theory]
        (empty_predicate.separation_exists source) ⟶ₘ
          (empty_set_exists.weakenFree SetSort.set) := by
    let target : SetOpenTerm [SetSort.set, SetSort.set] :=
      FreshVariable.newest
        (σ := signature) (free := [SetSort.set]) SetSort.set
    have hMapped :
        (sourceReflexive :: ([] : Context signature [SetSort.set])) ⊢ₘ[empty_set_theory]
          (empty_predicate.separation_exists source) ⟶ₘ
            ((empty_set_spec target).existsFreeTop SetSort.set) := by
      apply Metatheory.Derives.exists_imp_mono
      have hEquivalent := empty_separation_spec_iff
        (T := empty_set_theory)
        (Γ := FreshVariable.extendContext SetSort.set
          (sourceReflexive :: ([] : Context signature [SetSort.set])))
        (source.weakenFree SetSort.set) target
      apply FirstOrder.Derives.imp_intro
      have hEquivalent' :
          (empty_predicate.separation_spec
              (source.weakenFree SetSort.set) target ::
            FreshVariable.extendContext SetSort.set
              (sourceReflexive :: ([] : Context signature [SetSort.set])))
              ⊢ₘ[empty_set_theory]
                (empty_predicate.separation_spec
                    (source.weakenFree SetSort.set) target ↔ₘ
                  empty_set_spec target) :=
        FirstOrder.Derives.context_weaken_cons
          (assumption := empty_predicate.separation_spec
            (source.weakenFree SetSort.set) target) hEquivalent
      have hAssumption :
          (empty_predicate.separation_spec
              (source.weakenFree SetSort.set) target ::
            FreshVariable.extendContext SetSort.set
              (sourceReflexive :: ([] : Context signature [SetSort.set])))
              ⊢ₘ[empty_set_theory]
                empty_predicate.separation_spec
                  (source.weakenFree SetSort.set) target :=
        FirstOrder.Derives.assumption List.mem_cons_self
      exact FirstOrder.Derives.iff_elim_left hEquivalent' hAssumption
    simpa [empty_set_exists, target, FreshVariable.newest] using! hMapped
  have hSeparation' :
      (sourceReflexive :: ([] : Context signature [SetSort.set])) ⊢ₘ[empty_set_theory]
        empty_predicate.separation_exists source := by
    simpa [predicate, source, sourceReflexive,
      FreshVariable.extendContext] using! hSeparation
  exact FirstOrder.Derives.imp_elim hMap hSeparation'

end BasicSetTheory
end Nonlogical
end FirstOrder
end Logic
end YesMetaZFC
