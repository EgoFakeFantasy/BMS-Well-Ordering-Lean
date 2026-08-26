import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Substitution

/-!
# 等式原子的替换合同

等式的两个源项作为长度固定的参数表统一编译。该表示把左右两段连续见证区间交给
现有参数表闭包处理，使见证重定位与关系原子保持同一证明结构。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination

universe u v w

set_option autoImplicit false

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]

/-- 长度为二的编译值表解释为等式；其余分支只用于给出总函数。 -/
private def equality_core : List (Term σ) → Formula σ
  | [left, right] =>
      Formula.equal left right
  | _ =>
      Formula.falsum

/-- 任意起点的等式原子扁平编译。 -/
def equality_flat
    (D : Data σ) (start : Nat)
    (left right : Term σ) : Formula σ :=
  terms_flat_closure D start [left, right]
    equality_core

omit [DecidableEq σ.FuncSymbol] in
private theorem equality_core_admissible
    {sort : σ.SortSymbol}
    {values : List (Term σ)}
    (hValues :
      ArgsAdmissible values [sort, sort]) :
    Formula.Admissible (equality_core values) := by
  rcases hValues with ⟨hSorted, hScoped⟩
  cases hSorted with
  | cons hLeft hTail =>
      cases hTail with
      | cons hRight hRest =>
          cases hRest
          exact Formula.Admissible.equal
            ⟨hLeft, hScoped _ (by simp)⟩
            ⟨hRight, hScoped _ (by simp)⟩

omit [DecidableEq σ.FuncSymbol] in
private theorem equality_core_iff_of_equalities
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol}
    {left right : List (Term σ)}
    (hLeft :
      ArgsAdmissible left [sort, sort])
    (hRight :
      ArgsAdmissible right [sort, sort])
    (hEqual :
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
        T Γ left right) :
    Derives T Γ
      (Formula.iff
        (equality_core left)
        (equality_core right)) := by
  rcases hLeft with ⟨hLeftSorted, hLeftScoped⟩
  rcases hRight with ⟨hRightSorted, hRightScoped⟩
  cases hLeftSorted with
  | cons hLeftHead hLeftTail =>
      cases hLeftTail with
      | cons hLeftSecond hLeftRest =>
          cases hLeftRest
          cases hRightSorted with
          | cons hRightHead hRightTail =>
              cases hRightTail with
              | cons hRightSecond hRightRest =>
                  cases hRightRest
                  cases hEqual with
                  | cons hHead hTail =>
                      cases hTail with
                      | cons hSecond hRest =>
                          cases hRest
                          exact
                            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_iff_of_equalities
                              ⟨hLeftHead,
                                hLeftScoped _ (by simp)⟩
                              ⟨hRightHead,
                                hRightScoped _ (by simp)⟩
                              ⟨hLeftSecond,
                                hLeftScoped _ (by simp)⟩
                              ⟨hRightSecond,
                                hRightScoped _ (by simp)⟩
                              hHead hSecond

/-- 任意起点的等式扁平闭包不暴露偶数见证变量。 -/
theorem equality_flat_witness_fresh
    (D : Data σ) (start : Nat)
    (left right : Term σ) (index : Nat) :
    (D.sort, witness_id index) ∉
      Formula.freeSupport
        (equality_flat D start left right) := by
  let compiled := terms D start [left, right]
  have hNext : start ≤ compiled.next := by
    simpa [compiled] using
      terms_next_ge D start [left, right]
  have hCount :
      start +
          ((terms D start [left, right]).next - start) =
        (terms D start [left, right]).next := by
    simpa [compiled] using
      (show start + (compiled.next - start) =
          compiled.next by
        omega)
  apply close_witnesses_from_witness_fresh
  intro hOutside
  apply condition_conjunction_fresh
  · intro condition hCondition
    rcases hOutside with hBelow | hAbove
    · exact terms_conditions_witness_fresh_below
        D start [left, right] hBelow condition <| by
          simpa [compiled] using hCondition
    · exact terms_conditions_witness_fresh_above
        D start [left, right] (by
          rw [hCount] at hAbove
          exact hAbove)
        condition <| by
          simpa [compiled] using hCondition
  · rcases hOutside with hBelow | hAbove
    · simpa [equality_core, Formula.freeSupport,
        Term.freeSupportList, compiled, terms] using
        terms_values_witness_fresh_below
          D start [left, right] hBelow
    · simpa [equality_core, Formula.freeSupport,
        Term.freeSupportList, compiled, terms] using
        terms_values_witness_fresh_above
          D start [left, right] (by
            rw [hCount] at hAbove
            exact hAbove)

/--
等式扁平闭包的源变量替换，等于对两项编译结果逐条件、逐值替换后的闭包。
-/
theorem equality_flat_substituteFree
    (D : Data σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ)
    (start : Nat) (left right : Term σ)
    (hClosed : Term.BoundClosed replacement)
    (hFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start [left, right]).next →
          (D.sort, witness_id index) ∉
            Term.freeSupport replacement) :
    Formula.substituteFree target (source_id id)
        replacement
        (equality_flat D start left right) =
      let parameterized :=
        (terms D start [left, right]).substituteFree
          target (source_id id) replacement
      close_witnesses_from D.sort start
        (parameterized.next - start)
        (condition_conjunction
          parameterized.conditions
          (equality_core parameterized.values)) := by
  rw [equality_flat,
    terms_flat_closure_substituteFree
      D target id replacement start [left, right]
        equality_core hClosed hFresh]
  simp [ArgsResult.substituteFree,
    equality_core, terms, Formula.substituteFree]

namespace GraphPresentation

variable {D : Data σ}

/--
两个不相交见证区间编译同一等式原子时，左侧闭包可在图理论中重建右侧闭包。
-/
theorem equality_flat_imp_of_disjoint
    (P : GraphPresentation D)
    {left right : Term σ} {sort : σ.SortSymbol}
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort)
    (leftStart rightStart : Nat)
    (hDisjoint :
      (terms D leftStart [left, right]).next ≤
          rightStart ∨
        (terms D rightStart [left, right]).next ≤
          leftStart) :
    Derives P.theory []
      (Formula.imp
        (equality_flat D leftStart left right)
        (equality_flat D rightStart left right)) := by
  let sources := [left, right]
  let sorts := [sort, sort]
  let leftCompiled := terms D leftStart sources
  let rightCompiled := terms D rightStart sources
  let leftFormula :=
    equality_flat D leftStart left right
  let rightFormula :=
    equality_flat D rightStart left right
  have hSources :
      ArgsAdmissible sources sorts := by
    exact ArgsAdmissible.cons hLeft <|
      ArgsAdmissible.cons hRight
        ArgsAdmissible.nil
  have hLeftValues :
      ArgsAdmissible leftCompiled.values sorts := by
    simpa [leftCompiled] using
      terms_admissible D leftStart hSources
  have hRightValues :
      ArgsAdmissible rightCompiled.values sorts := by
    simpa [rightCompiled] using
      terms_admissible D rightStart hSources
  have hLeftFormula :
      Formula.Admissible leftFormula := by
    exact terms_flat_closure_admissible
      D leftStart hSources equality_core
      equality_core_admissible
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        hLeftFormula)
  let Γ : Context σ := [leftFormula]
  have hLeftClosed :
      Derives P.theory Γ leftFormula :=
    Derives.assumption_of_mem
      (by simp [Γ])
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          hLeftFormula)
  change Derives P.theory Γ rightFormula
  apply P.terms_flat_elim_to_conditions
      leftStart hSources equality_core
  · exact equality_core_admissible
  · intro index hLower hUpper formula hFormula
    have hFormulaEq : formula = leftFormula :=
      List.mem_singleton.mp <| by
        simpa [Γ] using hFormula
    subst formula
    exact equality_flat_witness_fresh
      D leftStart left right index
  · intro index hLower hUpper
    exact equality_flat_witness_fresh
      D rightStart left right index
  · simpa [leftFormula, Γ] using hLeftClosed
  · let Δ : Context σ :=
      leftCompiled.conditions ++
        equality_core leftCompiled.values :: Γ
    apply P.terms_flat_derives_from_conditions
        rightStart hSources
        (Γ := Δ)
        (continuation := equality_core)
    · intro index hLower hUpper formula hFormula
      rcases List.mem_append.mp hFormula with
        hCondition | hFormula
      · rcases hDisjoint with hBefore | hAfter
        · exact terms_conditions_witness_fresh_above
            D leftStart sources
              (Nat.le_trans hBefore hLower)
              formula <| by
                simpa [leftCompiled] using hCondition
        · exact terms_conditions_witness_fresh_below
            D leftStart sources
              (Nat.lt_of_lt_of_le
                hUpper hAfter)
              formula <| by
                simpa [leftCompiled] using hCondition
      · rcases List.mem_cons.mp hFormula with
          rfl | hFormula
        · rcases hDisjoint with hBefore | hAfter
          · simpa [equality_core,
              Formula.freeSupport, Term.freeSupportList,
              leftCompiled, sources, terms] using
              terms_values_witness_fresh_above
                D leftStart sources
                  (Nat.le_trans hBefore hLower)
          · simpa [equality_core,
              Formula.freeSupport, Term.freeSupportList,
              leftCompiled, sources, terms] using
              terms_values_witness_fresh_below
                D leftStart sources
                  (Nat.lt_of_lt_of_le
                    hUpper hAfter)
        · have hFormulaEq :
              formula = leftFormula :=
            List.mem_singleton.mp <| by
              simpa [Γ] using hFormula
          subst formula
          exact equality_flat_witness_fresh
            D leftStart left right index
    · exact equality_core_admissible
    · have hEqual :=
        terms_compiled_eq P
          leftStart rightStart hSources
      have hEqual' :
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.TermwiseEquality
            P.theory
            (rightCompiled.conditions ++ Δ)
            leftCompiled.values
            rightCompiled.values := by
        apply hEqual.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hLeftCondition | hRightCondition
        · exact List.mem_append.mpr <| Or.inr <|
            List.mem_append.mpr <| Or.inl <| by
              simpa [leftCompiled] using
                hLeftCondition
        · exact List.mem_append.mpr <| Or.inl <| by
            simpa [rightCompiled] using
              hRightCondition
      have hEquivalent :=
        equality_core_iff_of_equalities
          hLeftValues hRightValues hEqual'
      have hLeftCore :
          Derives P.theory
            (rightCompiled.conditions ++ Δ)
            (equality_core leftCompiled.values) :=
        Derives.assumption_of_mem
          (List.mem_append.mpr <| Or.inr <|
            List.mem_append.mpr <| Or.inr <| by
              simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible <|
              equality_core_admissible hLeftValues)
      exact Derives.iff_elim_right
        hEquivalent hLeftCore

/-- 不相交见证区间中的两份等式原子扁平编译逻辑等价。 -/
theorem equality_flat_iff_of_disjoint
    (P : GraphPresentation D)
    {left right : Term σ} {sort : σ.SortSymbol}
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort)
    (leftStart rightStart : Nat)
    (hDisjoint :
      (terms D leftStart [left, right]).next ≤
          rightStart ∨
        (terms D rightStart [left, right]).next ≤
          leftStart) :
    Derives P.theory []
      (Formula.iff
        (equality_flat D leftStart left right)
        (equality_flat D rightStart left right)) := by
  apply Derives.iff_intro
  · exact Derives.imp_elim_assumption <|
      equality_flat_imp_of_disjoint P
        hLeft hRight leftStart rightStart hDisjoint
  · have hDisjoint' :
        (terms D rightStart [left, right]).next ≤
            leftStart ∨
          (terms D leftStart [left, right]).next ≤
            rightStart :=
      hDisjoint.elim Or.inr Or.inl
    exact Derives.imp_elim_assumption <|
      equality_flat_imp_of_disjoint P
        hLeft hRight rightStart leftStart hDisjoint'

/-- 同一等式原子的扁平编译与见证起点无关。 -/
theorem equality_flat_iff
    (P : GraphPresentation D)
    {left right : Term σ} {sort : σ.SortSymbol}
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort)
    (leftStart rightStart : Nat) :
    Derives P.theory []
      (Formula.iff
        (equality_flat D leftStart left right)
        (equality_flat D rightStart left right)) := by
  let commonStart :=
    max (terms D leftStart [left, right]).next
      (terms D rightStart [left, right]).next
  have hLeftEquivalent :=
    equality_flat_iff_of_disjoint P
      hLeft hRight leftStart commonStart <|
        Or.inl <| by
          exact Nat.le_max_left _ _
  have hRightEquivalent :=
    equality_flat_iff_of_disjoint P
      hLeft hRight rightStart commonStart <|
        Or.inl <| by
          exact Nat.le_max_right _ _
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hLeftEquivalent <|
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hRightEquivalent

/-- 公共等式编译器等价于任意起点的扁平二元项表闭包。 -/
theorem equality_iff_flat
    (P : GraphPresentation D)
    {left right : Term σ} {sort : σ.SortSymbol}
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort)
    (start : Nat) :
    Derives P.theory []
      (Formula.iff
        (FunctionGraphElimination.equality
          D left right)
        (equality_flat D start left right)) := by
  simpa [FunctionGraphElimination.equality,
    equality_flat, equality_core,
    terms_flat_closure, terms,
    close_witnesses_from_zero_start] using
      equality_flat_iff P hLeft hRight 0 start

/--
等式原子的直接替换编译，等价于先求出共享替换值，再代入原等式编译。
-/
theorem equality_substitute_iff
    (P : GraphPresentation D)
    (target : σ.SortSymbol) (id : FreeVarId)
    {replacement : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    {left right : Term σ} {sort : σ.SortSymbol}
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort) :
    Derives P.theory []
      (Formula.iff
        (FunctionGraphElimination.equality D
          (Term.substituteFree
            target id replacement left)
          (Term.substituteFree
            target id replacement right))
        (term_flat_closure D 0 replacement <| fun value =>
          Formula.substituteFree target
            (source_id id) value
            (FunctionGraphElimination.equality
              D left right))) := by
  let shared := term D 0 replacement
  let sourceStart := shared.next
  let sources := [left, right]
  let source := terms D sourceStart sources
  let parameterized :=
    source.substituteFree
      target (source_id id) shared.value
  let localStart := source.next
  let substituted :=
    sources.map
      (Term.substituteFree target id replacement)
  let compiledLocal :=
    terms D localStart substituted
  let localCore :=
    equality_core compiledLocal.values
  let parameterizedCore :=
    equality_core parameterized.values
  let localFlat :=
    terms_flat_closure D localStart substituted
      equality_core
  let parameterizedFlat :=
    close_witnesses_from D.sort sourceStart
      (parameterized.next - sourceStart)
      (condition_conjunction
        parameterized.conditions parameterizedCore)
  let sharedCore :=
    Formula.substituteFree target
      (source_id id) shared.value
      (FunctionGraphElimination.equality
        D left right)
  have hShared :
      Term.Admissible shared.value target :=
    ⟨(term_well_formed
        D 0 hReplacement.1).1,
      (term_scoped
        D 0 hReplacement.2).1⟩
  have hLeftSubstituted :
      Term.Admissible
        (Term.substituteFree
          target id replacement left) sort :=
    ⟨TermWellSorted.substituteFree
        id hLeft.1 hReplacement.1,
      Term.substituteFree_scoped
        hLeft.2 hReplacement.2⟩
  have hRightSubstituted :
      Term.Admissible
        (Term.substituteFree
          target id replacement right) sort :=
    ⟨TermWellSorted.substituteFree
        id hRight.1 hReplacement.1,
      Term.substituteFree_scoped
        hRight.2 hReplacement.2⟩
  have hSources :
      ArgsAdmissible sources [sort, sort] := by
    exact ArgsAdmissible.cons hLeft <|
      ArgsAdmissible.cons hRight
        ArgsAdmissible.nil
  have hSubstituted :
      ArgsAdmissible substituted [sort, sort] := by
    simpa [sources, substituted] using
      ArgsAdmissible.cons hLeftSubstituted <|
        ArgsAdmissible.cons hRightSubstituted
          ArgsAdmissible.nil
  have hSource :
      ArgsAdmissible source.values [sort, sort] := by
    simpa [source] using
      terms_admissible D sourceStart hSources
  have hParameterized :
      ArgsAdmissible parameterized.values
        [sort, sort] := by
    constructor
    · simpa [parameterized,
        ArgsResult.substituteFree] using
          ArgsWellSorted.substituteFree
            target (source_id id) hShared.1
              hSource.1
    · intro term hTerm
      rcases List.mem_map.mp (by
        simpa [parameterized,
          ArgsResult.substituteFree] using hTerm) with
        ⟨sourceTerm, hSourceTerm, rfl⟩
      exact Term.substituteFree_scoped
        (hSource.2 sourceTerm hSourceTerm)
        hShared.2
  have hSharedLocal :
      shared.next ≤ localStart := by
    simpa [sourceStart, source, localStart] using
      terms_next_ge D shared.next sources
  have hParameterizedConditions :
      ∀ condition,
        condition ∈ parameterized.conditions →
          Formula.Admissible condition := by
    intro condition hCondition
    rcases List.mem_map.mp (by
      simpa [parameterized, source,
        ArgsResult.substituteFree] using hCondition) with
      ⟨sourceCondition, hSourceCondition, rfl⟩
    exact Formula.Admissible.substituteFree
      target (source_id id)
      (terms_conditions_admissible
        D sourceStart hSources
        sourceCondition <| by
          simpa [source] using hSourceCondition)
      hShared
  have hLocalConditions :
      ∀ condition,
        condition ∈ compiledLocal.conditions →
          Formula.Admissible condition := by
    simpa [compiledLocal] using
      terms_conditions_admissible
        D localStart hSubstituted
  have hLocalFlat :
      Formula.Admissible localFlat := by
    exact terms_flat_closure_admissible
      D localStart hSubstituted
      equality_core equality_core_admissible
  have hParameterizedCore :
      Formula.Admissible parameterizedCore := by
    exact equality_core_admissible hParameterized
  have hSharedFresh :
      ∀ index,
        sourceStart ≤ index →
        index < source.next →
          (D.sort, witness_id index) ∉
            Term.freeSupport shared.value := by
    intro index hLower hUpper
    exact term_value_witness_fresh_above
      D 0 replacement <| by
        simpa [sourceStart, shared] using hLower
  have hSubstitutionEquivalent :
      Derives P.theory []
        (Formula.iff sharedCore
          parameterizedFlat) := by
    have hEquivalent :=
      equality_iff_flat P hLeft hRight sourceStart
    have hSubstitutedEquivalent :=
      Derives.substituteFree_theorem
        P.theory_sentence target
        (source_id id) hShared hEquivalent
    simp only [Formula.substituteFree]
      at hSubstitutedEquivalent
    rw [equality_flat_substituteFree
      D target id shared.value sourceStart
      left right hShared.2 hSharedFresh]
      at hSubstitutedEquivalent
    simpa [sharedCore, parameterizedFlat,
      source, parameterized] using
        hSubstitutedEquivalent
  have hParameterizedTruth :
      Derives P.theory []
        (close_witnesses_from D.sort sourceStart
          (parameterized.next - sourceStart)
          (condition_conjunction
            parameterized.conditions
            Formula.truth)) := by
    have hTruth :=
      P.terms_substitute_conditions_truth
        target id hShared sourceStart
        hSources hSharedFresh
    simpa [source, parameterized] using hTruth
  have hLocalTruth :
      Derives P.theory []
        (close_witnesses_from D.sort localStart
          (compiledLocal.next - localStart)
          (condition_conjunction
            compiledLocal.conditions
            Formula.truth)) := by
    simpa [localFlat, terms_flat_closure,
      compiledLocal] using
        P.terms_flat_truth
          localStart hSubstituted
  have hSharedTruth :
      Derives P.theory []
        (close_witnesses_from D.sort 0
          shared.next
          (condition_conjunction
            shared.conditions Formula.truth)) := by
    simpa [term_flat_closure, shared] using
      P.term_flat_truth 0 hReplacement
  have hCore :
      Derives P.theory
        (shared.conditions ++
          compiledLocal.conditions ++
            parameterized.conditions)
        (Formula.iff localCore
          parameterizedCore) := by
    simpa [shared, sourceStart, sources, source,
      parameterized, localStart, substituted,
      compiledLocal, localCore,
      parameterizedCore, terms,
      equality_core, TermResult.substituteFree,
      ArgsResult.substituteFree,
      List.map_append, List.append_assoc] using
        equality_substitute_core_iff P
          target id hReplacement
          0 localStart sourceStart
          hLeft hRight
  let Γ₁ : Context σ :=
    shared.conditions ++
      parameterized.conditions
  have hParameterizedConditionFreshAbove :
      ∀ index,
        localStart ≤ index →
        ∀ condition,
          condition ∈ parameterized.conditions →
            (D.sort, witness_id index) ∉
              Formula.freeSupport condition := by
    intro index hLower condition hCondition
    rcases List.mem_map.mp (by
      simpa [parameterized, source,
        ArgsResult.substituteFree] using hCondition) with
      ⟨sourceCondition, hSourceCondition, rfl⟩
    apply Formula.not_mem_freeSupport_substituteFree
    · exact term_value_witness_fresh_above
        D 0 replacement
          (Nat.le_trans hSharedLocal hLower)
    · exact terms_conditions_witness_fresh_above
        D sourceStart sources
          (by simpa [source, localStart] using hLower)
          sourceCondition <| by
            simpa [source] using hSourceCondition
  have hParameterizedCoreFreshAbove :
      ∀ index,
        localStart ≤ index →
          (D.sort, witness_id index) ∉
            Formula.freeSupport parameterizedCore := by
    intro index hLower
    have hFresh :=
      Formula.not_mem_freeSupport_substituteFree
        (D.sort, witness_id index)
        target (source_id id) shared.value
        (equality_core source.values)
        (term_value_witness_fresh_above
          D 0 replacement
          (Nat.le_trans hSharedLocal hLower))
        (by
          simpa [equality_core, Formula.freeSupport,
            Term.freeSupportList, source, sources,
            terms] using
              terms_values_witness_fresh_above
                D sourceStart sources <| by
                  simpa [source, localStart] using hLower)
    simpa [parameterizedCore, parameterized,
      ArgsResult.substituteFree, equality_core,
      source, sources, terms,
      Formula.substituteFree] using hFresh
  have hLocalParameterizedCore :
      Derives P.theory Γ₁
        (Formula.iff localFlat
          parameterizedCore) := by
    apply closed_conditions_iff_source_in_context
        P.theory_sentence D.sort localStart
        (compiledLocal.next - localStart)
        hLocalConditions hParameterizedCore
    · intro index hLower hUpper formula hFormula
      rcases List.mem_append.mp hFormula with
        hSharedCondition | hParameterizedCondition
      · exact term_conditions_witness_fresh_above
          D 0 replacement
            (Nat.le_trans hSharedLocal hLower)
            formula <| by
              simpa [shared] using hSharedCondition
      · exact hParameterizedConditionFreshAbove
          index hLower formula <| by
            simpa [Γ₁] using hParameterizedCondition
    · intro index hLower hUpper
      exact hParameterizedCoreFreshAbove
        index hLower
    · apply hLocalTruth.context_weaken
      intro formula hFormula
      cases hFormula
    · apply hCore.context_weaken
      intro formula hFormula
      rcases List.mem_append.mp hFormula with
        hFirst | hParameterizedCondition
      · rcases List.mem_append.mp hFirst with
          hSharedCondition | hLocalCondition
        · simp [Γ₁, hSharedCondition]
        · simp [Γ₁, hLocalCondition]
      · simp [Γ₁, hParameterizedCondition]
  let Γ₂ : Context σ := shared.conditions
  have hParameterizedLocal :
      Derives P.theory Γ₂
        (Formula.iff parameterizedFlat
          localFlat) := by
    apply closed_conditions_iff_source_in_context
        P.theory_sentence D.sort sourceStart
        (parameterized.next - sourceStart)
        hParameterizedConditions hLocalFlat
    · intro index hLower hUpper formula hFormula
      exact term_conditions_witness_fresh_above
        D 0 replacement
          (by simpa [sourceStart, shared] using hLower)
          formula <| by
            simpa [Γ₂, shared] using hFormula
    · intro index hLower hUpper
      exact equality_flat_witness_fresh
        D localStart
          (Term.substituteFree
            target id replacement left)
          (Term.substituteFree
            target id replacement right)
          index
    · apply hParameterizedTruth.context_weaken
      intro formula hFormula
      cases hFormula
    · have hEquivalent :
          Derives P.theory
            (parameterized.conditions ++ Γ₂)
            (Formula.iff localFlat
              parameterizedCore) := by
        apply hLocalParameterizedCore.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hSharedCondition | hParameterizedCondition
        · exact List.mem_append.mpr <|
            Or.inr <| by
              simpa [Γ₂] using hSharedCondition
        · exact List.mem_append.mpr <|
            Or.inl hParameterizedCondition
      exact
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hEquivalent
  have hOuterLocal :
      Derives P.theory []
        (Formula.iff
          (term_flat_closure D 0 replacement <| fun value =>
            Formula.substituteFree target
              (source_id id) value
              (FunctionGraphElimination.equality
                D left right))
          localFlat) := by
    have hSharedEquivalent :
        Derives P.theory shared.conditions
          (Formula.iff sharedCore localFlat) :=
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
        (hSubstitutionEquivalent.context_weaken
          (by
            intro formula hFormula
            cases hFormula))
        (by simpa [Γ₂] using hParameterizedLocal)
    have hClosed :=
      closed_conditions_iff_source_in_context
        (conditions := shared.conditions)
        (core := sharedCore)
        (source := localFlat)
        P.theory_sentence D.sort 0 shared.next
        (by
          simpa [shared] using
            term_conditions_admissible
              D 0 hReplacement)
        hLocalFlat
        (Γ := ([] : Context σ))
        (by
          intro index hLower hUpper formula hFormula
          cases hFormula)
        (by
          intro index hLower hUpper
          exact equality_flat_witness_fresh
            D localStart
              (Term.substituteFree
                target id replacement left)
              (Term.substituteFree
                target id replacement right)
              index)
        hSharedTruth
        (by simpa using hSharedEquivalent)
    simpa [term_flat_closure, sharedCore,
      shared] using hClosed
  have hDirect :=
    equality_iff_flat P
      hLeftSubstituted hRightSubstituted
      localStart
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hDirect <|
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hOuterLocal

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
