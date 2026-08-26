import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Proof

/-!
# 函数图见证闭包消去

本模块给出扁平见证闭包的逆向接口。构造侧把图条件关闭成连续存在量词；消去侧
在保持理论、上下文和结论新鲜性的前提下，恢复全部图条件与末端核心作为局部前提。
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

omit [DecidableEq σ.FuncSymbol] in
/-- 连续存在见证闭包可逐层消去回原始主体。 -/
theorem close_witnesses_from_elim
    {T : Theory σ}
    (hTheory :
      ∀ {formula}, T formula →
        Formula.Sentence formula)
    (sort : σ.SortSymbol) (start count : Nat)
    {body conclusion : Formula σ}
    (hBody : Formula.Admissible body)
    {Γ : Context σ}
    (hContextFresh :
      ∀ index,
        start ≤ index →
        index < start + count →
        ∀ formula, formula ∈ Γ →
          (sort, witness_id index) ∉
            Formula.freeSupport formula)
    (hConclusionFresh :
      ∀ index,
        start ≤ index →
        index < start + count →
          (sort, witness_id index) ∉
            Formula.freeSupport conclusion)
    (hClosed :
      Derives T Γ
        (close_witnesses_from
          sort start count body))
    (hCase :
      Derives T (body :: Γ) conclusion) :
    Derives T Γ conclusion := by
  induction count generalizing Γ with
  | zero =>
      have hBody' : Derives T Γ body := by
        simpa [close_witnesses_from] using hClosed
      exact hBody'.cut hCase
  | succ count ih =>
      let inner :=
        close_witnesses_from sort start count body
      have hInner :
          Formula.Admissible inner :=
        close_witnesses_from_admissible
          sort start count hBody
      apply Derives.exists_elim
        (sort := sort)
        (eigen := witness_id (start + count))
        (body := inner)
      · intro formula hFormula
        rw [(hTheory hFormula).2]
        simp
      · intro formula hFormula
        exact hContextFresh
          (start + count) (by omega) (by omega)
          formula hFormula
      · exact hConclusionFresh
          (start + count) (by omega) (by omega)
      · simpa [close_witnesses_from, inner] using
          hClosed
      · apply ih
          (Γ := inner :: Γ)
        · intro index hLower hUpper formula hFormula
          rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · exact close_witnesses_from_witness_fresh
              sort start count index body <| by
                intro hOutside
                omega
          · exact hContextFresh index hLower
              (by omega) formula hFormula
        · intro index hLower hUpper
          exact hConclusionFresh index hLower
            (by omega)
        · exact Derives.assumption_of_mem
            (by simp [inner])
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible
                hInner)
        · apply hCase.context_weaken
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · simp
          · simp [hFormula]

omit [DecidableEq σ.FuncSymbol] in
/--
上下文中的闭包条件透明性：条件块可满足，且条件上下文中的核心等价于一个对见证
区间新鲜的源公式时，整个存在闭包可在同一上下文中消去。
-/
theorem closed_conditions_iff_source_in_context
    {T : Theory σ}
    (hTheory :
      ∀ {formula}, T formula →
        Formula.Sentence formula)
    (sort : σ.SortSymbol) (start count : Nat)
    {conditions : List (Formula σ)}
    {core source : Formula σ}
    (hConditions :
      ∀ condition, condition ∈ conditions →
        Formula.Admissible condition)
    (hSource : Formula.Admissible source)
    {Γ : Context σ}
    (hContextFresh :
      ∀ index,
        start ≤ index →
        index < start + count →
        ∀ formula, formula ∈ Γ →
          (sort, witness_id index) ∉
            Formula.freeSupport formula)
    (hSourceFresh :
      ∀ index,
        start ≤ index →
        index < start + count →
          (sort, witness_id index) ∉
            Formula.freeSupport source)
    (hSatisfiable :
      Derives T Γ
        (close_witnesses_from sort start count
          (condition_conjunction
            conditions Formula.truth)))
    (hEquivalent :
      Derives T (conditions ++ Γ)
        (Formula.iff core source)) :
    Derives T Γ
      (Formula.iff
        (close_witnesses_from sort start count
          (condition_conjunction conditions core))
        source) := by
  let coreBody :=
    condition_conjunction conditions core
  let closedCore :=
    close_witnesses_from sort start count coreBody
  have hCoreBody :
      Formula.Admissible coreBody :=
    condition_conjunction_admissible
      hConditions <|
        Formula.Admissible.iff_left
          hEquivalent.admissible
  have hClosedCore :
      Formula.Admissible closedCore :=
    close_witnesses_from_admissible
      sort start count hCoreBody
  apply Derives.iff_intro
  · let Δ : Context σ := closedCore :: Γ
    have hClosed :
        Derives T Δ closedCore :=
      Derives.assumption_of_mem
        (by simp [Δ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hClosedCore)
    apply close_witnesses_from_elim
        hTheory sort start count hCoreBody
        (Γ := Δ) (conclusion := source)
    · intro index hLower hUpper formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · exact close_witnesses_from_witness_fresh
          sort start count index coreBody <| by
            intro hOutside
            omega
      · exact hContextFresh index hLower
          hUpper formula hFormula
    · exact hSourceFresh
    · simpa [closedCore] using hClosed
    · let Θ : Context σ :=
        conditions ++ coreBody :: Δ
      have hBlock :
          Derives T
            (coreBody :: Δ) coreBody :=
        Derives.assumption_of_mem
          (by simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              hCoreBody)
      apply condition_conjunction_cut hBlock
      have hBlock' :
          Derives T Θ coreBody :=
        Derives.assumption_of_mem
          (by simp [Θ])
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              hCoreBody)
      have hCore :
          Derives T Θ core :=
        condition_conjunction_core hBlock'
      have hEquivalent' :
          Derives T Θ
            (Formula.iff core source) := by
        apply hEquivalent.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hCondition | hFormula
        · exact List.mem_append.mpr <|
            Or.inl hCondition
        · exact List.mem_append.mpr <|
            Or.inr <| by
              simp [Δ, hFormula]
      exact Derives.iff_elim_right
        hEquivalent' hCore
  · let Δ : Context σ := source :: Γ
    have hTruth :
        Derives T Δ
          (close_witnesses_from sort start count
            (condition_conjunction
              conditions Formula.truth)) :=
      hSatisfiable.context_weaken_cons
    apply close_witnesses_from_elim
        hTheory sort start count
        (condition_conjunction_admissible
          hConditions Formula.Admissible.truth)
        (Γ := Δ) (conclusion := closedCore)
    · intro index hLower hUpper formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · exact hSourceFresh index hLower hUpper
      · exact hContextFresh index hLower
          hUpper formula hFormula
    · intro index hLower hUpper
      exact close_witnesses_from_witness_fresh
        sort start count index coreBody <| by
          intro hOutside
          omega
    · exact hTruth
    · let truthBody :=
        condition_conjunction
          conditions Formula.truth
      let Θ : Context σ :=
        conditions ++ truthBody :: Δ
      have hBlock :
          Derives T
            (truthBody :: Δ) truthBody :=
        Derives.assumption_of_mem
          (by simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible <|
              condition_conjunction_admissible
                hConditions Formula.Admissible.truth)
      apply close_witnesses_from_intro
        sort start count
      apply condition_conjunction_cut hBlock
      have hEquivalent' :
          Derives T Θ
            (Formula.iff core source) := by
        apply hEquivalent.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hCondition | hFormula
        · exact List.mem_append.mpr <|
            Or.inl hCondition
        · exact List.mem_append.mpr <|
            Or.inr <| by
              simp [Δ, hFormula]
      have hSource' :
          Derives T Θ source :=
        Derives.assumption_of_mem
          (by simp [Θ, Δ])
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              hSource)
      have hCore :
          Derives T Θ core :=
        Derives.iff_elim_left
          hEquivalent' hSource'
      exact condition_conjunction_intro
        (fun condition hCondition =>
          Derives.assumption_of_mem
            (List.mem_append.mpr <|
              Or.inl hCondition)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                hConditions condition hCondition))
        hCore

omit [DecidableEq σ.FuncSymbol] in
/--
句子理论中的空上下文定理可先对象级全称化，再以任意 admissible 项实例化。
-/
theorem _root_.YesMetaZFC.Logic.FirstOrder.Derives.substituteFree_theorem
    {T : Theory σ}
    (hTheory :
      ∀ {formula}, T formula →
        Formula.Sentence formula)
    (target : σ.SortSymbol) (id : FreeVarId)
    {replacement : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    {body : Formula σ}
    (hBody : Derives T [] body) :
    Derives T []
      (Formula.substituteFree
        target id replacement body) := by
  have hUniversal :
      Derives T []
        (Formula.forallE target
          (Formula.closeFreeAt target id 0 body)) := by
    apply Derives.forall_intro
    · intro formula hFormula
      rw [(hTheory hFormula).2]
      simp
    · intro formula hFormula
      cases hFormula
    · exact hBody
  have hInstance :=
    Derives.forall_elim
      (term := replacement) hUniversal
      (hTermCheck :=
        Term.check_certificate_of_admissible
          hReplacement)
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree]
    using hInstance

/-- 任意起点的关系参数扁平闭包不暴露任何偶数见证变量。 -/
theorem relation_flat_witness_fresh
    (D : Data σ) (start : Nat)
    (relation : σ.RelSymbol)
    (arguments : List (Term σ))
    (index : Nat) :
    (D.sort, witness_id index) ∉
      Formula.freeSupport
        (terms_flat_closure D start arguments
          (Formula.rel relation)) := by
  let compiled := terms D start arguments
  have hNext : start ≤ compiled.next := by
    simpa [compiled] using
      terms_next_ge D start arguments
  have hCount :
      start +
          ((terms D start arguments).next - start) =
        (terms D start arguments).next := by
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
        D start arguments hBelow condition <| by
          simpa [compiled] using hCondition
    · exact terms_conditions_witness_fresh_above
        D start arguments (by
          rw [hCount] at hAbove
          exact hAbove)
        condition <| by
          simpa [compiled] using hCondition
  · rcases hOutside with hBelow | hAbove
    · simpa [Formula.freeSupport, compiled] using
        terms_values_witness_fresh_below
          D start arguments hBelow
    · simpa [Formula.freeSupport, compiled] using
        terms_values_witness_fresh_above
          D start arguments (by
            rw [hCount] at hAbove
            exact hAbove)

namespace GraphPresentation

variable {D : Data σ}

/--
扁平项闭包可消去为编译条件与续延核心。区间新鲜性只要求覆盖实际分配的见证。
-/
theorem term_flat_elim_to_conditions
    (P : GraphPresentation D) (start : Nat)
    {source : Term σ} {sort : σ.SortSymbol}
    (hSource : Term.Admissible source sort)
    (continuation : Term σ → Formula σ)
    (hContinuation :
      ∀ {value},
        Term.Admissible value sort →
          Formula.Admissible (continuation value))
    {Γ : Context σ} {conclusion : Formula σ}
    (hContextFresh :
      ∀ index,
        start ≤ index →
        index < (term D start source).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (hConclusionFresh :
      ∀ index,
        start ≤ index →
        index < (term D start source).next →
          (D.sort, witness_id index) ∉
            Formula.freeSupport conclusion)
    (hClosed :
      Derives P.theory Γ
        (term_flat_closure D start source
          continuation))
    (hCase :
      Derives P.theory
        ((term D start source).conditions ++
          continuation (term D start source).value :: Γ)
        conclusion) :
    Derives P.theory Γ conclusion := by
  let compiled := term D start source
  let body :=
    condition_conjunction compiled.conditions
      (continuation compiled.value)
  have hNext : start ≤ compiled.next := by
    simpa [compiled] using
      term_next_ge D start source
  have hCount :
      start + (compiled.next - start) =
        compiled.next := by
    omega
  have hValue :
      Term.Admissible compiled.value sort :=
    ⟨(term_well_formed
        D start hSource.1).1,
      (term_scoped
        D start hSource.2).1⟩
  have hConditions :
      ∀ condition,
        condition ∈ compiled.conditions →
          Formula.Admissible condition := by
    simpa [compiled] using
      term_conditions_admissible D start hSource
  have hBody :
      Formula.Admissible body :=
    condition_conjunction_admissible
      hConditions (hContinuation hValue)
  apply close_witnesses_from_elim
      P.theory_sentence D.sort start
        (compiled.next - start) hBody
  · intro index hLower hUpper formula hFormula
    apply hContextFresh index hLower
    · simpa [hCount] using hUpper
    · exact hFormula
  · intro index hLower hUpper
    apply hConclusionFresh index hLower
    simpa [hCount] using hUpper
  · simpa [term_flat_closure, compiled, body] using
      hClosed
  · let block := body
    have hBlock :
        Derives P.theory (block :: Γ) block :=
      Derives.assumption_of_mem
        (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hBody)
    have hPremises :
        ∀ formula,
          formula ∈
              compiled.conditions ++
                [continuation compiled.value] →
            Derives P.theory (block :: Γ) formula := by
      intro formula hFormula
      rcases List.mem_append.mp hFormula with
        hCondition | hCore
      · exact condition_conjunction_member
          hBlock hCondition
      · rw [List.mem_singleton.mp hCore]
        exact condition_conjunction_core hBlock
    apply Derives.multi_cut
      (premises :=
        compiled.conditions ++
          [continuation compiled.value])
      hPremises
    apply hCase.context_weaken
    intro formula hFormula
    rcases List.mem_append.mp hFormula with
      hCondition | hFormula
    · exact List.mem_append.mpr <| Or.inl <|
        List.mem_append.mpr <| Or.inl <| by
          simpa [compiled] using hCondition
    · rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · exact List.mem_append.mpr <| Or.inl <|
          List.mem_append.mpr <| Or.inr <| by
            simp [compiled]
      · exact List.mem_append.mpr <| Or.inr <|
          List.mem_cons.mpr <| Or.inr hFormula

/-- 扁平参数闭包的逆向接口与单项版本完全对称。 -/
theorem terms_flat_elim_to_conditions
    (P : GraphPresentation D) (start : Nat)
    {sources : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hSources : ArgsAdmissible sources sorts)
    (continuation :
      List (Term σ) → Formula σ)
    (hContinuation :
      ∀ {values},
        ArgsAdmissible values sorts →
          Formula.Admissible (continuation values))
    {Γ : Context σ} {conclusion : Formula σ}
    (hContextFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start sources).next →
        ∀ formula, formula ∈ Γ →
          (D.sort, witness_id index) ∉
            Formula.freeSupport formula)
    (hConclusionFresh :
      ∀ index,
        start ≤ index →
        index < (terms D start sources).next →
          (D.sort, witness_id index) ∉
            Formula.freeSupport conclusion)
    (hClosed :
      Derives P.theory Γ
        (terms_flat_closure D start sources
          continuation))
    (hCase :
      Derives P.theory
        ((terms D start sources).conditions ++
          continuation (terms D start sources).values :: Γ)
        conclusion) :
    Derives P.theory Γ conclusion := by
  let compiled := terms D start sources
  let body :=
    condition_conjunction compiled.conditions
      (continuation compiled.values)
  have hNext : start ≤ compiled.next := by
    simpa [compiled] using
      terms_next_ge D start sources
  have hCount :
      start + (compiled.next - start) =
        compiled.next := by
    omega
  have hValues :
      ArgsAdmissible compiled.values sorts := by
    simpa [compiled] using
      terms_admissible D start hSources
  have hConditions :
      ∀ condition,
        condition ∈ compiled.conditions →
          Formula.Admissible condition := by
    simpa [compiled] using
      terms_conditions_admissible D start hSources
  have hBody :
      Formula.Admissible body :=
    condition_conjunction_admissible
      hConditions (hContinuation hValues)
  apply close_witnesses_from_elim
      P.theory_sentence D.sort start
        (compiled.next - start) hBody
  · intro index hLower hUpper formula hFormula
    apply hContextFresh index hLower
    · simpa [hCount] using hUpper
    · exact hFormula
  · intro index hLower hUpper
    apply hConclusionFresh index hLower
    simpa [hCount] using hUpper
  · simpa [terms_flat_closure, compiled, body] using
      hClosed
  · let block := body
    have hBlock :
        Derives P.theory (block :: Γ) block :=
      Derives.assumption_of_mem
        (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hBody)
    have hPremises :
        ∀ formula,
          formula ∈
              compiled.conditions ++
                [continuation compiled.values] →
            Derives P.theory (block :: Γ) formula := by
      intro formula hFormula
      rcases List.mem_append.mp hFormula with
        hCondition | hCore
      · exact condition_conjunction_member
          hBlock hCondition
      · rw [List.mem_singleton.mp hCore]
        exact condition_conjunction_core hBlock
    apply Derives.multi_cut
      (premises :=
        compiled.conditions ++
          [continuation compiled.values])
      hPremises
    apply hCase.context_weaken
    intro formula hFormula
    rcases List.mem_append.mp hFormula with
      hCondition | hFormula
    · exact List.mem_append.mpr <| Or.inl <|
        List.mem_append.mpr <| Or.inl <| by
          simpa [compiled] using hCondition
    · rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · exact List.mem_append.mpr <| Or.inl <|
          List.mem_append.mpr <| Or.inr <| by
            simp [compiled]
      · exact List.mem_append.mpr <| Or.inr <|
          List.mem_cons.mpr <| Or.inr hFormula

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
