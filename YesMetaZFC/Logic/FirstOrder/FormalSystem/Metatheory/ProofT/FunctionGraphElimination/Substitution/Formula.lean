import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Substitution.Equality

/-!
# 公式模板的共享值闭包

本模块处理整公式替换归纳的公共难点：同一源项可以在任意见证区间求值，而把所得
值代入同一公式模板后，闭包结果在图理论中保持逻辑等价。
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

/-- 将源项求值后代入给定公式模板。 -/
def formula_substitution_closure
    (D : Data σ) (start : Nat)
    (source : Term σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (body : Formula σ) : Formula σ :=
  term_flat_closure D start source <| fun value =>
    Formula.substituteFree target id value body

/--
若模板本身不含偶数见证变量，则求值并代入后的完整闭包也不暴露这些变量。
-/
theorem formula_substitution_closure_witness_fresh
    (D : Data σ) (start : Nat)
    (source : Term σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (body : Formula σ)
    (hBodyFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport body)
    (index : Nat) :
    (D.sort, witness_id index) ∉
      Formula.freeSupport
        (formula_substitution_closure
          D start source target id body) := by
  let compiled := term D start source
  apply close_witnesses_from_witness_fresh
  intro hOutside
  have hConditionFresh :
      ∀ condition,
        condition ∈ compiled.conditions →
          (D.sort, witness_id index) ∉
            Formula.freeSupport condition := by
    rcases hOutside with hBelow | hAbove
    · exact term_conditions_witness_fresh_below
        D start source hBelow
    · rw [Nat.add_sub_of_le
          (term_next_ge D start source)]
        at hAbove
      exact term_conditions_witness_fresh_above
        D start source hAbove
  have hValueFresh :
      (D.sort, witness_id index) ∉
        Term.freeSupport compiled.value := by
    rcases hOutside with hBelow | hAbove
    · exact term_value_witness_fresh_below
        D start source hBelow
    · rw [Nat.add_sub_of_le
          (term_next_ge D start source)]
        at hAbove
      exact term_value_witness_fresh_above
        D start source hAbove
  apply condition_conjunction_fresh
  · intro condition hCondition
    exact hConditionFresh condition <| by
      simpa [compiled] using hCondition
  · exact Formula.not_mem_freeSupport_substituteFree
      (D.sort, witness_id index)
      target id compiled.value body
      hValueFresh (hBodyFresh index)

namespace GraphPresentation

variable {D : Data σ}

/--
两个不相交区间对同一项求值并代入同一公式模板时，左闭包可重建右闭包。
-/
theorem formula_substitution_closure_imp_of_disjoint
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId) {body : Formula σ}
    (hBody : Formula.Admissible body)
    (hBodyFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport body)
    (leftStart rightStart : Nat)
    (hDisjoint :
      (term D leftStart source).next ≤
          rightStart ∨
        (term D rightStart source).next ≤
          leftStart) :
    Derives P.theory []
      (Formula.imp
        (formula_substitution_closure
          D leftStart source target id body)
        (formula_substitution_closure
          D rightStart source target id body)) := by
  let left := term D leftStart source
  let right := term D rightStart source
  let leftFormula :=
    formula_substitution_closure
      D leftStart source target id body
  let rightFormula :=
    formula_substitution_closure
      D rightStart source target id body
  have hLeftValue :
      Term.Admissible left.value target :=
    ⟨(term_well_formed
        D leftStart hSource.1).1,
      (term_scoped
        D leftStart hSource.2).1⟩
  have hRightValue :
      Term.Admissible right.value target :=
    ⟨(term_well_formed
        D rightStart hSource.1).1,
      (term_scoped
        D rightStart hSource.2).1⟩
  have hLeftFormula :
      Formula.Admissible leftFormula := by
    exact term_flat_closure_admissible
      D leftStart hSource
      (fun value =>
        Formula.substituteFree target id value body)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hBody hValue)
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
  apply P.term_flat_elim_to_conditions
      leftStart hSource
      (fun value =>
        Formula.substituteFree target id value body)
  · intro value hValue
    exact Formula.Admissible.substituteFree
      target id hBody hValue
  · intro index hLower hUpper formula hFormula
    have hFormulaEq : formula = leftFormula :=
      List.mem_singleton.mp <| by
        simpa [Γ] using hFormula
    subst formula
    exact formula_substitution_closure_witness_fresh
      D leftStart source target id body
      hBodyFresh index
  · intro index hLower hUpper
    exact formula_substitution_closure_witness_fresh
      D rightStart source target id body
      hBodyFresh index
  · simpa [leftFormula, Γ] using hLeftClosed
  · let Δ : Context σ :=
      left.conditions ++
        Formula.substituteFree target id
          left.value body :: Γ
    apply P.term_flat_derives_from_conditions
        rightStart hSource
        (Γ := Δ)
        (continuation := fun value =>
          Formula.substituteFree target id value body)
    · intro index hLower hUpper formula hFormula
      rcases List.mem_append.mp hFormula with
        hCondition | hFormula
      · rcases hDisjoint with hBefore | hAfter
        · exact term_conditions_witness_fresh_above
            D leftStart source
              (Nat.le_trans hBefore hLower)
              formula <| by
                simpa [left] using hCondition
        · exact term_conditions_witness_fresh_below
            D leftStart source
              (Nat.lt_of_lt_of_le
                hUpper hAfter)
              formula <| by
                simpa [left] using hCondition
      · rcases List.mem_cons.mp hFormula with
          rfl | hFormula
        · apply Formula.not_mem_freeSupport_substituteFree
          · rcases hDisjoint with hBefore | hAfter
            · exact term_value_witness_fresh_above
                D leftStart source
                  (Nat.le_trans hBefore hLower)
            · exact term_value_witness_fresh_below
                D leftStart source
                  (Nat.lt_of_lt_of_le
                    hUpper hAfter)
          · exact hBodyFresh index
        · have hFormulaEq :
              formula = leftFormula :=
            List.mem_singleton.mp <| by
              simpa [Γ] using hFormula
          subst formula
          exact formula_substitution_closure_witness_fresh
            D leftStart source target id body
            hBodyFresh index
    · intro value hValue
      exact Formula.Admissible.substituteFree
        target id hBody hValue
    · have hEqual :=
        term_compiled_eq P
          leftStart rightStart hSource
      have hEqual' :
          Derives P.theory
            (right.conditions ++ Δ)
            (Formula.equal left.value
              right.value) := by
        apply hEqual.context_weaken
        intro formula hFormula
        rcases List.mem_append.mp hFormula with
          hLeftCondition | hRightCondition
        · exact List.mem_append.mpr <| Or.inr <|
            List.mem_append.mpr <| Or.inl <| by
              simpa [left] using hLeftCondition
        · exact List.mem_append.mpr <| Or.inl <| by
            simpa [right] using hRightCondition
      have hEquivalent :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_iff_of_equality
          (sort := target) (eigen := id)
          (body := body) hEqual'
          (hLeftCheck :=
            Term.check_certificate_of_admissible
              hLeftValue)
          (hRightCheck :=
            Term.check_certificate_of_admissible
              hRightValue)
          (hBodyCheck :=
            Formula.check_certificate_of_admissible
              hBody)
      have hLeftCore :
          Derives P.theory
            (right.conditions ++ Δ)
            (Formula.substituteFree target id
              left.value body) :=
        Derives.assumption_of_mem
          (List.mem_append.mpr <| Or.inr <|
            List.mem_append.mpr <| Or.inr <| by
              simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible <|
              Formula.Admissible.substituteFree
                target id hBody hLeftValue)
      exact Derives.iff_elim_right
        hEquivalent hLeftCore

/--
不相交区间中的两份公式模板替换闭包逻辑等价。
-/
theorem formula_substitution_closure_iff_of_disjoint
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId) {body : Formula σ}
    (hBody : Formula.Admissible body)
    (hBodyFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport body)
    (leftStart rightStart : Nat)
    (hDisjoint :
      (term D leftStart source).next ≤
          rightStart ∨
        (term D rightStart source).next ≤
          leftStart) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D leftStart source target id body)
        (formula_substitution_closure
          D rightStart source target id body)) := by
  apply Derives.iff_intro
  · exact Derives.imp_elim_assumption <|
      formula_substitution_closure_imp_of_disjoint
        P hSource id hBody hBodyFresh
        leftStart rightStart hDisjoint
  · have hDisjoint' :
        (term D rightStart source).next ≤
            leftStart ∨
          (term D leftStart source).next ≤
            rightStart :=
      hDisjoint.elim Or.inr Or.inl
    exact Derives.imp_elim_assumption <|
      formula_substitution_closure_imp_of_disjoint
        P hSource id hBody hBodyFresh
        rightStart leftStart hDisjoint'

/-- 同一公式模板的求值替换闭包与见证起点无关。 -/
theorem formula_substitution_closure_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId) {body : Formula σ}
    (hBody : Formula.Admissible body)
    (hBodyFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport body)
    (leftStart rightStart : Nat) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D leftStart source target id body)
        (formula_substitution_closure
          D rightStart source target id body)) := by
  let commonStart :=
    max (term D leftStart source).next
      (term D rightStart source).next
  have hLeft :=
    formula_substitution_closure_iff_of_disjoint
      P hSource id hBody hBodyFresh
      leftStart commonStart <|
        Or.inl <| by
          exact Nat.le_max_left _ _
  have hRight :=
    formula_substitution_closure_iff_of_disjoint
      P hSource id hBody hBodyFresh
      rightStart commonStart <|
        Or.inl <| by
          exact Nat.le_max_right _ _
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hLeft <|
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hRight

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
