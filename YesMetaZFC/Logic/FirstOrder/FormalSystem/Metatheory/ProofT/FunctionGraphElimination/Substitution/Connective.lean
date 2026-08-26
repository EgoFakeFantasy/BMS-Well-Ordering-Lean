import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Substitution.Formula

/-!
# 公式替换闭包的逻辑联结词合同

本模块把源项求值闭包提升为逻辑联结词同态。核心难点是两个闭包各自携带一份
局部见证：反向合取先把右支搬到左支区间之后，再由函数图唯一性对齐两次求值。
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
private theorem de_morgan_iff
    {T : Theory σ} {left right : Formula σ}
    (hLeft : Formula.Admissible left)
    (hRight : Formula.Admissible right) :
    Derives T []
      (Formula.iff
        (Formula.neg
          (Formula.conj
            (Formula.neg left)
            (Formula.neg right)))
        (Formula.disj left right)) := by
  derive_prop

omit [DecidableEq σ.FuncSymbol] in
private theorem neg_disj_iff_imp
    {T : Theory σ} {left right : Formula σ}
    (hLeft : Formula.Admissible left)
    (hRight : Formula.Admissible right) :
    Derives T []
      (Formula.iff
        (Formula.disj
          (Formula.neg left) right)
        (Formula.imp left right)) := by
  derive_prop

omit [DecidableEq σ.FuncSymbol] in
private theorem conj_imp_iff
    {T : Theory σ} {left right : Formula σ}
    (hLeft : Formula.Admissible left)
    (hRight : Formula.Admissible right) :
    Derives T []
      (Formula.iff
        (Formula.conj
          (Formula.imp left right)
          (Formula.imp right left))
        (Formula.iff left right)) := by
  derive_prop

/-- 已证明的编译条件和当前值核心可以重建完整公式替换闭包。 -/
theorem formula_substitution_closure_intro
    {T : Theory σ} {Γ : Context σ}
    (D : Data σ) (start : Nat)
    (source : Term σ)
    (target : σ.SortSymbol) (id : FreeVarId)
    (body : Formula σ)
    (hConditions :
      ∀ condition,
        condition ∈ (term D start source).conditions →
          Derives T Γ condition)
    (hCore :
      Derives T Γ
        (Formula.substituteFree target id
          (term D start source).value body)) :
    Derives T Γ
      (formula_substitution_closure
        D start source target id body) := by
  apply close_witnesses_from_intro
  exact condition_conjunction_intro
    hConditions hCore

/--
句子理论中的模板等价可逐层提升为公式替换闭包等价。

该合同只使用源项的 admissibility 与背景理论的闭句性；不需要函数图存在性或
唯一性。
-/
theorem formula_substitution_closure_iff_mono_theory
    {T : Theory σ}
    (hTheory :
      ∀ {formula}, T formula →
        Formula.Sentence formula)
    (D : Data σ) (start : Nat)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId)
    {left right : Formula σ}
    (hEquivalent :
      Derives T []
        (Formula.iff left right)) :
    Derives T []
      (Formula.iff
        (formula_substitution_closure
          D start source target id left)
        (formula_substitution_closure
          D start source target id right)) := by
  let compiled := term D start source
  have hValue :
      Term.Admissible compiled.value target :=
    ⟨(term_well_formed
        D start hSource.1).1,
      (term_scoped
        D start hSource.2).1⟩
  have hSubstituted :=
    Derives.substituteFree_theorem
      (T := T) hTheory
      target id hValue hEquivalent
  have hConditions :
      ∀ condition,
        condition ∈ compiled.conditions →
          Formula.Admissible condition := by
    simpa [compiled] using
      term_conditions_admissible
        D start hSource
  have hCore :=
    condition_conjunction_iff_of_context
      hConditions <| by
        simpa [Formula.substituteFree]
          using hSubstituted.context_weaken
            (Δ := compiled.conditions) <| by
              intro formula hFormula
              cases hFormula
  have hClosed :=
    close_witnesses_from_iff_mono_theory
      hTheory
      D.sort start (compiled.next - start)
      hCore
  simpa [formula_substitution_closure,
    term_flat_closure, compiled] using hClosed

/--
空背景中的模板等价可逐层提升为公式替换闭包等价。
-/
theorem formula_substitution_closure_iff_mono
    (D : Data σ) (start : Nat)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId)
    {left right : Formula σ}
    (hEquivalent :
      Derives (Theory.empty : Theory σ) []
        (Formula.iff left right)) :
    Derives (Theory.empty : Theory σ) []
      (Formula.iff
        (formula_substitution_closure
          D start source target id left)
        (formula_substitution_closure
          D start source target id right)) :=
  formula_substitution_closure_iff_mono_theory
    (by
      intro formula hFormula
      cases hFormula)
    D start hSource id hEquivalent

namespace GraphPresentation

variable {D : Data σ}

/-- 公式替换闭包保持假。 -/
theorem formula_substitution_closure_falsum_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId) (start : Nat) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D start source target id Formula.falsum)
        Formula.falsum) := by
  have hClosed :
      Formula.Admissible
        (formula_substitution_closure
          D start source target id Formula.falsum) :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value
          Formula.falsum)
      (fun hValue => by
        exact Formula.Admissible.substituteFree
          target id Formula.Admissible.falsum hValue)
  apply Derives.iff_intro
  · let Γ : Context σ :=
      [formula_substitution_closure
        D start source target id Formula.falsum]
    have hFalseClosed :
        Derives P.theory Γ
          (formula_substitution_closure
            D start source target id Formula.falsum) :=
      Derives.assumption_of_mem
        (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hClosed)
    change Derives P.theory Γ Formula.falsum
    apply P.term_flat_elim_to_conditions
        start hSource
        (fun value =>
          Formula.substituteFree target id value
            Formula.falsum)
    · intro value hValue
      exact Formula.Admissible.substituteFree
        target id Formula.Admissible.falsum hValue
    · intro index hLower hUpper formula hFormula
      have hFormulaEq :
          formula =
            formula_substitution_closure
              D start source target id
                Formula.falsum :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hFormula
      subst formula
      exact formula_substitution_closure_witness_fresh
        D start source target id Formula.falsum
        (by
          intro index
          simp [Formula.freeSupport])
        index
    · intro index hLower hUpper
      simp [Formula.freeSupport]
    · exact hFalseClosed
    · exact Derives.assumption_of_mem
        (List.mem_append.mpr <| Or.inr <| by
          simp [Formula.substituteFree])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            Formula.Admissible.falsum)
  · exact Derives.falsum_elim
      (Derives.assumption_of_mem
        (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            Formula.Admissible.falsum))
      (hCheck :=
        Formula.check_certificate_of_admissible
          hClosed)

/-- 公式替换闭包保持真。 -/
theorem formula_substitution_closure_truth_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId) (start : Nat) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D start source target id Formula.truth)
        Formula.truth) := by
  apply Derives.iff_intro
  · exact Derives.truth_intro
  · simpa [formula_substitution_closure,
      Formula.substituteFree] using
        (P.term_flat_truth start hSource).context_weaken_cons

/--
公式替换闭包保持合取。

正向复用同一批见证；反向把右闭包重定位到左区间之后，由图功能性证明两次
编译值相等，再沿等式把右核心运输回左值。
-/
theorem formula_substitution_closure_conj_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId)
    {left right : Formula σ}
    (hLeft : Formula.Admissible left)
    (hRight : Formula.Admissible right)
    (hLeftFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport left)
    (hRightFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport right)
    (start : Nat) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D start source target id
          (Formula.conj left right))
        (Formula.conj
          (formula_substitution_closure
            D start source target id left)
          (formula_substitution_closure
            D start source target id right))) := by
  let compiled := term D start source
  let next := compiled.next
  let leftClosed :=
    formula_substitution_closure
      D start source target id left
  let rightClosed :=
    formula_substitution_closure
      D start source target id right
  let conjunctionClosed :=
    formula_substitution_closure
      D start source target id
        (Formula.conj left right)
  have hLeftClosed :
      Formula.Admissible leftClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value left)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hLeft hValue)
  have hRightClosed :
      Formula.Admissible rightClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value right)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hRight hValue)
  have hConjunctionClosed :
      Formula.Admissible conjunctionClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value
          (Formula.conj left right))
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id
          (Formula.Admissible.conj hLeft hRight)
          hValue)
  apply Derives.iff_intro
  · let Γ : Context σ := [conjunctionClosed]
    have hClosed :
        Derives P.theory Γ conjunctionClosed :=
      Derives.assumption_of_mem
        (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hConjunctionClosed)
    change Derives P.theory Γ
      (Formula.conj leftClosed rightClosed)
    apply P.term_flat_elim_to_conditions
        start hSource
        (fun value =>
          Formula.substituteFree target id value
            (Formula.conj left right))
    · intro value hValue
      exact Formula.Admissible.substituteFree
        target id
        (Formula.Admissible.conj hLeft hRight)
        hValue
    · intro index hLower hUpper formula hFormula
      have hFormulaEq : formula = conjunctionClosed :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hFormula
      subst formula
      exact formula_substitution_closure_witness_fresh
        D start source target id
        (Formula.conj left right)
        (fun index => by
          simpa [Formula.freeSupport] using
            And.intro
              (hLeftFresh index)
              (hRightFresh index))
        index
    · intro index hLower hUpper
      simp only [Formula.freeSupport,
        List.mem_append]
      intro hMember
      rcases hMember with hMember | hMember
      · exact
          (formula_substitution_closure_witness_fresh
            D start source target id left
            hLeftFresh index) hMember
      · exact
          (formula_substitution_closure_witness_fresh
            D start source target id right
            hRightFresh index) hMember
    · simpa [conjunctionClosed, Γ] using hClosed
    · let Δ : Context σ :=
        compiled.conditions ++
          Formula.substituteFree target id
            compiled.value
            (Formula.conj left right) :: Γ
      have hCore :
          Derives P.theory Δ
            (Formula.substituteFree target id
              compiled.value
              (Formula.conj left right)) :=
        Derives.assumption_of_mem
          (List.mem_append.mpr <| Or.inr <| by simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible <| by
              exact Formula.Admissible.substituteFree
                target id
                (Formula.Admissible.conj hLeft hRight)
                ⟨(term_well_formed
                    D start hSource.1).1,
                  (term_scoped
                    D start hSource.2).1⟩)
      have hLeftCore :
          Derives P.theory Δ
            (Formula.substituteFree target id
              compiled.value left) := by
        simpa [Formula.substituteFree] using
          Derives.conj_elim_left hCore
      have hRightCore :
          Derives P.theory Δ
            (Formula.substituteFree target id
              compiled.value right) := by
        simpa [Formula.substituteFree] using
          Derives.conj_elim_right hCore
      apply Derives.conj_intro
      · apply formula_substitution_closure_intro
          D start source target id left
        · intro condition hCondition
          exact Derives.assumption_of_mem
            (List.mem_append.mpr <| Or.inl <| by
              simpa [compiled] using hCondition)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                term_conditions_admissible
                  D start hSource condition <| by
                    simpa [compiled] using hCondition)
        · exact hLeftCore
      · apply formula_substitution_closure_intro
          D start source target id right
        · intro condition hCondition
          exact Derives.assumption_of_mem
            (List.mem_append.mpr <| Or.inl <| by
              simpa [compiled] using hCondition)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                term_conditions_admissible
                  D start hSource condition <| by
                    simpa [compiled] using hCondition)
        · exact hRightCore
  · let Γ : Context σ :=
      [Formula.conj leftClosed rightClosed]
    have hPair :
        Derives P.theory Γ
          (Formula.conj leftClosed rightClosed) :=
      Derives.assumption_of_mem
        (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible <|
            Formula.Admissible.conj
              hLeftClosed hRightClosed)
    have hLeftClosed' :
        Derives P.theory Γ leftClosed :=
      Derives.conj_elim_left hPair
    have hRightClosed' :
        Derives P.theory Γ rightClosed :=
      Derives.conj_elim_right hPair
    have hRightRebasedIff :=
      formula_substitution_closure_iff
        P hSource id hRight hRightFresh
        start next
    have hRightRebased :
        Derives P.theory Γ
          (formula_substitution_closure
            D next source target id right) :=
      Derives.iff_elim_right
        (hRightRebasedIff.context_weaken <| by
          simp)
        hRightClosed'
    change Derives P.theory Γ conjunctionClosed
    apply P.term_flat_elim_to_conditions
        start hSource
        (fun value =>
          Formula.substituteFree target id value left)
    · intro value hValue
      exact Formula.Admissible.substituteFree
        target id hLeft hValue
    · intro index hLower hUpper formula hFormula
      have hFormulaEq :
          formula =
            Formula.conj leftClosed rightClosed :=
        List.mem_singleton.mp <| by
          simpa [Γ] using hFormula
      subst formula
      simp only [Formula.freeSupport,
        List.mem_append]
      intro hMember
      rcases hMember with hMember | hMember
      · exact
          (formula_substitution_closure_witness_fresh
            D start source target id left
            hLeftFresh index) hMember
      · exact
          (formula_substitution_closure_witness_fresh
            D start source target id right
            hRightFresh index) hMember
    · intro index hLower hUpper
      exact formula_substitution_closure_witness_fresh
        D start source target id
        (Formula.conj left right)
        (fun index => by
          simpa [Formula.freeSupport] using
            And.intro
              (hLeftFresh index)
              (hRightFresh index))
        index
    · simpa [leftClosed, Γ] using hLeftClosed'
    · let Δ : Context σ :=
        compiled.conditions ++
          Formula.substituteFree target id
            compiled.value left :: Γ
      have hRightRebased' :
          Derives P.theory Δ
            (formula_substitution_closure
              D next source target id right) :=
        hRightRebased.context_weaken <| by
          intro formula hFormula
          exact List.mem_append.mpr <| Or.inr <|
            List.mem_cons.mpr <| Or.inr hFormula
      apply P.term_flat_elim_to_conditions
          next hSource
          (fun value =>
            Formula.substituteFree target id value right)
      · intro value hValue
        exact Formula.Admissible.substituteFree
          target id hRight hValue
      · intro index hLower hUpper formula hFormula
        rcases List.mem_append.mp hFormula with
          hCondition | hFormula
        · exact term_conditions_witness_fresh_above
            D start source hLower formula <| by
              simpa [compiled, next] using hCondition
        · rcases List.mem_cons.mp hFormula with
            rfl | hFormula
          · apply Formula.not_mem_freeSupport_substituteFree
            · exact term_value_witness_fresh_above
                D start source hLower
            · exact hLeftFresh index
          · have hFormulaEq :
                formula =
                  Formula.conj leftClosed rightClosed :=
              List.mem_singleton.mp <| by
                simpa [Γ] using hFormula
            subst formula
            simp only [Formula.freeSupport,
              List.mem_append]
            intro hMember
            rcases hMember with hMember | hMember
            · exact
                (formula_substitution_closure_witness_fresh
                  D start source target id left
                  hLeftFresh index) hMember
            · exact
                (formula_substitution_closure_witness_fresh
                  D start source target id right
                  hRightFresh index) hMember
      · intro index hLower hUpper
        exact formula_substitution_closure_witness_fresh
          D start source target id
          (Formula.conj left right)
          (fun index => by
            simpa [Formula.freeSupport] using
              And.intro
                (hLeftFresh index)
                (hRightFresh index))
          index
      · simpa [next] using hRightRebased'
      · let rightCompiled := term D next source
        let Θ : Context σ :=
          rightCompiled.conditions ++
            Formula.substituteFree target id
              rightCompiled.value right :: Δ
        have hEqual :=
          term_compiled_eq P
            start next hSource
        have hEqual' :
            Derives P.theory Θ
              (Formula.equal compiled.value
                rightCompiled.value) := by
          apply hEqual.context_weaken
          intro formula hFormula
          rcases List.mem_append.mp hFormula with
            hLeftCondition | hRightCondition
          · exact List.mem_append.mpr <| Or.inr <|
              List.mem_cons.mpr <| Or.inr <|
                List.mem_append.mpr <| Or.inl <| by
                  simpa [compiled] using hLeftCondition
          · exact List.mem_append.mpr <| Or.inl <| by
              simpa [rightCompiled, next] using
                hRightCondition
        have hEquivalent :=
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.equality_iff_of_equality
            (sort := target) (eigen := id)
            (body := right) hEqual'
            (hLeftCheck :=
              Term.check_certificate_of_admissible
                ⟨(term_well_formed
                    D start hSource.1).1,
                  (term_scoped
                    D start hSource.2).1⟩)
            (hRightCheck :=
              Term.check_certificate_of_admissible
                ⟨(term_well_formed
                    D next hSource.1).1,
                  (term_scoped
                    D next hSource.2).1⟩)
            (hBodyCheck :=
              Formula.check_certificate_of_admissible
                hRight)
        have hRightCore :
            Derives P.theory Θ
              (Formula.substituteFree target id
                rightCompiled.value right) :=
          Derives.assumption_of_mem
            (List.mem_append.mpr <| Or.inr <| by
              simp)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                Formula.Admissible.substituteFree
                  target id hRight
                    ⟨(term_well_formed
                        D next hSource.1).1,
                      (term_scoped
                        D next hSource.2).1⟩)
        have hRightAtLeft :
            Derives P.theory Θ
              (Formula.substituteFree target id
                compiled.value right) :=
          Derives.iff_elim_left
            hEquivalent hRightCore
        have hLeftCore :
            Derives P.theory Θ
              (Formula.substituteFree target id
                compiled.value left) :=
          Derives.assumption_of_mem
            (List.mem_append.mpr <| Or.inr <|
              List.mem_cons.mpr <| Or.inr <|
                List.mem_append.mpr <| Or.inr <| by
                  simp)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                Formula.Admissible.substituteFree
                  target id hLeft
                    ⟨(term_well_formed
                        D start hSource.1).1,
                      (term_scoped
                        D start hSource.2).1⟩)
        apply formula_substitution_closure_intro
            D start source target id
            (Formula.conj left right)
        · intro condition hCondition
          exact Derives.assumption_of_mem
            (List.mem_append.mpr <| Or.inr <|
              List.mem_cons.mpr <| Or.inr <|
                List.mem_append.mpr <| Or.inl <| by
                  simpa [compiled] using hCondition)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                term_conditions_admissible
                  D start hSource condition <| by
                    simpa [compiled] using hCondition)
        · simpa [Formula.substituteFree] using
            Derives.conj_intro
              hLeftCore hRightAtLeft

/--
公式替换闭包保持否定。

正向由合取合同把冲突合并到同一次求值；反向利用图总性取得一个值，并在该值处
对公式做经典二分。
-/
theorem formula_substitution_closure_neg_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId)
    {body : Formula σ}
    (hBody : Formula.Admissible body)
    (hBodyFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport body)
    (start : Nat) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D start source target id
            (Formula.neg body))
        (Formula.neg
          (formula_substitution_closure
            D start source target id body))) := by
  let bodyClosed :=
    formula_substitution_closure
      D start source target id body
  let negClosed :=
    formula_substitution_closure
      D start source target id
        (Formula.neg body)
  have hBodyClosed :
      Formula.Admissible bodyClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value body)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hBody hValue)
  have hNegClosed :
      Formula.Admissible negClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value
          (Formula.neg body))
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id
          (Formula.Admissible.neg hBody)
          hValue)
  have hConjunction :=
    formula_substitution_closure_conj_iff
      P hSource id
      (Formula.Admissible.neg hBody) hBody
      (fun index => by
        simpa [Formula.freeSupport] using
          hBodyFresh index)
      hBodyFresh start
  have hContradictionTemplate :
      Derives (Theory.empty : Theory σ) []
        (Formula.iff
          (Formula.conj
            (Formula.neg body) body)
          Formula.falsum) := by
    derive_prop
  have hContradiction :=
    formula_substitution_closure_iff_mono
      D start hSource id
        hContradictionTemplate
  have hFalsum :=
    formula_substitution_closure_falsum_iff
      P hSource id start
  apply Derives.iff_intro
  · let Γ : Context σ := [negClosed]
    apply Derives.neg_intro
      (hBodyCheck :=
        Formula.check_certificate_of_admissible
          hBodyClosed)
    have hNeg :
        Derives P.theory (bodyClosed :: Γ)
          negClosed :=
      Derives.assumption_of_mem
        (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hNegClosed)
    have hPositive :
        Derives P.theory (bodyClosed :: Γ)
          bodyClosed :=
      Derives.assumption_of_mem
        (by simp)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hBodyClosed)
    have hPair :
        Derives P.theory (bodyClosed :: Γ)
          (Formula.conj negClosed bodyClosed) :=
      Derives.conj_intro hNeg hPositive
    have hClosedContradiction :=
      Derives.iff_elim_left
        (hConjunction.context_weaken <| by simp)
        hPair
    have hClosedFalsum :=
      Derives.iff_elim_right
        (Derives.of_empty hContradiction)
        hClosedContradiction
    exact Derives.iff_elim_right
      (hFalsum.context_weaken <| by simp)
      hClosedFalsum
  · let Γ : Context σ :=
      [Formula.neg negClosed,
        Formula.neg bodyClosed]
    apply Derives.by_contradiction
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          hNegClosed)
    change Derives P.theory Γ Formula.falsum
    have hTruth :
        Derives P.theory Γ
          (term_flat_closure D start source
            (fun _ => Formula.truth)) :=
      (P.term_flat_truth start hSource).context_weaken <| by
        simp
    apply P.term_flat_elim_to_conditions
        start hSource
        (fun _ => Formula.truth)
    · intro value hValue
      exact Formula.Admissible.truth
    · intro index hLower hUpper formula hFormula
      rcases List.mem_cons.mp hFormula with
        rfl | hFormula
      · simpa [Formula.freeSupport] using
          formula_substitution_closure_witness_fresh
            D start source target id
            (Formula.neg body)
            (fun index => by
              simpa [Formula.freeSupport] using
                hBodyFresh index)
            index
      · have hFormulaEq :
            formula = Formula.neg bodyClosed :=
          List.mem_singleton.mp hFormula
        subst formula
        simpa [Formula.freeSupport] using
          formula_substitution_closure_witness_fresh
            D start source target id body
            hBodyFresh index
    · intro index hLower hUpper
      simp [Formula.freeSupport]
    · exact hTruth
    · let compiled := term D start source
      let Δ : Context σ :=
        compiled.conditions ++ Formula.truth :: Γ
      have hValue :
          Term.Admissible compiled.value target :=
        ⟨(term_well_formed
            D start hSource.1).1,
          (term_scoped
            D start hSource.2).1⟩
      let core :=
        Formula.substituteFree target id
          compiled.value body
      apply
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.by_formula_cases
          (φ := core)
          (Formula.Admissible.substituteFree
            target id hBody hValue)
      · have hNegCore :
            Derives P.theory
              (Formula.neg core :: Δ)
              (Formula.neg core) :=
          Derives.assumption_of_mem
            (by simp)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                Formula.Admissible.neg <|
                  Formula.Admissible.substituteFree
                    target id hBody hValue)
        have hClosed :
            Derives P.theory
              (Formula.neg core :: Δ)
              negClosed := by
          apply formula_substitution_closure_intro
              D start source target id
              (Formula.neg body)
          · intro condition hCondition
            exact Derives.assumption_of_mem
              (by simp [Δ, compiled, hCondition])
              (hFormulaCheck :=
                Formula.check_certificate_of_admissible <|
                  term_conditions_admissible
                    D start hSource condition <| by
                      simpa [compiled] using hCondition)
          · simpa [core, Formula.substituteFree]
              using hNegCore
        have hNotClosed :
            Derives P.theory
              (Formula.neg core :: Δ)
              (Formula.neg negClosed) :=
          Derives.assumption_of_mem
            (by simp [Δ, Γ])
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                Formula.Admissible.neg hNegClosed)
        exact Derives.neg_elim
          hClosed hNotClosed
      · have hCore :
            Derives P.theory (core :: Δ) core :=
          Derives.assumption_of_mem
            (by simp)
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                Formula.Admissible.substituteFree
                  target id hBody hValue)
        have hClosed :
            Derives P.theory
              (core :: Δ) bodyClosed := by
          apply formula_substitution_closure_intro
              D start source target id body
          · intro condition hCondition
            exact Derives.assumption_of_mem
              (by simp [Δ, compiled, hCondition])
              (hFormulaCheck :=
                Formula.check_certificate_of_admissible <|
                  term_conditions_admissible
                    D start hSource condition <| by
                      simpa [compiled] using hCondition)
          · simpa [core] using hCore
        have hNotClosed :
            Derives P.theory (core :: Δ)
              (Formula.neg bodyClosed) :=
          Derives.assumption_of_mem
            (by simp [Δ, Γ])
            (hFormulaCheck :=
              Formula.check_certificate_of_admissible <|
                Formula.Admissible.neg hBodyClosed)
        exact Derives.neg_elim
          hClosed hNotClosed

/-- 公式替换闭包保持析取。 -/
theorem formula_substitution_closure_disj_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId)
    {left right : Formula σ}
    (hLeft : Formula.Admissible left)
    (hRight : Formula.Admissible right)
    (hLeftFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport left)
    (hRightFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport right)
    (start : Nat) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D start source target id
            (Formula.disj left right))
        (Formula.disj
          (formula_substitution_closure
            D start source target id left)
          (formula_substitution_closure
            D start source target id right))) := by
  let leftClosed :=
    formula_substitution_closure
      D start source target id left
  let rightClosed :=
    formula_substitution_closure
      D start source target id right
  have hLeftClosed :
      Formula.Admissible leftClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value left)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hLeft hValue)
  have hRightClosed :
      Formula.Admissible rightClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value right)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hRight hValue)
  have hTemplate :
      Derives (Theory.empty : Theory σ) []
        (Formula.iff
          (Formula.disj left right)
          (Formula.neg
            (Formula.conj
              (Formula.neg left)
              (Formula.neg right)))) := by
    derive_prop
  have hTemplateClosed :
      Derives P.theory []
        (Formula.iff
          (formula_substitution_closure
            D start source target id
              (Formula.disj left right))
          (formula_substitution_closure
            D start source target id
              (Formula.neg
                (Formula.conj
                  (Formula.neg left)
                  (Formula.neg right))))) :=
    Derives.of_empty <|
      formula_substitution_closure_iff_mono
        D start hSource id hTemplate
  have hOuterNeg :=
    formula_substitution_closure_neg_iff
      P hSource id
      (Formula.Admissible.conj
        (Formula.Admissible.neg hLeft)
        (Formula.Admissible.neg hRight))
      (fun index => by
        simpa [Formula.freeSupport] using
          And.intro
            (hLeftFresh index)
            (hRightFresh index))
      start
  have hInnerConj :=
    formula_substitution_closure_conj_iff
      P hSource id
      (Formula.Admissible.neg hLeft)
      (Formula.Admissible.neg hRight)
      (fun index => by
        simpa [Formula.freeSupport] using
          hLeftFresh index)
      (fun index => by
        simpa [Formula.freeSupport] using
          hRightFresh index)
      start
  have hInnerConjNeg :=
    (DerivationEquivalent.of_iff
      hInnerConj).neg_congr.to_iff
  have hLeftNeg :=
    formula_substitution_closure_neg_iff
      P hSource id hLeft hLeftFresh start
  have hRightNeg :=
    formula_substitution_closure_neg_iff
      P hSource id hRight hRightFresh start
  have hComponents :=
    (DerivationEquivalent.of_iff hLeftNeg).conj_congr
      (DerivationEquivalent.of_iff hRightNeg)
  have hComponentsNeg :=
    hComponents.neg_congr.to_iff
  have hTarget :
      Derives P.theory []
        (Formula.iff
          (Formula.neg
            (Formula.conj
              (Formula.neg leftClosed)
              (Formula.neg rightClosed)))
          (Formula.disj
            leftClosed rightClosed)) :=
    de_morgan_iff
      hLeftClosed hRightClosed
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hTemplateClosed <|
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hOuterNeg <|
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
              hInnerConjNeg <|
                _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
                  hComponentsNeg hTarget

/-- 公式替换闭包保持蕴含。 -/
theorem formula_substitution_closure_imp_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId)
    {left right : Formula σ}
    (hLeft : Formula.Admissible left)
    (hRight : Formula.Admissible right)
    (hLeftFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport left)
    (hRightFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport right)
    (start : Nat) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D start source target id
            (Formula.imp left right))
        (Formula.imp
          (formula_substitution_closure
            D start source target id left)
          (formula_substitution_closure
            D start source target id right))) := by
  let leftClosed :=
    formula_substitution_closure
      D start source target id left
  let rightClosed :=
    formula_substitution_closure
      D start source target id right
  have hLeftClosed :
      Formula.Admissible leftClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value left)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hLeft hValue)
  have hRightClosed :
      Formula.Admissible rightClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value right)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hRight hValue)
  have hTemplate :
      Derives (Theory.empty : Theory σ) []
        (Formula.iff
          (Formula.imp left right)
          (Formula.disj
            (Formula.neg left) right)) := by
    derive_prop
  have hTemplateClosed :
      Derives P.theory []
        (Formula.iff
          (formula_substitution_closure
            D start source target id
              (Formula.imp left right))
          (formula_substitution_closure
            D start source target id
              (Formula.disj
                (Formula.neg left) right))) :=
    Derives.of_empty <|
      formula_substitution_closure_iff_mono
        D start hSource id hTemplate
  have hDisjunction :=
    formula_substitution_closure_disj_iff
      P hSource id
      (Formula.Admissible.neg hLeft) hRight
      (fun index => by
        simpa [Formula.freeSupport] using
          hLeftFresh index)
      hRightFresh start
  have hNegation :=
    formula_substitution_closure_neg_iff
      P hSource id hLeft hLeftFresh start
  have hComponents :=
    (DerivationEquivalent.of_iff
      hNegation).disj_congr
        (DerivationEquivalent.refl hRightClosed)
  have hTarget :
      Derives P.theory []
        (Formula.iff
          (Formula.disj
            (Formula.neg leftClosed)
            rightClosed)
          (Formula.imp
            leftClosed rightClosed)) :=
    neg_disj_iff_imp
      hLeftClosed hRightClosed
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hTemplateClosed <|
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hDisjunction <|
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
              hComponents.to_iff hTarget

/-- 公式替换闭包保持双条件。 -/
theorem formula_substitution_closure_iff_iff
    (P : GraphPresentation D)
    {source : Term σ} {target : σ.SortSymbol}
    (hSource : Term.Admissible source target)
    (id : FreeVarId)
    {left right : Formula σ}
    (hLeft : Formula.Admissible left)
    (hRight : Formula.Admissible right)
    (hLeftFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport left)
    (hRightFresh :
      ∀ index,
        (D.sort, witness_id index) ∉
          Formula.freeSupport right)
    (start : Nat) :
    Derives P.theory []
      (Formula.iff
        (formula_substitution_closure
          D start source target id
            (Formula.iff left right))
        (Formula.iff
          (formula_substitution_closure
            D start source target id left)
          (formula_substitution_closure
            D start source target id right))) := by
  let leftClosed :=
    formula_substitution_closure
      D start source target id left
  let rightClosed :=
    formula_substitution_closure
      D start source target id right
  have hLeftClosed :
      Formula.Admissible leftClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value left)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hLeft hValue)
  have hRightClosed :
      Formula.Admissible rightClosed :=
    term_flat_closure_admissible
      D start hSource
      (fun value =>
        Formula.substituteFree target id value right)
      (fun hValue =>
        Formula.Admissible.substituteFree
          target id hRight hValue)
  have hTemplate :
      Derives (Theory.empty : Theory σ) []
        (Formula.iff
          (Formula.iff left right)
          (Formula.conj
            (Formula.imp left right)
            (Formula.imp right left))) := by
    derive_prop
  have hTemplateClosed :
      Derives P.theory []
        (Formula.iff
          (formula_substitution_closure
            D start source target id
              (Formula.iff left right))
          (formula_substitution_closure
            D start source target id
              (Formula.conj
                (Formula.imp left right)
                (Formula.imp right left)))) :=
    Derives.of_empty <|
      formula_substitution_closure_iff_mono
        D start hSource id hTemplate
  have hConjunction :=
    formula_substitution_closure_conj_iff
      P hSource id
      (Formula.Admissible.imp hLeft hRight)
      (Formula.Admissible.imp hRight hLeft)
      (fun index => by
        simpa [Formula.freeSupport] using
          And.intro
            (hLeftFresh index)
            (hRightFresh index))
      (fun index => by
        simpa [Formula.freeSupport] using
          And.intro
            (hRightFresh index)
            (hLeftFresh index))
      start
  have hForward :=
    formula_substitution_closure_imp_iff
      P hSource id hLeft hRight
      hLeftFresh hRightFresh start
  have hBackward :=
    formula_substitution_closure_imp_iff
      P hSource id hRight hLeft
      hRightFresh hLeftFresh start
  have hComponents :=
    (DerivationEquivalent.of_iff
      hForward).conj_congr
        (DerivationEquivalent.of_iff hBackward)
  have hTarget :
      Derives P.theory []
        (Formula.iff
          (Formula.conj
            (Formula.imp leftClosed rightClosed)
            (Formula.imp rightClosed leftClosed))
          (Formula.iff
            leftClosed rightClosed)) :=
    conj_imp_iff
      hLeftClosed hRightClosed
  exact
    _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
      hTemplateClosed <|
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hConjunction <|
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
              hComponents.to_iff hTarget

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
