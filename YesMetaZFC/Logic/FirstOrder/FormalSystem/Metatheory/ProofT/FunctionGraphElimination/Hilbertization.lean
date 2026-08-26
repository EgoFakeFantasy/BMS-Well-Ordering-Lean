import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Formula
import YesMetaZFC.Logic.FirstOrder.Hilbert.Hilbertization
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Monotonicity

/-!
# 函数图编译与 Hilbert 归约相容

Hilbert 归约虽然会复制、重排部分子公式，但不改变任一 sort 上自由变量编号的
最大值，因此量词编译器仍会选择同一个 canonical 新鲜变量。原子函数图编译会
引入存在量词与合取，所以两种变换并非语法相等；本模块给出正确的证明级结论：
二者在纯图理论中严格双向可达。
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
  {D : Data σ}

omit [DecidableEq σ.FuncSymbol] in
/-- 支持列表拼接后的编号上界等于两侧上界的最大值。 -/
private theorem support_bound_append
    (sort : σ.SortSymbol)
    (left right : FreeVariable.Support σ) :
    FreshVariable.support_bound sort
        (left ++ right) =
      Nat.max
        (FreshVariable.support_bound sort left)
        (FreshVariable.support_bound sort right) := by
  induction left with
  | nil =>
      simp [FreshVariable.support_bound]
  | cons head tail ih =>
      rcases head with ⟨entrySort, id⟩
      simp [FreshVariable.support_bound, ih,
        Nat.max_assoc]

omit [DecidableEq σ.FuncSymbol] in
/-- Hilbert 归约不改变任一 sort 上自由变量编号的 canonical 上界。 -/
theorem formula_bound_hilbertize
    (anchorSort sort : σ.SortSymbol)
    (source : Formula σ) :
    FreshVariable.formula_bound sort
        (Formula.hilbertize anchorSort source) =
      FreshVariable.formula_bound sort source := by
  induction source with
  | falsum =>
      simp [FreshVariable.formula_bound,
        Formula.hilbertize,
        Formula.hilbert_falsum,
        Formula.hilbert_truth,
        Formula.freeSupport,
        Term.freeSupport,
        FreshVariable.support_bound]
  | truth =>
      simp [FreshVariable.formula_bound,
        Formula.hilbertize,
        Formula.hilbert_truth,
        Formula.freeSupport,
        Term.freeSupport,
        FreshVariable.support_bound]
  | rel relation arguments =>
      rfl
  | equal left right =>
      rfl
  | neg body ih =>
      simpa [FreshVariable.formula_bound,
        Formula.hilbertize,
        Formula.freeSupport] using ih
  | conj left right ihLeft ihRight =>
      change
        FreshVariable.support_bound sort
            (Formula.freeSupport
              (Formula.hilbertize anchorSort left)) =
          FreshVariable.support_bound sort
            (Formula.freeSupport left) at ihLeft
      change
        FreshVariable.support_bound sort
            (Formula.freeSupport
              (Formula.hilbertize anchorSort right)) =
          FreshVariable.support_bound sort
            (Formula.freeSupport right) at ihRight
      simp [FreshVariable.formula_bound,
        Formula.hilbertize,
        Formula.hilbert_conj,
        Formula.freeSupport,
        support_bound_append, ihLeft, ihRight]
  | disj left right ihLeft ihRight =>
      change
        FreshVariable.support_bound sort
            (Formula.freeSupport
              (Formula.hilbertize anchorSort left)) =
          FreshVariable.support_bound sort
            (Formula.freeSupport left) at ihLeft
      change
        FreshVariable.support_bound sort
            (Formula.freeSupport
              (Formula.hilbertize anchorSort right)) =
          FreshVariable.support_bound sort
            (Formula.freeSupport right) at ihRight
      simp [FreshVariable.formula_bound,
        Formula.hilbertize,
        Formula.freeSupport,
        support_bound_append, ihLeft, ihRight]
  | imp antecedent consequent
      ihAntecedent ihConsequent =>
      change
        FreshVariable.support_bound sort
            (Formula.freeSupport
              (Formula.hilbertize
                anchorSort antecedent)) =
          FreshVariable.support_bound sort
            (Formula.freeSupport antecedent)
        at ihAntecedent
      change
        FreshVariable.support_bound sort
            (Formula.freeSupport
              (Formula.hilbertize
                anchorSort consequent)) =
          FreshVariable.support_bound sort
            (Formula.freeSupport consequent)
        at ihConsequent
      simp [FreshVariable.formula_bound,
        Formula.hilbertize,
        Formula.freeSupport,
        support_bound_append,
        ihAntecedent, ihConsequent]
  | iff left right ihLeft ihRight =>
      change
        FreshVariable.support_bound sort
            (Formula.freeSupport
              (Formula.hilbertize anchorSort left)) =
          FreshVariable.support_bound sort
            (Formula.freeSupport left) at ihLeft
      change
        FreshVariable.support_bound sort
            (Formula.freeSupport
              (Formula.hilbertize anchorSort right)) =
          FreshVariable.support_bound sort
            (Formula.freeSupport right) at ihRight
      simp only [FreshVariable.formula_bound,
        Formula.hilbertize,
        Formula.hilbert_iff,
        Formula.hilbert_conj,
        Formula.freeSupport,
        support_bound_append, ihLeft, ihRight]
      simp [Nat.max_comm]
  | forallE sort body ih =>
      simpa [FreshVariable.formula_bound,
        Formula.hilbertize,
        Formula.freeSupport] using ih
  | existsE sort body ih =>
      simpa [FreshVariable.formula_bound,
        Formula.hilbertize,
        Formula.freeSupport] using ih

omit [DecidableEq σ.FuncSymbol] in
/-- Hilbert 归约前后，单公式 canonical 新鲜变量完全相同。 -/
theorem fresh_id_hilbertize
    (anchorSort sort : σ.SortSymbol)
    (source : Formula σ) :
    FreshVariable.fresh_id sort
        [Formula.hilbertize anchorSort source] =
      FreshVariable.fresh_id sort [source] := by
  simp [FreshVariable.fresh_id,
    FreshVariable.formulas_bound,
    formula_bound_hilbertize]

namespace GraphPresentation

/-- 图理论由闭句组成，所以任意自由变量均对理论新鲜。 -/
private theorem theory_fresh
    (P : GraphPresentation D)
    (sort : σ.SortSymbol) (id : FreeVarId) :
    ∀ φ, P.theory φ →
      (sort, id) ∉ Formula.freeSupport φ := by
  intro φ hφ
  rw [(P.theory_sentence hφ).2]
  exact List.not_mem_nil

/--
函数图编译与 Hilbert 归约严格双向可达。

原子分支直接使用完整 Hilbert 化等价；量词分支由 canonical 上界不变保证两侧
选取同一 opening，再将归纳等价关闭回 binder。
-/
theorem hilbertize_equivalent
    (P : GraphPresentation D)
    (anchorSort : σ.SortSymbol)
    (source : Formula σ)
    (hSource : Formula.Admissible source) :
    DerivationEquivalent P.theory []
      (formula D
        (Formula.hilbertize anchorSort source))
      (Formula.hilbertize anchorSort
        (formula D source)) := by
  cases source with
  | falsum =>
      have hCompiled :
          formula D
              (Formula.hilbertize anchorSort
                (Formula.falsum : Formula σ)) =
            Formula.hilbert_falsum anchorSort := by
        apply formula_eq_of_sentence_avoids
        · simp [Formula.hilbertize,
            Formula.hilbert_falsum,
            Formula.hilbert_truth,
            FormulaAvoids, TermAvoids]
        · exact
            ⟨Formula.Admissible.hilbert_falsum
                anchorSort,
              by
                change
                  Formula.freeSupport
                      (Formula.hilbert_truth
                        anchorSort) = []
                exact
                  Formula.freeSupport_hilbert_truth
                    anchorSort⟩
      rw [hCompiled]
      simpa [formula, Formula.hilbertize] using
          DerivationEquivalent.refl
            (theory := P.theory) (context := [])
            (Formula.Admissible.hilbert_falsum
              anchorSort)
  | truth =>
      have hCompiled :
          formula D
              (Formula.hilbertize anchorSort
                (Formula.truth : Formula σ)) =
            Formula.hilbert_truth anchorSort := by
        apply formula_eq_of_sentence_avoids
        · simp [Formula.hilbertize,
            Formula.hilbert_truth,
            FormulaAvoids, TermAvoids]
        · exact
            ⟨Formula.Admissible.hilbert_truth
                anchorSort,
              Formula.freeSupport_hilbert_truth
                anchorSort⟩
      rw [hCompiled]
      simpa [formula, Formula.hilbertize] using
          DerivationEquivalent.refl
            (theory := P.theory) (context := [])
            (Formula.Admissible.hilbert_truth
              anchorSort)
  | rel relation arguments =>
      have hCompiled :
          Formula.Admissible
            (FunctionGraphElimination.relation
              D relation arguments) := by
        simpa [formula] using
          formula_admissible D hSource
      simpa [Formula.hilbertize, formula] using
        DerivationEquivalent.hilbertize
          anchorSort
          (FunctionGraphElimination.relation
            D relation arguments)
          hCompiled
  | equal left right =>
      have hCompiled :
          Formula.Admissible
            (FunctionGraphElimination.equality
              D left right) := by
        simpa [formula] using
          formula_admissible D hSource
      simpa [Formula.hilbertize, formula] using
        DerivationEquivalent.hilbertize
          anchorSort
          (FunctionGraphElimination.equality
            D left right)
          hCompiled
  | neg body =>
      simpa [Formula.hilbertize, formula] using
        (P.hilbertize_equivalent
          anchorSort body
          (Formula.Admissible.neg_body
            hSource)).neg_congr
  | conj left right =>
      have hLeft :=
        P.hilbertize_equivalent anchorSort
          left (Formula.Admissible.conj_left
            hSource)
      have hRight :=
        P.hilbertize_equivalent anchorSort
          right (Formula.Admissible.conj_right
            hSource)
      simpa [Formula.hilbertize,
        Formula.hilbert_conj, formula] using
          (hLeft.imp_congr
            hRight.neg_congr).neg_congr
  | disj left right =>
      have hLeft :=
        P.hilbertize_equivalent anchorSort
          left (Formula.Admissible.disj_left
            hSource)
      have hRight :=
        P.hilbertize_equivalent anchorSort
          right (Formula.Admissible.disj_right
            hSource)
      simpa [Formula.hilbertize, formula] using
        hLeft.neg_congr.imp_congr hRight
  | imp antecedent consequent =>
      have hAntecedent :=
        P.hilbertize_equivalent anchorSort
          antecedent
          (Formula.Admissible.imp_left hSource)
      have hConsequent :=
        P.hilbertize_equivalent anchorSort
          consequent
          (Formula.Admissible.imp_right hSource)
      simpa [Formula.hilbertize, formula] using
        hAntecedent.imp_congr hConsequent
  | iff left right =>
      have hLeft :=
        P.hilbertize_equivalent anchorSort
          left (Formula.Admissible.iff_left
            hSource)
      have hRight :=
        P.hilbertize_equivalent anchorSort
          right (Formula.Admissible.iff_right
            hSource)
      have hForward :=
        hLeft.imp_congr hRight
      have hBackward :=
        hRight.imp_congr hLeft
      simpa [Formula.hilbertize,
        Formula.hilbert_iff,
        Formula.hilbert_conj, formula] using
          (hForward.imp_congr
            hBackward.neg_congr).neg_congr
  | forallE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      have hFresh :
          (sort, eigen) ∉
            Formula.freeSupport body := by
        dsimp [eigen]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hOpened :
          Formula.Admissible opened := by
        dsimp [opened]
        exact Formula.Admissible.forall_openAt
          sort hSource
            ⟨TermWellSorted.fvar sort eigen,
              TermScoped.fvar sort eigen⟩
      have hEquivalent :=
        P.hilbertize_equivalent
          anchorSort opened hOpened
      have hClosed :=
        Metatheory.Derives.forall_iff_mono
          (T := P.theory) (Γ := [])
          (sort := sort)
          (eigen := source_id eigen)
          (P.theory_fresh sort
            (source_id eigen))
          (by simp) hEquivalent.to_iff
      have hCanonical :=
        fresh_id_hilbertize
          anchorSort sort body
      simpa [Formula.hilbertize, formula,
        eigen, opened, hCanonical,
        Formula.openAt,
        Formula.closeFreeAt,
        Formula.hilbertize_openAt,
        Formula.hilbertize_closeFreeAt] using
          DerivationEquivalent.of_iff hClosed
  | existsE sort body =>
      let eigen :=
        FreshVariable.fresh_id sort [body]
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      have hOpened :
          Formula.Admissible opened := by
        dsimp [opened]
        exact Formula.Admissible.exists_openAt
          sort hSource
            ⟨TermWellSorted.fvar sort eigen,
              TermScoped.fvar sort eigen⟩
      have hEquivalent :=
        P.hilbertize_equivalent
          anchorSort opened hOpened
      have hClosed :=
        Metatheory.Derives.forall_iff_mono
          (T := P.theory) (Γ := [])
          (sort := sort)
          (eigen := source_id eigen)
          (P.theory_fresh sort
            (source_id eigen))
          (by simp) hEquivalent.neg_congr.to_iff
      have hCanonical :
          FreshVariable.fresh_id sort
              [Formula.neg
                (Formula.hilbertize
                  anchorSort body)] =
            eigen := by
        simpa [eigen,
          FreshVariable.fresh_id,
          FreshVariable.formulas_bound,
          FreshVariable.formula_bound,
          Formula.freeSupport] using
            fresh_id_hilbertize
              anchorSort sort body
      simpa [Formula.hilbertize, formula,
        eigen, opened, hCanonical,
        Formula.openAt,
        Formula.closeFreeAt,
        Formula.hilbertize_openAt,
        Formula.hilbertize_closeFreeAt] using
          (DerivationEquivalent.of_iff
            hClosed).neg_congr
termination_by Formula.complexity source
decreasing_by
  all_goals
    simp_all [Formula.complexity] <;>
      first
      | exact Nat.lt_succ_of_le
          (Nat.le_max_left _ _)
      | exact Nat.lt_succ_of_le
          (Nat.le_max_right _ _)
      | omega

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
