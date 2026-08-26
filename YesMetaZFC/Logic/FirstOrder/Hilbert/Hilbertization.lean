import YesMetaZFC.Logic.FirstOrder.FormulaComplexity
import YesMetaZFC.Logic.FirstOrder.Hilbert.Encoding
/-!
# 完整公式 Hilbert 化的严格等价
本模块证明每个 admissible 一阶公式都与其 `hilbertize` 结果严格双向可达。量词分支
不把 binder 体误当作空 scope 下的公式，而是：
1. 选择对量词体新鲜的 canonical free variable；
2. 打开 binder，得到真正 admissible 的顶层公式；
3. 按公式复杂度良基递归；
4. 使用 `forall_congr_open` / `exists_congr_open` 重新闭合。
因此该定理同时覆盖多排序、locally nameless 作用域和全部公共联结词。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace DerivationEquivalent
/-- 空背景中，admissible 公式与其 Hilbert 归约严格等价。 -/
theorem hilbertize_empty
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol) (formula : Formula σ) (hFormula : Formula.Admissible formula) :
    DerivationEquivalent (Theory.empty : Theory σ) []
      formula (Formula.hilbertize anchorSort formula) := by
  cases formula with
  | falsum =>
      simpa [Formula.hilbertize] using (DerivationEquivalent.Encoding.falsum_hilbert (theory := (Theory.empty : Theory σ)) (context := []) anchorSort)
  | truth =>
      simpa [Formula.hilbertize] using (DerivationEquivalent.Encoding.truth_hilbert (theory := (Theory.empty : Theory σ)) (context := []) anchorSort)
  | rel relation arguments =>
      simpa [Formula.hilbertize] using (DerivationEquivalent.refl (theory := (Theory.empty : Theory σ)) (context := []) hFormula)
  | equal left right =>
      simpa [Formula.hilbertize] using (DerivationEquivalent.refl (theory := (Theory.empty : Theory σ)) (context := []) hFormula)
  | neg body =>
      have hBody :=
        Formula.Admissible.neg_body hFormula
      have hBodyEquivalent :=
        hilbertize_empty anchorSort body hBody
      simpa [Formula.hilbertize] using
        hBodyEquivalent.neg_congr
  | conj left right =>
      have hLeft :=
        Formula.Admissible.conj_left hFormula
      have hRight :=
        Formula.Admissible.conj_right hFormula
      have hLeftEquivalent :=
        hilbertize_empty anchorSort left hLeft
      have hRightEquivalent :=
        hilbertize_empty anchorSort right hRight
      have hNative :=
        DerivationEquivalent.conj_congr
          hLeftEquivalent hRightEquivalent
      have hEncoded :=
        DerivationEquivalent.Encoding.conj_hilbert (theory := (Theory.empty : Theory σ)) (context := [])
          hLeftEquivalent.right_admissible
          hRightEquivalent.right_admissible
      simpa [Formula.hilbertize] using
        hNative.trans hEncoded
  | disj left right =>
      have hLeft :=
        Formula.Admissible.disj_left hFormula
      have hRight :=
        Formula.Admissible.disj_right hFormula
      have hLeftEquivalent :=
        hilbertize_empty anchorSort left hLeft
      have hRightEquivalent :=
        hilbertize_empty anchorSort right hRight
      have hNative :=
        DerivationEquivalent.disj_congr
          hLeftEquivalent hRightEquivalent
      have hEncoded :=
        DerivationEquivalent.Encoding.disj_hilbert (theory := (Theory.empty : Theory σ)) (context := [])
          hLeftEquivalent.right_admissible
          hRightEquivalent.right_admissible
      simpa [Formula.hilbertize] using
        hNative.trans hEncoded
  | imp antecedent consequent =>
      have hAntecedent :=
        Formula.Admissible.imp_left hFormula
      have hConsequent :=
        Formula.Admissible.imp_right hFormula
      have hAntecedentEquivalent :=
        hilbertize_empty anchorSort antecedent hAntecedent
      have hConsequentEquivalent :=
        hilbertize_empty anchorSort consequent hConsequent
      simpa [Formula.hilbertize] using (DerivationEquivalent.imp_congr
          hAntecedentEquivalent hConsequentEquivalent)
  | iff left right =>
      have hLeft :=
        Formula.Admissible.iff_left hFormula
      have hRight :=
        Formula.Admissible.iff_right hFormula
      have hLeftEquivalent :=
        hilbertize_empty anchorSort left hLeft
      have hRightEquivalent :=
        hilbertize_empty anchorSort right hRight
      have hNative :=
        DerivationEquivalent.iff_congr
          hLeftEquivalent hRightEquivalent
      have hEncoded :=
        DerivationEquivalent.Encoding.iff_hilbert (theory := (Theory.empty : Theory σ)) (context := [])
          hLeftEquivalent.right_admissible
          hRightEquivalent.right_admissible
      simpa [Formula.hilbertize] using
        hNative.trans hEncoded
  | forallE sort body =>
      let eigen := FreshVariable.fresh_id sort [body]
      let witness : Term σ :=
        Term.var (.fvar sort eigen)
      have hFresh : (sort, eigen) ∉ Formula.freeSupport body := by
        dsimp [eigen]
        exact FreshVariable.fresh_id_not_mem_m (by simp)
      have hHilbertFresh : (sort, eigen) ∉
            Formula.freeSupport (Formula.hilbertize anchorSort body) := by
        intro hMember
        exact hFresh <| (Formula.mem_freeSupport_hilbertize_iff
            anchorSort (sort, eigen) body).mp hMember
      have hWitness :
          Term.Admissible witness sort :=
        ⟨TermWellSorted.fvar sort eigen,
          TermScoped.fvar sort eigen⟩
      have hOpened :
          Formula.Admissible (Formula.openAt sort 0 witness body) :=
        Formula.Admissible.forall_openAt
          sort hFormula hWitness
      have hOpenedEquivalent :=
        hilbertize_empty anchorSort (Formula.openAt sort 0 witness body) hOpened
      have hOpenedEquivalent' :
          DerivationEquivalent (Theory.empty : Theory σ) [] (Formula.openAt sort 0 witness body) (Formula.openAt sort 0 witness
              (Formula.hilbertize anchorSort body)) := by
        simpa [Formula.hilbertize_openAt] using
          hOpenedEquivalent
      have hHilbertForall :
          Formula.Admissible (Formula.forallE sort (Formula.hilbertize anchorSort body)) := by
        simpa [Formula.hilbertize] using (Formula.Admissible.hilbertize (anchorSort := anchorSort) hFormula)
      have hEquivalent :=
        DerivationEquivalent.forall_congr_open (theory := (Theory.empty : Theory σ)) (context := []) (sort := sort) (eigen := eigen) (left := body)
          (right := Formula.hilbertize anchorSort body) (by
            intro candidate hCandidate
            cases hCandidate) (by simp)
          hFormula hHilbertForall
          hFresh hHilbertFresh hOpenedEquivalent'
      simpa [Formula.hilbertize] using hEquivalent
  | existsE sort body =>
      let eigen := FreshVariable.fresh_id sort [body]
      let witness : Term σ :=
        Term.var (.fvar sort eigen)
      have hFresh : (sort, eigen) ∉ Formula.freeSupport body := by
        dsimp [eigen]
        exact FreshVariable.fresh_id_not_mem_m (by simp)
      have hHilbertFresh : (sort, eigen) ∉
            Formula.freeSupport (Formula.hilbertize anchorSort body) := by
        intro hMember
        exact hFresh <| (Formula.mem_freeSupport_hilbertize_iff
            anchorSort (sort, eigen) body).mp hMember
      have hWitness :
          Term.Admissible witness sort :=
        ⟨TermWellSorted.fvar sort eigen,
          TermScoped.fvar sort eigen⟩
      have hOpened :
          Formula.Admissible (Formula.openAt sort 0 witness body) :=
        Formula.Admissible.exists_openAt
          sort hFormula hWitness
      have hOpenedEquivalent :=
        hilbertize_empty anchorSort (Formula.openAt sort 0 witness body) hOpened
      have hOpenedEquivalent' :
          DerivationEquivalent (Theory.empty : Theory σ) [] (Formula.openAt sort 0 witness body) (Formula.openAt sort 0 witness
              (Formula.hilbertize anchorSort body)) := by
        simpa [Formula.hilbertize_openAt] using
          hOpenedEquivalent
      have hHilbertExists :
          Formula.Admissible (Formula.existsE sort (Formula.hilbertize anchorSort body)) := by
        apply Formula.Admissible.hilbert_exists_source
        simpa [Formula.hilbertize] using (Formula.Admissible.hilbertize (anchorSort := anchorSort) hFormula)
      have hCongruence :=
        DerivationEquivalent.exists_congr_open (theory := (Theory.empty : Theory σ)) (context := []) (sort := sort) (eigen := eigen) (left := body)
          (right := Formula.hilbertize anchorSort body) (by
            intro candidate hCandidate
            cases hCandidate) (by simp)
          hFormula hHilbertExists
          hFresh hHilbertFresh hOpenedEquivalent'
      have hEncoding :=
        DerivationEquivalent.Encoding.exists_hilbert (theory := (Theory.empty : Theory σ)) (context := [])
          sort (Formula.hilbertize anchorSort body)
          hHilbertExists
      simpa [Formula.hilbertize] using
        hCongruence.trans hEncoding
termination_by Formula.complexity formula
decreasing_by
  all_goals
    simp_all [Formula.complexity] <;>
      first
      | exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
      | exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
      | omega
/-- 任意背景中，admissible 公式与其 Hilbert 归约严格等价。 -/
theorem hilbertize
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {theory : Theory σ} {context : Context σ} (formula : Formula σ) (hFormula : Formula.Admissible formula) :
    DerivationEquivalent theory context
      formula (Formula.hilbertize anchorSort formula) := (hilbertize_empty anchorSort formula hFormula).of_empty
end DerivationEquivalent
end FirstOrder
end Logic
end YesMetaZFC
