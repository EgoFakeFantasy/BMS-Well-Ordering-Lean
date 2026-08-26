import YesMetaZFC.Logic.FirstOrder.Hilbert.Translation
/-!
# Hilbert 片段中的经典命题规则
本模块在标准 Hilbert 核中导出自然演绎编译所需的真假、否定、编码合取、编码析取
和编码双条件规则。所有证明只消费十二类基础模式、演绎定理与 MP。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace HilbertDerives
/-- 归约层选取的闭真式是一个逻辑公理。 -/
theorem truth {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) :
    HilbertDerives theory (Formula.hilbert_truth anchorSort) := by
  let eigen : FreeVarId := 0
  have hAxiom :
      HilbertLogicalAxiom (Formula.forallE anchorSort (Formula.closeFreeAt anchorSort eigen 0 (Formula.equal (Term.var (.fvar anchorSort eigen))
              (Term.var (.fvar anchorSort eigen))))) :=
    .forall_closure anchorSort eigen (.base (.equality_reflexivity anchorSort eigen))
  have hAxiomAdmissible :
      Formula.Admissible (Formula.forallE anchorSort (Formula.closeFreeAt anchorSort eigen 0 (Formula.equal (Term.var (.fvar anchorSort eigen))
              (Term.var (.fvar anchorSort eigen))))) :=
    Formula.Admissible.forall_closeFreeAt anchorSort eigen
      ⟨.equal (TermWellSorted.fvar anchorSort eigen) (TermWellSorted.fvar anchorSort eigen),
        .equal (TermScoped.fvar anchorSort eigen) (TermScoped.fvar anchorSort eigen)⟩
  simpa [Formula.hilbert_truth, Formula.closeFreeAt,
    Term.closeFreeAt] using (HilbertDerives.logical_axiom (theory := theory) hAxiom
      hAxiomAdmissible)
/-- 从归约层的假式可推出任意公式。 -/
theorem falsum_elim {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {conclusion : Formula σ} (hConclusion : Formula.Admissible conclusion) (hFalse :
      HilbertDerives theory (Formula.hilbert_falsum anchorSort)) :
    HilbertDerives theory conclusion := by
  have hExplosion :
      HilbertDerives theory (Formula.imp (Formula.neg (Formula.hilbert_truth anchorSort)) (Formula.imp (Formula.hilbert_truth anchorSort) conclusion)) :=
    base_axiom (.explosion (Formula.hilbert_truth anchorSort) conclusion) (Formula.Admissible.imp (Formula.Admissible.neg
          (Formula.Admissible.hilbert_truth anchorSort)) (Formula.Admissible.imp (Formula.Admissible.hilbert_truth anchorSort)
          hConclusion))
  have hStep :
      HilbertDerives theory (Formula.imp (Formula.hilbert_truth anchorSort) conclusion) :=
    .modus_ponens hFalse hExplosion
  exact .modus_ponens (truth anchorSort) hStep
/-- 一个公式及其否定推出任意结论。 -/
theorem neg_elim {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {formula conclusion : Formula σ} (hConclusion : Formula.Admissible conclusion) (hFormula : HilbertDerives theory formula)
    (hNegation : HilbertDerives theory (Formula.neg formula)) :
    HilbertDerives theory conclusion := by
  have hContradiction :
      HilbertDerives theory (Formula.imp formula (Formula.imp (Formula.neg formula) conclusion)) :=
    base_axiom (.contradiction formula conclusion) (Formula.Admissible.imp hFormula.admissible (Formula.Admissible.imp hNegation.admissible hConclusion))
  exact .modus_ponens hNegation (.modus_ponens hFormula hContradiction)
/-- 若临时假设公式会推出归约假式，则可推出该公式的否定。 -/
theorem neg_intro {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {formula : Formula σ} (hFormula : Formula.Admissible formula) (hFalse :
      HilbertDerives (Theory.insert formula theory) (Formula.hilbert_falsum anchorSort)) :
    HilbertDerives theory (Formula.neg formula) := by
  have hNegationUnderAssumption :
      HilbertDerives (Theory.insert formula theory) (Formula.neg formula) :=
    falsum_elim anchorSort (Formula.Admissible.neg hFormula) hFalse
  have hPositiveBranch :
      HilbertDerives theory (Formula.imp formula (Formula.neg formula)) :=
    deduction hFormula hNegationUnderAssumption
  have hNegativeBranch :
      HilbertDerives theory (Formula.imp (Formula.neg formula) (Formula.neg formula)) :=
    imp_refl (Formula.neg formula) (Formula.Admissible.neg hFormula)
  have hCases :
      HilbertDerives theory (Formula.imp (Formula.imp formula (Formula.neg formula)) (Formula.imp (Formula.imp (Formula.neg formula) (Formula.neg formula))
            (Formula.neg formula))) :=
    base_axiom (.case_analysis formula (Formula.neg formula)) (Formula.Admissible.imp (Formula.Admissible.imp hFormula (Formula.Admissible.neg hFormula))
        (Formula.Admissible.imp (Formula.Admissible.imp (Formula.Admissible.neg hFormula) (Formula.Admissible.neg hFormula)) (Formula.Admissible.neg hFormula)))
  exact .modus_ponens hNegativeBranch (.modus_ponens hPositiveBranch hCases)
/-- 经典反证法。 -/
theorem by_contradiction {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {formula : Formula σ} (hFormula : Formula.Admissible formula) (hFalse :
      HilbertDerives (Theory.insert (Formula.neg formula) theory) (Formula.hilbert_falsum anchorSort)) :
    HilbertDerives theory formula := by
  have hFormulaUnderNegation :
      HilbertDerives (Theory.insert (Formula.neg formula) theory)
        formula :=
    falsum_elim anchorSort hFormula hFalse
  have hReduction :
      HilbertDerives theory (Formula.imp (Formula.neg formula) formula) :=
    deduction (Formula.Admissible.neg hFormula)
      hFormulaUnderNegation
  have hClassical :
      HilbertDerives theory (Formula.imp (Formula.imp (Formula.neg formula) formula)
          formula) :=
    base_axiom (.classical formula) (Formula.Admissible.imp (Formula.Admissible.imp (Formula.Admissible.neg hFormula) hFormula)
        hFormula)
  exact .modus_ponens hReduction hClassical
/-- 两个结论可以组成 Hilbert 编码合取。 -/
theorem conj_intro {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {left right : Formula σ} (hLeft : HilbertDerives theory left)
    (hRight : HilbertDerives theory right) :
    HilbertDerives theory (Formula.hilbert_conj left right) := by
  apply neg_intro anchorSort (Formula.Admissible.imp hLeft.admissible (Formula.Admissible.neg hRight.admissible))
  have hLeft' :
      HilbertDerives (Theory.insert (Formula.imp left (Formula.neg right)) theory)
        left :=
    hLeft.theory_weakening (by
      intro formula hFormula
      exact Or.inr hFormula)
  have hRight' :
      HilbertDerives (Theory.insert (Formula.imp left (Formula.neg right)) theory)
        right :=
    hRight.theory_weakening (by
      intro formula hFormula
      exact Or.inr hFormula)
  have hImplication :
      HilbertDerives (Theory.insert (Formula.imp left (Formula.neg right)) theory) (Formula.imp left (Formula.neg right)) :=
    .theory_axiom (Or.inl rfl) (Formula.Admissible.imp hLeft.admissible (Formula.Admissible.neg hRight.admissible))
  have hNotRight :
      HilbertDerives (Theory.insert (Formula.imp left (Formula.neg right)) theory) (Formula.neg right) :=
    .modus_ponens hLeft' hImplication
  exact neg_elim (Formula.Admissible.hilbert_falsum anchorSort)
    hRight' hNotRight
/-- Hilbert 编码合取消去左侧。 -/
theorem conj_elim_left {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {left right : Formula σ} (hConjunction :
      HilbertDerives theory (Formula.hilbert_conj left right)) :
    HilbertDerives theory left := by
  have hLeftAdmissible :=
    Formula.Admissible.hilbert_conj_left
      hConjunction.admissible
  have hRightAdmissible :=
    Formula.Admissible.hilbert_conj_right
      hConjunction.admissible
  apply by_contradiction anchorSort hLeftAdmissible
  have hConjunction' :
      HilbertDerives (Theory.insert (Formula.neg left) theory) (Formula.hilbert_conj left right) :=
    hConjunction.theory_weakening (by
      intro formula hFormula
      exact Or.inr hFormula)
  have hNotLeft :
      HilbertDerives (Theory.insert (Formula.neg left) theory) (Formula.neg left) :=
    .theory_axiom (Or.inl rfl) (Formula.Admissible.neg hLeftAdmissible)
  have hExplosion :
      HilbertDerives (Theory.insert (Formula.neg left) theory) (Formula.imp (Formula.neg left) (Formula.imp left (Formula.neg right))) :=
    base_axiom (.explosion left (Formula.neg right)) (Formula.Admissible.imp (Formula.Admissible.neg hLeftAdmissible) (Formula.Admissible.imp hLeftAdmissible
          (Formula.Admissible.neg hRightAdmissible)))
  have hImplication :
      HilbertDerives (Theory.insert (Formula.neg left) theory) (Formula.imp left (Formula.neg right)) :=
    .modus_ponens hNotLeft hExplosion
  exact neg_elim (Formula.Admissible.hilbert_falsum anchorSort)
    hImplication hConjunction'
/-- Hilbert 编码合取消去右侧。 -/
theorem conj_elim_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {left right : Formula σ} (hConjunction :
      HilbertDerives theory (Formula.hilbert_conj left right)) :
    HilbertDerives theory right := by
  have hLeftAdmissible :=
    Formula.Admissible.hilbert_conj_left
      hConjunction.admissible
  have hRightAdmissible :=
    Formula.Admissible.hilbert_conj_right
      hConjunction.admissible
  apply by_contradiction anchorSort hRightAdmissible
  have hConjunction' :
      HilbertDerives (Theory.insert (Formula.neg right) theory) (Formula.hilbert_conj left right) :=
    hConjunction.theory_weakening (by
      intro formula hFormula
      exact Or.inr hFormula)
  have hNotRight :
      HilbertDerives (Theory.insert (Formula.neg right) theory) (Formula.neg right) :=
    .theory_axiom (Or.inl rfl) (Formula.Admissible.neg hRightAdmissible)
  have hImplication :
      HilbertDerives (Theory.insert (Formula.neg right) theory) (Formula.imp left (Formula.neg right)) :=
    imp_weaken left hLeftAdmissible hNotRight
  exact neg_elim (Formula.Admissible.hilbert_falsum anchorSort)
    hImplication hConjunction'
/-- 左侧结论引入 Hilbert 编码析取 `¬φ → ψ`。 -/
theorem disj_intro_left {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {left right : Formula σ} (hRightAdmissible : Formula.Admissible right) (hLeft : HilbertDerives theory left) :
    HilbertDerives theory (Formula.imp (Formula.neg left) right) := by
  have hContradiction :
      HilbertDerives theory (Formula.imp left (Formula.imp (Formula.neg left) right)) :=
    base_axiom (.contradiction left right) (Formula.Admissible.imp hLeft.admissible (Formula.Admissible.imp (Formula.Admissible.neg hLeft.admissible)
          hRightAdmissible))
  exact .modus_ponens hLeft hContradiction
/-- 右侧结论引入 Hilbert 编码析取。 -/
theorem disj_intro_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {left right : Formula σ} (hLeftAdmissible : Formula.Admissible left) (hRight : HilbertDerives theory right) :
    HilbertDerives theory (Formula.imp (Formula.neg left) right) :=
  imp_weaken (Formula.neg left) (Formula.Admissible.neg hLeftAdmissible) hRight
/-- Hilbert 编码析取的分类消去。 -/
theorem disj_elim {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {left right conclusion : Formula σ} (hDisjunction :
      HilbertDerives theory (Formula.imp (Formula.neg left) right)) (hLeft : HilbertDerives (Theory.insert left theory) conclusion)
    (hRight : HilbertDerives (Theory.insert right theory) conclusion) :
    HilbertDerives theory conclusion := by
  have hLeftAdmissible :=
    Formula.Admissible.neg_body <|
      Formula.Admissible.imp_left hDisjunction.admissible
  have hRightAdmissible :=
    Formula.Admissible.imp_right hDisjunction.admissible
  have hConclusionAdmissible := hLeft.admissible
  have hPositive :
      HilbertDerives theory (Formula.imp left conclusion) :=
    deduction hLeftAdmissible hLeft
  have hRightImp :
      HilbertDerives theory (Formula.imp right conclusion) :=
    deduction hRightAdmissible hRight
  have hNegative :
      HilbertDerives theory (Formula.imp (Formula.neg left) conclusion) :=
    imp_trans hDisjunction hRightImp
  have hCases :
      HilbertDerives theory (Formula.imp (Formula.imp left conclusion) (Formula.imp (Formula.imp (Formula.neg left) conclusion)
            conclusion)) :=
    base_axiom (.case_analysis left conclusion) (Formula.Admissible.imp (Formula.Admissible.imp hLeftAdmissible
          hConclusionAdmissible) (Formula.Admissible.imp (Formula.Admissible.imp (Formula.Admissible.neg hLeftAdmissible)
            hConclusionAdmissible)
          hConclusionAdmissible))
  exact .modus_ponens hNegative (.modus_ponens hPositive hCases)
/-- 两个方向的蕴含组成 Hilbert 编码双条件。 -/
theorem iff_intro {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {left right : Formula σ}
    (hForward : HilbertDerives (Theory.insert left theory) right) (hBackward : HilbertDerives (Theory.insert right theory) left) :
    HilbertDerives theory (Formula.hilbert_iff left right) :=
  conj_intro anchorSort (deduction hBackward.admissible hForward) (deduction hForward.admissible hBackward)
/-- Hilbert 编码双条件与右侧公式推出左侧公式。 -/
theorem iff_elim_left {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {left right : Formula σ}
    (hIff : HilbertDerives theory (Formula.hilbert_iff left right)) (hRight : HilbertDerives theory right) :
    HilbertDerives theory left :=
  .modus_ponens hRight (conj_elim_right anchorSort hIff)
/-- Hilbert 编码双条件与左侧公式推出右侧公式。 -/
theorem iff_elim_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ} (anchorSort : σ.SortSymbol) {left right : Formula σ}
    (hIff : HilbertDerives theory (Formula.hilbert_iff left right)) (hLeft : HilbertDerives theory left) :
    HilbertDerives theory right :=
  .modus_ponens hLeft (conj_elim_left anchorSort hIff)
end HilbertDerives
end FirstOrder
end Logic
end YesMetaZFC
