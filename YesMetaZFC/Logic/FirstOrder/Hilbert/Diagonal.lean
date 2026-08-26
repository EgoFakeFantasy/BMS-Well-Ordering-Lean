import YesMetaZFC.Logic.FirstOrder.Hilbert.Equality
import YesMetaZFC.Logic.FirstOrder.Admissibility
/-!
# Hilbert 对角化内核
本模块只处理对角引理中与具体 Gödel 编码无关的证明论部分。对角操作由二元关系图
表示；图在模板名称处的存在值给出固定点正向，图值唯一性给出反向。具体 quotation、
编码闭包及 substitution 图的表示性由形式系统编码层提供。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
/-! ## 关系图式对角模板 -/
/-- 二元关系图在给定源项与结果项上的实例。 -/
def hilbert_relation_instance
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (sourceId resultId : FreeVarId)
    (graph : Formula σ) (source result : Term σ) : Formula σ :=
  Formula.substituteFree sort resultId result (Formula.substituteFree sort sourceId source graph)
/--
Foundation 式关系对角模板：`x` 固定源编码，量化所有可能的图值 `y`，再把 `y`
送入目标公式。图的存在性负责正向，函数性负责反向。
-/
def hilbert_relational_diagonal_template
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (resultId : FreeVarId) (graph body : Formula σ) : Formula σ :=
  Formula.forallE sort (Formula.closeFreeAt sort resultId 0 (Formula.imp graph body))
/-- 把关系对角模板应用到表示模板自身编码值的闭项。 -/
def hilbert_relational_diagonal_fixed_point
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (sort : σ.SortSymbol) (sourceId resultId : FreeVarId) (graph : Formula σ) (selfName : Term σ)
    (body : Formula σ) : Formula σ :=
  Formula.substituteFree sort sourceId selfName (hilbert_relational_diagonal_template
      sort resultId graph body)
/--
源变量与图值变量互异、且自身名称不含图值变量时，关系固定点展开成预期的
`∀ y, graph(selfName,y) → body(y)`。
-/
theorem hilbert_relational_diagonal_fixed_point_eq
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {sort : σ.SortSymbol} {sourceId resultId : FreeVarId}
    {graph body : Formula σ} {selfName : Term σ} (hDistinct : sourceId ≠ resultId) (hSelfNameClosed : Term.BoundClosed selfName) (hSelfNameResultFresh :
      (sort, resultId) ∉ Term.freeSupport selfName) (hBodySourceFresh : (sort, sourceId) ∉ Formula.freeSupport body) :
    hilbert_relational_diagonal_fixed_point
        sort sourceId resultId graph selfName body =
      Formula.forallE sort (Formula.closeFreeAt sort resultId 0 (Formula.imp (Formula.substituteFree sort sourceId selfName graph)
            body)) := by
  unfold hilbert_relational_diagonal_fixed_point
    hilbert_relational_diagonal_template
  simp only [Formula.substituteFree]
  rw [← Formula.closeFreeAt_substituteFree_comm
    sort sourceId resultId 0 selfName (Formula.imp graph body) hDistinct
    hSelfNameClosed hSelfNameResultFresh]
  simp only [Formula.substituteFree]
  rw [Formula.substituteFree_eq_self_of_not_mem
    sort sourceId selfName body hBodySourceFresh]
namespace HilbertDerives
/-! ## 关系图式固定点 -/
/--
关系图式对角引理的纯 Hilbert 内核。
`hGraphValue` 说明图在模板自身名称处确实取到 `fixedPointCode`；`hGraphUnique`
说明同一源编码处的任意图值都等于该编码。两者分别给出固定点等价的正向与反向，
不再假设对象语言中存在一个全局对角函数项。
-/
theorem relational_diagonal_fixed_point
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {sort : σ.SortSymbol}
    {sourceId resultId : FreeVarId}
    {graph body : Formula σ}
    {selfName fixedPointCode : Term σ} (hDistinct : sourceId ≠ resultId) (hFixedPointCodeSorted : TermWellSorted fixedPointCode sort)
    (hSelfNameClosed : Term.BoundClosed selfName) (hFixedPointCodeClosed : Term.BoundClosed fixedPointCode) (hSelfNameResultFresh :
      (sort, resultId) ∉ Term.freeSupport selfName) (hFixedPointCodeResultFresh : (sort, resultId) ∉ Term.freeSupport fixedPointCode) (hBodySourceFresh :
      (sort, sourceId) ∉ Formula.freeSupport body) (hBodyAdmissible : Formula.Admissible body) (hTheoryResultFresh :
      ∀ formula, theory formula → (sort, resultId) ∉ Formula.freeSupport formula) (hGraphValue :
      HilbertDerives theory (hilbert_relation_instance
          sort sourceId resultId graph selfName fixedPointCode)) (hGraphUnique :
      HilbertDerives theory (Formula.imp (Formula.substituteFree sort sourceId selfName graph) (Formula.equal fixedPointCode
            (Term.var (.fvar sort resultId))))) :
    HilbertDerives theory (Formula.hilbert_iff (hilbert_relational_diagonal_fixed_point
          sort sourceId resultId graph selfName body) (Formula.substituteFree
          sort resultId fixedPointCode body)) := by
  let relationAtSource : Formula σ :=
    Formula.substituteFree sort sourceId selfName graph
  let targetInstance : Formula σ :=
    Formula.substituteFree sort resultId fixedPointCode body
  let fixedPoint : Formula σ :=
    hilbert_relational_diagonal_fixed_point
      sort sourceId resultId graph selfName body
  have hFixedPointNormal :
      fixedPoint =
        Formula.forallE sort (Formula.closeFreeAt sort resultId 0 (Formula.imp relationAtSource body)) := by
    exact hilbert_relational_diagonal_fixed_point_eq
      hDistinct hSelfNameClosed hSelfNameResultFresh hBodySourceFresh
  have hResultVariableSorted :
      TermWellSorted (Term.var (.fvar sort resultId)) sort :=
    .fvar sort resultId
  have hResultVariableClosed :
      Term.BoundClosed (Term.var (.fvar sort resultId)) :=
    .fvar sort resultId
  have hTargetResultFresh : (sort, resultId) ∉ Formula.freeSupport targetInstance := by
    exact Formula.target_not_mem_freeSupport_substituteFree
      sort resultId fixedPointCode body hFixedPointCodeResultFresh
  have hRelationAtSourceAdmissible :
      Formula.Admissible relationAtSource :=
    Formula.Admissible.imp_left hGraphUnique.admissible
  have hTargetInstanceAdmissible :
      Formula.Admissible targetInstance :=
    Formula.Admissible.substituteFree sort resultId
      hBodyAdmissible
      ⟨hFixedPointCodeSorted, hFixedPointCodeClosed⟩
  have hFixedPointAdmissible :
      Formula.Admissible fixedPoint := by
    rw [hFixedPointNormal]
    exact Formula.Admissible.forall_closeFreeAt sort resultId (Formula.Admissible.imp
        hRelationAtSourceAdmissible hBodyAdmissible)
  apply iff_intro sort
  · have hUniversal :
        HilbertDerives (Theory.insert fixedPoint theory) (Formula.forallE sort (Formula.closeFreeAt sort resultId 0 (Formula.imp relationAtSource body))) := by
      rw [← hFixedPointNormal]
      exact .theory_axiom (Or.inl rfl) hFixedPointAdmissible
    have hAtFixedPoint := forall_elim_m
      hFixedPointCodeSorted hFixedPointCodeClosed hUniversal
    have hImplication :
        HilbertDerives (Theory.insert fixedPoint theory) (Formula.imp (hilbert_relation_instance
              sort sourceId resultId graph selfName fixedPointCode)
            targetInstance) := by
      simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
        relationAtSource, targetInstance, hilbert_relation_instance] using
        hAtFixedPoint
    have hGraphValue' :
        HilbertDerives (Theory.insert fixedPoint theory) (hilbert_relation_instance
            sort sourceId resultId graph selfName fixedPointCode) :=
      hGraphValue.theory_weakening (fun _ hFormula => Or.inr hFormula)
    exact .modus_ponens hGraphValue' hImplication
  · let targetTheory : Theory σ := Theory.insert targetInstance theory
    have hOpenImplication :
        HilbertDerives targetTheory (Formula.imp relationAtSource body) := by
      apply deduction hRelationAtSourceAdmissible
      have hRelation :
          HilbertDerives (Theory.insert relationAtSource targetTheory)
            relationAtSource :=
        .theory_axiom (Or.inl rfl)
          hRelationAtSourceAdmissible
      have hUnique :
          HilbertDerives (Theory.insert relationAtSource targetTheory) (Formula.imp relationAtSource (Formula.equal fixedPointCode
                (Term.var (.fvar sort resultId)))) :=
        hGraphUnique.theory_weakening (by
          intro formula hFormula
          exact Or.inr (Or.inr hFormula))
      have hEquality :
          HilbertDerives (Theory.insert relationAtSource targetTheory) (Formula.equal fixedPointCode (Term.var (.fvar sort resultId))) :=
        .modus_ponens hRelation hUnique
      have hTarget :
          HilbertDerives (Theory.insert relationAtSource targetTheory)
            targetInstance :=
        .theory_axiom (Or.inr (Or.inl rfl))
          hTargetInstanceAdmissible
      have hBody := equality_elim
        hFixedPointCodeSorted hResultVariableSorted
        hFixedPointCodeClosed hResultVariableClosed
        hBodyAdmissible hEquality hTarget
      simpa only [targetInstance, Formula.substituteFree_self] using hBody
    have hTargetTheoryFresh :
        ∀ formula, targetTheory formula → (sort, resultId) ∉ Formula.freeSupport formula := by
      intro formula hFormula
      rcases hFormula with rfl | hFormula
      · exact hTargetResultFresh
      · exact hTheoryResultFresh formula hFormula
    have hUniversal := forall_closure
      sort resultId hTargetTheoryFresh hOpenImplication
    change HilbertDerives targetTheory fixedPoint
    rw [hFixedPointNormal]
    exact hUniversal
end HilbertDerives
end FirstOrder
end Logic
end YesMetaZFC
