import YesMetaZFC.Logic.FirstOrder.Hilbert.Substitution
import YesMetaZFC.Logic.FirstOrder.Admissibility
/-!
# Hilbert 等词公理的任意项实例
内部基础公理只包含变量版 Leibniz 替换。本模块选择两个 canonical 新鲜变量，先把
公式模板改名，再对变量版公理作两次全称闭包和两次特化，从而得到公共 `Derives`
等词消去所需的任意 bound-closed 项实例。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace HilbertDerives
/-- 任意两个可替换项上的 Leibniz 蕴含定理。 -/
theorem equality_substitution {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Term σ} {body : Formula σ} (hLeftTerm : TermWellSorted left sort) (hRightTerm : TermWellSorted right sort)
    (hLeftClosed : Term.BoundClosed left) (hRightClosed : Term.BoundClosed right) (hBodyAdmissible : Formula.Admissible body) :
    HilbertDerives theory (Formula.imp (Formula.equal left right) (Formula.imp (Formula.substituteFree sort eigen left body)
          (Formula.substituteFree sort eigen right body))) := by
  let eigenTerm : Term σ := Term.var (.fvar sort eigen)
  let freshnessBasis : List (Formula σ) :=
    [body, Formula.equal left left, Formula.equal right right,
      Formula.equal eigenTerm eigenTerm]
  let leftId : FreeVarId :=
    FreshVariable.fresh_id sort freshnessBasis
  let rightId : FreeVarId := leftId + 1
  let leftVariable : Term σ := Term.var (.fvar sort leftId)
  let rightVariable : Term σ := Term.var (.fvar sort rightId)
  let renamedBody : Formula σ :=
    Formula.substituteFree sort eigen leftVariable body
  let baseFormula : Formula σ :=
    Formula.imp (Formula.equal leftVariable rightVariable) (Formula.imp renamedBody (Formula.substituteFree sort leftId rightVariable renamedBody))
  have hLeftIdFreshBody : (sort, leftId) ∉ Formula.freeSupport body := by
    dsimp [leftId]
    exact FreshVariable.fresh_id_not_mem_m (formulas := freshnessBasis) (formula := body) (by simp [freshnessBasis])
  have hLeftIdFreshLeft : (sort, leftId) ∉ Term.freeSupport left := by
    have hFresh := FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := freshnessBasis) (formula := Formula.equal left left) (by simp [freshnessBasis])
    simpa [leftId, Formula.freeSupport] using hFresh
  have hLeftIdFreshRight : (sort, leftId) ∉ Term.freeSupport right := by
    have hFresh := FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := freshnessBasis) (formula := Formula.equal right right) (by simp [freshnessBasis])
    simpa [leftId, Formula.freeSupport] using hFresh
  have hRightIdFreshBody : (sort, rightId) ∉ Formula.freeSupport body := by
    intro hMember
    have hLt := FreshVariable.formulas_id_lt_m (sort := sort) (formulas := freshnessBasis) (formula := body) (by simp [freshnessBasis]) hMember
    change
      FreshVariable.formulas_bound sort freshnessBasis + 1 <
        FreshVariable.formulas_bound sort freshnessBasis at hLt
    omega
  have hRightIdFreshLeft : (sort, rightId) ∉ Term.freeSupport left := by
    intro hMember
    have hFormulaMember : (sort, rightId) ∈
          Formula.freeSupport (Formula.equal left left) := by
      simp [Formula.freeSupport, hMember]
    have hLt := FreshVariable.formulas_id_lt_m (sort := sort) (formulas := freshnessBasis) (formula := Formula.equal left left)
      (by simp [freshnessBasis]) hFormulaMember
    change
      FreshVariable.formulas_bound sort freshnessBasis + 1 <
        FreshVariable.formulas_bound sort freshnessBasis at hLt
    omega
  have hRightIdFreshRight : (sort, rightId) ∉ Term.freeSupport right := by
    intro hMember
    have hFormulaMember : (sort, rightId) ∈
          Formula.freeSupport (Formula.equal right right) := by
      simp [Formula.freeSupport, hMember]
    have hLt := FreshVariable.formulas_id_lt_m (sort := sort) (formulas := freshnessBasis) (formula := Formula.equal right right)
      (by simp [freshnessBasis]) hFormulaMember
    change
      FreshVariable.formulas_bound sort freshnessBasis + 1 <
        FreshVariable.formulas_bound sort freshnessBasis at hLt
    omega
  have hLeftIdNeRightId : leftId ≠ rightId := by
    exact Nat.ne_of_lt (by simp [rightId])
  have hRightIdNeLeftId : rightId ≠ leftId :=
    Ne.symm hLeftIdNeRightId
  have hRightIdFreshLeftVariable : (sort, rightId) ∉ Term.freeSupport leftVariable := by
    intro hMember
    have : rightId = leftId := by
      simpa [leftVariable, Term.freeSupport] using hMember
    exact hRightIdNeLeftId this
  have hLeftIdFreshRightVariable : (sort, leftId) ∉ Term.freeSupport rightVariable := by
    intro hMember
    have : leftId = rightId := by
      simpa [rightVariable, Term.freeSupport] using hMember
    exact hLeftIdNeRightId this
  have hRightIdFreshRenamedBody : (sort, rightId) ∉ Formula.freeSupport renamedBody := by
    exact Formula.not_mem_freeSupport_substituteFree (sort, rightId) sort eigen leftVariable body
      hRightIdFreshLeftVariable hRightIdFreshBody
  have hBaseAxiom : HilbertLogicalAxiom baseFormula := by
    exact .base (.equality_substitution sort leftId rightId renamedBody)
  have hLeftVariableAdmissible :
      Term.Admissible leftVariable sort :=
    ⟨TermWellSorted.fvar sort leftId,
      TermScoped.fvar sort leftId⟩
  have hRightVariableAdmissible :
      Term.Admissible rightVariable sort :=
    ⟨TermWellSorted.fvar sort rightId,
      TermScoped.fvar sort rightId⟩
  have hRenamedBodyAdmissible :
      Formula.Admissible renamedBody :=
    Formula.Admissible.substituteFree sort eigen
      hBodyAdmissible hLeftVariableAdmissible
  have hBaseFormulaAdmissible :
      Formula.Admissible baseFormula :=
    Formula.Admissible.imp
      ⟨.equal hLeftVariableAdmissible.1
          hRightVariableAdmissible.1,
        .equal hLeftVariableAdmissible.2
          hRightVariableAdmissible.2⟩ (Formula.Admissible.imp hRenamedBodyAdmissible (Formula.Admissible.substituteFree sort leftId
          hRenamedBodyAdmissible hRightVariableAdmissible))
  have hUniversal :
      HilbertDerives theory (Formula.forallE sort (Formula.closeFreeAt sort leftId 0 (Formula.forallE sort
              (Formula.closeFreeAt sort rightId 0 baseFormula)))) :=
    .logical_axiom (.forall_closure sort leftId (.forall_closure sort rightId hBaseAxiom)) (Formula.Admissible.forall_closeFreeAt sort leftId
        (Formula.Admissible.forall_closeFreeAt sort rightId
          hBaseFormulaAdmissible))
  have hLeftInstance :=
    HilbertDerives.forall_elim_m hLeftTerm hLeftClosed hUniversal
  have hFirstNormalization :
      Formula.openAt sort 0 left (Formula.closeFreeAt sort leftId 0 (Formula.forallE sort (Formula.closeFreeAt sort rightId 0 baseFormula))) =
        Formula.forallE sort (Formula.closeFreeAt sort rightId 0 (Formula.substituteFree sort leftId left baseFormula)) := by
    rw [Formula.openAt_closeFreeAt_eq_substituteFree]
    simp only [Formula.substituteFree]
    rw [← Formula.closeFreeAt_substituteFree_comm
      sort leftId rightId 0 left baseFormula
      hLeftIdNeRightId hLeftClosed hRightIdFreshLeft]
  rw [hFirstNormalization] at hLeftInstance
  have hRightInstance :=
    HilbertDerives.forall_elim_m hRightTerm hRightClosed hLeftInstance
  rw [Formula.openAt_closeFreeAt_eq_substituteFree] at hRightInstance
  have hRenamedLeft :
      Formula.substituteFree sort leftId left renamedBody =
        Formula.substituteFree sort eigen left body := by
    exact Formula.substituteFree_rename
      sort eigen leftId left body hLeftIdFreshBody
  have hRenamedRight :
      Formula.substituteFree sort leftId right renamedBody =
        Formula.substituteFree sort eigen right body := by
    exact Formula.substituteFree_rename
      sort eigen leftId right body hLeftIdFreshBody
  have hRightIdFreshLeftBody : (sort, rightId) ∉
        Formula.freeSupport (Formula.substituteFree sort eigen left body) := by
    exact Formula.not_mem_freeSupport_substituteFree (sort, rightId) sort eigen left body
      hRightIdFreshLeft hRightIdFreshBody
  have hLeftBodyFinal :
      Formula.substituteFree sort rightId right (Formula.substituteFree sort leftId left renamedBody) =
        Formula.substituteFree sort eigen left body := by
    rw [hRenamedLeft]
    exact Formula.substituteFree_eq_self_of_not_mem
      sort rightId right (Formula.substituteFree sort eigen left body)
      hRightIdFreshLeftBody
  have hLeftIdRemoved : (sort, leftId) ∉
        Formula.freeSupport (Formula.substituteFree sort leftId rightVariable renamedBody) :=
    Formula.target_not_mem_freeSupport_substituteFree
      sort leftId rightVariable renamedBody hLeftIdFreshRightVariable
  have hConsequentFinal :
      Formula.substituteFree sort rightId right (Formula.substituteFree sort leftId left (Formula.substituteFree sort leftId
              rightVariable renamedBody)) =
        Formula.substituteFree sort eigen right body := by
    rw [Formula.substituteFree_eq_self_of_not_mem
      sort leftId left (Formula.substituteFree sort leftId rightVariable renamedBody)
      hLeftIdRemoved]
    rw [Formula.substituteFree_rename
      sort leftId rightId right renamedBody
      hRightIdFreshRenamedBody]
    exact hRenamedRight
  have hEqualityFinal :
      Formula.substituteFree sort rightId right (Formula.substituteFree sort leftId left (Formula.equal leftVariable rightVariable)) =
        Formula.equal left right := by
    simp [Formula.substituteFree, Term.substituteFree,
      leftVariable, rightVariable,
      hRightIdNeLeftId,
      Term.substituteFree_eq_self_of_not_mem
        sort rightId right left hRightIdFreshLeft]
  have hBaseFinal :
      Formula.substituteFree sort rightId right (Formula.substituteFree sort leftId left baseFormula) =
        Formula.imp (Formula.equal left right) (Formula.imp (Formula.substituteFree sort eigen left body) (Formula.substituteFree sort eigen right body)) := by
    dsimp only [baseFormula]
    simp only [Formula.substituteFree] at hEqualityFinal hLeftBodyFinal hConsequentFinal ⊢
    rw [hEqualityFinal, hLeftBodyFinal, hConsequentFinal]
  rw [hBaseFinal] at hRightInstance
  exact hRightInstance
/-- Hilbert 等词消去：等式与左实例推出右实例。 -/
theorem equality_elim {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Term σ} {body : Formula σ} (hLeftTerm : TermWellSorted left sort) (hRightTerm : TermWellSorted right sort)
    (hLeftClosed : Term.BoundClosed left) (hRightClosed : Term.BoundClosed right) (hBodyAdmissible : Formula.Admissible body)
    (hEquality : HilbertDerives theory (Formula.equal left right)) (hBody :
      HilbertDerives theory (Formula.substituteFree sort eigen left body)) :
    HilbertDerives theory (Formula.substituteFree sort eigen right body) := by
  exact .modus_ponens hBody (.modus_ponens hEquality (equality_substitution
        hLeftTerm hRightTerm hLeftClosed hRightClosed
        hBodyAdmissible))
/-- 两个首尾相接的 Hilbert 等式可以传递合成。 -/
theorem equality_trans
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {sort : σ.SortSymbol}
    {left middle right : Term σ} (hMiddleTerm : TermWellSorted middle sort) (hRightTerm : TermWellSorted right sort) (hMiddleClosed : Term.BoundClosed middle)
    (hRightClosed : Term.BoundClosed right) (hLeftMiddle :
      HilbertDerives theory (Formula.equal left middle)) (hMiddleRight :
      HilbertDerives theory (Formula.equal middle right)) :
    HilbertDerives theory (Formula.equal left right) := by
  let basis : List (Formula σ) := [Formula.equal left left]
  let eigen : FreeVarId := FreshVariable.fresh_id sort basis
  let template : Formula σ :=
    Formula.equal left (Term.var (.fvar sort eigen))
  have hEigenFreshLeft : (sort, eigen) ∉ Term.freeSupport left := by
    have hFresh := FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := basis) (formula := Formula.equal left left) (by simp [basis])
    simpa [Formula.freeSupport] using hFresh
  have hMiddleInstance :
      HilbertDerives theory (Formula.substituteFree sort eigen middle template) := by
    simpa [template, Formula.substituteFree, Term.substituteFree,
      Term.substituteFree_eq_self_of_not_mem
        sort eigen middle left hEigenFreshLeft] using hLeftMiddle
  have hLeftTerm : TermWellSorted left sort := by
    cases hLeftMiddle.admissible.1 with
    | equal hLeft hMiddle =>
        have hSort := TermWellSorted.sort_unique hMiddle hMiddleTerm
        cases hSort
        exact hLeft
  have hLeftClosed : Term.BoundClosed left := by
    cases hLeftMiddle.admissible.2 with
    | equal hLeft _ =>
        exact hLeft
  have hTemplateAdmissible :
      Formula.Admissible template :=
    ⟨.equal hLeftTerm (TermWellSorted.fvar sort eigen),
      .equal hLeftClosed (TermScoped.fvar sort eigen)⟩
  have hResult := equality_elim (theory := theory) (sort := sort) (eigen := eigen) (left := middle) (right := right) (body := template)
    hMiddleTerm hRightTerm hMiddleClosed hRightClosed
    hTemplateAdmissible hMiddleRight hMiddleInstance
  simpa [template, Formula.substituteFree, Term.substituteFree,
    Term.substituteFree_eq_self_of_not_mem
      sort eigen right left hEigenFreshLeft] using hResult
/--
已证明的等式可以穿过任意项上下文。
`context` 中的自由变量 `(sourceSort, eigen)` 表示上下文的洞；左端项不再含该变量
这一条件保证构造自反性实例时不会发生二次替换。与针对某个具体函数符号逐参数证明
合同相比，这个接口可直接复用于后续所有对象编码函数。
-/
theorem equality_substitute_term_congr
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ}
    {sourceSort targetSort : σ.SortSymbol} {eigen : FreeVarId}
    {left right context : Term σ} (hLeftTerm : TermWellSorted left sourceSort) (hRightTerm : TermWellSorted right sourceSort)
    (hContextTerm : TermWellSorted context targetSort) (hLeftClosed : Term.BoundClosed left) (hRightClosed : Term.BoundClosed right)
    (hContextClosed : Term.BoundClosed context) (hLeftFresh : (sourceSort, eigen) ∉ Term.freeSupport left) (hEquality :
      HilbertDerives theory (Formula.equal left right)) :
    HilbertDerives theory (Formula.equal (Term.substituteFree sourceSort eigen left context) (Term.substituteFree sourceSort eigen right context)) := by
  let leftInstance :=
    Term.substituteFree sourceSort eigen left context
  have hLeftInstanceTerm :
      TermWellSorted leftInstance targetSort :=
    TermWellSorted.substituteFree eigen hContextTerm hLeftTerm
  have hLeftInstanceClosed : Term.BoundClosed leftInstance :=
    Term.substituteFree_scoped hContextClosed hLeftClosed
  have hLeftInstanceFresh : (sourceSort, eigen) ∉ Term.freeSupport leftInstance := by
    exact Term.target_not_mem_freeSupport_substituteFree
      sourceSort eigen left context hLeftFresh
  have hReflexive :
      HilbertDerives theory (Formula.equal leftInstance leftInstance) :=
    equality_refl leftInstance
      hLeftInstanceTerm hLeftInstanceClosed
  have hTransported := equality_elim (theory := theory) (sort := sourceSort) (eigen := eigen) (left := left) (right := right)
    (body := Formula.equal leftInstance context)
    hLeftTerm hRightTerm hLeftClosed hRightClosed
    ⟨.equal hLeftInstanceTerm hContextTerm,
      .equal hLeftInstanceClosed hContextClosed⟩
    hEquality
  have hLeftBody :
      HilbertDerives theory (Formula.substituteFree sourceSort eigen left (Formula.equal leftInstance context)) := by
    simpa [Formula.substituteFree,
      Term.substituteFree_eq_self_of_not_mem
        sourceSort eigen left leftInstance hLeftInstanceFresh,
      leftInstance] using hReflexive
  simpa [Formula.substituteFree,
    Term.substituteFree_eq_self_of_not_mem
      sourceSort eigen right leftInstance hLeftInstanceFresh,
    leftInstance] using hTransported hLeftBody
end HilbertDerives
end FirstOrder
end Logic
end YesMetaZFC
