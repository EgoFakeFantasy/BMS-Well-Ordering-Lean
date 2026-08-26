import YesMetaZFC.Logic.FirstOrder.Completeness.Henkin
/-!
# Henkin 完成理论的演绎闭包
本模块把 `Henkin.Result` 的有限一致性与逐公式完备性组合成真正的最大一致理论接口。
典范模型随后只消费这里的成员判定律，不需要重新展开公平调度或有限阶段。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin
namespace Result
universe u v w
/-- 完成候选不可能同时包含公式及其否定。 -/
theorem not_both {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {background : Background T} (result : Result background) {formula : Formula σ} (hFormula : result.candidate formula)
    (hNegated : result.candidate (Formula.neg formula)) :
    False := by
  have hFormulaAdmissible : Formula.Admissible formula :=
    result.wf.wf_candidate formula hFormula
  have hConsistent :
      Derives.Consistent T [formula, Formula.neg formula] :=
    result.wf.wf_consistent _ (by
      intro target hTarget
      rcases List.mem_cons.mp hTarget with rfl | hTarget
      · exact hFormula
      · have hNeg : target = Formula.neg formula := by
          simpa using hTarget
        subst target
        exact hNegated)
  apply hConsistent
  have hPositive :
      Derives T [formula, Formula.neg formula] formula :=
    .assumption (by simp)
  have hNegative :
      Derives T [formula, Formula.neg formula] (Formula.neg formula) :=
    .assumption (by simp)
  exact .negElim hPositive hNegative
/--
完成候选对背景理论上的有限 `Derives` 推导封闭。
该定理是语法完备性层的核心闭包接口：若结论的否定被候选选择，则它与有限推导
共同形成一个候选内的有限反证上下文。
-/
theorem contains_of_derives {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {context : Context σ} {formula : Formula σ} (hAdmissible : Formula.Admissible formula) (hDerives : Derives T context formula) (hContext :
      ∀ target, target ∈ context → result.candidate target) :
    result.candidate formula := by
  rcases result.decides formula hAdmissible with hFormula | hNegated
  · exact hFormula
  · have hConsistent :
        Derives.Consistent T (Formula.neg formula :: context) :=
      result.wf.wf_consistent _ (by
        intro target hTarget
        rcases List.mem_cons.mp hTarget with rfl | hTarget
        · exact hNegated
        · exact hContext target hTarget)
    exact False.elim <| hConsistent <|
      .negElim (.contextWeakening (by
            intro target hTarget
            simp [hTarget])
          hDerives) (.assumption (by simp))
/-- 背景理论中的每个公式都进入完成候选。 -/
theorem contains_background {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {formula : Formula σ} (hFormula : T formula) :
    result.candidate formula := by
  have hAdmissible : Formula.Admissible formula :=
    background.admissible formula hFormula
  exact result.contains_of_derives (context := [])
    hAdmissible (.theoryAxiom hFormula) (by
      intro target hTarget
      cases hTarget)
/-- 真公式属于完成候选。 -/
theorem contains_truth {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background) :
    result.candidate (Formula.truth : Formula σ) := by
  exact result.contains_of_derives Formula.Admissible.truth (context := [])
    .truthIntro (by
      intro target hTarget
      cases hTarget)
/-- 假公式不属于完成候选。 -/
theorem not_contains_falsum {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background) :
    ¬ result.candidate (Formula.falsum : Formula σ) := by
  intro hFalse
  have hConsistent : Derives.Consistent T [Formula.falsum] :=
    result.wf.wf_consistent _ (by
      intro target hTarget
      have hEq : target = Formula.falsum := by
        simpa using hTarget
      subst target
      exact hFalse)
  exact hConsistent (.assumption (by simp))
/-- 最大一致候选中的否定成员关系就是元层否定。 -/
theorem neg_mem_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {formula : Formula σ} (hAdmissible : Formula.Admissible formula) :
    result.candidate (Formula.neg formula) ↔
      ¬ result.candidate formula := by
  constructor
  · intro hNegated hFormula
    exact result.not_both hFormula hNegated
  · intro hNotFormula
    rcases result.decides formula hAdmissible with hFormula | hNegated
    · exact False.elim (hNotFormula hFormula)
    · exact hNegated
private theorem admissible_conj_parts {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {left right : Formula σ} (hFormula : Formula.Admissible (Formula.conj left right)) :
    Formula.Admissible left ∧ Formula.Admissible right := by
  rcases hFormula with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | conj hLeftWellFormed hRightWellFormed =>
      cases hScoped with
      | conj hLeftScoped hRightScoped =>
          exact
            ⟨⟨hLeftWellFormed, hLeftScoped⟩,
              ⟨hRightWellFormed, hRightScoped⟩⟩
private theorem admissible_disj_parts {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {left right : Formula σ} (hFormula : Formula.Admissible (Formula.disj left right)) :
    Formula.Admissible left ∧ Formula.Admissible right := by
  rcases hFormula with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | disj hLeftWellFormed hRightWellFormed =>
      cases hScoped with
      | disj hLeftScoped hRightScoped =>
          exact
            ⟨⟨hLeftWellFormed, hLeftScoped⟩,
              ⟨hRightWellFormed, hRightScoped⟩⟩
private theorem admissible_imp_parts {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {left right : Formula σ} (hFormula : Formula.Admissible (Formula.imp left right)) :
    Formula.Admissible left ∧ Formula.Admissible right := by
  rcases hFormula with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | imp hLeftWellFormed hRightWellFormed =>
      cases hScoped with
      | imp hLeftScoped hRightScoped =>
          exact
            ⟨⟨hLeftWellFormed, hLeftScoped⟩,
              ⟨hRightWellFormed, hRightScoped⟩⟩
private theorem admissible_iff_parts {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {left right : Formula σ} (hFormula : Formula.Admissible (Formula.iff left right)) :
    Formula.Admissible left ∧ Formula.Admissible right := by
  rcases hFormula with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | iff hLeftWellFormed hRightWellFormed =>
      cases hScoped with
      | iff hLeftScoped hRightScoped =>
          exact
            ⟨⟨hLeftWellFormed, hLeftScoped⟩,
              ⟨hRightWellFormed, hRightScoped⟩⟩
/-- 合取的候选成员关系逐分量分解。 -/
theorem conj_mem_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {left right : Formula σ} (hFormula : Formula.Admissible (Formula.conj left right)) :
    result.candidate (Formula.conj left right) ↔
      result.candidate left ∧ result.candidate right := by
  rcases admissible_conj_parts hFormula with ⟨hLeft, hRight⟩
  constructor
  · intro hConjunction
    constructor
    · exact result.contains_of_derives (context := [Formula.conj left right])
        hLeft (Derives.conjElimLeft (right := right)
          (.assumption (by simp))) (by
          intro target hTarget
          have hEq : target = Formula.conj left right := by
            simpa using hTarget
          subst target
          exact hConjunction)
    · exact result.contains_of_derives (context := [Formula.conj left right])
        hRight (Derives.conjElimRight (left := left)
          (.assumption (by simp))) (by
          intro target hTarget
          have hEq : target = Formula.conj left right := by
            simpa using hTarget
          subst target
          exact hConjunction)
  · rintro ⟨hLeftMember, hRightMember⟩
    exact result.contains_of_derives (context := [left, right])
      hFormula (.conjIntro (.assumption (by simp))
        (.assumption (by simp))) (by
        intro target hTarget
        rcases List.mem_cons.mp hTarget with rfl | hTarget
        · exact hLeftMember
        · have hEq : target = right := by
            simpa using hTarget
          subst target
          exact hRightMember)
/-- 析取的候选成员关系分解为元层析取。 -/
theorem disj_mem_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {left right : Formula σ} (hFormula : Formula.Admissible (Formula.disj left right)) :
    result.candidate (Formula.disj left right) ↔
      result.candidate left ∨ result.candidate right := by
  classical
  rcases admissible_disj_parts hFormula with ⟨hLeft, hRight⟩
  constructor
  · intro hDisjunction
    by_cases hLeftMember : result.candidate left
    · exact Or.inl hLeftMember
    · right
      by_cases hRightMember : result.candidate right
      · exact hRightMember
      · have hNegLeft :
            result.candidate (Formula.neg left) := (result.neg_mem_iff hLeft).mpr hLeftMember
        have hNegRight :
            result.candidate (Formula.neg right) := (result.neg_mem_iff hRight).mpr hRightMember
        have hConsistent :
            Derives.Consistent T
              [Formula.disj left right, Formula.neg left, Formula.neg right] :=
          result.wf.wf_consistent _ (by
            intro target hTarget
            rcases List.mem_cons.mp hTarget with rfl | hTarget
            · exact hDisjunction
            · rcases List.mem_cons.mp hTarget with rfl | hTarget
              · exact hNegLeft
              · have hEq : target = Formula.neg right := by
                  simpa using hTarget
                subst target
                exact hNegRight)
        have hFalse :
            Derives T
              [Formula.disj left right, Formula.neg left, Formula.neg right]
              Formula.falsum :=
          Derives.disjElim (left := left) (right := right)
            (.assumption (by simp))
            (Derives.negElim (body := left)
              (.assumption (by simp)) (.assumption (by simp)))
            (Derives.negElim (body := right)
              (.assumption (by simp)) (.assumption (by simp)))
        exact False.elim (hConsistent hFalse)
  · intro hMember
    rcases hMember with hLeftMember | hRightMember
    · exact result.contains_of_derives (context := [left]) hFormula
        (.disjIntroLeft (.assumption (by simp))) (by
          intro target hTarget
          have hEq : target = left := by
            simpa using hTarget
          subst target
          exact hLeftMember)
    · exact result.contains_of_derives (context := [right]) hFormula
        (.disjIntroRight (.assumption (by simp))) (by
          intro target hTarget
          have hEq : target = right := by
            simpa using hTarget
          subst target
          exact hRightMember)
/-- 蕴含的候选成员关系就是候选成员间的元层函数。 -/
theorem imp_mem_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {left right : Formula σ} (hFormula : Formula.Admissible (Formula.imp left right)) :
    result.candidate (Formula.imp left right) ↔ (result.candidate left → result.candidate right) := by
  rcases admissible_imp_parts hFormula with ⟨hLeft, hRight⟩
  constructor
  · intro hImplication hLeftMember
    exact result.contains_of_derives
      (context := [Formula.imp left right, left]) hRight
      (Derives.impElim (antecedent := left)
        (.assumption (by simp)) (.assumption (by simp))) (by
        intro target hTarget
        rcases List.mem_cons.mp hTarget with rfl | hTarget
        · exact hImplication
        · have hEq : target = left := by
            simpa using hTarget
          subst target
          exact hLeftMember)
  · intro hSemantic
    rcases result.decides left hLeft with hLeftMember | hNegLeft
    · have hRightMember := hSemantic hLeftMember
      exact result.contains_of_derives (context := [right]) hFormula
        (.impIntro (.assumption (by simp))) (by
          intro target hTarget
          have hEq : target = right := by
            simpa using hTarget
          subst target
          exact hRightMember)
    · exact result.contains_of_derives (context := [Formula.neg left])
        hFormula (.impIntro (.falsumElim
          (Derives.negElim (body := left)
            (.assumption (by simp)) (.assumption (by simp))))) (by
          intro target hTarget
          have hEq : target = Formula.neg left := by
            simpa using hTarget
          subst target
          exact hNegLeft)
/-- 等价的候选成员关系就是两侧成员关系的元层等价。 -/
theorem iff_mem_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {left right : Formula σ} (hFormula : Formula.Admissible (Formula.iff left right)) :
    result.candidate (Formula.iff left right) ↔ (result.candidate left ↔ result.candidate right) := by
  rcases admissible_iff_parts hFormula with ⟨hLeft, hRight⟩
  constructor
  · intro hEquivalence
    constructor
    · intro hLeftMember
      exact result.contains_of_derives (context := [Formula.iff left right, left]) hRight (Derives.iffElimRight (left := left) (right := right)
          (.assumption (by simp)) (.assumption (by simp))) (by
          intro target hTarget
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hEquivalence
          · have hEq : target = left := by
              simpa using hTarget
            subst target
            exact hLeftMember)
    · intro hRightMember
      exact result.contains_of_derives (context := [Formula.iff left right, right]) hLeft (Derives.iffElimLeft (left := left) (right := right)
          (.assumption (by simp)) (.assumption (by simp))) (by
          intro target hTarget
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hEquivalence
          · have hEq : target = right := by
              simpa using hTarget
            subst target
            exact hRightMember)
  · intro hSemantic
    rcases result.decides left hLeft with hLeftMember | hNegLeft
    · have hRightMember := hSemantic.mp hLeftMember
      exact result.contains_of_derives (context := [left, right])
        hFormula (.iffIntro (.assumption (by simp))
          (.assumption (by simp))) (by
          intro target hTarget
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hLeftMember
          · have hEq : target = right := by
              simpa using hTarget
            subst target
            exact hRightMember)
    · have hNotRight :
          ¬ result.candidate right := by
        intro hRightMember
        exact result.not_both (hSemantic.mpr hRightMember) hNegLeft
      have hNegRight :
          result.candidate (Formula.neg right) := (result.neg_mem_iff hRight).mpr hNotRight
      exact result.contains_of_derives
        (context := [Formula.neg left, Formula.neg right]) hFormula
        (.iffIntro
          (.falsumElim (Derives.negElim (body := left)
            (.assumption (by simp)) (.assumption (by simp))))
          (.falsumElim (Derives.negElim (body := right)
            (.assumption (by simp)) (.assumption (by simp))))) (by
          intro target hTarget
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hNegLeft
          · have hEq : target = Formula.neg right := by
              simpa using hTarget
            subst target
            exact hNegRight)
private theorem admissible_equal {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {sort : σ.SortSymbol}
    {left right : Term σ} (hLeft : Term.Admissible left sort) (hRight : Term.Admissible right sort) :
    Formula.Admissible (Formula.equal left right) :=
  ⟨.equal hLeft.1 hRight.1, .equal hLeft.2 hRight.2⟩
/-- 任意 admissible 闭项与自身的等词属于完成候选。 -/
theorem equal_mem_refl {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {sort : σ.SortSymbol} {term : Term σ} (hTerm : Term.Admissible term sort) :
    result.candidate (Formula.equal term term) := by
  exact result.contains_of_derives (context := [])
    (admissible_equal hTerm hTerm) (Derives.equalityRefl sort) (by
      intro target hTarget
      cases hTarget)
/-- 完成候选对核心 Leibniz 等词替换规则封闭。 -/
theorem substitute_mem_of_equal_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {background : Background T} (result : Result background)
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Term σ} {body : Formula σ} (hLeft : Term.Admissible left sort) (hRight : Term.Admissible right sort) (hBody : Formula.Admissible body)
    (hTarget :
      Formula.Admissible (Formula.substituteFree sort eigen right body)) (hEquality : result.candidate (Formula.equal left right)) (hSource :
      result.candidate (Formula.substituteFree sort eigen left body)) :
    result.candidate (Formula.substituteFree sort eigen right body) := by
  have hEqualityAdmissible :
      Formula.Admissible (Formula.equal left right) :=
    admissible_equal hLeft hRight
  have hSourceAdmissible :
      Formula.Admissible (Formula.substituteFree sort eigen left body) :=
    Formula.Admissible.substituteFree sort eigen hBody hLeft
  exact result.contains_of_derives (context := [
      Formula.equal left right,
      Formula.substituteFree sort eigen left body])
    hTarget (Derives.equalityElim (sort := sort) (eigen := eigen)
      (left := left) (right := right)
      (.assumption (by simp)) (.assumption (by simp))) (by
      intro target hMember
      rcases List.mem_cons.mp hMember with rfl | hMember
      · exact hEquality
      · have hEq :
            target = Formula.substituteFree sort eigen left body := by
          simpa using hMember
        subst target
        exact hSource)
/-- 完成候选中的等词成员关系具有对称性。 -/
theorem equal_mem_symm {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {sort : σ.SortSymbol} {left right : Term σ} (hLeft : Term.Admissible left sort) (hRight : Term.Admissible right sort)
    (hEquality : result.candidate (Formula.equal left right)) :
    result.candidate (Formula.equal right left) := by
  let equality := Formula.equal left right
  let eigen := FreshVariable.fresh_id sort [equality]
  let placeholder : Term σ := Term.var (.fvar sort eigen)
  let body := Formula.equal placeholder left
  have hPlaceholder : Term.Admissible placeholder sort :=
    ⟨TermWellSorted.fvar sort eigen, TermScoped.fvar sort eigen⟩
  have hBody : Formula.Admissible body := by
    exact admissible_equal hPlaceholder hLeft
  have hFreshEquality : (sort, eigen) ∉ Formula.freeSupport equality := by
    exact FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := [equality]) (formula := equality) (by simp)
  have hFreshLeft : (sort, eigen) ∉ Term.freeSupport left := by
    intro hMember
    exact hFreshEquality (by
      simp [equality, Formula.freeSupport, hMember])
  have hLeftFixed :
      Term.substituteFree sort eigen left left = left :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen left left hFreshLeft
  have hRightFixed :
      Term.substituteFree sort eigen right left = left :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen right left hFreshLeft
  have hSource :
      result.candidate (Formula.substituteFree sort eigen left body) := by
    simpa [body, placeholder, Formula.substituteFree,
      Term.substituteFree, hLeftFixed] using
      result.equal_mem_refl hLeft
  have hTarget :
      Formula.Admissible (Formula.substituteFree sort eigen right body) := by
    simpa [body, placeholder, Formula.substituteFree,
      Term.substituteFree, hRightFixed] using
      admissible_equal hRight hLeft
  have hSubstituted :=
    result.substitute_mem_of_equal_mem (sort := sort) (eigen := eigen) (left := left) (right := right) (body := body)
      hLeft hRight hBody hTarget hEquality hSource
  simpa [body, placeholder, Formula.substituteFree,
    Term.substituteFree, hRightFixed] using hSubstituted
/-- 完成候选中的等词成员关系具有传递性。 -/
theorem equal_mem_trans {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {sort : σ.SortSymbol} {left middle right : Term σ} (hLeft : Term.Admissible left sort) (hMiddle : Term.Admissible middle sort)
    (hRight : Term.Admissible right sort) (hLeftMiddle : result.candidate (Formula.equal left middle))
    (hMiddleRight : result.candidate (Formula.equal middle right)) :
    result.candidate (Formula.equal left right) := by
  let equality := Formula.equal left middle
  let eigen := FreshVariable.fresh_id sort [equality]
  let placeholder : Term σ := Term.var (.fvar sort eigen)
  let body := Formula.equal left placeholder
  have hPlaceholder : Term.Admissible placeholder sort :=
    ⟨TermWellSorted.fvar sort eigen, TermScoped.fvar sort eigen⟩
  have hBody : Formula.Admissible body := by
    exact admissible_equal hLeft hPlaceholder
  have hFreshEquality : (sort, eigen) ∉ Formula.freeSupport equality := by
    exact FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := [equality]) (formula := equality) (by simp)
  have hFreshLeft : (sort, eigen) ∉ Term.freeSupport left := by
    intro hMember
    exact hFreshEquality (by
      simp [equality, Formula.freeSupport, hMember])
  have hLeftFixedMiddle :
      Term.substituteFree sort eigen middle left = left :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen middle left hFreshLeft
  have hLeftFixedRight :
      Term.substituteFree sort eigen right left = left :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen right left hFreshLeft
  have hSource :
      result.candidate (Formula.substituteFree sort eigen middle body) := by
    simpa [body, placeholder, Formula.substituteFree,
      Term.substituteFree, hLeftFixedMiddle] using hLeftMiddle
  have hTarget :
      Formula.Admissible (Formula.substituteFree sort eigen right body) := by
    simpa [body, placeholder, Formula.substituteFree,
      Term.substituteFree, hLeftFixedRight] using
      admissible_equal hLeft hRight
  have hSubstituted :=
    result.substitute_mem_of_equal_mem (sort := sort) (eigen := eigen) (left := middle) (right := right) (body := body)
      hMiddle hRight hBody hTarget hMiddleRight hSource
  simpa [body, placeholder, Formula.substituteFree,
    Term.substituteFree, hLeftFixedRight] using hSubstituted
private theorem admissible_exists_neg_of_forall
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {sort : σ.SortSymbol} {body : Formula σ} (hFormula : Formula.Admissible (Formula.forallE sort body)) :
    Formula.Admissible (Formula.existsE sort (Formula.neg body)) := by
  rcases hFormula with ⟨hWellFormed, hScoped⟩
  cases hWellFormed with
  | forallE _ hBodyWellFormed =>
      cases hScoped with
      | forallE _ hBodyScoped =>
          exact
            ⟨.existsE sort (.neg hBodyWellFormed),
              .existsE sort (.neg hBodyScoped)⟩
/--
完成候选含有某个全称式的否定时，也含有其否定体的存在式。
证明完全留在 `Derives` 内：为否定体的存在式做反证，选择对待证公式新鲜的
eigenvariable，由 `∀` 引入恢复原全称式，再与候选中的否定冲突。
-/
theorem neg_forall_mem_imp_exists_neg_mem
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {background : Background T} (result : Result background) {sort : σ.SortSymbol} {body : Formula σ}
    (hFormula : Formula.Admissible (Formula.forallE sort body)) (hNegForall :
      result.candidate (Formula.neg (Formula.forallE sort body))) :
    result.candidate (Formula.existsE sort (Formula.neg body)) := by
  let universal := Formula.forallE sort body
  let counterexample := Formula.existsE sort (Formula.neg body)
  let eigen := FreshVariable.fresh_id sort [universal, counterexample]
  let witness : Term σ := Term.var (.fvar sort eigen)
  let opened := Formula.openAt sort 0 witness body
  have hEigenUniversal : (sort, eigen) ∉ Formula.freeSupport universal := by
    exact FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := [universal, counterexample]) (formula := universal) (by simp)
  have hEigenCounterexample : (sort, eigen) ∉ Formula.freeSupport counterexample := by
    exact FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := [universal, counterexample]) (formula := counterexample) (by simp)
  have hEigenBody : (sort, eigen) ∉ Formula.freeSupport body := by
    simpa [universal, Formula.freeSupport] using hEigenUniversal
  have hWitness : Term.Admissible witness sort := by
    exact
      ⟨TermWellSorted.fvar sort eigen,
        TermScoped.fvar sort eigen⟩
  have hCounterexampleAdmissible :
      Formula.Admissible counterexample := by
    simpa [counterexample] using
      admissible_exists_neg_of_forall hFormula
  have hOpenedAdmissible : Formula.Admissible opened := by
    simpa [opened, witness] using
      Formula.Admissible.forall_openAt sort hFormula hWitness
  have hDerivesCounterexample :
      Derives T [Formula.neg universal] counterexample := by
    nd_apply Derives.byContradiction
    have hOpened :
        Derives T
          [Formula.neg counterexample, Formula.neg universal] opened := by
      nd_apply Derives.byContradiction
      have hNegOpened :
          Derives T
            [Formula.neg opened, Formula.neg counterexample,
              Formula.neg universal] (Formula.neg opened) :=
        .assumption (by simp)
      have hCounterexample :
          Derives T
            [Formula.neg opened, Formula.neg counterexample,
              Formula.neg universal]
            counterexample := by
        exact Derives.existsIntro <| by
          simpa [counterexample, opened, witness, Formula.openAt] using
            hNegOpened
      have hNegCounterexample :
          Derives T
            [Formula.neg opened, Formula.neg counterexample,
              Formula.neg universal] (Formula.neg counterexample) :=
        .assumption (by simp)
      exact Derives.negElim (body := counterexample) hCounterexample hNegCounterexample
    have hContextFresh :
        ∀ formula,
          formula ∈ [Formula.neg counterexample, Formula.neg universal] → (sort, eigen) ∉ Formula.freeSupport formula := by
      intro formula hMember
      rcases List.mem_cons.mp hMember with rfl | hMember
      · simpa [Formula.freeSupport] using hEigenCounterexample
      · have hEq : formula = Formula.neg universal := by
          simpa using hMember
        subst formula
        simpa [Formula.freeSupport] using hEigenUniversal
    have hUniversalClosed :
        Derives T
          [Formula.neg counterexample, Formula.neg universal] (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 opened)) :=
      Derives.forallIntro (by
          intro formula hTheory
          exact background.free_fresh hTheory)
        hContextFresh hOpened
    have hUniversal :
        Derives T
          [Formula.neg counterexample, Formula.neg universal]
          universal := by
      simpa [universal, opened, witness,
        Formula.closeFreeAt_openAt sort eigen 0 body hEigenBody] using
        hUniversalClosed
    have hNegUniversal :
        Derives T
          [Formula.neg counterexample, Formula.neg universal] (Formula.neg universal) :=
      .assumption (by simp)
    exact Derives.negElim (body := universal) hUniversal hNegUniversal
  exact result.contains_of_derives (context := [Formula.neg universal])
    hCounterexampleAdmissible hDerivesCounterexample (by
      intro target hTarget
      have hEq : target = Formula.neg universal := by
        simpa using hTarget
      subst target
      simpa [universal] using hNegForall)
/-- 存在量词属于完成候选，当且仅当某个 admissible 闭项实例属于候选。 -/
theorem exists_mem_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {sort : σ.SortSymbol} {body : Formula σ} (hFormula : Formula.Admissible (Formula.existsE sort body)) :
    result.candidate (Formula.existsE sort body) ↔
      ∃ term, Term.Admissible term sort ∧
        result.candidate (Formula.openAt sort 0 term body) := by
  constructor
  · intro hExists
    rcases result.witnessed sort body hExists with ⟨eigen, hWitness⟩
    exact
      ⟨Term.var (.fvar sort eigen),
        ⟨TermWellSorted.fvar sort eigen, TermScoped.fvar sort eigen⟩,
        hWitness⟩
  · rintro ⟨term, hTerm, hInstance⟩
    have hInstanceAdmissible :
        Formula.Admissible (Formula.openAt sort 0 term body) :=
      Formula.Admissible.exists_openAt sort hFormula hTerm
    exact result.contains_of_derives (context := [Formula.openAt sort 0 term body])
      hFormula (Derives.existsIntro (term := term)
        (.assumption (by simp))) (by
        intro target hTarget
        have hEq : target = Formula.openAt sort 0 term body := by
          simpa using hTarget
        subst target
        exact hInstance)
/-- 全称量词属于完成候选，当且仅当每个 admissible 闭项实例都属于候选。 -/
theorem forall_mem_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (result : Result background)
    {sort : σ.SortSymbol} {body : Formula σ} (hFormula : Formula.Admissible (Formula.forallE sort body)) :
    result.candidate (Formula.forallE sort body) ↔
      ∀ term, Term.Admissible term sort →
        result.candidate (Formula.openAt sort 0 term body) := by
  constructor
  · intro hForall term hTerm
    have hInstanceAdmissible :
        Formula.Admissible (Formula.openAt sort 0 term body) :=
      Formula.Admissible.forall_openAt sort hFormula hTerm
    exact result.contains_of_derives (context := [Formula.forallE sort body])
      hInstanceAdmissible (Derives.forallElim (.assumption (by simp))) (by
        intro target hTarget
        have hEq : target = Formula.forallE sort body := by
          simpa using hTarget
        subst target
        exact hForall)
  · intro hInstances
    rcases result.decides (Formula.forallE sort body) hFormula with
      hForall | hNegForall
    · exact hForall
    · have hExistsNeg :
          result.candidate (Formula.existsE sort (Formula.neg body)) :=
        result.neg_forall_mem_imp_exists_neg_mem hFormula hNegForall
      rcases result.witnessed sort (Formula.neg body) hExistsNeg with
        ⟨eigen, hNegInstance⟩
      let term : Term σ := Term.var (.fvar sort eigen)
      have hTerm : Term.Admissible term sort := by
        exact
          ⟨TermWellSorted.fvar sort eigen,
            TermScoped.fvar sort eigen⟩
      have hInstance :=
        hInstances term hTerm
      have hNegInstance' :
          result.candidate (Formula.neg (Formula.openAt sort 0 term body)) := by
        simpa [term, Formula.openAt] using hNegInstance
      exact False.elim (result.not_both hInstance hNegInstance')
end Result
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
