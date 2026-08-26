import YesMetaZFC.Logic.FirstOrder.Metatheory.Equality
import YesMetaZFC.Logic.FirstOrder.Metatheory.Propositional
import YesMetaZFC.Logic.FirstOrder.Metatheory.Quantifier.Closure
import YesMetaZFC.Logic.FirstOrder.Admissibility.Args
/-!
# 基本等词定理
本模块以任意良构、bound-closed 项为主接口，而不把文献中的 `v₁`、`v₂`、`v₃`
实例化步骤固化为 API。等式的对称性、传递性与公式合同均从可信核的自反性和
Leibniz 替换导出；命题层的蕴含与双向包装交给 `derive_prop` 回放。
`equality_substitution_iff` 对任意公式模板成立，因此严格涵盖等式在任意关系参数、
量词体和复合公式中的替换。文献针对集合隶属关系逐条列出的九个公式，都是该定理
与 `Formula.forall_close` 的直接实例。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
universe u v w
namespace Derives
/-- 任意通过计算检查的项都等于自身。 -/
theorem equality_refl {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    (term : Term σ)
    (sort : σ.SortSymbol := Term.inferredSort term)
    (hTermCheck : Term.CheckCertificate term sort := by
      prove_term_check) :
    Γ ⊢ₘ[T] term ≐ₘ term :=
  FirstOrder.Derives.eq_refl_m term
    (sort := sort) (hTermCheck := hTermCheck)
/-- 已证明的等式可以交换两端。 -/
theorem equality_symm {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {left right : Term σ} (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] right ≐ₘ left := by
  let sort := Term.inferredSort left
  have hEqualityCheck :=
    Formula.CheckCertificate.equal_iff.mp
      hEquality.formula_checked
  let eigen :=
    FreshVariable.fresh_id sort [left ≐ₘ left]
  have hLeftFresh : (sort, eigen) ∉ Term.freeSupport left := by
    dsimp [eigen]
    exact FreshVariable.fresh_term_not_mem_m sort left
  have hSourceFixed :
      Term.substituteFree sort eigen left left = left :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen left left hLeftFresh
  have hTargetFixed :
      Term.substituteFree sort eigen right left = left :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen right left hLeftFresh
  have hReflexiveInstance :
      Γ ⊢ₘ[T] (v#[sort, eigen] ≐ₘ left)⟪sort, eigen ↦ left⟫ₘ := by
    simpa [Formula.substituteFree, Term.substituteFree,
      hSourceFixed] using
      (equality_refl (T := T) (Γ := Γ) left
        (hTermCheck := hEqualityCheck.1))
  have hSubstitute :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := sort) (eigen := eigen) (left := left) (right := right) (body := v#[sort, eigen] ≐ₘ left)
      hEquality hReflexiveInstance
      (hLeftCheck := hEqualityCheck.1)
      (hRightCheck := hEqualityCheck.2)
  simpa [Formula.substituteFree, Term.substituteFree,
    hSourceFixed, hTargetFixed] using hSubstitute

/-- 等式对称性的蕴含形式。 -/
theorem equality_symm_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {left right : Term σ}
    (sort : σ.SortSymbol := Term.inferredSort left)
    (hLeftCheck : Term.CheckCertificate left sort := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right sort := by
      prove_term_check) :
    Γ ⊢ₘ[T] (left ≐ₘ right) ⟶ₘ (right ≐ₘ left) := by
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.CheckCertificate.equal hLeftCheck hRightCheck)
  have hEquality :
      (left ≐ₘ right) :: Γ ⊢ₘ[T] left ≐ₘ right :=
    .assumption (by simp)
      (Formula.CheckCertificate.equal hLeftCheck hRightCheck)
  exact equality_symm hEquality
/-- 两个首尾相接的等式可以传递合成。 -/
theorem equality_trans {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {left middle right : Term σ}
    (hLeftMiddle : Γ ⊢ₘ[T] left ≐ₘ middle)
    (hMiddleRight : Γ ⊢ₘ[T] middle ≐ₘ right) :
    Γ ⊢ₘ[T] left ≐ₘ right := by
  let sort := Term.inferredSort middle
  have hMiddleRightCheck :=
    Formula.CheckCertificate.equal_iff.mp
      hMiddleRight.formula_checked
  let eigen :=
    FreshVariable.fresh_id sort [left ≐ₘ left]
  have hLeftFresh : (sort, eigen) ∉ Term.freeSupport left := by
    dsimp [eigen]
    exact FreshVariable.fresh_term_not_mem_m sort left
  have hSourceFixed :
      Term.substituteFree sort eigen middle left = left :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen middle left hLeftFresh
  have hTargetFixed :
      Term.substituteFree sort eigen right left = left :=
    Term.substituteFree_eq_self_of_not_mem
      sort eigen right left hLeftFresh
  have hLeftMiddleInstance :
      Γ ⊢ₘ[T] (left ≐ₘ v#[sort, eigen])⟪sort, eigen ↦ middle⟫ₘ := by
    simpa [Formula.substituteFree, Term.substituteFree,
      hSourceFixed] using hLeftMiddle
  have hSubstitute :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := sort) (eigen := eigen) (left := middle) (right := right) (body := left ≐ₘ v#[sort, eigen])
      hMiddleRight hLeftMiddleInstance
      (hLeftCheck := hMiddleRightCheck.1)
      (hRightCheck := hMiddleRightCheck.2)
  simpa [Formula.substituteFree, Term.substituteFree,
    hSourceFixed, hTargetFixed] using hSubstitute

/--
两端分别相等时，对应的两个等式公式逻辑等价。证明只使用等式的对称与传递，不再
引入额外公式模板。
-/
theorem equality_iff_of_equalities
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol}
    {left₁ left₂ right₁ right₂ : Term σ}
    (hLeft₁ : Term.Admissible left₁ sort)
    (hLeft₂ : Term.Admissible left₂ sort)
    (hRight₁ : Term.Admissible right₁ sort)
    (hRight₂ : Term.Admissible right₂ sort)
    (hLeft : Γ ⊢ₘ[T] left₁ ≐ₘ left₂)
    (hRight : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      (left₁ ≐ₘ right₁) ↔ₘ
        (left₂ ≐ₘ right₂) := by
  have hLeft₁Check :=
    Term.check_certificate_of_admissible hLeft₁
  have hLeft₂Check :=
    Term.check_certificate_of_admissible hLeft₂
  have hRight₁Check :=
    Term.check_certificate_of_admissible hRight₁
  have hRight₂Check :=
    Term.check_certificate_of_admissible hRight₂
  apply FirstOrder.Derives.iffIntro
  · have hSource :
        (left₁ ≐ₘ right₁) :: Γ
          ⊢ₘ[T] left₁ ≐ₘ right₁ :=
      .assumption (by simp)
        (Formula.CheckCertificate.equal
          hLeft₁Check hRight₁Check)
    have hLeft' :=
      equality_symm
        (hLeft.context_weaken_cons
          (assumption :=
            Formula.equal left₁ right₁))
    have hMiddle :=
      equality_trans hLeft' hSource
    exact equality_trans hMiddle
      (hRight.context_weaken_cons
        (assumption :=
          Formula.equal left₁ right₁))
  · have hTarget :
        (left₂ ≐ₘ right₂) :: Γ
          ⊢ₘ[T] left₂ ≐ₘ right₂ :=
      .assumption (by simp)
        (Formula.CheckCertificate.equal
          hLeft₂Check hRight₂Check)
    have hMiddle :=
      equality_trans
        (hLeft.context_weaken_cons
          (assumption :=
            Formula.equal left₂ right₂))
        hTarget
    exact equality_trans hMiddle <|
      equality_symm
        (hRight.context_weaken_cons
          (assumption :=
            Formula.equal left₂ right₂))

/--
两项分别等于同一中间项时可直接汇合。
第二条等式的对称与传递都从已检查推导自身恢复合法性。
-/
theorem equality_join {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {left middle right : Term σ}
    (hLeftMiddle : Γ ⊢ₘ[T] left ≐ₘ middle)
    (hRightMiddle : Γ ⊢ₘ[T] right ≐ₘ middle) :
    Γ ⊢ₘ[T] left ≐ₘ right :=
  equality_trans hLeftMiddle (equality_symm hRightMiddle)

/-- 等式传递性的嵌套蕴含形式。 -/
theorem equality_trans_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {left middle right : Term σ}
    (sort : σ.SortSymbol := Term.inferredSort left)
    (hLeftCheck : Term.CheckCertificate left sort := by
      prove_term_check)
    (hMiddleCheck : Term.CheckCertificate middle sort := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right sort := by
      prove_term_check) :
    Γ ⊢ₘ[T] (left ≐ₘ middle) ⟶ₘ ((middle ≐ₘ right) ⟶ₘ (left ≐ₘ right)) := by
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.CheckCertificate.equal hLeftCheck hMiddleCheck)
  apply FirstOrder.Derives.impIntro
    (hAntecedentCheck :=
      Formula.CheckCertificate.equal hMiddleCheck hRightCheck)
  have hLeftMiddle :
      (middle ≐ₘ right) :: (left ≐ₘ middle) :: Γ
        ⊢ₘ[T] left ≐ₘ middle :=
    .assumption (by simp)
      (Formula.CheckCertificate.equal hLeftCheck hMiddleCheck)
  have hMiddleRight :
      (middle ≐ₘ right) :: (left ≐ₘ middle) :: Γ
        ⊢ₘ[T] middle ≐ₘ right :=
    .assumption (by simp)
      (Formula.CheckCertificate.equal hMiddleCheck hRightCheck)
  exact equality_trans hLeftMiddle hMiddleRight
/--
相等项在任意公式模板中的实例逻辑等价。
命题组合由 `derive_prop` 完成；等式方向本身仍只来自已检查的 Leibniz 替换。
-/
theorem equality_substitution_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Term σ} {body : Formula σ}
    (hLeftCheck : Term.CheckCertificate left sort := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right sort := by
      prove_term_check)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Γ ⊢ₘ[T] (left ≐ₘ right) ⟶ₘ ((body⟪sort, eigen ↦ left⟫ₘ) ↔ₘ
          body⟪sort, eigen ↦ right⟫ₘ) := by
  have hForward :=
    equality_substitution (T := T) (Γ := Γ)
      (sort := sort) (eigen := eigen)
      (left := left) (right := right) (body := body)
      (hLeftCheck := hLeftCheck)
      (hRightCheck := hRightCheck)
      (hBodyCheck := hBodyCheck)
  have hSymmetry :=
    equality_symm_imp (T := T) (Γ := Γ)
      (sort := sort)
      (hLeftCheck := hLeftCheck)
      (hRightCheck := hRightCheck)
  have hBackward :=
    equality_substitution (T := T) (Γ := Γ)
      (sort := sort) (eigen := eigen)
      (left := right) (right := left) (body := body)
      (hLeftCheck := hRightCheck)
      (hRightCheck := hLeftCheck)
      (hBodyCheck := hBodyCheck)
  have hCombine :
      Γ ⊢ₘ[T] ((left ≐ₘ right) ⟶ₘ ((body⟪sort, eigen ↦ left⟫ₘ) ⟶ₘ
            body⟪sort, eigen ↦ right⟫ₘ)) ⟶ₘ (((left ≐ₘ right) ⟶ₘ (right ≐ₘ left)) ⟶ₘ (((right ≐ₘ left) ⟶ₘ ((body⟪sort, eigen ↦ right⟫ₘ) ⟶ₘ
                body⟪sort, eigen ↦ left⟫ₘ)) ⟶ₘ ((left ≐ₘ right) ⟶ₘ ((body⟪sort, eigen ↦ left⟫ₘ) ↔ₘ
                  body⟪sort, eigen ↦ right⟫ₘ)))) := by
    derive_prop
  exact .impElim (.impElim (.impElim hCombine hForward)
      hSymmetry)
    hBackward
/-- 已证明的等式把公式模板的两个实例提升为逻辑等价。 -/
theorem equality_iff_of_equality {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Term σ} {body : Formula σ}
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right)
    (hLeftCheck : Term.CheckCertificate left sort := by
      prove_term_check)
    (hRightCheck : Term.CheckCertificate right sort := by
      prove_term_check)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Γ ⊢ₘ[T] (body⟪sort, eigen ↦ left⟫ₘ) ↔ₘ
        body⟪sort, eigen ↦ right⟫ₘ := by
  have hCongruence :=
    equality_substitution_iff (T := T) (Γ := Γ)
      (sort := sort) (eigen := eigen)
      (left := left) (right := right) (body := body)
      (hLeftCheck := hLeftCheck)
      (hRightCheck := hRightCheck)
      (hBodyCheck := hBodyCheck)
  exact .impElim hCongruence hEquality
/--
已证明等式可穿过任意 admissible 项上下文。
`context` 中编号为 `parameter` 的自由变量是上下文孔；结论比较分别填入 `left`、
`right` 后得到的两个对象项。`hLeftFresh` 保证左实例不重新暴露该孔，从而可直接
调用可信核的 Leibniz 替换规则。
-/
theorem term_substituteFree_congr_of_equality
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    (sort : σ.SortSymbol) (parameter : FreeVarId)
    (left right context : Term σ)
    {contextSort : σ.SortSymbol}
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort)
    (hContext : Term.Admissible context contextSort)
    (hLeftFresh : (sort, parameter) ∉ Term.freeSupport left) (hEquality :
      Γ ⊢ₘ[T] Formula.equal left right) :
    Γ ⊢ₘ[T]
      Formula.equal (Term.substituteFree sort parameter left context) (Term.substituteFree sort parameter right context) := by
  let leftInstance :=
    Term.substituteFree sort parameter left context
  have hLeftInstance :
      Term.Admissible leftInstance contextSort :=
    ⟨TermWellSorted.substituteFree
        parameter hContext.1 hLeft.1,
      Term.substituteFree_scoped
        hContext.2 hLeft.2⟩
  have hLeftInstanceFresh : (sort, parameter) ∉
        Term.freeSupport leftInstance := by
    dsimp [leftInstance]
    refine Term.rec (motive_1 := fun term =>
        (sort, parameter) ∉
          Term.freeSupport (Term.substituteFree
              sort parameter left term)) (motive_2 := fun terms =>
        (sort, parameter) ∉
          Term.freeSupportList (terms.map (Term.substituteFree
                sort parameter left)))
      ?_ ?_ ?_ ?_ context
    · intro sourceVar
      cases sourceVar with
      | bvar sourceSort index =>
          simp [Term.substituteFree, Term.freeSupport]
      | fvar sourceSort sourceId =>
          by_cases hSort : sourceSort = sort
          · subst sourceSort
            by_cases hId : sourceId = parameter
            · subst sourceId
              simp [Term.substituteFree, hLeftFresh]
            · have hId' : parameter ≠ sourceId :=
                Ne.symm hId
              simp [Term.substituteFree,
                Term.freeSupport, hId, hId']
          · have hSort' : sort ≠ sourceSort :=
              Ne.symm hSort
            simp [Term.substituteFree,
              Term.freeSupport, hSort, hSort']
    · intro function arguments ih
      simpa [Term.substituteFree] using ih
    · simp [Term.freeSupportList]
    · intro head tail ihHead ihTail
      simp [Term.freeSupportList, ihHead, ihTail]
  have hReflexive :
      Γ ⊢ₘ[T]
        Formula.equal leftInstance leftInstance :=
    FirstOrder.Derives.eq_refl_m
      leftInstance (sort := contextSort)
  have hBody :
      Γ ⊢ₘ[T]
        Formula.substituteFree sort parameter left (Formula.equal leftInstance context) := by
    simpa [Formula.substituteFree,
      Term.substituteFree_eq_self_of_not_mem
        sort parameter left leftInstance
        hLeftInstanceFresh,
      leftInstance] using hReflexive
  have hTransport :=
    FirstOrder.Derives.eq_subst_m (T := T) (Γ := Γ) (sort := sort) (eigen := parameter) (left := left) (right := right)
      (body := Formula.equal leftInstance context)
      hEquality hBody
  simpa [Formula.substituteFree,
    Term.substituteFree_eq_self_of_not_mem
      sort parameter right leftInstance
      hLeftInstanceFresh,
    leftInstance] using hTransport

/--
固定函数应用的前后参数时，一条实参等式可提升为整个函数项的等式。孔 sort 由
`funcDomain` 的分解给出，函数结果 sort 可以与孔 sort 不同。
-/
theorem function_term_congr_argument_of_equality
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    (function : σ.FuncSymbol)
    {before after : List (Term σ)}
    {left right : Term σ}
    {beforeSorts afterSorts : List σ.SortSymbol}
    {sort : σ.SortSymbol}
    (hDomain :
      σ.funcDomain function =
        beforeSorts ++ sort :: afterSorts)
    (hBefore :
      ArgsAdmissible before beforeSorts)
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort)
    (hAfter :
      ArgsAdmissible after afterSorts)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      .app function (before ++ left :: after) ≐ₘ
        .app function (before ++ right :: after) := by
  let leftArguments := before ++ left :: after
  let leftTerm := Term.app function leftArguments
  let parameter :=
    FreshVariable.fresh_id sort
      [Formula.equal leftTerm leftTerm]
  let context :=
    Term.app function
      (before ++
        Term.var (.fvar sort parameter) :: after)
  have hLeftArguments :
      ArgsAdmissible leftArguments
        (σ.funcDomain function) := by
    rw [hDomain]
    exact hBefore.append
      (.cons hLeft hAfter)
  have hRightArguments :
      ArgsAdmissible
        (before ++ right :: after)
        (σ.funcDomain function) := by
    rw [hDomain]
    exact hBefore.append
      (.cons hRight hAfter)
  have hContextArguments :
      ArgsAdmissible
        (before ++
          Term.var (.fvar sort parameter) :: after)
        (σ.funcDomain function) := by
    rw [hDomain]
    exact hBefore.append
      (.cons
        ⟨TermWellSorted.fvar sort parameter,
          TermScoped.fvar sort parameter⟩
        hAfter)
  have hLeftTerm :
      Term.Admissible leftTerm
        (σ.funcCodomain function) :=
    ⟨TermWellSorted.app function
        hLeftArguments.1,
      TermScoped.app function leftArguments
        hLeftArguments.2⟩
  have hContext :
      Term.Admissible context
        (σ.funcCodomain function) :=
    ⟨TermWellSorted.app function
        hContextArguments.1,
      TermScoped.app function
        (before ++
          Term.var (.fvar sort parameter) :: after)
        hContextArguments.2⟩
  have hLeftTermFresh :
      (sort, parameter) ∉
        Term.freeSupport leftTerm := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m
      sort leftTerm
  have hArgumentsFresh :
      (sort, parameter) ∉
        Term.freeSupportList leftArguments := by
    simpa [leftTerm, Term.freeSupport] using
      hLeftTermFresh
  have hBeforeFresh :
      (sort, parameter) ∉
        Term.freeSupportList before := by
    intro hMember
    exact hArgumentsFresh <| by
      simp [leftArguments,
        Term.freeSupportList, hMember]
  have hLeftFresh :
      (sort, parameter) ∉
        Term.freeSupport left := by
    intro hMember
    exact hArgumentsFresh <|
      Term.mem_freeSupportList_of_mem
        (term := left) (terms := leftArguments)
        (by simp [leftArguments]) hMember
  have hAfterFresh :
      (sort, parameter) ∉
        Term.freeSupportList after := by
    intro hMember
    exact hArgumentsFresh <| by
      simp [leftArguments,
        Term.freeSupportList, hMember]
  have hTransport :=
    term_substituteFree_congr_of_equality
      sort parameter left right context
      hLeft hRight hContext hLeftFresh hEquality
  have hBeforeFixed :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter left before hBeforeFresh
  have hBeforeFixedRight :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter right before hBeforeFresh
  have hAfterFixed :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter left after hAfterFresh
  have hAfterFixedRight :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter right after hAfterFresh
  simpa [context, Term.substituteFree,
    hBeforeFixed, hBeforeFixedRight,
    hAfterFixed, hAfterFixedRight] using
      hTransport

/-- 两张同长参数表上的逐位置可导出等式。 -/
inductive TermwiseEquality
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    (T : Theory σ) (Γ : Context σ) :
    List (Term σ) → List (Term σ) → Prop where
  | nil :
      TermwiseEquality T Γ [] []
  | cons {left right : Term σ}
      {leftTail rightTail : List (Term σ)} :
      Γ ⊢ₘ[T] left ≐ₘ right →
      TermwiseEquality T Γ leftTail rightTail →
      TermwiseEquality T Γ
        (left :: leftTail) (right :: rightTail)

namespace TermwiseEquality

/-- 逐位置等式可整体提升到更大的局部上下文。 -/
theorem context_weaken
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ Δ : Context σ}
    {left right : List (Term σ)}
    (hSubset : ∀ φ, φ ∈ Γ → φ ∈ Δ)
    (hEqual : TermwiseEquality T Γ left right) :
    TermwiseEquality T Δ left right := by
  cases hEqual with
  | nil =>
      exact .nil
  | cons hHead hTail =>
      exact .cons
        (hHead.context_weaken hSubset)
        (context_weaken hSubset hTail)

end TermwiseEquality

/--
固定关系原子的前后参数时，一条实参等式可提升为两个原子的逻辑等价。孔的 sort
由关系签名的 domain 分解给出，其余实参通过 fresh 参数保持不变。
-/
theorem relation_congr_argument_of_equality
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    (relation : σ.RelSymbol)
    {before after : List (Term σ)}
    {left right : Term σ}
    {beforeSorts afterSorts : List σ.SortSymbol}
    {sort : σ.SortSymbol}
    (hDomain :
      σ.relDomain relation =
        beforeSorts ++ sort :: afterSorts)
    (hBefore :
      ArgsAdmissible before beforeSorts)
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort)
    (hAfter :
      ArgsAdmissible after afterSorts)
    (hEquality :
      Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T]
      Formula.rel relation
          (before ++ left :: after) ↔ₘ
        Formula.rel relation
          (before ++ right :: after) := by
  let leftArguments :=
    before ++ left :: after
  let leftFormula :=
    Formula.rel relation leftArguments
  let parameter :=
    FreshVariable.fresh_id sort [leftFormula]
  let body :=
    Formula.rel relation <|
      before ++
        Term.var (.fvar sort parameter) :: after
  have hLeftArguments :
      ArgsAdmissible leftArguments
        (σ.relDomain relation) := by
    rw [hDomain]
    exact hBefore.append
      (.cons hLeft hAfter)
  have hRightArguments :
      ArgsAdmissible
        (before ++ right :: after)
        (σ.relDomain relation) := by
    rw [hDomain]
    exact hBefore.append
      (.cons hRight hAfter)
  have hBodyArguments :
      ArgsAdmissible
        (before ++
          Term.var (.fvar sort parameter) :: after)
        (σ.relDomain relation) := by
    rw [hDomain]
    exact hBefore.append
      (.cons
        ⟨TermWellSorted.fvar sort parameter,
          TermScoped.fvar sort parameter⟩
        hAfter)
  have hLeftFormula :
      Formula.Admissible leftFormula :=
    ⟨FormulaWellFormed.rel relation
        hLeftArguments.1,
      FormulaScoped.rel relation
        leftArguments hLeftArguments.2⟩
  have hBody :
      Formula.Admissible body :=
    ⟨FormulaWellFormed.rel relation
        hBodyArguments.1,
      FormulaScoped.rel relation
        (before ++
          Term.var (.fvar sort parameter) :: after)
        hBodyArguments.2⟩
  have hArgumentsFresh :
      (sort, parameter) ∉
        Term.freeSupportList leftArguments := by
    dsimp [parameter]
    simpa [leftFormula, Formula.freeSupport] using
      (FreshVariable.fresh_id_not_mem_m
        (sort := sort) (formulas := [leftFormula])
        (formula := leftFormula)
        (by simp))
  have hBeforeFresh :
      (sort, parameter) ∉
        Term.freeSupportList before := by
    intro hMember
    exact hArgumentsFresh <| by
      simp [leftArguments,
        Term.freeSupportList, hMember]
  have hAfterFresh :
      (sort, parameter) ∉
        Term.freeSupportList after := by
    intro hMember
    exact hArgumentsFresh <| by
      simp [leftArguments,
        Term.freeSupportList, hMember]
  have hBeforeFixedLeft :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter left before hBeforeFresh
  have hBeforeFixedRight :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter right before hBeforeFresh
  have hAfterFixedLeft :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter left after hAfterFresh
  have hAfterFixedRight :=
    Term.substituteFreeList_eq_self_of_not_mem
      sort parameter right after hAfterFresh
  have hCongruence :=
    equality_iff_of_equality
      (T := T) (Γ := Γ)
      (sort := sort) (eigen := parameter)
      (body := body) hEquality
      (hLeftCheck :=
        Term.check_certificate_of_admissible hLeft)
      (hRightCheck :=
        Term.check_certificate_of_admissible hRight)
      (hBodyCheck :=
        Formula.check_certificate_of_admissible hBody)
  simpa [body, Formula.substituteFree,
    Term.substituteFree,
    hBeforeFixedLeft, hBeforeFixedRight,
    hAfterFixedLeft, hAfterFixedRight] using
      hCongruence

private theorem relation_congr_arguments_aux
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    (relation : σ.RelSymbol)
    (initial : List (Term σ))
    (initialSorts : List σ.SortSymbol)
    {left right : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hDomain :
      σ.relDomain relation =
        initialSorts ++ sorts)
    (hInitial :
      ArgsAdmissible initial initialSorts)
    (hLeft : ArgsAdmissible left sorts)
    (hRight : ArgsAdmissible right sorts)
    (hEqual :
      TermwiseEquality T Γ left right) :
    Γ ⊢ₘ[T]
      Formula.rel relation
          (initial ++ left) ↔ₘ
        Formula.rel relation
          (initial ++ right) := by
  cases hEqual with
  | nil =>
      cases hLeft.1
      have hArguments :
          ArgsAdmissible initial
            (σ.relDomain relation) := by
        rw [hDomain]
        simpa using hInitial
      exact iff_refl_m <| by
        simpa using
          Formula.Admissible.rel hArguments
  | @cons leftHead rightHead leftTail rightTail
      hHead hTail =>
      rcases ArgsAdmissible.exists_cons hLeft with
        ⟨sort, tailSorts, hSorts,
          hLeftHead, hLeftTail⟩
      subst sorts
      rcases ArgsAdmissible.exists_cons hRight with
        ⟨rightSort, rightTailSorts,
          hRightSorts, hRightHead,
          hRightTail⟩
      cases hRightSorts
      have hFirst :=
        relation_congr_argument_of_equality
          (T := T) (Γ := Γ) relation
          (before := initial)
          (after := leftTail)
          (beforeSorts := initialSorts)
          (afterSorts := tailSorts)
          (sort := sort)
          hDomain hInitial hLeftHead hRightHead
          hLeftTail hHead
      have hInitialNext :
          ArgsAdmissible
            (initial ++ [rightHead])
            (initialSorts ++ [sort]) :=
        hInitial.append
          (.cons hRightHead .nil)
      have hDomainNext :
          σ.relDomain relation =
            (initialSorts ++ [sort]) ++
              tailSorts := by
        simpa [List.append_assoc] using hDomain
      have hSecond :=
        relation_congr_arguments_aux
          (T := T) (Γ := Γ) relation
          (initial ++ [rightHead])
          (initialSorts ++ [sort])
          hDomainNext hInitialNext
          hLeftTail hRightTail hTail
      have hSecond' :
          Γ ⊢ₘ[T]
            Formula.rel relation
                (initial ++ rightHead :: leftTail) ↔ₘ
              Formula.rel relation
                (initial ++ rightHead :: rightTail) := by
        simpa [List.append_assoc] using hSecond
      exact iff_trans hFirst hSecond'

/--
逐位置相等的两张合法参数表，使任意相应关系原子逻辑等价。该接口由关系签名的
domain 驱动，同时覆盖任意元数与多 sort 关系。
-/
theorem relation_congr_arguments_of_equalities
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    (relation : σ.RelSymbol)
    {left right : List (Term σ)}
    (hLeft :
      ArgsAdmissible left
        (σ.relDomain relation))
    (hRight :
      ArgsAdmissible right
        (σ.relDomain relation))
    (hEqual :
      TermwiseEquality T Γ left right) :
    Γ ⊢ₘ[T]
      Formula.rel relation left ↔ₘ
        Formula.rel relation right := by
  simpa using
    relation_congr_arguments_aux
      (T := T) (Γ := Γ)
      relation [] []
      (left := left) (right := right)
      (sorts := σ.relDomain relation)
      (by simp) .nil hLeft hRight hEqual

private theorem function_term_congr_arguments_aux
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    (function : σ.FuncSymbol)
    (initial : List (Term σ))
    (initialSorts : List σ.SortSymbol)
    {left right : List (Term σ)}
    {sorts : List σ.SortSymbol}
    (hDomain :
      σ.funcDomain function =
        initialSorts ++ sorts)
    (hInitial :
      ArgsAdmissible initial initialSorts)
    (hLeft : ArgsAdmissible left sorts)
    (hRight : ArgsAdmissible right sorts)
    (hEqual :
      TermwiseEquality T Γ left right) :
    Γ ⊢ₘ[T]
      .app function (initial ++ left) ≐ₘ
        .app function (initial ++ right) := by
  cases hEqual with
  | nil =>
      cases hLeft.1
      have hArguments :
          ArgsAdmissible initial
            (σ.funcDomain function) := by
        rw [hDomain]
        simpa using hInitial
      have hTerm :
          Term.Admissible
            (.app function initial)
            (σ.funcCodomain function) :=
        ⟨TermWellSorted.app function
            hArguments.1,
          TermScoped.app function initial
            hArguments.2⟩
      simpa using
        (FirstOrder.Derives.eq_refl_m
          (T := T) (Γ := Γ)
          (.app function initial)
          (sort := σ.funcCodomain function)
          (hTermCheck :=
            Term.check_certificate_of_admissible
              hTerm))
  | @cons leftHead rightHead leftTail rightTail
      hHead hTail =>
      rcases ArgsAdmissible.exists_cons hLeft with
        ⟨sort, tailSorts, hSorts,
          hLeftHead, hLeftTail⟩
      subst sorts
      rcases ArgsAdmissible.exists_cons hRight with
        ⟨rightSort, rightTailSorts,
          hRightSorts, hRightHead,
          hRightTail⟩
      cases hRightSorts
      have hFirst :=
        function_term_congr_argument_of_equality
          (T := T) (Γ := Γ) function
          (before := initial)
          (after := leftTail)
          (beforeSorts := initialSorts)
          (afterSorts := tailSorts)
          (sort := sort)
          hDomain hInitial hLeftHead hRightHead
          hLeftTail hHead
      have hInitialNext :
          ArgsAdmissible
            (initial ++ [rightHead])
            (initialSorts ++ [sort]) :=
        hInitial.append
          (.cons hRightHead .nil)
      have hDomainNext :
          σ.funcDomain function =
            (initialSorts ++ [sort]) ++
              tailSorts := by
        simpa [List.append_assoc] using hDomain
      have hSecond :=
        function_term_congr_arguments_aux
          (T := T) (Γ := Γ) function
          (initial ++ [rightHead])
          (initialSorts ++ [sort])
          hDomainNext hInitialNext
          hLeftTail hRightTail hTail
      have hSecond' :
          Γ ⊢ₘ[T]
            .app function
                (initial ++ rightHead :: leftTail) ≐ₘ
              .app function
                (initial ++ rightHead :: rightTail) := by
        simpa [List.append_assoc] using hSecond
      exact equality_trans hFirst hSecond'

/--
逐位置相等的两张合法参数表给出对应函数项相等。该接口完全由函数签名中的 domain
驱动，因此同时覆盖任意元数与多 sort 函数。
-/
theorem function_term_congr_arguments_of_equalities
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    (function : σ.FuncSymbol)
    {left right : List (Term σ)}
    (hLeft :
      ArgsAdmissible left
        (σ.funcDomain function))
    (hRight :
      ArgsAdmissible right
        (σ.funcDomain function))
    (hEqual :
      TermwiseEquality T Γ left right) :
    Γ ⊢ₘ[T]
      .app function left ≐ₘ
        .app function right := by
  simpa using
    function_term_congr_arguments_aux
      (T := T) (Γ := Γ) function [] []
      (left := left) (right := right)
      (sorts := σ.funcDomain function)
      (by simp) .nil hLeft hRight hEqual

/--
两个独立的单孔项上下文可以把两条参数等式合成为一条复合项等式。
调用方只需证明两个中间实例定义相同；fresh 分配、Leibniz 运输和传递性在此统一完成。
-/
theorem term_context_pair_congr_of_equalities
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol}
    (leftParameter rightParameter : FreeVarId)
    (left₁ left₂ right₁ right₂ leftContext rightContext : Term σ)
    (hLeft₁ : Term.Admissible left₁ sort)
    (hLeft₂ : Term.Admissible left₂ sort)
    (hRight₁ : Term.Admissible right₁ sort)
    (hRight₂ : Term.Admissible right₂ sort)
    (hLeftContext : Term.Admissible leftContext sort)
    (hRightContext : Term.Admissible rightContext sort)
    (hLeftFresh : (sort, leftParameter) ∉ Term.freeSupport left₁)
    (hRightFresh : (sort, rightParameter) ∉ Term.freeSupport right₁)
    (hMiddle :
      Term.substituteFree sort leftParameter left₂ leftContext =
        Term.substituteFree sort rightParameter right₁ rightContext)
    (hLeftEquality : Γ ⊢ₘ[T] left₁ ≐ₘ left₂)
    (hRightEquality : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      Term.substituteFree sort leftParameter left₁ leftContext ≐ₘ
        Term.substituteFree sort rightParameter right₂ rightContext := by
  let leftSource :=
    Term.substituteFree sort leftParameter left₁ leftContext
  let leftTarget :=
    Term.substituteFree sort leftParameter left₂ leftContext
  let rightSource :=
    Term.substituteFree sort rightParameter right₁ rightContext
  let rightTarget :=
    Term.substituteFree sort rightParameter right₂ rightContext
  have hLeftSource : Term.Admissible leftSource sort :=
    ⟨TermWellSorted.substituteFree leftParameter hLeftContext.1 hLeft₁.1,
      Term.substituteFree_scoped hLeftContext.2 hLeft₁.2⟩
  have hRightSource : Term.Admissible rightSource sort :=
    ⟨TermWellSorted.substituteFree rightParameter hRightContext.1 hRight₁.1,
      Term.substituteFree_scoped hRightContext.2 hRight₁.2⟩
  have hRightTarget : Term.Admissible rightTarget sort :=
    ⟨TermWellSorted.substituteFree rightParameter hRightContext.1 hRight₂.1,
      Term.substituteFree_scoped hRightContext.2 hRight₂.2⟩
  have hFirst :
      Γ ⊢ₘ[T] leftSource ≐ₘ leftTarget := by
    simpa [leftSource, leftTarget] using
      term_substituteFree_congr_of_equality
        sort leftParameter left₁ left₂ leftContext
        hLeft₁ hLeft₂ hLeftContext hLeftFresh hLeftEquality
  have hSecond :
      Γ ⊢ₘ[T] rightSource ≐ₘ rightTarget := by
    simpa [rightSource, rightTarget] using
      term_substituteFree_congr_of_equality
        sort rightParameter right₁ right₂ rightContext
        hRight₁ hRight₂ hRightContext hRightFresh hRightEquality
  have hFirst' :
      Γ ⊢ₘ[T] leftSource ≐ₘ rightSource := by
    simpa [leftTarget, rightSource] using hMiddle ▸ hFirst
  exact equality_trans hFirst' hSecond
/--
一元项构造子只要保持 admissibility 且与自由替换交换，就自动保持已证明等式。
该接口把具体编码函数中的 fresh 上下文样板统一收回等式元理论。
-/
theorem unary_term_constructor_congr_of_equality
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {sort : σ.SortSymbol}
    (constructor : Term σ → Term σ)
    (hAdmissible :
      ∀ term, Term.Admissible term sort →
        Term.Admissible (constructor term) sort)
    (hSubstitute :
      ∀ parameter replacement term,
        Term.substituteFree sort parameter replacement (constructor term) =
          constructor (Term.substituteFree sort parameter replacement term))
    (left right : Term σ)
    (hLeft : Term.Admissible left sort)
    (hRight : Term.Admissible right sort)
    (hEquality : Γ ⊢ₘ[T] left ≐ₘ right) :
    Γ ⊢ₘ[T] constructor left ≐ₘ constructor right := by
  let parameter :=
    FreshVariable.fresh_id sort [left ≐ₘ left]
  let context := constructor v#[sort, parameter]
  have hFresh : (sort, parameter) ∉ Term.freeSupport left := by
    dsimp [parameter]
    exact FreshVariable.fresh_term_not_mem_m sort left
  have hContext : Term.Admissible context sort := by
    dsimp [context]
    exact hAdmissible _ ⟨TermWellSorted.fvar sort parameter,
      TermScoped.fvar sort parameter⟩
  have hTransport :=
    term_substituteFree_congr_of_equality
      sort parameter left right context
      hLeft hRight hContext hFresh hEquality
  simpa [context, hSubstitute, Term.substituteFree] using hTransport
/--
二元项构造子只要保持 admissibility 且逐参数与自由替换交换，就自动保持两条等式。
两个参数共用一个对四个输入都 fresh 的孔；中间项由替换交换律直接规范为
`constructor left₂ right₁`。
-/
theorem binary_term_constructor_congr_of_equalities
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {sort : σ.SortSymbol}
    (constructor : Term σ → Term σ → Term σ)
    (hAdmissible :
      ∀ left right,
        Term.Admissible left sort →
        Term.Admissible right sort →
        Term.Admissible (constructor left right) sort)
    (hSubstitute :
      ∀ parameter replacement left right,
        Term.substituteFree sort parameter replacement
            (constructor left right) =
          constructor
            (Term.substituteFree sort parameter replacement left)
            (Term.substituteFree sort parameter replacement right))
    (left₁ left₂ right₁ right₂ : Term σ)
    (hLeft₁ : Term.Admissible left₁ sort)
    (hLeft₂ : Term.Admissible left₂ sort)
    (hRight₁ : Term.Admissible right₁ sort)
    (hRight₂ : Term.Admissible right₂ sort)
    (hLeftEquality : Γ ⊢ₘ[T] left₁ ≐ₘ left₂)
    (hRightEquality : Γ ⊢ₘ[T] right₁ ≐ₘ right₂) :
    Γ ⊢ₘ[T]
      constructor left₁ right₁ ≐ₘ
        constructor left₂ right₂ := by
  let formulas :=
    [left₁ ≐ₘ left₁, left₂ ≐ₘ left₂,
      right₁ ≐ₘ right₁, right₂ ≐ₘ right₂]
  let parameter := FreshVariable.fresh_id sort formulas
  let leftContext := constructor v#[sort, parameter] right₁
  let rightContext := constructor left₂ v#[sort, parameter]
  have hFresh (term : Term σ)
      (hTerm : term ≐ₘ term ∈ formulas) :
      (sort, parameter) ∉ Term.freeSupport term := by
    dsimp [parameter]
    have h :=
      FreshVariable.fresh_id_not_mem_m
        (sort := sort) (formulas := formulas)
        (formula := term ≐ₘ term) hTerm
    simpa [Formula.freeSupport] using h
  have hLeft₁Fresh :
      (sort, parameter) ∉ Term.freeSupport left₁ :=
    hFresh left₁ (by simp [formulas])
  have hLeft₂Fresh :
      (sort, parameter) ∉ Term.freeSupport left₂ :=
    hFresh left₂ (by simp [formulas])
  have hRight₁Fresh :
      (sort, parameter) ∉ Term.freeSupport right₁ :=
    hFresh right₁ (by simp [formulas])
  have hLeft₂Fixed (replacement : Term σ) :
      Term.substituteFree sort parameter replacement left₂ = left₂ :=
    Term.substituteFree_eq_self_of_not_mem
      sort parameter replacement left₂ hLeft₂Fresh
  have hRight₁Fixed (replacement : Term σ) :
      Term.substituteFree sort parameter replacement right₁ = right₁ :=
    Term.substituteFree_eq_self_of_not_mem
      sort parameter replacement right₁ hRight₁Fresh
  have hLeftContext : Term.Admissible leftContext sort := by
    dsimp [leftContext]
    exact hAdmissible _ _ ⟨TermWellSorted.fvar sort parameter,
      TermScoped.fvar sort parameter⟩ hRight₁
  have hRightContext : Term.Admissible rightContext sort := by
    dsimp [rightContext]
    exact hAdmissible _ _ hLeft₂ ⟨TermWellSorted.fvar sort parameter,
      TermScoped.fvar sort parameter⟩
  have hMiddle :
      Term.substituteFree sort parameter left₂ leftContext =
        Term.substituteFree sort parameter right₁ rightContext := by
    simp [leftContext, rightContext, hSubstitute,
      Term.substituteFree, hLeft₂Fixed, hRight₁Fixed]
  have hTransport :=
    term_context_pair_congr_of_equalities
      parameter parameter
      left₁ left₂ right₁ right₂
      leftContext rightContext
      hLeft₁ hLeft₂ hRight₁ hRight₂
      hLeftContext hRightContext
      hLeft₁Fresh hRight₁Fresh hMiddle
      hLeftEquality hRightEquality
  simpa [leftContext, rightContext, hSubstitute,
    Term.substituteFree, hLeft₂Fixed, hRight₁Fixed] using hTransport

/--
三元项构造子只要保持 admissibility 且逐参数与自由替换交换，就保持三条等式。
三个参数共用一个对六个输入都 fresh 的孔，依次替换三个坐标后用传递性合成。
-/
theorem ternary_term_constructor_congr_of_equalities
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {sort : σ.SortSymbol}
    (constructor : Term σ → Term σ → Term σ → Term σ)
    (hAdmissible :
      ∀ first second third,
        Term.Admissible first sort →
        Term.Admissible second sort →
        Term.Admissible third sort →
        Term.Admissible (constructor first second third) sort)
    (hSubstitute :
      ∀ parameter replacement first second third,
        Term.substituteFree sort parameter replacement
            (constructor first second third) =
          constructor
            (Term.substituteFree sort parameter replacement first)
            (Term.substituteFree sort parameter replacement second)
            (Term.substituteFree sort parameter replacement third))
    (first₁ first₂ second₁ second₂ third₁ third₂ : Term σ)
    (hFirst₁ : Term.Admissible first₁ sort)
    (hFirst₂ : Term.Admissible first₂ sort)
    (hSecond₁ : Term.Admissible second₁ sort)
    (hSecond₂ : Term.Admissible second₂ sort)
    (hThird₁ : Term.Admissible third₁ sort)
    (hThird₂ : Term.Admissible third₂ sort)
    (hFirstEquality : Γ ⊢ₘ[T] first₁ ≐ₘ first₂)
    (hSecondEquality : Γ ⊢ₘ[T] second₁ ≐ₘ second₂)
    (hThirdEquality : Γ ⊢ₘ[T] third₁ ≐ₘ third₂) :
    Γ ⊢ₘ[T]
      constructor first₁ second₁ third₁ ≐ₘ
        constructor first₂ second₂ third₂ := by
  let formulas := [
    first₁ ≐ₘ first₁, first₂ ≐ₘ first₂,
    second₁ ≐ₘ second₁, second₂ ≐ₘ second₂,
    third₁ ≐ₘ third₁, third₂ ≐ₘ third₂]
  let parameter := FreshVariable.fresh_id sort formulas
  have hFresh (term : Term σ)
      (hTerm : term ≐ₘ term ∈ formulas) :
      (sort, parameter) ∉ Term.freeSupport term := by
    dsimp [parameter]
    have h :=
      FreshVariable.fresh_id_not_mem_m
        (sort := sort) (formulas := formulas)
        (formula := term ≐ₘ term) hTerm
    simpa [Formula.freeSupport] using h
  have hFirst₂Fixed (replacement : Term σ) :
      Term.substituteFree sort parameter replacement first₂ = first₂ :=
    Term.substituteFree_eq_self_of_not_mem
      sort parameter replacement first₂
        (hFresh first₂ (by simp [formulas]))
  have hSecond₁Fixed (replacement : Term σ) :
      Term.substituteFree sort parameter replacement second₁ = second₁ :=
    Term.substituteFree_eq_self_of_not_mem
      sort parameter replacement second₁
        (hFresh second₁ (by simp [formulas]))
  have hSecond₂Fixed (replacement : Term σ) :
      Term.substituteFree sort parameter replacement second₂ = second₂ :=
    Term.substituteFree_eq_self_of_not_mem
      sort parameter replacement second₂
        (hFresh second₂ (by simp [formulas]))
  have hThird₁Fixed (replacement : Term σ) :
      Term.substituteFree sort parameter replacement third₁ = third₁ :=
    Term.substituteFree_eq_self_of_not_mem
      sort parameter replacement third₁
        (hFresh third₁ (by simp [formulas]))
  let firstContext :=
    constructor v#[sort, parameter] second₁ third₁
  let secondContext :=
    constructor first₂ v#[sort, parameter] third₁
  let thirdContext :=
    constructor first₂ second₂ v#[sort, parameter]
  have hFirstContext : Term.Admissible firstContext sort := by
    dsimp [firstContext]
    exact hAdmissible _ _ _
      ⟨TermWellSorted.fvar sort parameter,
        TermScoped.fvar sort parameter⟩
      hSecond₁ hThird₁
  have hSecondContext : Term.Admissible secondContext sort := by
    dsimp [secondContext]
    exact hAdmissible _ _ _ hFirst₂
      ⟨TermWellSorted.fvar sort parameter,
        TermScoped.fvar sort parameter⟩
      hThird₁
  have hThirdContext : Term.Admissible thirdContext sort := by
    dsimp [thirdContext]
    exact hAdmissible _ _ _ hFirst₂ hSecond₂
      ⟨TermWellSorted.fvar sort parameter,
        TermScoped.fvar sort parameter⟩
  have hFirstTransport :=
    term_substituteFree_congr_of_equality
      sort parameter first₁ first₂ firstContext
      hFirst₁ hFirst₂ hFirstContext
      (hFresh first₁ (by simp [formulas])) hFirstEquality
  have hFirst :
      Γ ⊢ₘ[T]
        constructor first₁ second₁ third₁ ≐ₘ
          constructor first₂ second₁ third₁ := by
    simpa [firstContext, hSubstitute, Term.substituteFree,
      hSecond₁Fixed, hThird₁Fixed] using hFirstTransport
  have hSecondTransport :=
    term_substituteFree_congr_of_equality
      sort parameter second₁ second₂ secondContext
      hSecond₁ hSecond₂ hSecondContext
      (hFresh second₁ (by simp [formulas])) hSecondEquality
  have hSecond :
      Γ ⊢ₘ[T]
        constructor first₂ second₁ third₁ ≐ₘ
          constructor first₂ second₂ third₁ := by
    simpa [secondContext, hSubstitute, Term.substituteFree,
      hFirst₂Fixed, hThird₁Fixed] using hSecondTransport
  have hThirdTransport :=
    term_substituteFree_congr_of_equality
      sort parameter third₁ third₂ thirdContext
      hThird₁ hThird₂ hThirdContext
      (hFresh third₁ (by simp [formulas])) hThirdEquality
  have hThird :
      Γ ⊢ₘ[T]
        constructor first₂ second₂ third₁ ≐ₘ
          constructor first₂ second₂ third₂ := by
    simpa [thirdContext, hSubstitute, Term.substituteFree,
      hFirst₂Fixed, hSecond₂Fixed] using hThirdTransport
  exact equality_trans hFirst (equality_trans hSecond hThird)

/-- 等式反身性的单变量全称闭包。 -/
theorem forall_equality_refl {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (eigen : FreeVarId) :
    Γ ⊢ₘ[T]
      ∀ₘ[sort, eigen],
        v#[sort, eigen] ≐ₘ v#[sort, eigen] := by
  derive_close (eigen) using
    equality_refl (T := (Theory.empty : Theory σ)) (Γ := [])
      v#[sort, eigen]
/-- 等式对称性的双变量全称闭包。 -/
theorem forall_equality_symm {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (left right : FreeVarId) :
    Γ ⊢ₘ[T]
      ∀ₘ[sort, left],
        ∀ₘ[sort, right], (v#[sort, left] ≐ₘ v#[sort, right]) ⟶ₘ (v#[sort, right] ≐ₘ v#[sort, left]) := by
  have hOpen :
      ⊢ₘ (v#[sort, left] ≐ₘ v#[sort, right]) ⟶ₘ (v#[sort, right] ≐ₘ v#[sort, left]) :=
    equality_symm_imp (T := (Theory.empty : Theory σ))
      (Γ := [])
  derive_close (left, right) using hOpen
/-- 等式传递性的三变量全称闭包。 -/
theorem forall_equality_trans {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (left middle right : FreeVarId) :
    Γ ⊢ₘ[T]
      ∀ₘ[sort, left],
        ∀ₘ[sort, middle],
          ∀ₘ[sort, right], (v#[sort, left] ≐ₘ v#[sort, middle]) ⟶ₘ ((v#[sort, middle] ≐ₘ v#[sort, right]) ⟶ₘ (v#[sort, left] ≐ₘ v#[sort, right])) := by
  have hOpen :
      ⊢ₘ (v#[sort, left] ≐ₘ v#[sort, middle]) ⟶ₘ ((v#[sort, middle] ≐ₘ v#[sort, right]) ⟶ₘ (v#[sort, left] ≐ₘ v#[sort, right])) :=
    equality_trans_imp (T := (Theory.empty : Theory σ))
      (Γ := [])
  derive_close (left, middle, right) using hOpen
end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
