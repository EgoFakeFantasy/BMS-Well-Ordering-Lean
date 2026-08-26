import YesMetaZFC.Logic.FirstOrder.Derivation.Core
import YesMetaZFC.Logic.FirstOrder.FreshVariable
/-!
# 一阶量词推导接口
本模块只整理量词构造子、有限见证与 locally nameless 关闭/打开合同。满足关系上的
环境更新引理留在 `Derivation.Soundness`，避免纯语法推导链依赖语义可靠性。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Derives
theorem forall_intro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) ∉ Formula.freeSupport formula) (hContextFresh :
      ∀ formula, formula ∈ Γ → (sort, eigen) ∉ Formula.freeSupport formula) (hBody : Derives T Γ body) :
    Derives T Γ (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 body)) :=
  .forallIntro hTheoryFresh hContextFresh hBody
theorem forall_elim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {body : Formula σ} {term : Term σ}
    (hForall : Derives T Γ (Formula.forallE sort body))
    (hTermCheck : Term.CheckCertificate term sort := by
      prove_term_check) :
    Derives T Γ (Formula.openAt sort 0 term body) :=
  .forallElim hForall hTermCheck
/--
以指定 sort 的 free 变量实例化全称公式。
搜索后端只需提交变量编号；sort 正确与 bound-closed 证书仍由可信核接口统一生成。
-/
theorem forall_elim_fvar
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (id : FreeVarId) (body : Formula σ) (hForall : Derives T Γ (Formula.forallE sort body)) :
    Derives T Γ (Formula.openAt sort 0 (Term.var (.fvar sort id)) body) :=
  .forallElim hForall
theorem exists_intro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {body : Formula σ} {term : Term σ}
    (hBody : Derives T Γ (Formula.openAt sort 0 term body))
    (hTermCheck : Term.CheckCertificate term sort := by
      prove_term_check) :
    Derives T Γ (Formula.existsE sort body) :=
  .existsIntro hBody hTermCheck
/--
由一个已经证明的自由变量替换实例，直接引入对应的存在闭包。
与 `exists_intro` 相比，本接口不要求调用方重复提交整个存在式的 admissibility：
替换实例的合法性可由 `Derives.admissible` 取得，再借
`Formula.Admissible.substituteFree_source` 反演出原模板的合法性。对象编码层大量使用
闭 quotation 项作存在见证，因此把这段机械证书恢复集中到量词公共层可以避免每个
编码模块各自维护一套脆弱的展开证明。
-/
theorem exists_intro_substituted
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} (eigen : FreeVarId)
    {body : Formula σ} {witness : Term σ}
    (hInstance :
      Derives T Γ (Formula.substituteFree sort eigen witness body))
    (hWitnessCheck : Term.CheckCertificate witness sort := by
      prove_term_check) :
    Derives T Γ (Formula.existsE sort (Formula.closeFreeAt sort eigen 0 body)) := by
  apply Derives.existsIntro
      (hTermCheck := hWitnessCheck)
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree] using
    hInstance
/--
一次引入一列闭见证对应的嵌套存在闭包。

该接口只要求可信核实际消费的三类信息：变量编号无重复、每个见证通过项检查、每个
见证没有自由变量。它统一覆盖编码层常见的一至十个有限见证，而不再按元数复制证明。
-/
theorem exists_intro_substituted_assignments
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol}
    (assignments : List (FreeVarId × Term σ))
    (body : Formula σ)
    (hIds :
      (assignments.map (fun assignment => assignment.1)).Nodup)
    (hWitnessCheck :
      ∀ assignment, assignment ∈ assignments →
        Term.CheckCertificate assignment.2 sort)
    (hWitnessFree :
      ∀ assignment, assignment ∈ assignments →
        Term.freeSupport assignment.2 = [])
    (hInstance :
      Derives T Γ
        (Formula.substituteFreeAssignments sort assignments body)) :
    Derives T Γ
      (Formula.existsFreeAssignments sort assignments body) := by
  induction assignments generalizing body with
  | nil =>
      simpa [Formula.substituteFreeAssignments,
        Formula.existsFreeAssignments] using hInstance
  | cons assignment assignments ih =>
      rcases assignment with ⟨id, witness⟩
      have hIdsCons :
          (id :: assignments.map
            (fun assignment => assignment.1)).Nodup := by
        simpa using hIds
      rcases List.nodup_cons.mp hIdsCons with
        ⟨hIdFresh, hTailIds⟩
      have hWitnessCheckHead :
          Term.CheckCertificate witness sort :=
        hWitnessCheck (id, witness) (by simp)
      have hWitnessFreeHead :
          Term.freeSupport witness = [] :=
        hWitnessFree (id, witness) (by simp)
      have hTail :
          Derives T Γ
            (Formula.existsFreeAssignments sort assignments
              (Formula.substituteFree sort id witness body)) := by
        apply ih
        · exact hTailIds
        · intro assignment hAssignment
          exact hWitnessCheck assignment (by simp [hAssignment])
        · intro assignment hAssignment
          exact hWitnessFree assignment (by simp [hAssignment])
        · simpa [Formula.substituteFreeAssignments] using
            hInstance
      simp only [Formula.existsFreeAssignments]
      apply Derives.exists_intro_substituted
        (witness := witness) id
        (hWitnessCheck := hWitnessCheckHead)
      · rw [←
          Formula.existsFreeAssignments_substituteFree_comm_fresh
            sort id witness assignments body hIdFresh
            hWitnessCheckHead.admissible.2
            (fun binder _ => by
              rw [hWitnessFreeHead]
              exact List.not_mem_nil)]
        exact hTail
/--
以指定 sort 的 free 变量作为存在见证。
该接口把自动化反复需要的 sort 与 bound-closed 证书固定为可信核构造，不把这些
机械证明留给每个搜索后端重新拼装。
-/
theorem exists_intro_fvar
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol)
    (id : FreeVarId) (body : Formula σ)
    (hBody :
      Derives T Γ (Formula.openAt sort 0 (Term.var (.fvar sort id)) body)) :
    Derives T Γ (Formula.existsE sort body) :=
  .existsIntro hBody (Term.CheckCertificate.fvar sort id)
theorem exists_elim
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body conclusion : Formula σ} (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) ∉ Formula.freeSupport formula) (hContextFresh :
      ∀ formula, formula ∈ Γ → (sort, eigen) ∉ Formula.freeSupport formula) (hConclusionFresh : (sort, eigen) ∉ Formula.freeSupport conclusion)
    (hExists :
      Derives T Γ (Formula.existsE sort (Formula.closeFreeAt sort eigen 0 body)))
    (hCase : Derives T (body :: Γ) conclusion)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Derives T Γ conclusion :=
  .existsElim hTheoryFresh hContextFresh hConclusionFresh
    hExists hCase hBodyCheck
/-- 全称公式可以实例化为任意 sort 正确且 bound-closed 的项。 -/
theorem forall_specialization
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {body : Formula σ} {term : Term σ}
    (hTermCheck : Term.CheckCertificate term sort := by
      prove_term_check)
    (hForallCheck :
      Formula.CheckCertificate (Formula.forallE sort body) := by
        prove_nd_formula_check) :
    Derives T Γ (Formula.imp (Formula.forallE sort body) (Formula.openAt sort 0 term body)) :=
  .impIntro
    (.forallElim
      (.assumption (by simp) hForallCheck)
      hTermCheck)
    hForallCheck
/--
自由变量不在公式中出现时，可以把对应的 universal closure 作为无关量词引入。
结论使用 LN 的 canonical closure，而不是要求调用方手工处理 binder index 移动。
-/
theorem forall_vacuous_intro
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ}
    (hFresh : (sort, eigen) ∉ Formula.freeSupport body)
    (hBodyCheck : Formula.CheckCertificate body := by
      prove_nd_formula_check) :
    Derives T Γ (Formula.imp body (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 body))) := by
  apply Derives.contextWeakening (Γ := [])
  · simp
  apply Derives.theoryWeakening (T := (Theory.empty : Theory σ)) (U := T)
  · simp [Theory.empty]
  nd_apply Derives.impIntro
  apply Derives.forall_intro
  · intro formula hFormula
    cases hFormula
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    exact hFresh
  · exact .assumption (by simp) hBodyCheck
/--
全称量词保持蕴含。
证明在空理论、空上下文中选择一个由有限支持计算出的 canonical eigenvariable，
完成局部实例化后再全称化，最后通过结构弱化用于任意理论和上下文。
-/
theorem forall_imp_distribution
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (left right : Formula σ) (hForallImp :
      Formula.CheckCertificate (Formula.forallE sort (Formula.imp left right)) := by
        prove_nd_formula_check) (hForallLeft :
      Formula.CheckCertificate (Formula.forallE sort left) := by
        prove_nd_formula_check) :
    Derives T Γ (Formula.imp (Formula.forallE sort (Formula.imp left right)) (Formula.imp (Formula.forallE sort left) (Formula.forallE sort right))) := by
  let eigen := FreshVariable.fresh_id sort [left, right]
  have hLeftFresh : (sort, eigen) ∉ Formula.freeSupport left := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hRightFresh : (sort, eigen) ∉ Formula.freeSupport right := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  apply Derives.contextWeakening (Γ := [])
  · simp
  apply Derives.theoryWeakening (T := (Theory.empty : Theory σ)) (U := T)
  · simp [Theory.empty]
  nd_apply Derives.impIntro
  nd_apply Derives.impIntro
  have hUniversalImp :
      Derives (Theory.empty : Theory σ)
        [Formula.forallE sort left,
          Formula.forallE sort (Formula.imp left right)] (Formula.forallE sort (Formula.imp left right)) :=
    .assumption (by simp)
  have hUniversalLeft :
      Derives (Theory.empty : Theory σ)
        [Formula.forallE sort left,
          Formula.forallE sort (Formula.imp left right)] (Formula.forallE sort left) :=
    .assumption (by simp)
  have hOpenedImp :
      Derives (Theory.empty : Theory σ)
        [Formula.forallE sort left,
          Formula.forallE sort (Formula.imp left right)] (Formula.imp (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left)
          (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right)) := by
    simpa [Formula.openAt] using
      (Derives.forall_elim hUniversalImp)
  have hOpenedLeft :
      Derives (Theory.empty : Theory σ)
        [Formula.forallE sort left,
          Formula.forallE sort (Formula.imp left right)] (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left) :=
    Derives.forall_elim hUniversalLeft
  have hOpenedRight :
      Derives (Theory.empty : Theory σ)
        [Formula.forallE sort left,
          Formula.forallE sort (Formula.imp left right)] (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right) :=
    .impElim hOpenedImp hOpenedLeft
  have hGeneralized :=
    Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ :=
        [Formula.forallE sort left,
          Formula.forallE sort (Formula.imp left right)]) (sort := sort) (eigen := eigen) (body :=
        Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · simpa [Formula.freeSupport] using hLeftFresh
        · rcases List.mem_singleton.mp hFormula with rfl
          simp [Formula.freeSupport, hLeftFresh, hRightFresh])
      hOpenedRight
  simpa [Formula.closeFreeAt_openAt sort eigen 0 right hRightFresh] using
    hGeneralized
/-- 由打开实例引入存在量词。 -/
theorem exists_intro_imp
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {body : Formula σ} {term : Term σ}
    (hTermCheck : Term.CheckCertificate term sort := by
      prove_term_check)
    (hOpenedCheck :
      Formula.CheckCertificate (Formula.openAt sort 0 term body) := by
        prove_nd_formula_check) :
    Derives T Γ (Formula.imp (Formula.openAt sort 0 term body) (Formula.existsE sort body)) := by
  nd_apply Derives.imp_intro
  exact Derives.exists_intro
    (Derives.assumption (by simp) hOpenedCheck)
    hTermCheck
/-- 存在量词保持一个对结论变量新鲜的蕴含。 -/
theorem exists_imp_of_imp
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body conclusion : Formula σ} (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) ∉ Formula.freeSupport formula) (hContextFresh :
      ∀ formula, formula ∈ Γ → (sort, eigen) ∉ Formula.freeSupport formula) (hConclusionFresh : (sort, eigen) ∉ Formula.freeSupport conclusion)
    (hImplication :
      Derives T Γ (Formula.imp body conclusion)) :
    Derives T Γ (Formula.imp (Formula.existsE sort (Formula.closeFreeAt sort eigen 0 body))
        conclusion) := by
  have hBody :
      Formula.Admissible body :=
    Formula.Admissible.imp_left hImplication.admissible
  have hBodyCheck :
      Formula.CheckCertificate body :=
    Formula.check_admissible_complete hBody
  nd_apply Derives.imp_intro
  apply Derives.exists_elim (sort := sort) (eigen := eigen) (body := body) (conclusion := conclusion)
  · exact hTheoryFresh
  · intro formula hFormula
    rcases List.mem_cons.mp hFormula with rfl | hFormula
    · simpa [Formula.freeSupport] using
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
    · exact hContextFresh formula hFormula
  · exact hConclusionFresh
  · exact Derives.assumption (by simp)
  · have hImplication' :
        Derives T (body ::
            Formula.existsE sort (Formula.closeFreeAt sort eigen 0 body) :: Γ) (Formula.imp body conclusion) :=
      Derives.contextWeakening (by
          intro formula hFormula
          simp [hFormula])
        hImplication
    exact hImplication'.imp_elim (Derives.assumption (by simp))
end Derives
end FirstOrder
end Logic
end YesMetaZFC
