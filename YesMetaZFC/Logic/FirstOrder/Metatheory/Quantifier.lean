import YesMetaZFC.Logic.FirstOrder.Metatheory.Basic
/-!
# 一阶元数理量词定理
本模块收纳不依赖具体理论的量词推导模式。命题骨架仍由 `derive_prop` 重放；
eigenvariable、新鲜性、打开/关闭与自由变量替换则显式消费 `Derives` 核的量词规则。
纸面文献中的具名约束变量在 locally nameless 核中不进入接口。所谓“变量可替换”
被拆成 sort 正确、bound-closed witness 与 `substituteFree`，从而避免把偶然的变量名
约定传播到后续自动化。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Metatheory
universe u v w
namespace Derives
/-- 全称量化的合取可以推出左侧全称公式。 -/
theorem forall_conj_elim_left {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (left right : Formula σ) (hUniversalConj :
      Formula.Admissible (∀ₘ[sort], left ∧ₘ right)) :
    Γ ⊢ₘ[T] (∀ₘ[sort], left ∧ₘ right) ⟶ₘ (∀ₘ[sort], left) := by
  let eigen := FreshVariable.fresh_id sort [left, right]
  have hLeftFresh : (sort, eigen) freshForₘ left := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hRightFresh : (sort, eigen) freshForₘ right := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  apply FirstOrder.Derives.of_empty
  nd_apply FirstOrder.Derives.impIntro
  have hUniversal :
      [∀ₘ[sort], left ∧ₘ right] ⊢ₘ
        ∀ₘ[sort], left ∧ₘ right :=
    .assumption (by simp)
  have hOpened :
      [∀ₘ[sort], left ∧ₘ right] ⊢ₘ (left ∧ₘ right)⟦sort, 0 ↦ v#[sort, eigen]⟧ₘ :=
    FirstOrder.Derives.forallElim
      (term := v#[sort, eigen]) hUniversal
  have hOpenedLeft :
      [∀ₘ[sort], left ∧ₘ right] ⊢ₘ
        left⟦sort, 0 ↦ v#[sort, eigen]⟧ₘ := by
    simpa [Formula.openAt] using (FirstOrder.Derives.conjElimLeft hOpened)
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [∀ₘ[sort], left ∧ₘ right]) (sort := sort) (eigen := eigen)
      (body := left⟦sort, 0 ↦ v#[sort, eigen]⟧ₘ) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        simp [Formula.freeSupport, hLeftFresh, hRightFresh])
      hOpenedLeft
  simpa [Formula.closeFreeAt_openAt sort eigen 0 left hLeftFresh] using
    hGeneralized
/-- 全称量化的合取可以推出右侧全称公式。 -/
theorem forall_conj_elim_right {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (left right : Formula σ) (hUniversalConj :
      Formula.Admissible (∀ₘ[sort], left ∧ₘ right)) :
    Γ ⊢ₘ[T] (∀ₘ[sort], left ∧ₘ right) ⟶ₘ (∀ₘ[sort], right) := by
  let eigen := FreshVariable.fresh_id sort [left, right]
  have hLeftFresh : (sort, eigen) freshForₘ left := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hRightFresh : (sort, eigen) freshForₘ right := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  apply FirstOrder.Derives.of_empty
  nd_apply FirstOrder.Derives.impIntro
  have hUniversal :
      [∀ₘ[sort], left ∧ₘ right] ⊢ₘ
        ∀ₘ[sort], left ∧ₘ right :=
    .assumption (by simp)
  have hOpened :
      [∀ₘ[sort], left ∧ₘ right] ⊢ₘ (left ∧ₘ right)⟦sort, 0 ↦ v#[sort, eigen]⟧ₘ :=
    FirstOrder.Derives.forallElim
      (term := v#[sort, eigen]) hUniversal
  have hOpenedRight :
      [∀ₘ[sort], left ∧ₘ right] ⊢ₘ
        right⟦sort, 0 ↦ v#[sort, eigen]⟧ₘ := by
    simpa [Formula.openAt] using (FirstOrder.Derives.conjElimRight hOpened)
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [∀ₘ[sort], left ∧ₘ right]) (sort := sort) (eigen := eigen)
      (body := right⟦sort, 0 ↦ v#[sort, eigen]⟧ₘ) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        simp [Formula.freeSupport, hLeftFresh, hRightFresh])
      hOpenedRight
  simpa [Formula.closeFreeAt_openAt sort eigen 0 right hRightFresh] using
    hGeneralized
/-- 两个同 sort 的全称公式可以组成全称合取。 -/
theorem forall_conj_intro {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (left right : Formula σ) (hUniversalPair :
      Formula.Admissible ((∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right))) :
    Γ ⊢ₘ[T] ((∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right)) ⟶ₘ (∀ₘ[sort], left ∧ₘ right) := by
  let eigen := FreshVariable.fresh_id sort [left, right]
  have hLeftFresh : (sort, eigen) freshForₘ left := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hRightFresh : (sort, eigen) freshForₘ right := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hConjFresh : (sort, eigen) freshForₘ (left ∧ₘ right) := by
    simp [Formula.freeSupport, hLeftFresh, hRightFresh]
  apply FirstOrder.Derives.of_empty
  nd_apply FirstOrder.Derives.impIntro
  have hUniversalConj :
      [(∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right)] ⊢ₘ (∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right) :=
    .assumption (by simp)
  have hUniversalLeft :
      [(∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right)] ⊢ₘ
        ∀ₘ[sort], left :=
    .conjElimLeft hUniversalConj
  have hUniversalRight :
      [(∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right)] ⊢ₘ
        ∀ₘ[sort], right :=
    .conjElimRight hUniversalConj
  have hOpenedLeft :=
    FirstOrder.Derives.forallElim
      (term := v#[sort, eigen]) hUniversalLeft
  have hOpenedRight :=
    FirstOrder.Derives.forallElim
      (term := v#[sort, eigen]) hUniversalRight
  have hOpenedConj :
      [(∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right)] ⊢ₘ (left ∧ₘ right)⟦sort, 0 ↦ v#[sort, eigen]⟧ₘ := by
    simpa [Formula.openAt] using (FirstOrder.Derives.conjIntro hOpenedLeft hOpenedRight)
  have hGeneralized :=
    FirstOrder.Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ := [(∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right)]) (sort := sort) (eigen := eigen)
      (body := (left ∧ₘ right)⟦sort, 0 ↦ v#[sort, eigen]⟧ₘ) (by
        intro formula hFormula
        cases hFormula) (by
        intro formula hFormula
        rcases List.mem_singleton.mp hFormula with rfl
        simp [Formula.freeSupport, hLeftFresh, hRightFresh])
      hOpenedConj
  simpa [
    Formula.closeFreeAt_openAt sort eigen 0 (left ∧ₘ right) hConjFresh] using hGeneralized
/-- 全称量词分配到同 sort 合取的双向形式。 -/
theorem forall_conj_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (left right : Formula σ) (hUniversalConj :
      Formula.Admissible (∀ₘ[sort], left ∧ₘ right)) (hUniversalPair :
      Formula.Admissible ((∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right))) :
    Γ ⊢ₘ[T] (∀ₘ[sort], left ∧ₘ right) ↔ₘ ((∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right)) := by
  have hLeft :=
    forall_conj_elim_left (T := T) (Γ := Γ) sort left right hUniversalConj
  have hRight :=
    forall_conj_elim_right (T := T) (Γ := Γ) sort left right hUniversalConj
  have hForward :
      Γ ⊢ₘ[T] (∀ₘ[sort], left ∧ₘ right) ⟶ₘ ((∀ₘ[sort], left) ∧ₘ (∀ₘ[sort], right)) := by
    derive_prop
  have hBackward :=
    forall_conj_intro (T := T) (Γ := Γ) sort left right hUniversalPair
  exact .iffIntro (FirstOrder.Derives.imp_elim_assumption hForward) (FirstOrder.Derives.imp_elim_assumption hBackward)
/--
由一个自由变量替换实例引入其 existential closure。
sort 正确和 bound-closed 正是 LN 核中对应纸面“可代入”的证明携带边界。
-/
theorem exists_intro_substitute {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body : Formula σ} {witness : Term σ} (hWitnessSorted : TermWellSorted witness sort) (hWitnessClosed : Term.BoundClosed witness)
    (hBody : Formula.Admissible body) :
    Γ ⊢ₘ[T]
      body⟪sort, eigen ↦ witness⟫ₘ ⟶ₘ (∃ₘ[sort, eigen], body) := by
  have hWitness : Term.Admissible witness sort :=
    ⟨hWitnessSorted, hWitnessClosed⟩
  have hInstanceAdmissible :
      Formula.Admissible (body⟪sort, eigen ↦ witness⟫ₘ) :=
    Formula.Admissible.substituteFree sort eigen hBody hWitness
  have hExistential :
      Formula.Admissible (∃ₘ[sort, eigen], body) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBody
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.existsIntro (term := witness)
  have hInstance : (body⟪sort, eigen ↦ witness⟫ₘ :: Γ) ⊢ₘ[T]
        body⟪sort, eigen ↦ witness⟫ₘ :=
    .assumption (by simp)
  simpa [Formula.openAt_closeFreeAt_eq_substituteFree] using
    hInstance
/-- 以另一个同 sort 自由变量作为 witness 的存在量词引入。 -/
theorem exists_intro_free_variable {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (eigen witness : FreeVarId)
    (body : Formula σ) (hBody : Formula.Admissible body) :
    Γ ⊢ₘ[T]
      body⟪sort, eigen ↦ v#[sort, witness]⟫ₘ ⟶ₘ (∃ₘ[sort, eigen], body) :=
  exists_intro_substitute (T := T) (Γ := Γ) (sort := sort) (eigen := eigen) (body := body) (witness := v#[sort, witness])
    (.fvar sort witness) (.fvar sort witness) hBody
/-- 以被关闭的同一自由变量作为 witness 引入存在量词。 -/
theorem exists_intro_self {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (eigen : FreeVarId) (body : Formula σ) (hBody : Formula.Admissible body) :
    Γ ⊢ₘ[T] body ⟶ₘ (∃ₘ[sort, eigen], body) := by
  have hExistential :
      Formula.Admissible (∃ₘ[sort, eigen], body) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBody
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.existsIntro
    (term := v#[sort, eigen])
  simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using
    (FirstOrder.Derives.assumption (T := T)
      (Γ := body :: Γ) (φ := body) (by simp))
/-- 以被关闭的同一自由变量实例化全称量词。 -/
theorem forall_elim_self {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ} (sort : σ.SortSymbol) (eigen : FreeVarId) (body : Formula σ) (hBody : Formula.Admissible body) :
    Γ ⊢ₘ[T] (∀ₘ[sort, eigen], body) ⟶ₘ body := by
  have hUniversalAdmissible :
      Formula.Admissible (∀ₘ[sort, eigen], body) :=
    Formula.Admissible.forall_closeFreeAt sort eigen hBody
  nd_apply FirstOrder.Derives.impIntro
  have hUniversal : ((∀ₘ[sort, eigen], body) :: Γ) ⊢ₘ[T]
        ∀ₘ[sort, eigen], body :=
    .assumption (by simp)
  have hOpened :=
    FirstOrder.Derives.forallElim
      (term := v#[sort, eigen]) hUniversal
  simpa [Formula.openAt_closeFreeAt sort eigen 0 body] using hOpened
/-- 被量化变量不自由出现时，存在量词可以消去。 -/
theorem exists_vacuous_elim {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hBody : Formula.Admissible body) (hFresh : (sort, eigen) freshForₘ body) :
    Γ ⊢ₘ[T] (∃ₘ[sort, eigen], body) ⟶ₘ body := by
  have hExistential :
      Formula.Admissible (∃ₘ[sort, eigen], body) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBody
  apply FirstOrder.Derives.of_empty
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.existsElim
    (T := (Theory.empty : Theory σ))
    (Γ := [∃ₘ[sort, eigen], body]) (sort := sort) (eigen := eigen)
      (body := body) (conclusion := body)
  · intro formula hFormula
    cases hFormula
  · intro formula hFormula
    rcases List.mem_singleton.mp hFormula with rfl
    simpa [Formula.freeSupport] using
      Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
  · exact hFresh
  · exact .assumption (by simp)
  · exact .assumption (by simp)
/-- 被量化变量不自由出现时，存在量词与原公式等价。 -/
theorem exists_vacuous_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hBody : Formula.Admissible body) (hFresh : (sort, eigen) freshForₘ body) :
    Γ ⊢ₘ[T] (∃ₘ[sort, eigen], body) ↔ₘ body := by
  exact .iffIntro (FirstOrder.Derives.imp_elim_assumption (exists_vacuous_elim (T := T) (Γ := Γ)
        hBody hFresh)) (FirstOrder.Derives.imp_elim_assumption (exists_intro_self (T := T) (Γ := Γ)
        sort eigen body hBody))
/-- 被量化变量不自由出现时，全称量词与原公式等价。 -/
theorem forall_vacuous_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hBody : Formula.Admissible body) (hFresh : (sort, eigen) freshForₘ body) :
    Γ ⊢ₘ[T] (∀ₘ[sort, eigen], body) ↔ₘ body := by
  exact .iffIntro (FirstOrder.Derives.imp_elim_assumption (forall_elim_self (T := T) (Γ := Γ)
        sort eigen body hBody)) (FirstOrder.Derives.imp_elim_assumption (FirstOrder.Derives.forall_vacuous_intro (T := T) (Γ := Γ)
        hFresh))
/--
存在量词保持一个对结论变量新鲜的蕴含。
推广到非空理论和上下文时，eigenvariable 也必须对背景新鲜；空背景上的文献定理
由下一条接口直接给出。
-/
theorem exists_imp_of_imp {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body conclusion : Formula σ} (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) freshForₘ formula) (hContextFresh :
      ∀ formula, formula ∈ Γ → (sort, eigen) freshForₘ formula) (hConclusionFresh : (sort, eigen) freshForₘ conclusion) (hImp : Γ ⊢ₘ[T] body ⟶ₘ conclusion) :
    Γ ⊢ₘ[T] (∃ₘ[sort, eigen], body) ⟶ₘ conclusion := by
  have hBody : Formula.Admissible body :=
    Formula.Admissible.imp_left hImp.admissible
  have hExistential :
      Formula.Admissible (∃ₘ[sort, eigen], body) :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBody
  nd_apply FirstOrder.Derives.impIntro
  nd_apply FirstOrder.Derives.existsElim (T := T)
    (Γ := (∃ₘ[sort, eigen], body) :: Γ)
    (sort := sort) (eigen := eigen)
    (body := body) (conclusion := conclusion)
  · exact hTheoryFresh
  · intro formula hFormula
    rcases List.mem_cons.mp hFormula with rfl | hFormula
    · simpa [Formula.freeSupport] using
        Formula.not_mem_freeSupport_closeFreeAt sort eigen 0 body
    · exact hContextFresh formula hFormula
  · exact hConclusionFresh
  · exact .assumption (by simp)
  · have hImp' : (body :: (∃ₘ[sort, eigen], body) :: Γ) ⊢ₘ[T]
          body ⟶ₘ conclusion :=
      FirstOrder.Derives.context_weaken_cons (assumption := body) (FirstOrder.Derives.context_weaken_cons (assumption := ∃ₘ[sort, eigen], body)
          hImp)
    exact .impElim hImp' (.assumption (by simp))
/-- 空背景中的蕴含可按新鲜结论推广到存在前件。 -/
theorem exists_imp_of_theorem {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {body conclusion : Formula σ} (hConclusionFresh : (sort, eigen) freshForₘ conclusion) (hImp : ⊢ₘ body ⟶ₘ conclusion) :
    Γ ⊢ₘ[T] (∃ₘ[sort, eigen], body) ⟶ₘ conclusion := by
  apply FirstOrder.Derives.of_empty
  exact exists_imp_of_imp (T := (Theory.empty : Theory σ)) (Γ := []) (sort := sort) (eigen := eigen) (body := body) (conclusion := conclusion) (by
      intro formula hFormula
      cases hFormula) (by
      intro formula hFormula
      cases hFormula)
    hConclusionFresh hImp
end Derives
end Metatheory
end FirstOrder
end Logic
end YesMetaZFC
