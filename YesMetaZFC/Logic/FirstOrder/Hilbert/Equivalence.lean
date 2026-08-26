import YesMetaZFC.Logic.FirstOrder.Derivation
/-!
# 严格自然演绎中的双向可达关系
`DerivationEquivalent T Γ φ ψ` 不把等价性压缩成一个 opaque 派生定理，而是同时保存
`φ → ψ` 与 `ψ → φ` 的严格证书。它是后续 `hilbertize` 反射、定义扩张消去以及
编码前后公式替换的公共中间层。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
/-- 同一背景下两个公式的严格双向可达证书。 -/
structure DerivationEquivalent
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (theory : Theory σ) (context : Context σ) (left right : Formula σ) : Prop where
  forward :
    Derives theory context (Formula.imp left right)
  backward :
    Derives theory context (Formula.imp right left)
namespace DerivationEquivalent
/-- 双向可达自动给出左公式 admissibility。 -/
theorem left_admissible
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hEquivalent : DerivationEquivalent theory context left right) :
    Formula.Admissible left :=
  Formula.Admissible.imp_left hEquivalent.forward.admissible
/-- 双向可达自动给出右公式 admissibility。 -/
theorem right_admissible
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hEquivalent : DerivationEquivalent theory context left right) :
    Formula.Admissible right :=
  Formula.Admissible.imp_right hEquivalent.forward.admissible
/-- 严格双向可达的自反性。 -/
theorem refl
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {formula : Formula σ} (hFormula : Formula.Admissible formula) :
    DerivationEquivalent theory context formula formula :=
  ⟨Derives.Propositional.imp_refl hFormula,
    Derives.Propositional.imp_refl hFormula⟩
/-- 严格双向可达的对称性。 -/
theorem symm
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hEquivalent : DerivationEquivalent theory context left right) :
    DerivationEquivalent theory context right left :=
  ⟨hEquivalent.backward, hEquivalent.forward⟩
/-- 严格双向可达沿上下文包含关系单调。 -/
theorem context_weaken
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {small large : Context σ}
    {left right : Formula σ} (hSubset : ∀ candidate, candidate ∈ small → candidate ∈ large) (hEquivalent : DerivationEquivalent theory small left right) :
    DerivationEquivalent theory large left right :=
  ⟨hEquivalent.forward.context_weaken hSubset,
    hEquivalent.backward.context_weaken hSubset⟩
/-- 严格双向可达沿理论包含关系单调。 -/
theorem theory_weaken
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory stronger : Theory σ} {context : Context σ}
    {left right : Formula σ} (hSubset : ∀ candidate, theory candidate → stronger candidate) (hEquivalent : DerivationEquivalent theory context left right) :
    DerivationEquivalent stronger context left right :=
  ⟨hEquivalent.forward.theory_weaken hSubset,
    hEquivalent.backward.theory_weaken hSubset⟩
/-- 同时扩大理论和上下文。 -/
theorem monotone
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory stronger : Theory σ} {small large : Context σ}
    {left right : Formula σ} (hTheory : ∀ candidate, theory candidate → stronger candidate) (hContext : ∀ candidate, candidate ∈ small → candidate ∈ large)
    (hEquivalent : DerivationEquivalent theory small left right) :
    DerivationEquivalent stronger large left right := (hEquivalent.theory_weaken hTheory).context_weaken hContext
/-- 空背景中的严格等价可用于任意理论和上下文。 -/
theorem of_empty
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hEquivalent :
      DerivationEquivalent (Theory.empty : Theory σ) [] left right) :
    DerivationEquivalent theory context left right :=
  hEquivalent.monotone (by simp [Theory.empty]) (by simp)
/-- 严格双向可达的传递性。 -/
theorem trans
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left middle right : Formula σ} (hLeftMiddle :
      DerivationEquivalent theory context left middle) (hMiddleRight :
      DerivationEquivalent theory context middle right) :
    DerivationEquivalent theory context left right := by
  have hLeftAdmissible := hLeftMiddle.left_admissible
  have hRightAdmissible := hMiddleRight.right_admissible
  constructor
  · nd_apply Derives.imp_intro
    have hLeft :
        Derives theory (left :: context) left :=
      Derives.assumption (by simp)
    have hMiddle :=
      hLeftMiddle.forward.context_weaken_cons.imp_elim hLeft
    exact hMiddleRight.forward.context_weaken_cons.imp_elim hMiddle
  · nd_apply Derives.imp_intro
    have hRight :
        Derives theory (right :: context) right :=
      Derives.assumption (by simp)
    have hMiddle :=
      hMiddleRight.backward.context_weaken_cons.imp_elim hRight
    exact hLeftMiddle.backward.context_weaken_cons.imp_elim hMiddle
/-- 双向蕴含证书合成为原生双条件证明。 -/
theorem to_iff
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hEquivalent : DerivationEquivalent theory context left right) :
    Derives theory context (Formula.iff left right) :=
  Derives.iff_intro
    hEquivalent.forward.imp_elim_assumption
    hEquivalent.backward.imp_elim_assumption
/-- 原生双条件证明展开为严格双向蕴含证书。 -/
theorem of_iff
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hIff :
      Derives theory context (Formula.iff left right)) :
    DerivationEquivalent theory context left right := by
  have hLeft :=
    Formula.Admissible.iff_left hIff.admissible
  have hRight :=
    Formula.Admissible.iff_right hIff.admissible
  constructor
  · nd_apply Derives.imp_intro
    exact Derives.iff_elim_right
      hIff.context_weaken_cons (Derives.assumption (by simp))
  · nd_apply Derives.imp_intro
    exact Derives.iff_elim_left
      hIff.context_weaken_cons (Derives.assumption (by simp))
/-- 否定保持严格双向可达。 -/
theorem neg_congr
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hEquivalent : DerivationEquivalent theory context left right) :
    DerivationEquivalent theory context (Formula.neg left) (Formula.neg right) := by
  have hLeftAdmissible := hEquivalent.left_admissible
  have hRightAdmissible := hEquivalent.right_admissible
  constructor
  · nd_apply Derives.imp_intro
    nd_apply Derives.neg_intro
    have hRight :
        Derives theory (right :: Formula.neg left :: context) right :=
      Derives.assumption (by simp)
    have hLeft := (hEquivalent.backward.context_weaken_prefix (initial := [right, Formula.neg left])).imp_elim hRight
    exact Derives.neg_elim hLeft (Derives.assumption (by simp))
  · nd_apply Derives.imp_intro
    nd_apply Derives.neg_intro
    have hLeft :
        Derives theory (left :: Formula.neg right :: context) left :=
      Derives.assumption (by simp)
    have hRight := (hEquivalent.forward.context_weaken_prefix (initial := [left, Formula.neg right])).imp_elim hLeft
    exact Derives.neg_elim hRight (Derives.assumption (by simp))
/-- 蕴含对前件反变、对后件协变。 -/
theorem imp_congr
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left₁ left₂ right₁ right₂ : Formula σ} (hLeft :
      DerivationEquivalent theory context left₁ left₂) (hRight :
      DerivationEquivalent theory context right₁ right₂) :
    DerivationEquivalent theory context (Formula.imp left₁ right₁) (Formula.imp left₂ right₂) := by
  have hLeft₁Admissible := hLeft.left_admissible
  have hLeft₂Admissible := hLeft.right_admissible
  have hRight₁Admissible := hRight.left_admissible
  have hRight₂Admissible := hRight.right_admissible
  constructor
  · nd_apply Derives.imp_intro
    nd_apply Derives.imp_intro
    have hLeft₂ :
        Derives theory (left₂ :: Formula.imp left₁ right₁ :: context) left₂ :=
      Derives.assumption (by simp)
    have hLeft₁ := (hLeft.backward.context_weaken_prefix (initial := [left₂, Formula.imp left₁ right₁])).imp_elim hLeft₂
    have hImp₁ :
        Derives theory (left₂ :: Formula.imp left₁ right₁ :: context)
          (Formula.imp left₁ right₁) :=
      Derives.assumption (by simp)
    have hRight₁ := hImp₁.imp_elim hLeft₁
    exact (hRight.forward.context_weaken_prefix (initial := [left₂, Formula.imp left₁ right₁])).imp_elim hRight₁
  · nd_apply Derives.imp_intro
    nd_apply Derives.imp_intro
    have hLeft₁ :
        Derives theory (left₁ :: Formula.imp left₂ right₂ :: context) left₁ :=
      Derives.assumption (by simp)
    have hLeft₂ := (hLeft.forward.context_weaken_prefix (initial := [left₁, Formula.imp left₂ right₂])).imp_elim hLeft₁
    have hImp₂ :
        Derives theory (left₁ :: Formula.imp left₂ right₂ :: context)
          (Formula.imp left₂ right₂) :=
      Derives.assumption (by simp)
    have hRight₂ := hImp₂.imp_elim hLeft₂
    exact (hRight.backward.context_weaken_prefix (initial := [left₁, Formula.imp left₂ right₂])).imp_elim hRight₂
/-- 合取逐分量保持严格双向可达。 -/
theorem conj_congr
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left₁ left₂ right₁ right₂ : Formula σ} (hLeft :
      DerivationEquivalent theory context left₁ left₂) (hRight :
      DerivationEquivalent theory context right₁ right₂) :
    DerivationEquivalent theory context (Formula.conj left₁ right₁) (Formula.conj left₂ right₂) := by
  have hLeft₁Admissible := hLeft.left_admissible
  have hLeft₂Admissible := hLeft.right_admissible
  have hRight₁Admissible := hRight.left_admissible
  have hRight₂Admissible := hRight.right_admissible
  constructor
  · nd_apply Derives.imp_intro
    have hSource :
        Derives theory (Formula.conj left₁ right₁ :: context) (Formula.conj left₁ right₁) :=
      Derives.assumption (by simp)
    exact Derives.conj_intro (hLeft.forward.context_weaken_cons.imp_elim
        hSource.conj_elim_left) (hRight.forward.context_weaken_cons.imp_elim
        hSource.conj_elim_right)
  · nd_apply Derives.imp_intro
    have hSource :
        Derives theory (Formula.conj left₂ right₂ :: context) (Formula.conj left₂ right₂) :=
      Derives.assumption (by simp)
    exact Derives.conj_intro (hLeft.backward.context_weaken_cons.imp_elim
        hSource.conj_elim_left) (hRight.backward.context_weaken_cons.imp_elim
        hSource.conj_elim_right)
/-- 析取逐分量保持严格双向可达。 -/
theorem disj_congr
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left₁ left₂ right₁ right₂ : Formula σ} (hLeft :
      DerivationEquivalent theory context left₁ left₂) (hRight :
      DerivationEquivalent theory context right₁ right₂) :
    DerivationEquivalent theory context (Formula.disj left₁ right₁) (Formula.disj left₂ right₂) := by
  have hLeft₁Admissible := hLeft.left_admissible
  have hLeft₂Admissible := hLeft.right_admissible
  have hRight₁Admissible := hRight.left_admissible
  have hRight₂Admissible := hRight.right_admissible
  constructor
  · nd_apply Derives.imp_intro
    apply Derives.disj_elim (left := left₁) (right := right₁)
      (Derives.assumption (by simp))
    · exact Derives.disj_intro_left
        ((hLeft.forward.context_weaken_prefix (initial := [left₁,
              Formula.disj left₁ right₁])).imp_elim
          (Derives.assumption (by simp)))
    · exact Derives.disj_intro_right
        ((hRight.forward.context_weaken_prefix (initial := [right₁,
              Formula.disj left₁ right₁])).imp_elim
          (Derives.assumption (by simp)))
  · nd_apply Derives.imp_intro
    apply Derives.disj_elim (left := left₂) (right := right₂)
      (Derives.assumption (by simp))
    · exact Derives.disj_intro_left
        ((hLeft.backward.context_weaken_prefix (initial := [left₂,
              Formula.disj left₂ right₂])).imp_elim
          (Derives.assumption (by simp)))
    · exact Derives.disj_intro_right
        ((hRight.backward.context_weaken_prefix (initial := [right₂,
              Formula.disj left₂ right₂])).imp_elim
          (Derives.assumption (by simp)))
/-- 原生双条件等价于两个方向蕴含的原生合取。 -/
theorem iff_conjunction
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hLeft : Formula.Admissible left) (hRight : Formula.Admissible right) :
    DerivationEquivalent theory context (Formula.iff left right) (Formula.conj (Formula.imp left right) (Formula.imp right left)) := by
  constructor
  · nd_apply Derives.imp_intro
    have hIff :
        Derives theory (Formula.iff left right :: context) (Formula.iff left right) :=
      Derives.assumption (by simp)
    exact Derives.conj_intro ((DerivationEquivalent.of_iff hIff).forward) ((DerivationEquivalent.of_iff hIff).backward)
  · nd_apply Derives.imp_intro
    have hConj :
        Derives theory (Formula.conj (Formula.imp left right) (Formula.imp right left) :: context) (Formula.conj (Formula.imp left right)
            (Formula.imp right left)) :=
      Derives.assumption (by simp)
    exact Derives.iff_intro
      hConj.conj_elim_left.imp_elim_assumption
      hConj.conj_elim_right.imp_elim_assumption
/-- 原生双条件逐分量保持严格双向可达。 -/
theorem iff_congr
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left₁ left₂ right₁ right₂ : Formula σ} (hLeft :
      DerivationEquivalent theory context left₁ left₂) (hRight :
      DerivationEquivalent theory context right₁ right₂) :
    DerivationEquivalent theory context (Formula.iff left₁ right₁) (Formula.iff left₂ right₂) := by
  have hForwardImp :=
    imp_congr hLeft hRight
  have hBackwardImp :=
    imp_congr hRight hLeft
  have hConjunction :=
    conj_congr hForwardImp hBackwardImp
  have hLeftIff :=
    iff_conjunction (theory := theory) (context := context)
      hLeft.left_admissible hRight.left_admissible
  have hRightIff :=
    iff_conjunction (theory := theory) (context := context)
      hLeft.right_admissible hRight.right_admissible
  exact hLeftIff.trans (hConjunction.trans hRightIff.symm)
/--
打开同一个 eigenvariable 后严格等价的两个量词体，其全称闭包严格等价。
背景新鲜性显式保留，因此该接口既能用于空背景逻辑定理，也能用于带参数理论的
定义扩张。
-/
theorem forall_congr_open
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Formula σ} (hTheoryFresh :
      ∀ formula, theory formula → (sort, eigen) ∉ Formula.freeSupport formula) (hContextFresh :
      ∀ formula, formula ∈ context → (sort, eigen) ∉ Formula.freeSupport formula) (hLeftForall :
      Formula.Admissible (Formula.forallE sort left)) (hRightForall :
      Formula.Admissible (Formula.forallE sort right)) (hLeftFresh : (sort, eigen) ∉ Formula.freeSupport left) (hRightFresh :
      (sort, eigen) ∉ Formula.freeSupport right) (hOpened :
      DerivationEquivalent theory context (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left) (Formula.openAt sort 0
          (Term.var (.fvar sort eigen)) right)) :
    DerivationEquivalent theory context (Formula.forallE sort left) (Formula.forallE sort right) := by
  have hTerm :
      Term.Admissible (Term.var (.fvar sort eigen)) sort :=
    ⟨TermWellSorted.fvar sort eigen,
      TermScoped.fvar sort eigen⟩
  constructor
  · nd_apply Derives.imp_intro
    have hUniversal :
        Derives theory (Formula.forallE sort left :: context) (Formula.forallE sort left) :=
      Derives.assumption (by simp)
    have hOpenedLeft :=
      Derives.forall_elim
        (term := Term.var (.fvar sort eigen)) hUniversal
    have hOpenedRight :=
      hOpened.forward.context_weaken_cons.imp_elim hOpenedLeft
    have hGeneralized :=
      Derives.forall_intro (T := theory) (Γ := Formula.forallE sort left :: context) (sort := sort) (eigen := eigen)
        hTheoryFresh (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with rfl | hFormula
          · simpa [Formula.freeSupport] using hLeftFresh
          · exact hContextFresh formula hFormula)
        hOpenedRight
    have hClose :
        Formula.closeFreeAt sort eigen 0 (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right) =
          right :=
      Formula.closeFreeAt_openAt
        sort eigen 0 right hRightFresh
    exact Derives.formula_cast (congrArg (Formula.forallE sort) hClose)
      hGeneralized
  · nd_apply Derives.imp_intro
    have hUniversal :
        Derives theory (Formula.forallE sort right :: context) (Formula.forallE sort right) :=
      Derives.assumption (by simp)
    have hOpenedRight :=
      Derives.forall_elim
        (term := Term.var (.fvar sort eigen)) hUniversal
    have hOpenedLeft :=
      hOpened.backward.context_weaken_cons.imp_elim hOpenedRight
    have hGeneralized :=
      Derives.forall_intro (T := theory) (Γ := Formula.forallE sort right :: context) (sort := sort) (eigen := eigen)
        hTheoryFresh (by
          intro formula hFormula
          rcases List.mem_cons.mp hFormula with rfl | hFormula
          · simpa [Formula.freeSupport] using hRightFresh
          · exact hContextFresh formula hFormula)
        hOpenedLeft
    have hClose :
        Formula.closeFreeAt sort eigen 0 (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left) =
          left :=
      Formula.closeFreeAt_openAt
        sort eigen 0 left hLeftFresh
    exact Derives.formula_cast (congrArg (Formula.forallE sort) hClose)
      hGeneralized
/-- 打开后严格等价的两个量词体，其存在闭包严格等价。 -/
theorem exists_congr_open
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId}
    {left right : Formula σ} (hTheoryFresh :
      ∀ formula, theory formula → (sort, eigen) ∉ Formula.freeSupport formula) (hContextFresh :
      ∀ formula, formula ∈ context → (sort, eigen) ∉ Formula.freeSupport formula) (hLeftExists :
      Formula.Admissible (Formula.existsE sort left)) (hRightExists :
      Formula.Admissible (Formula.existsE sort right)) (hLeftFresh : (sort, eigen) ∉ Formula.freeSupport left) (hRightFresh :
      (sort, eigen) ∉ Formula.freeSupport right) (hOpened :
      DerivationEquivalent theory context (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left) (Formula.openAt sort 0
          (Term.var (.fvar sort eigen)) right)) :
    DerivationEquivalent theory context (Formula.existsE sort left) (Formula.existsE sort right) := by
  have hTerm :
      Term.Admissible (Term.var (.fvar sort eigen)) sort :=
    ⟨TermWellSorted.fvar sort eigen,
      TermScoped.fvar sort eigen⟩
  have hOpenedLeft :
      Formula.Admissible (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left) :=
    Formula.Admissible.exists_openAt
      sort hLeftExists hTerm
  have hOpenedRight :
      Formula.Admissible (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right) :=
    Formula.Admissible.exists_openAt
      sort hRightExists hTerm
  constructor
  · nd_apply Derives.imp_intro
    have hOriginal :
        Derives theory (Formula.existsE sort left :: context) (Formula.existsE sort left) :=
      Derives.assumption (by simp)
    have hCloseLeft :
        Formula.closeFreeAt sort eigen 0 (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left) =
          left :=
      Formula.closeFreeAt_openAt
        sort eigen 0 left hLeftFresh
    have hExists :
        Derives theory (Formula.existsE sort left :: context) (Formula.existsE sort (Formula.closeFreeAt sort eigen 0 (Formula.openAt sort 0
                (Term.var (.fvar sort eigen)) left))) :=
      Derives.formula_cast (congrArg (Formula.existsE sort) hCloseLeft.symm)
        hOriginal
    nd_apply Derives.exists_elim (sort := sort) (eigen := eigen) (body :=
          Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left) (conclusion := Formula.existsE sort right)
    · exact hTheoryFresh
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · simpa [Formula.freeSupport] using hLeftFresh
      · exact hContextFresh formula hFormula
    · simpa [Formula.freeSupport] using hRightFresh
    · exact hExists
    · have hLeftProof :
          Derives theory (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left ::
              Formula.existsE sort left :: context) (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left) :=
        Derives.assumption (by simp)
      have hRightProof := (hOpened.forward.context_weaken_prefix (initial :=
            [Formula.openAt sort 0 (Term.var (.fvar sort eigen)) left,
              Formula.existsE sort left])).imp_elim hLeftProof
      exact Derives.exists_intro
        (term := Term.var (.fvar sort eigen)) hRightProof
  · nd_apply Derives.imp_intro
    have hOriginal :
        Derives theory (Formula.existsE sort right :: context) (Formula.existsE sort right) :=
      Derives.assumption (by simp)
    have hCloseRight :
        Formula.closeFreeAt sort eigen 0 (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right) =
          right :=
      Formula.closeFreeAt_openAt
        sort eigen 0 right hRightFresh
    have hExists :
        Derives theory (Formula.existsE sort right :: context) (Formula.existsE sort (Formula.closeFreeAt sort eigen 0 (Formula.openAt sort 0
                (Term.var (.fvar sort eigen)) right))) :=
      Derives.formula_cast (congrArg (Formula.existsE sort) hCloseRight.symm)
        hOriginal
    nd_apply Derives.exists_elim (sort := sort) (eigen := eigen) (body :=
          Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right) (conclusion := Formula.existsE sort left)
    · exact hTheoryFresh
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · simpa [Formula.freeSupport] using hRightFresh
      · exact hContextFresh formula hFormula
    · simpa [Formula.freeSupport] using hLeftFresh
    · exact hExists
    · have hRightProof :
          Derives theory (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right ::
              Formula.existsE sort right :: context) (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right) :=
        Derives.assumption (by simp)
      have hLeftProof := (hOpened.backward.context_weaken_prefix (initial :=
            [Formula.openAt sort 0 (Term.var (.fvar sort eigen)) right,
              Formula.existsE sort right])).imp_elim hRightProof
      exact Derives.exists_intro
        (term := Term.var (.fvar sort eigen)) hLeftProof
end DerivationEquivalent
end FirstOrder
end Logic
end YesMetaZFC
