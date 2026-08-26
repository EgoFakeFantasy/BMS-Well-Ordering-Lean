import YesMetaZFC.Logic.FirstOrder.Hilbert.Compilation
import YesMetaZFC.Logic.FirstOrder.Hilbert.Equivalence
/-!
# Hilbert 基本编码的严格双向证明
本模块证明公共联结词与内部 `¬/→/∀/=/原子` 编码之间的基础等价。所有证明都返回
`DerivationEquivalent`，因此既可在自然演绎中按方向使用，也可继续编译成 Hilbert
有限证书。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace DerivationEquivalent
namespace Encoding
/-- 原生真公式与 Hilbert 闭真式严格等价。 -/
theorem truth_hilbert
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {theory : Theory σ} {context : Context σ} :
  DerivationEquivalent theory context
      Formula.truth (Formula.hilbert_truth anchorSort) := by
  constructor
  · nd_apply Derives.imp_intro
    exact ((HilbertDerives.truth (theory := theory) anchorSort).to_derives).context_weaken (by simp)
  · nd_apply Derives.imp_intro
    exact Derives.truth_intro
/-- 原生假公式与 Hilbert 闭假式严格等价。 -/
theorem falsum_hilbert
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {theory : Theory σ} {context : Context σ} :
  DerivationEquivalent theory context
      Formula.falsum (Formula.hilbert_falsum anchorSort) := by
  constructor
  · nd_apply Derives.imp_intro
    nd_apply Derives.falsum_elim
    exact Derives.assumption (by simp)
  · nd_apply Derives.imp_intro
    have hTruth :
        Derives theory (Formula.hilbert_falsum anchorSort :: context) (Formula.hilbert_truth anchorSort) := ((HilbertDerives.truth
        (theory := theory) anchorSort).to_derives).context_weaken (by simp)
    exact Derives.neg_elim hTruth (Derives.assumption (by
          simp [Formula.hilbert_falsum]))
/-- 原生合取与 `¬(φ → ¬ψ)` 严格等价。 -/
theorem conj_hilbert
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hLeft : Formula.Admissible left) (hRight : Formula.Admissible right) :
    DerivationEquivalent theory context (Formula.conj left right) (Formula.hilbert_conj left right) := by
  have hNative :
      Formula.Admissible (Formula.conj left right) :=
    Formula.Admissible.conj hLeft hRight
  have hImpNeg :
      Formula.Admissible (Formula.imp left (Formula.neg right)) :=
    Formula.Admissible.imp hLeft (Formula.Admissible.neg hRight)
  have hEncoded :
      Formula.Admissible (Formula.hilbert_conj left right) :=
    Formula.Admissible.hilbert_conj hLeft hRight
  constructor
  · nd_apply Derives.imp_intro
    nd_apply Derives.neg_intro
    have hConjunction :
        Derives theory (Formula.imp left (Formula.neg right) ::
            Formula.conj left right :: context) (Formula.conj left right) :=
      Derives.assumption (by simp)
    have hImplication :
        Derives theory (Formula.imp left (Formula.neg right) ::
            Formula.conj left right :: context) (Formula.imp left (Formula.neg right)) :=
      Derives.assumption (by simp)
    exact Derives.neg_elim
      hConjunction.conj_elim_right (hImplication.imp_elim hConjunction.conj_elim_left)
  · nd_apply Derives.imp_intro
    have hEncodedProof :
        Derives theory (Formula.hilbert_conj left right :: context) (Formula.hilbert_conj left right) :=
      Derives.assumption (by simp)
    have hLeftProof :
        Derives theory (Formula.hilbert_conj left right :: context) left := by
      nd_apply Derives.by_contradiction
      have hCandidate :
          Derives theory (Formula.neg left ::
              Formula.hilbert_conj left right :: context) (Formula.imp left (Formula.neg right)) := by
        nd_apply Derives.imp_intro
        nd_apply Derives.falsum_elim
        exact Derives.neg_elim (body := left)
          (Derives.assumption (φ := left) (by simp))
          (Derives.assumption (φ := Formula.neg left) (by simp))
      exact Derives.neg_elim hCandidate
        hEncodedProof.context_weaken_cons
    have hRightProof :
        Derives theory (Formula.hilbert_conj left right :: context) right := by
      nd_apply Derives.by_contradiction
      have hCandidate :
          Derives theory (Formula.neg right ::
              Formula.hilbert_conj left right :: context) (Formula.imp left (Formula.neg right)) := by
        nd_apply Derives.imp_intro
        exact Derives.assumption (by simp)
      exact Derives.neg_elim hCandidate
        hEncodedProof.context_weaken_cons
    exact Derives.conj_intro hLeftProof hRightProof
/-- 原生析取与经典 Hilbert 编码 `¬φ → ψ` 严格等价。 -/
theorem disj_hilbert
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hLeft : Formula.Admissible left) (hRight : Formula.Admissible right) :
    DerivationEquivalent theory context (Formula.disj left right) (Formula.imp (Formula.neg left) right) := by
  have hDisjunction :
      Formula.Admissible (Formula.disj left right) :=
    Formula.Admissible.disj hLeft hRight
  have hEncoded :
      Formula.Admissible (Formula.imp (Formula.neg left) right) :=
    Formula.Admissible.imp (Formula.Admissible.neg hLeft) hRight
  constructor
  · nd_apply Derives.imp_intro
    nd_apply Derives.imp_intro
    apply Derives.disj_elim
      (Derives.assumption (φ := Formula.disj left right) (by simp))
    · nd_apply Derives.falsum_elim
      exact Derives.neg_elim (body := left)
        (Derives.assumption (φ := left) (by simp))
        (Derives.assumption (φ := Formula.neg left) (by simp))
    · exact Derives.assumption (φ := right) (by simp)
  · nd_apply Derives.imp_intro
    nd_apply Derives.by_contradiction
    have hNegDisjunction :
        Derives theory (Formula.neg (Formula.disj left right) ::
            Formula.imp (Formula.neg left) right :: context) (Formula.neg (Formula.disj left right)) :=
      Derives.assumption (by simp)
    have hNegLeft :
        Derives theory (Formula.neg (Formula.disj left right) ::
            Formula.imp (Formula.neg left) right :: context) (Formula.neg left) := by
      nd_apply Derives.neg_intro
      have hPositive :
          Derives theory (left ::
              Formula.neg (Formula.disj left right) ::
              Formula.imp (Formula.neg left) right :: context) (Formula.disj left right) :=
        Derives.disj_intro_left (Derives.assumption (by simp))
      exact Derives.neg_elim hPositive
        hNegDisjunction.context_weaken_cons
    have hRightProof :
        Derives theory (Formula.neg (Formula.disj left right) ::
            Formula.imp (Formula.neg left) right :: context)
          right := (Derives.assumption (by simp)).imp_elim hNegLeft
    have hDisjunctionProof :
        Derives theory (Formula.neg (Formula.disj left right) ::
            Formula.imp (Formula.neg left) right :: context) (Formula.disj left right) :=
      Derives.disj_intro_right hRightProof
    exact Derives.neg_elim
      hDisjunctionProof hNegDisjunction
/-- 原生双条件与 Hilbert 编码双条件严格等价。 -/
theorem iff_hilbert
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ}
    {left right : Formula σ} (hLeft : Formula.Admissible left) (hRight : Formula.Admissible right) :
    DerivationEquivalent theory context (Formula.iff left right) (Formula.hilbert_iff left right) := by
  have hNative :=
    DerivationEquivalent.iff_conjunction (theory := theory) (context := context)
      hLeft hRight
  have hEncoded :=
    DerivationEquivalent.Encoding.conj_hilbert (theory := theory) (context := context) (Formula.Admissible.imp hLeft hRight)
      (Formula.Admissible.imp hRight hLeft)
  simpa [Formula.hilbert_iff] using hNative.trans hEncoded
/-- 原生存在量词与经典 Hilbert 编码 `¬∀¬` 严格等价。 -/
theorem exists_hilbert
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {context : Context σ} (sort : σ.SortSymbol) (body : Formula σ) (hExistential :
      Formula.Admissible (Formula.existsE sort body)) :
    DerivationEquivalent theory context (Formula.existsE sort body) (Formula.neg (Formula.forallE sort (Formula.neg body))) := by
  let eigen := FreshVariable.fresh_id sort [body]
  let witness : Term σ := Term.var (.fvar sort eigen)
  let opened : Formula σ :=
    Formula.openAt sort 0 witness body
  have hFresh : (sort, eigen) ∉ Formula.freeSupport body := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m (by simp)
  have hWitness :
      Term.Admissible witness sort :=
    ⟨TermWellSorted.fvar sort eigen,
      TermScoped.fvar sort eigen⟩
  have hOpened :
      Formula.Admissible opened :=
    Formula.Admissible.exists_openAt
      sort hExistential hWitness
  have hEncoded :
      Formula.Admissible (Formula.neg (Formula.forallE sort (Formula.neg body))) :=
    Formula.Admissible.hilbert_exists hExistential
  apply DerivationEquivalent.of_empty
  constructor
  · nd_apply Derives.imp_intro
    nd_apply Derives.neg_intro
    have hExists :
        Derives (Theory.empty : Theory σ)
          [Formula.forallE sort (Formula.neg body),
            Formula.existsE sort body] (Formula.existsE sort (Formula.closeFreeAt sort eigen 0 opened)) := by
      have hOriginal :
          Derives (Theory.empty : Theory σ)
            [Formula.forallE sort (Formula.neg body),
              Formula.existsE sort body] (Formula.existsE sort body) :=
        Derives.assumption (by simp)
      have hClose :
          Formula.closeFreeAt sort eigen 0 opened = body := by
        simpa [opened, witness] using
          Formula.closeFreeAt_openAt
            sort eigen 0 body hFresh
      exact Derives.formula_cast (congrArg (Formula.existsE sort) hClose.symm)
        hOriginal
    nd_apply Derives.existsElim (sort := sort) (eigen := eigen)
      (body := opened) (conclusion := Formula.falsum)
    · intro formula hFormula
      cases hFormula
    · intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · simpa [Formula.freeSupport] using hFresh
      · rcases List.mem_singleton.mp hFormula with rfl
        simpa [Formula.freeSupport] using hFresh
    · simp [Formula.freeSupport]
    · exact hExists
    · have hUniversal :
          Derives (Theory.empty : Theory σ) (opened ::
              Formula.forallE sort (Formula.neg body) ::
              Formula.existsE sort body :: []) (Formula.forallE sort (Formula.neg body)) :=
        Derives.assumption (by simp)
      have hOpenedNeg :=
        Derives.forallElim hUniversal
      have hOpenedNeg' :
          Derives (Theory.empty : Theory σ) (opened ::
              Formula.forallE sort (Formula.neg body) ::
              Formula.existsE sort body :: []) (Formula.neg opened) := by
        simpa [opened, witness, Formula.openAt] using hOpenedNeg
      exact Derives.neg_elim (Derives.assumption (by simp))
        hOpenedNeg'
  · nd_apply Derives.imp_intro
    nd_apply Derives.by_contradiction
    have hNegExists :
        Derives (Theory.empty : Theory σ)
          [Formula.neg (Formula.existsE sort body),
            Formula.neg (Formula.forallE sort (Formula.neg body))] (Formula.neg (Formula.existsE sort body)) :=
      Derives.assumption (by simp)
    have hForallNeg :
        Derives (Theory.empty : Theory σ)
          [Formula.neg (Formula.existsE sort body),
            Formula.neg (Formula.forallE sort (Formula.neg body))] (Formula.forallE sort (Formula.neg body)) := by
      have hOpenedNeg :
          Derives (Theory.empty : Theory σ)
            [Formula.neg (Formula.existsE sort body),
              Formula.neg (Formula.forallE sort (Formula.neg body))] (Formula.neg opened) := by
        nd_apply Derives.neg_intro
        have hExists :
            Derives (Theory.empty : Theory σ) (opened ::
                Formula.neg (Formula.existsE sort body) ::
                Formula.neg (Formula.forallE sort (Formula.neg body)) :: []) (Formula.existsE sort body) :=
          Derives.existsIntro (by
              change Derives (Theory.empty : Theory σ) (opened ::
                  Formula.neg (Formula.existsE sort body) ::
                  Formula.neg (Formula.forallE sort (Formula.neg body)) :: [])
                opened
              exact Derives.assumption (by simp))
        exact Derives.neg_elim hExists
          hNegExists.context_weaken_cons
      have hGeneralized :=
        Derives.forall_intro (T := (Theory.empty : Theory σ)) (Γ :=
            [Formula.neg (Formula.existsE sort body),
              Formula.neg (Formula.forallE sort (Formula.neg body))]) (sort := sort) (eigen := eigen) (body := Formula.neg opened) (by
            intro formula hFormula
            cases hFormula) (by
            intro formula hFormula
            rcases List.mem_cons.mp hFormula with rfl | hFormula
            · simpa [Formula.freeSupport] using hFresh
            · rcases List.mem_singleton.mp hFormula with rfl
              simpa [Formula.freeSupport] using hFresh)
          hOpenedNeg
      have hClose :
          Formula.closeFreeAt sort eigen 0 (Formula.neg opened) =
            Formula.neg body := by
        simp [Formula.closeFreeAt, opened, witness,
          Formula.closeFreeAt_openAt
            sort eigen 0 body hFresh]
      exact Derives.formula_cast (congrArg (Formula.forallE sort) hClose)
        hGeneralized
    exact Derives.neg_elim hForallNeg (Derives.assumption (by simp))
end Encoding
end DerivationEquivalent
end FirstOrder
end Logic
end YesMetaZFC
