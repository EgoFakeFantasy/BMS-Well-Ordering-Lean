import YesMetaZFC.Logic.FirstOrder.Hilbert.Equality
/-!
# `Derives` 到标准 Hilbert 证明的编译
本模块把理论与有限局部上下文统一翻译成 Hilbert 理论，并直接按内生合法的
`Derives` 证明树编译标准 Hilbert 推导。所有量词与等词所需的 sort、闭项和公式
合法性信息都由 `Derives` 构造器携带，不再另设事后“可编译性”判断。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Theory
/-- 把原理论和有限局部上下文一并翻译成 Hilbert 理论。 -/
def hilbertize_context {σ : Signature.{u, v, w}} (anchorSort : σ.SortSymbol) (theory : Theory σ) :
    Context σ → Theory σ
  | [] => Theory.hilbertize anchorSort theory
  | formula :: context =>
      Theory.insert (Formula.hilbertize anchorSort formula) (hilbertize_context anchorSort theory context)
/-- Hilbert 化理论成员的来源恰为原理论或局部上下文。 -/
theorem mem_hilbertize_context_iff {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ}
    {context : Context σ} {encoded : Formula σ} :
    hilbertize_context anchorSort theory context encoded ↔
      ∃ source, (theory source ∨ source ∈ context) ∧
          encoded = Formula.hilbertize anchorSort source := by
  induction context with
  | nil =>
      constructor
      · rintro ⟨source, hTheory, rfl⟩
        exact ⟨source, Or.inl hTheory, rfl⟩
      · rintro ⟨source, hSource, rfl⟩
        rcases hSource with hTheory | hContext
        · exact ⟨source, hTheory, rfl⟩
        · cases hContext
  | cons head tail ih =>
      constructor
      · intro hEncoded
        rcases hEncoded with hHead | hTail
        · exact ⟨head, Or.inr (by simp), hHead⟩
        · rcases ih.mp hTail with ⟨source, hSource, hEq⟩
          exact ⟨source, hSource.elim Or.inl (fun hMem => Or.inr (by simp [hMem])), hEq⟩
      · rintro ⟨source, hSource, hEq⟩
        rcases hSource with hTheory | hContext
        · exact Or.inr (ih.mpr ⟨source, Or.inl hTheory, hEq⟩)
        · rcases List.mem_cons.mp hContext with rfl | hTail
          · exact Or.inl hEq
          · exact Or.inr (ih.mpr ⟨source, Or.inr hTail, hEq⟩)
/-- 原理论公理进入合并后的 Hilbert 理论。 -/
theorem hilbertize_context_mem_theory {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ}
    {context : Context σ} {formula : Formula σ} (hTheory : theory formula) :
    hilbertize_context anchorSort theory context (Formula.hilbertize anchorSort formula) :=
  mem_hilbertize_context_iff.mpr
    ⟨formula, Or.inl hTheory, rfl⟩
/-- 局部假设进入合并后的 Hilbert 理论。 -/
theorem hilbertize_context_mem_context {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ}
    {context : Context σ} {formula : Formula σ} (hContext : formula ∈ context) :
    hilbertize_context anchorSort theory context (Formula.hilbertize anchorSort formula) :=
  mem_hilbertize_context_iff.mpr
    ⟨formula, Or.inr hContext, rfl⟩
/-- 原理论与上下文同时扩大时，Hilbert 化理论保持包含关系。 -/
theorem hilbertize_context_mono {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory stronger : Theory σ}
    {context larger : Context σ} (hTheory : ∀ formula, theory formula → stronger formula) (hContext : ∀ formula, formula ∈ context → formula ∈ larger) :
    ∀ encoded,
      hilbertize_context anchorSort theory context encoded →
        hilbertize_context anchorSort stronger larger encoded := by
  intro encoded hEncoded
  rcases mem_hilbertize_context_iff.mp hEncoded with
    ⟨source, hSource, hEq⟩
  apply mem_hilbertize_context_iff.mpr
  exact ⟨source, hSource.elim (fun h => Or.inl (hTheory source h)) (fun h => Or.inr (hContext source h)), hEq⟩
/-- 理论和上下文的新鲜条件穿过 Hilbert 化。 -/
theorem hilbertize_context_fresh {σ : Signature.{u, v, w}}
    {anchorSort sort : σ.SortSymbol} {eigen : FreeVarId}
    {theory : Theory σ} {context : Context σ} (hTheoryFresh :
      ∀ formula, theory formula → (sort, eigen) ∉ Formula.freeSupport formula) (hContextFresh :
      ∀ formula, formula ∈ context → (sort, eigen) ∉ Formula.freeSupport formula) :
    ∀ encoded,
      hilbertize_context anchorSort theory context encoded → (sort, eigen) ∉ Formula.freeSupport encoded := by
  intro encoded hEncoded
  rcases mem_hilbertize_context_iff.mp hEncoded with
    ⟨source, hSource, rfl⟩
  intro hMember
  have hSourceMember := (Formula.mem_freeSupport_hilbertize_iff
      anchorSort (sort, eigen) source).mp hMember
  exact hSource.elim (fun h => hTheoryFresh source h hSourceMember) (fun h => hContextFresh source h hSourceMember)
/-- 合并理论已完全处于 Hilbert 归约像中，再次归约可收缩回原理论。 -/
theorem hilbertize_hilbertize_context_subset
    {σ : Signature.{u, v, w}}
    {anchorSort : σ.SortSymbol} {theory : Theory σ}
    {context : Context σ} :
    ∀ encoded,
      Theory.hilbertize anchorSort (hilbertize_context anchorSort theory context) encoded →
        hilbertize_context anchorSort theory context encoded := by
  intro encoded hEncoded
  rcases hEncoded with ⟨middle, hMiddle, rfl⟩
  rcases mem_hilbertize_context_iff.mp hMiddle with
    ⟨source, hSource, rfl⟩
  rw [Formula.hilbertize_idempotent]
  exact mem_hilbertize_context_iff.mpr
    ⟨source, hSource, rfl⟩
end Theory
namespace ND_Raw
/--
通过整树检查的自然演绎原始树可以逐构造编译为标准 Hilbert 推导。
理论公理与局部假设统一进入 `Theory.hilbertize_context`；量词与等词分支需要的
合法性信息直接从节点检查等式恢复。
-/
theorem to_hilbert {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {theory : Theory σ} {context : Context σ}
    {formula : Formula σ} (raw : ND_Raw theory context formula) :
    raw.check = true →
      HilbertDerives
        (Theory.hilbertize_context anchorSort theory context)
        (Formula.hilbertize anchorSort formula) := by
  induction raw with
  | assumption hMem =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact .theory_axiom
        (Theory.hilbertize_context_mem_context hMem)
        (Formula.Admissible.hilbertize
          (Formula.check_admissible_sound hCheck.1))
  | theoryAxiom hMem =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact .theory_axiom
        (Theory.hilbertize_context_mem_theory hMem)
        (Formula.Admissible.hilbertize
          (Formula.check_admissible_sound hCheck.1))
  | contextWeakening hSubset hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact (ih hCheck.2).theory_weakening
        (Theory.hilbertize_context_mono
          (fun _ hTheory => hTheory) hSubset)
  | theoryWeakening hSubset hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact (ih hCheck.2).theory_weakening
        (Theory.hilbertize_context_mono hSubset
          (fun _ hContext => hContext))
  | truthIntro =>
      intro _
      change HilbertDerives _ (Formula.hilbert_truth anchorSort)
      exact HilbertDerives.truth anchorSort
  | falsumElim hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact HilbertDerives.falsum_elim anchorSort
        (Formula.Admissible.hilbertize
          (Formula.check_admissible_sound hCheck.1))
        (ih hCheck.2)
  | conjIntro hLeft hRight ihLeft ihRight =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with ⟨⟨_, hLeftCheck⟩, hRightCheck⟩
      simpa [Formula.hilbertize] using
        (HilbertDerives.conj_intro anchorSort
          (ihLeft hLeftCheck) (ihRight hRightCheck))
  | conjElimLeft hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact HilbertDerives.conj_elim_left anchorSort
        (ih hCheck.2)
  | conjElimRight hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact HilbertDerives.conj_elim_right anchorSort
        (ih hCheck.2)
  | disjIntroLeft hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      have hDisjunction :=
        Formula.check_admissible_sound hCheck.1
      exact HilbertDerives.disj_intro_left
        (Formula.Admissible.hilbertize hDisjunction.disj_right)
        (ih hCheck.2)
  | disjIntroRight hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      have hDisjunction :=
        Formula.check_admissible_sound hCheck.1
      exact HilbertDerives.disj_intro_right
        (Formula.Admissible.hilbertize hDisjunction.disj_left)
        (ih hCheck.2)
  | disjElim hDisjunction hLeft hRight
      ihDisjunction ihLeft ihRight =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨⟨_, hDisjunctionCheck⟩, hLeftCheck⟩, hRightCheck⟩
      exact HilbertDerives.disj_elim
        (ihDisjunction hDisjunctionCheck)
        (ihLeft hLeftCheck) (ihRight hRightCheck)
  | impIntro hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      have hImplication :=
        Formula.check_admissible_sound hCheck.1
      exact HilbertDerives.deduction
        (Formula.Admissible.hilbertize hImplication.imp_left)
        (ih hCheck.2)
  | impElim hImplication hAntecedent
      ihImplication ihAntecedent =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨_, hImplicationCheck⟩, hAntecedentCheck⟩
      exact .modus_ponens
        (ihAntecedent hAntecedentCheck)
        (ihImplication hImplicationCheck)
  | iffIntro hForward hBackward ihForward ihBackward =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨_, hForwardCheck⟩, hBackwardCheck⟩
      exact HilbertDerives.iff_intro anchorSort
        (ihForward hForwardCheck) (ihBackward hBackwardCheck)
  | iffElimLeft hIff hRight ihIff ihRight =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with ⟨⟨_, hIffCheck⟩, hRightCheck⟩
      exact HilbertDerives.iff_elim_left anchorSort
        (ihIff hIffCheck) (ihRight hRightCheck)
  | iffElimRight hIff hLeft ihIff ihLeft =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with ⟨⟨_, hIffCheck⟩, hLeftCheck⟩
      exact HilbertDerives.iff_elim_right anchorSort
        (ihIff hIffCheck) (ihLeft hLeftCheck)
  | negIntro hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      have hNegation :=
        Formula.check_admissible_sound hCheck.1
      exact HilbertDerives.neg_intro anchorSort
        (Formula.Admissible.hilbertize hNegation.neg_body)
        (ih hCheck.2)
  | negElim hBody hNegation ihBody ihNegation =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with ⟨⟨_, hBodyCheck⟩, hNegationCheck⟩
      exact HilbertDerives.neg_elim
        (Formula.Admissible.hilbert_falsum anchorSort)
        (ihBody hBodyCheck) (ihNegation hNegationCheck)
  | byContradiction hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      exact HilbertDerives.by_contradiction anchorSort
        (Formula.Admissible.hilbertize
          (Formula.check_admissible_sound hCheck.1))
        (ih hCheck.2)
  | @forallIntro theory context sort eigen body
      hTheoryFresh hContextFresh hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      have hFresh :=
        Theory.hilbertize_context_fresh (anchorSort := anchorSort)
          hTheoryFresh hContextFresh
      simpa [Formula.hilbertize,
        Formula.hilbertize_closeFreeAt] using
          (HilbertDerives.forall_closure sort eigen hFresh
            (ih hCheck.2))
  | @forallElim theory context sort body term
      hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨_, hTermCheck⟩, hDerivationCheck⟩
      have hTerm :=
        Term.check_admissible_sound hTermCheck
      simpa [Formula.hilbertize,
        Formula.hilbertize_openAt] using
          (HilbertDerives.forall_elim_m
            hTerm.1 hTerm.2 (ih hDerivationCheck))
  | @existsIntro theory context sort body term
      hDerivation ih =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨hExistentialCheck, hTermCheck⟩, hDerivationCheck⟩
      have hTerm :=
        Term.check_admissible_sound hTermCheck
      have hExistential :=
        Formula.check_admissible_sound hExistentialCheck
      have hBody :
          HilbertDerives
            (Theory.hilbertize_context anchorSort theory context)
            (Formula.openAt sort 0 term
              (Formula.hilbertize anchorSort body)) := by
        simpa [Formula.hilbertize_openAt] using
          (ih hDerivationCheck)
      exact HilbertDerives.exists_intro_m anchorSort
        hTerm.1 hTerm.2
        (Formula.Admissible.hilbertize hExistential) hBody
  | @existsElim theory context sort eigen body conclusion
      hTheoryFresh hContextFresh hConclusionFresh
      hExists hCase ihExists ihCase =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨⟨_, hBodyCheck⟩, hExistsCheck⟩, hCaseCheck⟩
      have hFresh :=
        Theory.hilbertize_context_fresh (anchorSort := anchorSort)
          hTheoryFresh hContextFresh
      have hConclusionFresh' : (sort, eigen) ∉
            Formula.freeSupport
              (Formula.hilbertize anchorSort conclusion) := by
        intro hMember
        exact hConclusionFresh
          ((Formula.mem_freeSupport_hilbertize_iff
            anchorSort (sort, eigen) conclusion).mp hMember)
      have hExists' :
          HilbertDerives
            (Theory.hilbertize_context anchorSort theory context)
            (Formula.neg
              (Formula.forallE sort
                (Formula.neg
                  (Formula.closeFreeAt sort eigen 0
                    (Formula.hilbertize anchorSort body))))) := by
        simpa [Formula.hilbertize,
          Formula.hilbertize_closeFreeAt] using
            (ihExists hExistsCheck)
      exact HilbertDerives.exists_elim_m
        anchorSort sort eigen hFresh hConclusionFresh'
        (Formula.Admissible.hilbertize
          (Formula.check_admissible_sound hBodyCheck))
        hExists' (ihCase hCaseCheck)
  | equalityRefl sort =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      have hTerm :=
        Term.check_admissible_sound hCheck.2
      exact HilbertDerives.equality_refl _ hTerm.1 hTerm.2
  | @equalityElim theory context sort eigen left right body
      hEquality hBody ihEquality ihBody =>
      intro hCheck
      simp only [check, Bool.and_eq_true_iff] at hCheck
      rcases hCheck with
        ⟨⟨⟨⟨⟨_, hLeftCheck⟩, hRightCheck⟩, hBodyCheck⟩,
          hEqualityCheck⟩, hDerivationCheck⟩
      have hLeft :=
        Term.check_admissible_sound hLeftCheck
      have hRight :=
        Term.check_admissible_sound hRightCheck
      have hBody' :
          HilbertDerives
            (Theory.hilbertize_context anchorSort theory context)
            (Formula.substituteFree sort eigen left
              (Formula.hilbertize anchorSort body)) := by
        simpa [Formula.hilbertize_substituteFree] using
          (ihBody hDerivationCheck)
      simpa [Formula.hilbertize_substituteFree] using
        (HilbertDerives.equality_elim
          hLeft.1 hRight.1 hLeft.2 hRight.2
          (Formula.Admissible.hilbertize
            (Formula.check_admissible_sound hBodyCheck))
          (ihEquality hEqualityCheck) hBody')

end ND_Raw

namespace Derives

/-- checked 自然演绎证书的公共 Hilbert 编译接口。 -/
theorem to_hilbert {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {theory : Theory σ} {context : Context σ}
    {formula : Formula σ} (hDerives : Derives theory context formula) :
    HilbertDerives
      (Theory.hilbertize_context anchorSort theory context)
      (Formula.hilbertize anchorSort formula) := by
  rcases hDerives with ⟨cert⟩
  exact cert.raw.to_hilbert anchorSort cert.checked
/-- 编译结果可线性化为以翻译目标为末行的标准有限 Hilbert 证明。 -/
theorem exists_finite_hilbert_proof
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {theory : Theory σ} {context : Context σ}
    {formula : Formula σ} (hDerives : Derives theory context formula) :
    ∃ initial,
      HilbertProof (Theory.hilbertize_context anchorSort theory context) (initial ++ [Formula.hilbertize anchorSort formula]) :=
  HilbertProof.exists_finite (hDerives.to_hilbert anchorSort)
/--
已经处于 Hilbert 归约像中的自然演绎证明，可回到同一个 Hilbert 理论和目标；
二次归约由 `Formula.hilbertize` 的幂等性消去。
-/
theorem normalized_to_hilbert
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {sourceTheory : Theory σ} {sourceContext : Context σ}
    {sourceFormula : Formula σ} (hDerives :
      Derives (Theory.hilbertize_context
          anchorSort sourceTheory sourceContext)
        [] (Formula.hilbertize anchorSort sourceFormula)) :
    HilbertDerives (Theory.hilbertize_context
        anchorSort sourceTheory sourceContext) (Formula.hilbertize anchorSort sourceFormula) := by
  have hEncoded := hDerives.to_hilbert anchorSort
  have hCollapsed := hEncoded.theory_weakening (Theory.hilbertize_hilbertize_context_subset (anchorSort := anchorSort)
      (theory := sourceTheory) (context := sourceContext))
  simpa [Theory.hilbertize_context] using hCollapsed
/-- 归约像中的自然演绎证明也给出同理论上的标准有限 Hilbert 列表。 -/
theorem normalized_exists_finite_hilbert_proof
    {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (anchorSort : σ.SortSymbol)
    {sourceTheory : Theory σ} {sourceContext : Context σ}
    {sourceFormula : Formula σ} (hDerives :
      Derives (Theory.hilbertize_context
          anchorSort sourceTheory sourceContext)
        [] (Formula.hilbertize anchorSort sourceFormula)) :
    ∃ initial,
      HilbertProof (Theory.hilbertize_context
          anchorSort sourceTheory sourceContext) (initial ++ [Formula.hilbertize anchorSort sourceFormula]) :=
  HilbertProof.exists_finite (hDerives.normalized_to_hilbert anchorSort)
end Derives
/-- 标准有限 Hilbert 列表可以无条件回放为归约像上的公共 `Derives`。 -/
theorem HilbertProof.to_normalized_derives
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {anchorSort : σ.SortSymbol} {sourceTheory : Theory σ}
    {sourceContext : Context σ} {sourceFormula : Formula σ}
    {initial : List (Formula σ)} (hProof :
      HilbertProof (Theory.hilbertize_context
          anchorSort sourceTheory sourceContext) (initial ++ [Formula.hilbertize anchorSort sourceFormula])) :
    Derives (Theory.hilbertize_context
        anchorSort sourceTheory sourceContext)
      [] (Formula.hilbertize anchorSort sourceFormula) := (hProof.derives_of_mem (by simp)).to_derives
end FirstOrder
end Logic
end YesMetaZFC
