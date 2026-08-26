import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Hilbertization
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Substitution.Induction
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency

/-!
# 函数图消去的 Hilbert 推导翻译

本模块把完整公式编译提升到 Hilbert 推导树。逻辑公理的命题分支由编译同态直接
保持；量词分支统一通过公开的 binder 归一化与 substitution 合同处理。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT
namespace FunctionGraphElimination

universe u v w

set_option autoImplicit false

variable
  {σ : Signature.{u, v, w}}
  [DecidableEq σ.SortSymbol]
  [DecidableEq σ.FuncSymbol]
  {D : Data σ}

/--
单排序语言中的函数图编译保持闭句性。

编译器把源自由变量送入奇数区，把局部图见证送入偶数区；单排序假设使这两个
新鲜性不变量覆盖编译公式的全部自由变量编号。
-/
theorem formula_sentence_of_single_sort
    (D : Data σ)
    (hSort : ∀ sort, sort = D.sort)
    {source : Formula σ}
    (hSource : Formula.Sentence source) :
    Formula.Sentence (formula D source) := by
  constructor
  · exact formula_admissible D hSource.1
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro entry hEntry
    rcases entry with ⟨sort, id⟩
    have hSortEq := hSort sort
    subst sort
    by_cases hEven : id % 2 = 0
    · have hId :
          id = witness_id (id / 2) := by
        have hDivision := Nat.mod_add_div id 2
        simpa [witness_id, hEven] using
          hDivision.symm
      rw [hId] at hEntry
      exact formula_witness_fresh
        D source (id / 2) hEntry
    · have hOdd : id % 2 = 1 := by
        have hRemainder := Nat.mod_lt id
          (by decide : 0 < 2)
        exact Nat.le_antisymm
          (Nat.le_of_lt_succ hRemainder)
          (Nat.one_le_iff_ne_zero.mpr hEven)
      have hId :
          id = source_id (id / 2) := by
        have hDivision := Nat.mod_add_div id 2
        simpa [source_id, hOdd,
          Nat.add_comm] using hDivision.symm
      have hSourceFresh :
          (D.sort, id / 2) ∉
            Formula.freeSupport source := by
        rw [hSource.2]
        exact List.not_mem_nil
      rw [hId] at hEntry
      exact formula_compiled_source_fresh
        D D.sort (id / 2) source
          hSourceFresh hEntry

namespace GraphPresentation

/-- 图理论由闭句组成，因此任意自由变量均可用于全称化。 -/
private theorem theory_fresh
    (P : GraphPresentation D)
    (sort : σ.SortSymbol) (id : FreeVarId) :
    ∀ formula, P.theory formula →
      (sort, id) ∉ Formula.freeSupport formula := by
  intro formula hFormula
  rw [(P.theory_sentence hFormula).2]
  exact List.not_mem_nil

/--
已证明的开放编译公式可沿一个源自由变量闭合。编译器把源变量送到奇数区，
因此先在 `source_id id` 处全称化，再由 binder 合同回到源公式的编译像。
-/
theorem formula_forall_close_derives
    (P : GraphPresentation D)
    (sort : σ.SortSymbol) (id : FreeVarId)
    (source : Formula σ)
    (hSource : Formula.Admissible source)
    (hCompiled :
      Derives P.theory [] (formula D source)) :
    Derives P.theory []
      (formula D
        (Formula.forallE sort
          (Formula.closeFreeAt sort id 0 source))) := by
  have hClosed :
      Derives P.theory []
        (Formula.forallE sort
          (Formula.closeFreeAt sort
            (source_id id) 0
            (formula D source))) := by
    apply Derives.forall_intro
    · exact P.theory_fresh sort (source_id id)
    · intro formula hFormula
      cases hFormula
    · exact hCompiled
  exact Derives.iff_elim_left
    (P.formula_forall_close_iff
      sort id source hSource)
    hClosed

/-- 函数图编译保持十二类 Hilbert 基础逻辑公理的可导性。 -/
theorem base_axiom
    (P : GraphPresentation D)
    {source : Formula σ}
    (hAxiom : HilbertBaseAxiom source)
    (hSource : Formula.Admissible source) :
    Derives P.theory [] (formula D source) := by
  cases hAxiom with
  | implication_distribution antecedent middle consequent =>
      have hMain :=
        Formula.Admissible.imp_left hSource
      have hAntecedent :=
        Formula.Admissible.imp_left hMain
      have hMiddleConsequent :=
        Formula.Admissible.imp_right hMain
      have hMiddle :=
        Formula.Admissible.imp_left hMiddleConsequent
      have hConsequent :=
        Formula.Admissible.imp_right hMiddleConsequent
      simpa [formula] using
        Derives.Propositional.imp_distribution
          (T := P.theory) (Γ := [])
          (formula_admissible D hAntecedent)
          (formula_admissible D hMiddle)
          (formula_admissible D hConsequent)
  | self_implication source =>
      have hFormula :=
        Formula.Admissible.imp_left hSource
      simpa [formula] using
        Derives.Propositional.imp_const
          (T := P.theory) (Γ := [])
          (formula_admissible D hFormula)
          (formula_admissible D hFormula)
  | weakening source extra =>
      have hFormula :=
        Formula.Admissible.imp_left hSource
      have hExtra :=
        Formula.Admissible.imp_left
          (Formula.Admissible.imp_right hSource)
      simpa [formula] using
        Derives.Propositional.imp_const
          (T := P.theory) (Γ := [])
          (formula_admissible D hFormula)
          (formula_admissible D hExtra)
  | contradiction source conclusion =>
      have hFormula :=
        Formula.Admissible.imp_left hSource
      have hConclusion :=
        Formula.Admissible.imp_right
          (Formula.Admissible.imp_right hSource)
      simpa [formula] using
        Derives.Propositional.imp_neg_elim
          (T := P.theory) (Γ := [])
          (formula_admissible D hFormula)
          (formula_admissible D hConclusion)
  | classical source =>
      have hFormula :=
        Formula.Admissible.imp_right hSource
      simpa [formula] using
        Derives.Propositional.classical_reduction
          (T := P.theory) (Γ := [])
          (formula_admissible D hFormula)
  | explosion source conclusion =>
      have hNegFormula :=
        Formula.Admissible.imp_left hSource
      have hFormula :=
        Formula.Admissible.neg_body hNegFormula
      have hConclusion :=
        Formula.Admissible.imp_right
          (Formula.Admissible.imp_right hSource)
      simpa [formula] using
        Derives.Propositional.neg_imp_elim
          (T := P.theory) (Γ := [])
          (formula_admissible D hFormula)
          (formula_admissible D hConclusion)
  | case_analysis source conclusion =>
      have hPositive :=
        Formula.Admissible.imp_left hSource
      have hFormula :=
        Formula.Admissible.imp_left hPositive
      have hConclusion :=
        Formula.Admissible.imp_right hPositive
      simpa [formula] using
        Derives.Propositional.case_analysis
          (T := P.theory) (Γ := [])
          (formula_admissible D hFormula)
          (formula_admissible D hConclusion)
  | forall_specialization sort body source
      hSorted hClosed =>
      have hForall :=
        Formula.Admissible.imp_left hSource
      simpa [formula] using
        P.formula_forall_elim
          sort body source hForall
            ⟨hSorted, hClosed⟩
  | forall_distribution sort antecedent consequent =>
      have hForallImp :=
        Formula.Admissible.imp_left hSource
      have hForallAntecedent :=
        Formula.Admissible.imp_left
          (Formula.Admissible.imp_right hSource)
      have hForallConsequent :=
        Formula.Admissible.imp_right
          (Formula.Admissible.imp_right hSource)
      let eigen :=
        FreshVariable.fresh_id sort
          [antecedent, consequent]
      let openedAntecedent :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) antecedent
      let openedConsequent :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) consequent
      let compiledAntecedent :=
        formula D openedAntecedent
      let compiledConsequent :=
        formula D openedConsequent
      let closedAntecedent :=
        Formula.closeFreeAt sort
          (source_id eigen) 0 compiledAntecedent
      let closedConsequent :=
        Formula.closeFreeAt sort
          (source_id eigen) 0 compiledConsequent
      have hAntecedentFresh :
          (sort, eigen) ∉
            Formula.freeSupport antecedent := by
        dsimp [eigen]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hConsequentFresh :
          (sort, eigen) ∉
            Formula.freeSupport consequent := by
        dsimp [eigen]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hImpFresh :
          (sort, eigen) ∉
            Formula.freeSupport
              (Formula.imp antecedent consequent) := by
        simpa [Formula.freeSupport] using
          And.intro hAntecedentFresh
            hConsequentFresh
      have hImpAt :=
        P.formula_forall_iff_at
          sort (Formula.imp antecedent consequent)
          hForallImp eigen hImpFresh
      have hAntecedentAt :=
        P.formula_forall_iff_at
          sort antecedent hForallAntecedent
          eigen hAntecedentFresh
      have hConsequentAt :=
        P.formula_forall_iff_at
          sort consequent hForallConsequent
          eigen hConsequentFresh
      suffices hCompiled :
          Derives P.theory []
          (Formula.imp
            (formula D
              (Formula.forallE sort
                (Formula.imp antecedent consequent)))
            (Formula.imp
              (formula D
                (Formula.forallE sort antecedent))
              (formula D
                (Formula.forallE sort consequent)))) by
        simpa [formula] using hCompiled
      apply Derives.imp_intro
        (hAntecedentCheck :=
          Formula.check_certificate_of_admissible
            (formula_admissible D hForallImp))
      apply Derives.imp_intro
        (hAntecedentCheck :=
          Formula.check_certificate_of_admissible
            (formula_admissible D
              hForallAntecedent))
      let Γ : Context σ :=
        [formula D (Formula.forallE sort antecedent),
          formula D
            (Formula.forallE sort
              (Formula.imp antecedent consequent))]
      have hImp :
          Derives P.theory Γ
            (formula D
              (Formula.forallE sort
                (Formula.imp antecedent consequent))) :=
        Derives.assumption_of_mem
          (by simp [Γ])
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              (formula_admissible D hForallImp))
      have hAntecedent :
          Derives P.theory Γ
            (formula D
              (Formula.forallE sort antecedent)) :=
        Derives.assumption_of_mem
          (by simp [Γ])
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              (formula_admissible D
                hForallAntecedent))
      have hNormalizedImp :
          Derives P.theory Γ
            (Formula.forallE sort
              (Formula.imp closedAntecedent
                closedConsequent)) := by
        have hResult :=
          Derives.iff_elim_right
            (hImpAt.context_weaken
              (by simp [Γ]))
            hImp
        simpa [openedAntecedent,
          openedConsequent,
          compiledAntecedent,
          compiledConsequent,
          closedAntecedent,
          closedConsequent,
          Formula.openAt,
          Formula.closeFreeAt,
          formula] using hResult
      have hNormalizedAntecedent :
          Derives P.theory Γ
            (Formula.forallE sort
              closedAntecedent) := by
        simpa [closedAntecedent,
          compiledAntecedent,
          openedAntecedent] using
            Derives.iff_elim_right
              (hAntecedentAt.context_weaken
                (by simp [Γ]))
              hAntecedent
      have hDistribution :=
        Derives.forall_imp_distribution
          (T := P.theory) (Γ := Γ)
          sort closedAntecedent
            closedConsequent
      have hNormalizedConsequent :
          Derives P.theory Γ
            (Formula.forallE sort
              closedConsequent) :=
        hDistribution.imp_elim
          hNormalizedImp |>.imp_elim
            hNormalizedAntecedent
      have hResult :=
        Derives.iff_elim_left
          (hConsequentAt.context_weaken
            (by simp [Γ]))
          hNormalizedConsequent
      simpa [Γ] using hResult
  | vacuous_forall sort eigen source hFresh =>
      have hFormula :=
        Formula.Admissible.imp_left hSource
      have hCompiledFresh :
          (sort, source_id eigen) ∉
            Formula.freeSupport
              (formula D source) :=
        formula_compiled_source_fresh
          D sort eigen source hFresh
      have hForall :=
        P.formula_forall_close_iff
          sort eigen source hFormula
      suffices hCompiled :
          Derives P.theory []
          (Formula.imp
            (formula D source)
            (formula D
              (Formula.forallE sort
                (Formula.closeFreeAt sort eigen 0
                  source)))) by
        simpa [formula] using hCompiled
      apply Derives.imp_intro
        (hAntecedentCheck :=
          Formula.check_certificate_of_admissible
            (formula_admissible D hFormula))
      have hBody :
          Derives P.theory [formula D source]
            (formula D source) :=
        Derives.assumption_of_mem
          (by simp)
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              (formula_admissible D hFormula))
      have hClosed :=
        (Derives.forall_vacuous_intro
          (T := P.theory) (Γ := [])
          hCompiledFresh).context_weaken_cons.imp_elim
            hBody
      exact Derives.iff_elim_left
        hForall.context_weaken_cons hClosed
  | equality_substitution sort leftId rightId body =>
      have hEqualitySource :=
        Formula.Admissible.imp_left hSource
      have hBody :=
        Formula.Admissible.imp_left
          (Formula.Admissible.imp_right hSource)
      let left :=
        Term.var
          (.fvar sort (source_id leftId))
      let right :=
        Term.var
          (.fvar sort (source_id rightId))
      have hRight :
          Term.Admissible
            (.var (.fvar sort rightId)) sort :=
        ⟨TermWellSorted.fvar sort rightId,
          TermScoped.fvar sort rightId⟩
      have hSubstitution :=
        P.formula_substitute_iff
          sort leftId hRight body hBody
      have hSubstitution' :
          Derives P.theory []
            (Formula.iff
              (formula D
                (Formula.substituteFree sort leftId
                  (.var (.fvar sort rightId)) body))
              (Formula.substituteFree sort
                (source_id leftId) right
                (formula D body))) := by
        simpa [formula_substitution_closure,
          term_flat_closure, term,
          close_witnesses_from,
          condition_conjunction, right] using
            hSubstitution
      suffices hCompiled :
          Derives P.theory []
          (Formula.imp
            (formula D
              (Formula.equal
                (.var (.fvar sort leftId))
                (.var (.fvar sort rightId))))
            (Formula.imp
              (formula D body)
              (formula D
                (Formula.substituteFree sort leftId
                  (.var (.fvar sort rightId))
                  body)))) by
        simpa [formula] using hCompiled
      apply Derives.imp_intro
        (hAntecedentCheck :=
          Formula.check_certificate_of_admissible
            (formula_admissible D
              hEqualitySource))
      apply Derives.imp_intro
        (hAntecedentCheck :=
          Formula.check_certificate_of_admissible
            (formula_admissible D hBody))
      let Γ : Context σ :=
        [formula D body,
          Formula.equal left right]
      have hEquality :
          Derives P.theory Γ
            (Formula.equal left right) :=
        Derives.assumption_of_mem
          (by simp [Γ])
      have hBodyDerives :
          Derives P.theory Γ
            (formula D body) :=
        Derives.assumption_of_mem
          (by simp [Γ])
          (hFormulaCheck :=
            Formula.check_certificate_of_admissible
              (formula_admissible D hBody))
      have hRule :=
        Metatheory.Derives.equality_substitute_free_variable
          (T := P.theory) (Γ := Γ)
          (sort := sort)
          (eigen := source_id leftId)
          (replacement := right)
          (body := formula D body)
      have hReplaced :=
        hRule.imp_elim hEquality |>.imp_elim
          hBodyDerives
      have hResult :=
        Derives.iff_elim_left
          (hSubstitution'.context_weaken
            (by simp [Γ]))
          hReplaced
      simpa [formula, FunctionGraphElimination.equality,
        term, terms, close_witnesses,
        close_witnesses_from,
        condition_conjunction, left, right,
        Γ] using hResult
  | equality_reflexivity sort id =>
      simpa [formula,
        FunctionGraphElimination.equality,
        term, terms, close_witnesses,
        close_witnesses_from,
        condition_conjunction] using
          Metatheory.Derives.equality_refl
            (T := P.theory) (Γ := [])
            (.var (.fvar sort (source_id id)))
            (sort := sort)

/-- 函数图编译保持有限全称闭包后的 Hilbert 逻辑公理。 -/
theorem logical_axiom
    (P : GraphPresentation D)
    {source : Formula σ}
    (hAxiom : HilbertLogicalAxiom source)
    (hSource : Formula.Admissible source) :
    Derives P.theory [] (formula D source) := by
  induction hAxiom with
  | base hBase =>
      exact P.base_axiom hBase hSource
  | @forall_closure source sort eigen hAxiom ih =>
      have hBody :
          Formula.Admissible source := by
        have hOpened :=
          Formula.Admissible.forall_openAt
            sort hSource
              ⟨TermWellSorted.fvar sort eigen,
                TermScoped.fvar sort eigen⟩
        simpa [Formula.openAt_closeFreeAt] using
          hOpened
      have hGeneralized :
          Derives P.theory []
            (Formula.forallE sort
              (Formula.closeFreeAt sort
                (source_id eigen) 0
                (formula D source))) := by
        exact Derives.forall_intro
          (P.theory_fresh sort
            (source_id eigen))
          (by simp)
          (ih hBody)
      exact Derives.iff_elim_left
        (P.formula_forall_close_iff
          sort eigen source hBody)
          hGeneralized

/--
图表示可沿目标理论包含关系提升。

图公式、全体性与单值性均保持不变；这里只把它们已有的证明嵌入更强理论。
-/
def theory_weaken
    (P : GraphPresentation D)
    (target : Theory σ)
    (hSubset :
      ∀ φ, P.theory φ → target φ)
    (hSentence :
      ∀ {φ}, target φ →
        Formula.Sentence φ) :
    GraphPresentation D where
  theory := target
  theory_sentence := hSentence
  total := by
    intro arguments resultId
      hArguments hFresh
    exact
      (P.total resultId hArguments
        hFresh).theory_weaken hSubset
  functional := by
    intro arguments left right
      hArguments hLeft hRight
    exact
      (P.functional hArguments
        hLeft hRight).theory_weaken hSubset

/-- 图公理与源理论逐公式编译像的联合理论。 -/
def compiled_theory
    (P : GraphPresentation D)
    (sourceTheory : Theory σ) :
    Theory σ :=
  Theory.union P.theory <| fun target =>
    ∃ source,
      sourceTheory source ∧
        target = formula D source

/--
Hilbert 推导可逐树编译到图理论与源公理编译像的联合理论。

该接口不要求调用方预先证明任何编译公理；理论行自动进入右侧编译像，逻辑公理
和 MP 则由本模块递归翻译。
-/
theorem hilbert
    (P : GraphPresentation D)
    {sourceTheory : Theory σ}
    {source : Formula σ}
    (hSource :
      HilbertDerives sourceTheory source) :
    Derives (P.compiled_theory sourceTheory) []
      (formula D source) := by
  induction hSource with
  | logical_axiom hAxiom hAdmissible =>
      exact (P.logical_axiom
        hAxiom hAdmissible).theory_weaken
          (fun _ hFormula => Or.inl hFormula)
  | theory_axiom hAxiom hAdmissible =>
      exact Derives.theory_mem
        (T := P.compiled_theory sourceTheory)
        (Or.inr ⟨_, hAxiom, rfl⟩)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            (formula_admissible D hAdmissible))
  | @modus_ponens antecedent consequent
      hAntecedent hImplication
      ihAntecedent ihImplication =>
      have hImplication' :
          Derives (P.compiled_theory sourceTheory) []
            (Formula.imp
              (formula D antecedent)
              (formula D consequent)) := by
        simpa [formula] using ihImplication
      exact hImplication'.imp_elim
        ihAntecedent

/--
若每条源理论公理的编译像已经可由纯图理论推出，则整棵 Hilbert 推导可直接消解
回纯图理论。
-/
theorem hilbert_to_base
    (P : GraphPresentation D)
    {sourceTheory : Theory σ}
    (hTheory :
      ∀ {source}, sourceTheory source →
        Formula.Admissible source →
        Derives P.theory []
          (formula D source))
    {source : Formula σ}
    (hSource :
      HilbertDerives sourceTheory source) :
    Derives P.theory []
      (formula D source) := by
  induction hSource with
  | logical_axiom hAxiom hAdmissible =>
      exact P.logical_axiom
        hAxiom hAdmissible
  | theory_axiom hAxiom hAdmissible =>
      exact hTheory hAxiom hAdmissible
  | @modus_ponens antecedent consequent
      hAntecedent hImplication
      ihAntecedent ihImplication =>
      have hImplication' :
          Derives P.theory []
            (Formula.imp
              (formula D antecedent)
              (formula D consequent)) := by
        simpa [formula] using ihImplication
      exact hImplication'.imp_elim
        ihAntecedent

/-- 源理论的 Hilbert 矛盾经逐公理消解后回传为纯图理论矛盾。 -/
theorem hilbert_falsum
    (P : GraphPresentation D)
    {sourceTheory : Theory σ}
    (hTheory :
      ∀ {source}, sourceTheory source →
        Derives P.theory []
          (formula D source))
    (hSource :
      HilbertDerives sourceTheory
        Formula.falsum) :
    Derives P.theory []
      Formula.falsum := by
  simpa [formula] using
    P.hilbert_to_base
      (fun h _ => hTheory h) hSource

/-- 纯图理论一致且能消解所有编译公理时，源 Hilbert 理论一致。 -/
theorem hilbert_consistent
    (P : GraphPresentation D)
    {sourceTheory : Theory σ}
    (hBase :
      Derives.Consistent P.theory [])
    (hTheory :
      ∀ {source}, sourceTheory source →
        Derives P.theory []
          (formula D source)) :
    ¬ HilbertDerives sourceTheory
      Formula.falsum := by
  intro hSource
  exact hBase (P.hilbert_falsum hTheory hSource)

end GraphPresentation

/--
一个函数符号在整套源理论上的证明级消去表示。

图表示负责公式与逻辑规则；本接口只额外登记源理论以及每条源公理编译后的
目标证明。这样具体定义插件不再重复整棵 Hilbert 翻译与一致性回传外壳。
-/
structure TheoryPresentation (D : Data σ) where
  graph : GraphPresentation D
  source : Theory σ
  compile_axiom :
    ∀ {φ}, source φ →
      Derives graph.theory []
        (formula D φ)

namespace GraphPresentation

/--
把任意闭句理论整体编译为“图理论与逐公理编译像”的联合。

该构造不要求预先逐条消解定义公理，因而适合在大型理论上连续消去多个函数符号；
每一步的目标理论可直接作为下一步的源理论。
-/
def compile_theory
    (P : GraphPresentation D)
    (T : Theory σ)
    (hT : ∀ {φ}, T φ → Formula.Sentence φ)
    (hSort : ∀ sort, sort = D.sort) :
    TheoryPresentation D where
  graph :=
    P.theory_weaken
      (P.compiled_theory T)
      (fun _ hφ => Or.inl hφ)
      (by
        intro φ hφ
        rcases hφ with hφ | ⟨source, hSource, rfl⟩
        · exact P.theory_sentence hφ
        · exact formula_sentence_of_single_sort
            D hSort (hT hSource))
  source := T
  compile_axiom := by
    intro φ hφ
    exact Derives.theory_mem
      (T := P.compiled_theory T)
      (Or.inr ⟨φ, hφ, rfl⟩)
      (hFormulaCheck :=
        Formula.check_certificate_of_admissible
          (formula_admissible D (hT hφ).1))

end GraphPresentation

namespace TheoryPresentation

variable {D E : Data σ}

/-!
## 已检查理论并入

避让接口只能处理“新增公理编译后保持原式”的情况。这里保留同一理论树的
checked 版本，允许调用方直接提供新增公理在并入后的图理论中的编译证明；
因此依赖其他待消去符号的规格可以显式接入，而不必伪造 `FormulaAvoids`。
-/

/-!
## 编译理论并入

源附加理论与目标附加理论可以不同；后者承载源公理经过当前图编译后的公式。
这正是依赖型规格随函数图消去逐层变换时所需的最小理论接口。
-/

/-- 在函数图理论右侧并入一个可变换到目标理论的源理论。 -/
def union_right_mapped
    (P : TheoryPresentation D)
    (U V : Theory σ)
    (hVSentence :
      ∀ {φ}, V φ → Formula.Sentence φ)
    (hCompile :
      ∀ {φ}, U φ →
        Derives (Theory.union P.graph.theory V) []
          (formula D φ)) :
    TheoryPresentation D where
  graph :=
    P.graph.theory_weaken
      (Theory.union P.graph.theory V)
      (fun _ hφ => Or.inl hφ)
      (by
        intro φ hφ
        exact hφ.elim P.graph.theory_sentence
          hVSentence)
  source := Theory.union P.source U
  compile_axiom := by
    intro φ hφ
    rcases hφ with hφ | hφ
    · exact
        (P.compile_axiom hφ).theory_union_left
    · exact hCompile hφ

/-- 在函数图理论左侧并入一个可变换到目标理论的源理论。 -/
def union_left_mapped
    (P : TheoryPresentation D)
    (U V : Theory σ)
    (hVSentence :
      ∀ {φ}, V φ → Formula.Sentence φ)
    (hCompile :
      ∀ {φ}, U φ →
        Derives (Theory.union V P.graph.theory) []
          (formula D φ)) :
    TheoryPresentation D where
  graph :=
    P.graph.theory_weaken
      (Theory.union V P.graph.theory)
      (fun _ hφ => Or.inr hφ)
      (by
        intro φ hφ
        exact hφ.elim hVSentence
          P.graph.theory_sentence)
  source := Theory.union U P.source
  compile_axiom := by
    intro φ hφ
    rcases hφ with hφ | hφ
    · exact hCompile hφ
    · exact
        (P.compile_axiom hφ).theory_union_right

/--
在源理论左侧加入一条公理，并在目标理论中只保留其函数图编译像。

该构造用于让依赖型定义公理随函数符号消去逐层变换；调用方只需证明编译像仍是
闭句，源公理本身的编译证明由目标理论行直接给出。
-/
def insert_compiled
    (P : TheoryPresentation D)
    (φ : Formula σ)
    (hSentence :
      Formula.Sentence (formula D φ)) :
    TheoryPresentation D :=
  union_left_mapped P
    (Theory.singleton φ)
    (Theory.singleton (formula D φ))
    (by
      intro ψ hψ
      change ψ = formula D φ at hψ
      subst ψ
      exact hSentence)
    (by
      intro ψ hψ
      change ψ = φ at hψ
      subst ψ
      exact Derives.theory_mem
        (T := Theory.union
          (Theory.singleton (formula D φ))
          P.graph.theory)
        (Or.inl rfl)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            hSentence.1))

/-- 在函数图理论右侧并入一组已给出编译证明的闭句公理。 -/
def union_right_checked
    (P : TheoryPresentation D)
    (U : Theory σ)
    (hSentence :
      ∀ {φ}, U φ → Formula.Sentence φ)
    (hCompile :
      ∀ {φ}, U φ →
        Derives (Theory.union P.graph.theory U) []
          (formula D φ)) :
    TheoryPresentation D :=
  union_right_mapped P U U
    hSentence hCompile

/-- 在函数图理论左侧并入一组已给出编译证明的闭句公理。 -/
def union_left_checked
    (P : TheoryPresentation D)
    (U : Theory σ)
    (hSentence :
      ∀ {φ}, U φ → Formula.Sentence φ)
    (hCompile :
      ∀ {φ}, U φ →
        Derives (Theory.union U P.graph.theory) []
          (formula D φ)) :
    TheoryPresentation D :=
  union_left_mapped P U U
    hSentence hCompile

/--
在函数图插件右侧并入不含待消去函数的任意闭句理论。

右侧公理的编译严格保持原式，因此无需为每个有限扩张复制一条公理 rejection 链。
-/
def union_right
    (P : TheoryPresentation D)
    (U : Theory σ)
    (hSentence :
      ∀ {φ}, U φ → Formula.Sentence φ)
    (hAvoids :
      ∀ {φ}, U φ →
        FormulaAvoids D.symbol φ) :
    TheoryPresentation D :=
    union_right_checked P U hSentence (by
      intro φ hφ
      rw [formula_eq_of_sentence_avoids
          D φ (hAvoids hφ) (hSentence hφ)]
      exact Derives.theory_mem
        (T := Theory.union P.graph.theory U)
        (Or.inr hφ)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            (hSentence hφ).1))

/--
在函数图插件左侧并入不含待消去函数的任意闭句理论。

该版本与 `union_right` 对称，便于直接贴合现有理论树的括号方向。
-/
def union_left
    (P : TheoryPresentation D)
    (U : Theory σ)
    (hSentence :
      ∀ {φ}, U φ → Formula.Sentence φ)
    (hAvoids :
      ∀ {φ}, U φ →
        FormulaAvoids D.symbol φ) :
    TheoryPresentation D :=
    union_left_checked P U hSentence (by
      intro φ hφ
      rw [formula_eq_of_sentence_avoids
          D φ (hAvoids hφ) (hSentence hφ)]
      exact Derives.theory_mem
        (T := Theory.union U P.graph.theory)
        (Or.inl hφ)
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            (hSentence hφ).1))

/-- 理论表示自动把整棵源 Hilbert 推导编译到图理论。 -/
theorem hilbert
    (P : TheoryPresentation D)
    {φ : Formula σ}
    (hφ : HilbertDerives P.source φ) :
    Derives P.graph.theory []
      (formula D φ) :=
  P.graph.hilbert_to_base
    (fun h _ => P.compile_axiom h) hφ

/--
任意 checked 自然演绎证明可先正规化为 Hilbert 证明，再完整执行函数图消去。

理论行的 admissibility 直接来自正规化后的 Hilbert 证书；函数图编译与 Hilbert
归约的相容性负责消去两侧的编码差异。
-/
theorem derives
    (P : TheoryPresentation D)
    (anchorSort : σ.SortSymbol)
    {φ : Formula σ}
    (hφ : Derives P.source [] φ) :
    Derives P.graph.theory []
      (formula D φ) := by
  have hNormalized :=
    hφ.to_hilbert anchorSort
  have hCompiled :
      Derives P.graph.theory []
        (formula D
          (Formula.hilbertize
            anchorSort φ)) := by
    apply P.graph.hilbert_to_base
      (sourceTheory :=
        Theory.hilbertize_context
          anchorSort P.source [])
    · intro encoded hEncoded hAdmissible
      rcases
          Theory.mem_hilbertize_context_iff.mp
            hEncoded with
        ⟨source, hSource, rfl⟩
      rcases hSource with hSource | hSource
      · have hSourceAdmissible :
            Formula.Admissible source :=
          Formula.Admissible.hilbertize_source
            hAdmissible
        have hAxiom :=
          P.compile_axiom hSource
        have hHilbertized :
            Derives P.graph.theory []
              (Formula.hilbertize anchorSort
                (formula D source)) :=
          (DerivationEquivalent.hilbertize
              anchorSort (formula D source)
              (formula_admissible D
                hSourceAdmissible)).forward.imp_elim
            hAxiom
        exact
          (P.graph.hilbertize_equivalent
              anchorSort source
              hSourceAdmissible).backward.imp_elim
            hHilbertized
      · cases hSource
    · exact hNormalized
  have hHilbertized :
      Derives P.graph.theory []
        (Formula.hilbertize anchorSort
          (formula D φ)) :=
    (P.graph.hilbertize_equivalent
        anchorSort φ hφ.admissible).forward.imp_elim
      hCompiled
  exact
    (DerivationEquivalent.hilbertize
        anchorSort (formula D φ)
        (formula_admissible D
          hφ.admissible)).backward.imp_elim
      hHilbertized

/-- 源理论中的 Hilbert 矛盾回传为图理论中的自然演绎矛盾。 -/
theorem hilbert_falsum
    (P : TheoryPresentation D)
    (h : HilbertDerives P.source
      Formula.falsum) :
    Derives P.graph.theory []
      Formula.falsum := by
  simpa [formula] using P.hilbert h

/-- 源理论中的 checked 自然演绎矛盾回传为图理论矛盾。 -/
theorem derives_falsum
    (P : TheoryPresentation D)
    (anchorSort : σ.SortSymbol)
    (h : Derives P.source []
      Formula.falsum) :
    Derives P.graph.theory []
      Formula.falsum := by
  simpa [formula] using P.derives anchorSort h

/-! ## 组合表示的任意公式翻译 -/

/--
两个理论表示在中间理论包含时可直接组合任意闭公式的证明翻译。

输出公式按先 `upper`、后 `lower` 的顺序嵌套编译；矛盾回传只是该接口在
`Formula.falsum` 上的保守特例。
-/
theorem derives_comp
    (upper : TheoryPresentation D)
    (lower : TheoryPresentation E)
    (upperAnchor lowerAnchor : σ.SortSymbol)
    (hMiddle :
      ∀ φ, upper.graph.theory φ →
        lower.source φ)
    {φ : Formula σ}
    (h :
      Derives upper.source [] φ) :
    Derives lower.graph.theory []
      (formula E (formula D φ)) :=
  lower.derives lowerAnchor <|
    (upper.derives upperAnchor h).theory_weaken hMiddle

/--
两个理论表示在中间理论包含时可直接组合矛盾回传。

该定理只组合 `⊥`，因此不需要把两次公式编译压成单次语法变换；这正是定义扩张
一致性链所需的最弱接口。
-/
theorem derives_falsum_comp
    (upper : TheoryPresentation D)
    (lower : TheoryPresentation E)
    (upperAnchor lowerAnchor : σ.SortSymbol)
    (hMiddle :
      ∀ φ, upper.graph.theory φ →
        lower.source φ)
    (h :
      Derives upper.source []
        Formula.falsum) :
    Derives lower.graph.theory []
      Formula.falsum :=
  lower.derives_falsum lowerAnchor <|
    (upper.derives_falsum
      upperAnchor h).theory_weaken hMiddle

/-- 图理论一致时，源 checked 自然演绎理论一致。 -/
theorem consistent
    (P : TheoryPresentation D)
    (anchorSort : σ.SortSymbol)
    (hGraph :
      Derives.Consistent P.graph.theory []) :
    Derives.Consistent P.source [] := by
  intro h
  exact hGraph (P.derives_falsum anchorSort h)

/-- 两个理论表示可沿中间理论包含关系组合一致性传递。 -/
theorem consistent_comp
    (upper : TheoryPresentation D)
    (lower : TheoryPresentation E)
    (upperAnchor lowerAnchor : σ.SortSymbol)
    (hMiddle :
      ∀ φ, upper.graph.theory φ →
        lower.source φ)
    (hLower :
      Derives.Consistent
        lower.graph.theory []) :
    Derives.Consistent upper.source [] := by
  intro h
  exact hLower <|
    upper.derives_falsum_comp lower
      upperAnchor lowerAnchor hMiddle h

/-- 图理论一致时，源 Hilbert 理论一致。 -/
theorem hilbert_consistent
    (P : TheoryPresentation D)
    (hGraph :
      Derives.Consistent P.graph.theory []) :
    ¬ HilbertDerives P.source
      Formula.falsum := by
  intro h
  exact hGraph (P.hilbert_falsum h)

end TheoryPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
