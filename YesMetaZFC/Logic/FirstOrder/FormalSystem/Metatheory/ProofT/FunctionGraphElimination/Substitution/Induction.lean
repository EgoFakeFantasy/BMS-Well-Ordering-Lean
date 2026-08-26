import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.FunctionGraphElimination.Substitution.CompilerFreshness

/-!
# 完整公式替换归纳

本模块把原子、联结词与量词合同装配为完整公式的自由替换定理。量词分支先把
编译器选取的 canonical binder 统一到一份公共新鲜变量，再应用具名量词合同。
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

namespace GraphPresentation

/-- 整公式替换量词分支共用的源层新鲜 binder。 -/
private def substitution_fresh_id
    (sort target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ) (body : Formula σ) :
    FreeVarId :=
  FreshVariable.fresh_id sort
    [body,
      Formula.substituteFree target id replacement body,
      Formula.equal replacement replacement,
      Formula.equal
        (.var (.fvar target id))
        (.var (.fvar target id))]

/-- 公共 binder 对原量词体新鲜。 -/
private theorem substitution_fresh_id_body
    (sort target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ) (body : Formula σ) :
    (sort,
      substitution_fresh_id
        sort target id replacement body) ∉
      Formula.freeSupport body := by
  exact FreshVariable.fresh_id_not_mem_m
    (by simp)

/-- 公共 binder 对替换后的量词体新鲜。 -/
private theorem substitution_fresh_id_substituted
    (sort target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ) (body : Formula σ) :
    (sort,
      substitution_fresh_id
        sort target id replacement body) ∉
      Formula.freeSupport
        (Formula.substituteFree
          target id replacement body) := by
  exact FreshVariable.fresh_id_not_mem_m
    (by simp)

/-- 公共 binder 对替换项新鲜。 -/
private theorem substitution_fresh_id_replacement
    (sort target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ) (body : Formula σ) :
    (sort,
      substitution_fresh_id
        sort target id replacement body) ∉
      Term.freeSupport replacement := by
  have hFresh :=
    FreshVariable.fresh_id_not_mem_m
      (sort := sort)
      (formulas :=
        [body,
          Formula.substituteFree
            target id replacement body,
          Formula.equal replacement replacement,
          Formula.equal
            (.var (.fvar target id))
            (.var (.fvar target id))])
      (formula :=
        Formula.equal replacement replacement)
      (by simp)
  intro hMember
  apply hFresh
  have hMember' :
      (sort,
        FreshVariable.fresh_id sort
          [body,
            Formula.substituteFree
              target id replacement body,
            Formula.equal replacement replacement,
            Formula.equal
              (.var (.fvar target id))
              (.var (.fvar target id))]) ∈
        Term.freeSupport replacement := by
    simpa [substitution_fresh_id] using hMember
  exact List.mem_append.mpr <| Or.inl hMember'

/-- 公共 binder 与待替换自由变量对不同。 -/
private theorem substitution_fresh_id_ne
    (sort target : σ.SortSymbol) (id : FreeVarId)
    (replacement : Term σ) (body : Formula σ) :
    (target, id) ≠
      (sort,
        substitution_fresh_id
          sort target id replacement body) := by
  have hFresh :=
    FreshVariable.fresh_id_not_mem_m
      (sort := sort)
      (formulas :=
        [body,
          Formula.substituteFree
            target id replacement body,
          Formula.equal replacement replacement,
          Formula.equal
            (.var (.fvar target id))
            (.var (.fvar target id))])
      (formula :=
        Formula.equal
          (.var (.fvar target id))
          (.var (.fvar target id)))
      (by simp)
  intro hEqual
  apply hFresh
  change
    (target, id) =
      (sort,
        FreshVariable.fresh_id sort
          [body,
            Formula.substituteFree
              target id replacement body,
            Formula.equal replacement replacement,
            Formula.equal
              (.var (.fvar target id))
              (.var (.fvar target id))])
      at hEqual
  simp only [Formula.freeSupport, Term.freeSupport,
    List.mem_append, List.mem_singleton]
  exact Or.inl hEqual.symm

variable
  [DecidableEq σ.FuncSymbol]
  {D : Data σ}

/-- 图理论均由闭句组成，因此任意自由变量对理论新鲜。 -/
private theorem theory_fresh
    (P : GraphPresentation D)
    (sort : σ.SortSymbol) (id : FreeVarId) :
    ∀ formula, P.theory formula →
      (sort, id) ∉ Formula.freeSupport formula := by
  intro formula hFormula
  rw [(P.theory_sentence hFormula).2]
  exact List.not_mem_nil

/--
把全称公式编译器的 canonical binder 改名为任意对源量词体新鲜的变量。

参数 `hOpenedEquivalent` 正是较低复杂度打开体上的替换归纳假设。
-/
private theorem formula_forall_at_iff
    (P : GraphPresentation D)
    (sort : σ.SortSymbol) (body : Formula σ)
    (hSource :
      Formula.Admissible
        (Formula.forallE sort body))
    (eigen : FreeVarId)
    (hEigenFresh :
      (sort, eigen) ∉ Formula.freeSupport body)
    (hOpenedEquivalent :
      let canonical :=
        FreshVariable.fresh_id sort [body]
      let openedCanonical :=
        Formula.openAt sort 0
          (.var (.fvar sort canonical)) body
      let openedTarget :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      Derives P.theory []
        (Formula.iff
          (formula D openedTarget)
          (Formula.substituteFree sort
            (source_id canonical)
            (.var (.fvar sort (source_id eigen)))
            (formula D openedCanonical)))) :
    Derives P.theory []
      (Formula.iff
        (formula D (Formula.forallE sort body))
        (Formula.forallE sort
          (Formula.closeFreeAt sort
            (source_id eigen) 0
            (formula D
              (Formula.openAt sort 0
                (.var (.fvar sort eigen)) body))))) := by
  let canonical :=
    FreshVariable.fresh_id sort [body]
  let openedCanonical :=
    Formula.openAt sort 0
      (.var (.fvar sort canonical)) body
  let openedTarget :=
    Formula.openAt sort 0
      (.var (.fvar sort eigen)) body
  have hCanonicalFresh :
      (sort, canonical) ∉
        Formula.freeSupport body := by
    dsimp [canonical]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hCanonicalTerm :
      Term.Admissible
        (.var (.fvar sort canonical)) sort :=
    ⟨TermWellSorted.fvar sort canonical,
      TermScoped.fvar sort canonical⟩
  have hTargetTerm :
      Term.Admissible
        (.var (.fvar sort eigen)) sort :=
    ⟨TermWellSorted.fvar sort eigen,
      TermScoped.fvar sort eigen⟩
  have hOpenedCanonical :
      Formula.Admissible openedCanonical := by
    dsimp [openedCanonical]
    exact Formula.Admissible.forall_openAt
      sort hSource hCanonicalTerm
  have hOpenedTarget :
      Formula.Admissible openedTarget := by
    dsimp [openedTarget]
    exact Formula.Admissible.forall_openAt
      sort hSource hTargetTerm
  by_cases hSame : eigen = canonical
  · subst eigen
    simpa [formula, canonical,
      openedCanonical, openedTarget] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := P.theory) (Γ := [])
          (Formula.Admissible.forall_closeFreeAt
            sort (source_id canonical)
              (formula_admissible D
                hOpenedCanonical))
  · have hTargetFreshCanonical :
        (sort, eigen) ∉
          Formula.freeSupport openedCanonical := by
      dsimp [openedCanonical]
      apply Formula.not_mem_freeSupport_openAt
      · simpa [Term.freeSupport] using hSame
      · exact hEigenFresh
    have hEncodedFresh :
        (sort, source_id eigen) ∉
          Formula.freeSupport
            (formula D openedCanonical) :=
      formula_compiled_source_fresh
        D sort eigen openedCanonical
          hTargetFreshCanonical
    have hRenameBound :=
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.forall_rename_bound_iff
        (T := P.theory) (Γ := [])
        (sort := sort)
        (source := source_id canonical)
        (target := source_id eigen)
        (body := formula D openedCanonical)
        (formula_admissible D hOpenedCanonical)
        hEncodedFresh
    have hOpenedEquivalent' :
        Derives P.theory []
          (Formula.iff
            (formula D openedTarget)
            (Formula.substituteFree sort
              (source_id canonical)
              (.var (.fvar sort (source_id eigen)))
              (formula D openedCanonical))) := by
      simpa [canonical, openedCanonical,
        openedTarget] using hOpenedEquivalent
    have hUnderBinder :=
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.forall_iff_mono
        (T := P.theory) (Γ := [])
        (sort := sort)
        (eigen := source_id eigen)
        (theory_fresh P sort
          (source_id eigen))
        (by simp)
        (_root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hOpenedEquivalent')
    simpa [formula, canonical,
      openedCanonical, openedTarget] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hRenameBound hUnderBinder

/-- 存在量词版本的 canonical binder 改名。 -/
private theorem formula_exists_at_iff
    (P : GraphPresentation D)
    (sort : σ.SortSymbol) (body : Formula σ)
    (hSource :
      Formula.Admissible
        (Formula.existsE sort body))
    (eigen : FreeVarId)
    (hEigenFresh :
      (sort, eigen) ∉ Formula.freeSupport body)
    (hOpenedEquivalent :
      let canonical :=
        FreshVariable.fresh_id sort [body]
      let openedCanonical :=
        Formula.openAt sort 0
          (.var (.fvar sort canonical)) body
      let openedTarget :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      Derives P.theory []
        (Formula.iff
          (formula D openedTarget)
          (Formula.substituteFree sort
            (source_id canonical)
            (.var (.fvar sort (source_id eigen)))
            (formula D openedCanonical)))) :
    Derives P.theory []
      (Formula.iff
        (formula D (Formula.existsE sort body))
        (Formula.existsE sort
          (Formula.closeFreeAt sort
            (source_id eigen) 0
            (formula D
              (Formula.openAt sort 0
                (.var (.fvar sort eigen)) body))))) := by
  let canonical :=
    FreshVariable.fresh_id sort [body]
  let openedCanonical :=
    Formula.openAt sort 0
      (.var (.fvar sort canonical)) body
  let openedTarget :=
    Formula.openAt sort 0
      (.var (.fvar sort eigen)) body
  have hCanonicalFresh :
      (sort, canonical) ∉
        Formula.freeSupport body := by
    dsimp [canonical]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hCanonicalTerm :
      Term.Admissible
        (.var (.fvar sort canonical)) sort :=
    ⟨TermWellSorted.fvar sort canonical,
      TermScoped.fvar sort canonical⟩
  have hTargetTerm :
      Term.Admissible
        (.var (.fvar sort eigen)) sort :=
    ⟨TermWellSorted.fvar sort eigen,
      TermScoped.fvar sort eigen⟩
  have hOpenedCanonical :
      Formula.Admissible openedCanonical := by
    dsimp [openedCanonical]
    exact Formula.Admissible.exists_openAt
      sort hSource hCanonicalTerm
  have hOpenedTarget :
      Formula.Admissible openedTarget := by
    dsimp [openedTarget]
    exact Formula.Admissible.exists_openAt
      sort hSource hTargetTerm
  by_cases hSame : eigen = canonical
  · subst eigen
    simpa [formula, canonical,
      openedCanonical, openedTarget] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_refl_m
          (T := P.theory) (Γ := [])
          (Formula.Admissible.exists_closeFreeAt
            sort (source_id canonical)
              (formula_admissible D
                hOpenedCanonical))
  · have hTargetFreshCanonical :
        (sort, eigen) ∉
          Formula.freeSupport openedCanonical := by
      dsimp [openedCanonical]
      apply Formula.not_mem_freeSupport_openAt
      · simpa [Term.freeSupport] using hSame
      · exact hEigenFresh
    have hEncodedFresh :
        (sort, source_id eigen) ∉
          Formula.freeSupport
            (formula D openedCanonical) :=
      formula_compiled_source_fresh
        D sort eigen openedCanonical
          hTargetFreshCanonical
    have hRenameBound :=
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_rename_bound_iff
        (T := P.theory) (Γ := [])
        (sort := sort)
        (source := source_id canonical)
        (target := source_id eigen)
        (body := formula D openedCanonical)
        (formula_admissible D hOpenedCanonical)
        hEncodedFresh
    have hOpenedEquivalent' :
        Derives P.theory []
          (Formula.iff
            (formula D openedTarget)
            (Formula.substituteFree sort
              (source_id canonical)
              (.var (.fvar sort (source_id eigen)))
              (formula D openedCanonical))) := by
      simpa [canonical, openedCanonical,
        openedTarget] using hOpenedEquivalent
    have hUnderBinder :=
      _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_iff_mono
        (T := P.theory) (Γ := [])
        (sort := sort)
        (eigen := source_id eigen)
        (theory_fresh P sort
          (source_id eigen))
        (by simp)
        (_root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          hOpenedEquivalent')
    simpa [formula, canonical,
      openedCanonical, openedTarget] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hRenameBound hUnderBinder

/--
完整公式编译与自由替换交换。

左侧直接编译源公式的替换实例；右侧只编译一次替换项，并把共享图值代入原公式
编译。该接口只要求 `GraphPresentation` 的图全体性与单值性。
-/
theorem formula_substitute_iff
    (P : GraphPresentation D)
    (target : σ.SortSymbol) (id : FreeVarId)
    {replacement : Term σ}
    (hReplacement :
      Term.Admissible replacement target)
    (source : Formula σ)
    (hSource : Formula.Admissible source) :
    Derives P.theory []
      (Formula.iff
        (formula D
          (Formula.substituteFree
            target id replacement source))
        (formula_substitution_closure
          D 0 replacement target
            (source_id id) (formula D source))) := by
  cases source with
  | falsum =>
      simpa [formula, Formula.substituteFree] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          (formula_substitution_closure_falsum_iff
            P hReplacement (source_id id) 0)
  | truth =>
      simpa [formula, Formula.substituteFree] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
          (formula_substitution_closure_truth_iff
            P hReplacement (source_id id) 0)
  | rel relation arguments =>
      rcases hSource with
        ⟨hWellFormed, hScoped⟩
      cases hWellFormed with
      | rel _ hSorted =>
          cases hScoped with
          | rel _ _ hArguments =>
              have hArguments' :
                  ArgsAdmissible arguments
                    (σ.relDomain relation) :=
                ⟨hSorted, hArguments⟩
              simpa [formula, Formula.substituteFree,
                formula_substitution_closure] using
                  relation_substitute_iff
                    P target id hReplacement
                      relation hArguments'
  | equal left right =>
      rcases hSource with
        ⟨hWellFormed, hScoped⟩
      cases hWellFormed with
      | equal hLeftSorted hRightSorted =>
          cases hScoped with
          | equal hLeftScoped hRightScoped =>
              simpa [formula, Formula.substituteFree,
                formula_substitution_closure] using
                  equality_substitute_iff
                    P target id hReplacement
                      ⟨hLeftSorted, hLeftScoped⟩
                      ⟨hRightSorted, hRightScoped⟩
  | neg body =>
      have hBody :=
        Formula.Admissible.neg_body hSource
      have hDirect :=
        (DerivationEquivalent.of_iff <|
          formula_substitute_iff
            P target id hReplacement body hBody).neg_congr.to_iff
      have hClosure :=
        formula_substitution_closure_neg_iff
          P hReplacement (source_id id)
          (formula_admissible D hBody)
          (formula_witness_fresh D body)
          0
      simpa [formula, Formula.substituteFree] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hDirect <|
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
              hClosure
  | conj left right =>
      have hLeft :=
        Formula.Admissible.conj_left hSource
      have hRight :=
        Formula.Admissible.conj_right hSource
      have hDirect :=
        (DerivationEquivalent.of_iff <|
          formula_substitute_iff
            P target id hReplacement left hLeft).conj_congr
          (DerivationEquivalent.of_iff <|
            formula_substitute_iff
              P target id hReplacement right hRight)
      have hClosure :=
        formula_substitution_closure_conj_iff
          P hReplacement (source_id id)
          (formula_admissible D hLeft)
          (formula_admissible D hRight)
          (formula_witness_fresh D left)
          (formula_witness_fresh D right)
          0
      simpa [formula, Formula.substituteFree] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hDirect.to_iff <|
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
              hClosure
  | disj left right =>
      have hLeft :=
        Formula.Admissible.disj_left hSource
      have hRight :=
        Formula.Admissible.disj_right hSource
      have hDirect :=
        (DerivationEquivalent.of_iff <|
          formula_substitute_iff
            P target id hReplacement left hLeft).disj_congr
          (DerivationEquivalent.of_iff <|
            formula_substitute_iff
              P target id hReplacement right hRight)
      have hClosure :=
        formula_substitution_closure_disj_iff
          P hReplacement (source_id id)
          (formula_admissible D hLeft)
          (formula_admissible D hRight)
          (formula_witness_fresh D left)
          (formula_witness_fresh D right)
          0
      simpa [formula, Formula.substituteFree] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hDirect.to_iff <|
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
              hClosure
  | imp left right =>
      have hLeft :=
        Formula.Admissible.imp_left hSource
      have hRight :=
        Formula.Admissible.imp_right hSource
      have hDirect :=
        (DerivationEquivalent.of_iff <|
          formula_substitute_iff
            P target id hReplacement left hLeft).imp_congr
          (DerivationEquivalent.of_iff <|
            formula_substitute_iff
              P target id hReplacement right hRight)
      have hClosure :=
        formula_substitution_closure_imp_iff
          P hReplacement (source_id id)
          (formula_admissible D hLeft)
          (formula_admissible D hRight)
          (formula_witness_fresh D left)
          (formula_witness_fresh D right)
          0
      simpa [formula, Formula.substituteFree] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hDirect.to_iff <|
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
              hClosure
  | iff left right =>
      have hLeft :=
        Formula.Admissible.iff_left hSource
      have hRight :=
        Formula.Admissible.iff_right hSource
      have hDirect :=
        (DerivationEquivalent.of_iff <|
          formula_substitute_iff
            P target id hReplacement left hLeft).iff_congr
          (DerivationEquivalent.of_iff <|
            formula_substitute_iff
              P target id hReplacement right hRight)
      have hClosure :=
        formula_substitution_closure_iff_iff
          P hReplacement (source_id id)
          (formula_admissible D hLeft)
          (formula_admissible D hRight)
          (formula_witness_fresh D left)
          (formula_witness_fresh D right)
          0
      simpa [formula, Formula.substituteFree] using
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
          hDirect.to_iff <|
            _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
              hClosure
  | forallE sort body =>
      let substituted :=
        Formula.substituteFree
          target id replacement body
      let eigen :=
        substitution_fresh_id
          sort target id replacement body
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      let openedSubstituted :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) substituted
      have hEigenTerm :
          Term.Admissible
            (.var (.fvar sort eigen)) sort :=
        ⟨TermWellSorted.fvar sort eigen,
          TermScoped.fvar sort eigen⟩
      have hBodyFresh :
          (sort, eigen) ∉
            Formula.freeSupport body := by
        simpa [eigen] using
          substitution_fresh_id_body
            sort target id replacement body
      have hSubstitutedFresh :
          (sort, eigen) ∉
            Formula.freeSupport substituted := by
        simpa [eigen, substituted] using
          substitution_fresh_id_substituted
            sort target id replacement body
      have hReplacementFresh :
          (sort, eigen) ∉
            Term.freeSupport replacement := by
        simpa [eigen] using
          substitution_fresh_id_replacement
            sort target id replacement body
      have hDistinct :
          (target, id) ≠ (sort, eigen) := by
        simpa [eigen] using
          substitution_fresh_id_ne
            sort target id replacement body
      have hEncodedDistinct :
          (target, source_id id) ≠
            (sort, source_id eigen) := by
        intro hEqual
        apply hDistinct
        have hSort :
            target = sort :=
          congrArg
            (fun pair :
              σ.SortSymbol × FreeVarId =>
                pair.1) hEqual
        have hId :
            id = eigen :=
          source_id_injective <|
            congrArg
              (fun pair :
                σ.SortSymbol × FreeVarId =>
                  pair.2) hEqual
        exact Prod.ext hSort hId
      have hOpened :
          Formula.Admissible opened := by
        dsimp [opened]
        exact Formula.Admissible.forall_openAt
          sort hSource hEigenTerm
      have hSubstitutedSource :
          Formula.Admissible
            (Formula.forallE sort substituted) := by
        simpa [substituted] using
          Formula.Admissible.substituteFree
            target id hSource hReplacement
      have hOpenedSubstituted :
          Formula.Admissible openedSubstituted := by
        dsimp [openedSubstituted]
        exact Formula.Admissible.forall_openAt
          sort hSubstitutedSource hEigenTerm
      have hOpenSubstitution :
          Formula.substituteFree target id
              replacement opened =
            openedSubstituted := by
        dsimp [opened, openedSubstituted,
          substituted]
        exact
          Formula.substituteFree_openAt_comm_of_pair_ne
            sort target id eigen 0 replacement body
            hDistinct hReplacement.2
            hReplacementFresh hBodyFresh
      let canonical :=
        FreshVariable.fresh_id sort [body]
      let openedCanonical :=
        Formula.openAt sort 0
          (.var (.fvar sort canonical)) body
      have hCanonicalFresh :
          (sort, canonical) ∉
            Formula.freeSupport body := by
        dsimp [canonical]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hCanonicalTerm :
          Term.Admissible
            (.var (.fvar sort canonical)) sort :=
        ⟨TermWellSorted.fvar sort canonical,
          TermScoped.fvar sort canonical⟩
      have hOpenedCanonical :
          Formula.Admissible openedCanonical := by
        dsimp [openedCanonical]
        exact Formula.Admissible.forall_openAt
          sort hSource hCanonicalTerm
      have hCanonicalRename :
          Formula.substituteFree sort canonical
              (.var (.fvar sort eigen))
              openedCanonical =
            opened := by
        calc
          Formula.substituteFree sort canonical
              (.var (.fvar sort eigen))
              openedCanonical =
            Formula.openAt sort 0
              (.var (.fvar sort eigen))
              (Formula.closeFreeAt sort canonical 0
                openedCanonical) := by
                  symm
                  exact
                    Formula.openAt_closeFreeAt_eq_substituteFree
                      sort canonical 0
                      (.var (.fvar sort eigen))
                      openedCanonical
          _ = opened := by
            rw [Formula.closeFreeAt_openAt
              sort canonical 0 body hCanonicalFresh]
      have hOpenedEquivalent :
          Derives P.theory []
            (Formula.iff
              (formula D opened)
              (Formula.substituteFree sort
                (source_id canonical)
                (.var (.fvar sort (source_id eigen)))
                (formula D openedCanonical))) := by
        have hRecursive :=
          formula_substitute_iff
            P sort canonical hEigenTerm
              openedCanonical hOpenedCanonical
        rw [hCanonicalRename] at hRecursive
        simpa [formula_substitution_closure,
          term_flat_closure, term,
          close_witnesses_from,
          condition_conjunction] using hRecursive
      have hOriginalAt :=
        formula_forall_at_iff
          P sort body hSource eigen
            hBodyFresh <| by
              simpa [canonical, openedCanonical,
                opened] using hOpenedEquivalent
      let canonicalSubstituted :=
        FreshVariable.fresh_id sort [substituted]
      let openedCanonicalSubstituted :=
        Formula.openAt sort 0
          (.var (.fvar sort canonicalSubstituted))
          substituted
      have hCanonicalSubstitutedFresh :
          (sort, canonicalSubstituted) ∉
            Formula.freeSupport substituted := by
        dsimp [canonicalSubstituted]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hCanonicalSubstitutedTerm :
          Term.Admissible
            (.var (.fvar sort
              canonicalSubstituted)) sort :=
        ⟨TermWellSorted.fvar sort
            canonicalSubstituted,
          TermScoped.fvar sort
            canonicalSubstituted⟩
      have hOpenedCanonicalSubstituted :
          Formula.Admissible
            openedCanonicalSubstituted := by
        dsimp [openedCanonicalSubstituted]
        exact Formula.Admissible.forall_openAt
          sort hSubstitutedSource
            hCanonicalSubstitutedTerm
      have hCanonicalSubstitutedRename :
          Formula.substituteFree sort
              canonicalSubstituted
              (.var (.fvar sort eigen))
              openedCanonicalSubstituted =
            openedSubstituted := by
        calc
          Formula.substituteFree sort
              canonicalSubstituted
              (.var (.fvar sort eigen))
              openedCanonicalSubstituted =
            Formula.openAt sort 0
              (.var (.fvar sort eigen))
              (Formula.closeFreeAt sort
                canonicalSubstituted 0
                openedCanonicalSubstituted) := by
                  symm
                  exact
                    Formula.openAt_closeFreeAt_eq_substituteFree
                      sort canonicalSubstituted 0
                      (.var (.fvar sort eigen))
                      openedCanonicalSubstituted
          _ = openedSubstituted := by
            rw [Formula.closeFreeAt_openAt
              sort canonicalSubstituted 0
              substituted
                hCanonicalSubstitutedFresh]
      have hOpenedSubstitutedEquivalent :
          Derives P.theory []
            (Formula.iff
              (formula D openedSubstituted)
              (Formula.substituteFree sort
                (source_id canonicalSubstituted)
                (.var (.fvar sort (source_id eigen)))
                (formula D
                  openedCanonicalSubstituted))) := by
        have hRecursive :=
          formula_substitute_iff
            P sort canonicalSubstituted hEigenTerm
              openedCanonicalSubstituted
                hOpenedCanonicalSubstituted
        rw [hCanonicalSubstitutedRename]
          at hRecursive
        simpa [formula_substitution_closure,
          term_flat_closure, term,
          close_witnesses_from,
          condition_conjunction] using hRecursive
      have hSubstitutedAt :=
        formula_forall_at_iff
          P sort substituted
            hSubstitutedSource eigen
            hSubstitutedFresh <| by
              simpa [canonicalSubstituted,
                openedCanonicalSubstituted,
                openedSubstituted] using
                  hOpenedSubstitutedEquivalent
      have hBodyRecursive :=
        formula_substitute_iff
          P target id hReplacement
            opened hOpened
      rw [hOpenSubstitution] at hBodyRecursive
      have hUnderBinder :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.forall_iff_mono
          (T := P.theory) (Γ := [])
          (sort := sort)
          (eigen := source_id eigen)
          (theory_fresh P sort
            (source_id eigen))
          (by simp)
          hBodyRecursive
      have hCompiledFresh :=
        term_compiled_source_fresh
          D 0 sort eigen replacement
            hReplacementFresh
      have hQuantifierClosure :=
        formula_substitution_closure_forall_iff
          P hReplacement (source_id id)
          (formula_admissible D hOpened)
          (formula_witness_fresh D opened)
          sort (source_id eigen)
          hEncodedDistinct hCompiledFresh.2
            hCompiledFresh.1
      have hOriginalClosure :=
        formula_substitution_closure_iff_mono_theory
          P.theory_sentence D 0 hReplacement
            (source_id id) hOriginalAt
      simpa [formula, Formula.substituteFree,
        substituted, eigen, opened,
        openedSubstituted] using
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
            hSubstitutedAt <|
              _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
                hUnderBinder <|
                  _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
                    (_root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
                      hQuantifierClosure)
                    (_root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
                      hOriginalClosure)
  | existsE sort body =>
      let substituted :=
        Formula.substituteFree
          target id replacement body
      let eigen :=
        substitution_fresh_id
          sort target id replacement body
      let opened :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) body
      let openedSubstituted :=
        Formula.openAt sort 0
          (.var (.fvar sort eigen)) substituted
      have hEigenTerm :
          Term.Admissible
            (.var (.fvar sort eigen)) sort :=
        ⟨TermWellSorted.fvar sort eigen,
          TermScoped.fvar sort eigen⟩
      have hBodyFresh :
          (sort, eigen) ∉
            Formula.freeSupport body := by
        simpa [eigen] using
          substitution_fresh_id_body
            sort target id replacement body
      have hSubstitutedFresh :
          (sort, eigen) ∉
            Formula.freeSupport substituted := by
        simpa [eigen, substituted] using
          substitution_fresh_id_substituted
            sort target id replacement body
      have hReplacementFresh :
          (sort, eigen) ∉
            Term.freeSupport replacement := by
        simpa [eigen] using
          substitution_fresh_id_replacement
            sort target id replacement body
      have hDistinct :
          (target, id) ≠ (sort, eigen) := by
        simpa [eigen] using
          substitution_fresh_id_ne
            sort target id replacement body
      have hEncodedDistinct :
          (target, source_id id) ≠
            (sort, source_id eigen) := by
        intro hEqual
        apply hDistinct
        have hSort :
            target = sort :=
          congrArg
            (fun pair :
              σ.SortSymbol × FreeVarId =>
                pair.1) hEqual
        have hId :
            id = eigen :=
          source_id_injective <|
            congrArg
              (fun pair :
                σ.SortSymbol × FreeVarId =>
                  pair.2) hEqual
        exact Prod.ext hSort hId
      have hOpened :
          Formula.Admissible opened := by
        dsimp [opened]
        exact Formula.Admissible.exists_openAt
          sort hSource hEigenTerm
      have hSubstitutedSource :
          Formula.Admissible
            (Formula.existsE sort substituted) := by
        simpa [substituted] using
          Formula.Admissible.substituteFree
            target id hSource hReplacement
      have hOpenedSubstituted :
          Formula.Admissible openedSubstituted := by
        dsimp [openedSubstituted]
        exact Formula.Admissible.exists_openAt
          sort hSubstitutedSource hEigenTerm
      have hOpenSubstitution :
          Formula.substituteFree target id
              replacement opened =
            openedSubstituted := by
        dsimp [opened, openedSubstituted,
          substituted]
        exact
          Formula.substituteFree_openAt_comm_of_pair_ne
            sort target id eigen 0 replacement body
            hDistinct hReplacement.2
            hReplacementFresh hBodyFresh
      let canonical :=
        FreshVariable.fresh_id sort [body]
      let openedCanonical :=
        Formula.openAt sort 0
          (.var (.fvar sort canonical)) body
      have hCanonicalFresh :
          (sort, canonical) ∉
            Formula.freeSupport body := by
        dsimp [canonical]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hCanonicalTerm :
          Term.Admissible
            (.var (.fvar sort canonical)) sort :=
        ⟨TermWellSorted.fvar sort canonical,
          TermScoped.fvar sort canonical⟩
      have hOpenedCanonical :
          Formula.Admissible openedCanonical := by
        dsimp [openedCanonical]
        exact Formula.Admissible.exists_openAt
          sort hSource hCanonicalTerm
      have hCanonicalRename :
          Formula.substituteFree sort canonical
              (.var (.fvar sort eigen))
              openedCanonical =
            opened := by
        calc
          Formula.substituteFree sort canonical
              (.var (.fvar sort eigen))
              openedCanonical =
            Formula.openAt sort 0
              (.var (.fvar sort eigen))
              (Formula.closeFreeAt sort canonical 0
                openedCanonical) := by
                  symm
                  exact
                    Formula.openAt_closeFreeAt_eq_substituteFree
                      sort canonical 0
                      (.var (.fvar sort eigen))
                      openedCanonical
          _ = opened := by
            rw [Formula.closeFreeAt_openAt
              sort canonical 0 body hCanonicalFresh]
      have hOpenedEquivalent :
          Derives P.theory []
            (Formula.iff
              (formula D opened)
              (Formula.substituteFree sort
                (source_id canonical)
                (.var (.fvar sort (source_id eigen)))
                (formula D openedCanonical))) := by
        have hRecursive :=
          formula_substitute_iff
            P sort canonical hEigenTerm
              openedCanonical hOpenedCanonical
        rw [hCanonicalRename] at hRecursive
        simpa [formula_substitution_closure,
          term_flat_closure, term,
          close_witnesses_from,
          condition_conjunction] using hRecursive
      have hOriginalAt :=
        formula_exists_at_iff
          P sort body hSource eigen
            hBodyFresh <| by
              simpa [canonical, openedCanonical,
                opened] using hOpenedEquivalent
      let canonicalSubstituted :=
        FreshVariable.fresh_id sort [substituted]
      let openedCanonicalSubstituted :=
        Formula.openAt sort 0
          (.var (.fvar sort canonicalSubstituted))
          substituted
      have hCanonicalSubstitutedFresh :
          (sort, canonicalSubstituted) ∉
            Formula.freeSupport substituted := by
        dsimp [canonicalSubstituted]
        exact FreshVariable.fresh_id_not_mem_m
          (by simp)
      have hCanonicalSubstitutedTerm :
          Term.Admissible
            (.var (.fvar sort
              canonicalSubstituted)) sort :=
        ⟨TermWellSorted.fvar sort
            canonicalSubstituted,
          TermScoped.fvar sort
            canonicalSubstituted⟩
      have hOpenedCanonicalSubstituted :
          Formula.Admissible
            openedCanonicalSubstituted := by
        dsimp [openedCanonicalSubstituted]
        exact Formula.Admissible.exists_openAt
          sort hSubstitutedSource
            hCanonicalSubstitutedTerm
      have hCanonicalSubstitutedRename :
          Formula.substituteFree sort
              canonicalSubstituted
              (.var (.fvar sort eigen))
              openedCanonicalSubstituted =
            openedSubstituted := by
        calc
          Formula.substituteFree sort
              canonicalSubstituted
              (.var (.fvar sort eigen))
              openedCanonicalSubstituted =
            Formula.openAt sort 0
              (.var (.fvar sort eigen))
              (Formula.closeFreeAt sort
                canonicalSubstituted 0
                openedCanonicalSubstituted) := by
                  symm
                  exact
                    Formula.openAt_closeFreeAt_eq_substituteFree
                      sort canonicalSubstituted 0
                      (.var (.fvar sort eigen))
                      openedCanonicalSubstituted
          _ = openedSubstituted := by
            rw [Formula.closeFreeAt_openAt
              sort canonicalSubstituted 0
              substituted
                hCanonicalSubstitutedFresh]
      have hOpenedSubstitutedEquivalent :
          Derives P.theory []
            (Formula.iff
              (formula D openedSubstituted)
              (Formula.substituteFree sort
                (source_id canonicalSubstituted)
                (.var (.fvar sort (source_id eigen)))
                (formula D
                  openedCanonicalSubstituted))) := by
        have hRecursive :=
          formula_substitute_iff
            P sort canonicalSubstituted hEigenTerm
              openedCanonicalSubstituted
                hOpenedCanonicalSubstituted
        rw [hCanonicalSubstitutedRename]
          at hRecursive
        simpa [formula_substitution_closure,
          term_flat_closure, term,
          close_witnesses_from,
          condition_conjunction] using hRecursive
      have hSubstitutedAt :=
        formula_exists_at_iff
          P sort substituted
            hSubstitutedSource eigen
            hSubstitutedFresh <| by
              simpa [canonicalSubstituted,
                openedCanonicalSubstituted,
                openedSubstituted] using
                  hOpenedSubstitutedEquivalent
      have hBodyRecursive :=
        formula_substitute_iff
          P target id hReplacement
            opened hOpened
      rw [hOpenSubstitution] at hBodyRecursive
      have hUnderBinder :=
        _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.exists_iff_mono
          (T := P.theory) (Γ := [])
          (sort := sort)
          (eigen := source_id eigen)
          (theory_fresh P sort
            (source_id eigen))
          (by simp)
          hBodyRecursive
      have hCompiledFresh :=
        term_compiled_source_fresh
          D 0 sort eigen replacement
            hReplacementFresh
      have hQuantifierClosure :=
        formula_substitution_closure_exists_iff
          P hReplacement (source_id id)
          (formula_admissible D hOpened)
          (formula_witness_fresh D opened)
          sort (source_id eigen)
          hEncodedDistinct hCompiledFresh.2
            hCompiledFresh.1
      have hOriginalClosure :=
        formula_substitution_closure_iff_mono_theory
          P.theory_sentence D 0 hReplacement
            (source_id id) hOriginalAt
      simpa [formula, Formula.substituteFree,
        substituted, eigen, opened,
        openedSubstituted] using
          _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
            hSubstitutedAt <|
              _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
                hUnderBinder <|
                  _root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_trans
                    (_root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
                      hQuantifierClosure)
                    (_root_.YesMetaZFC.Logic.FirstOrder.Metatheory.Derives.iff_symm
                      hOriginalClosure)
termination_by Formula.complexity source
decreasing_by
  all_goals
    simp_all [Formula.complexity] <;>
      first
      | exact Nat.lt_succ_of_le
          (Nat.le_max_left _ _)
      | exact Nat.lt_succ_of_le
          (Nat.le_max_right _ _)
      | omega

/--
把全称公式编译器的 canonical binder 改名为任意源层新鲜变量。

完整替换定理已经负责证明两个打开体之间的编译一致性，因此公开接口不再要求
调用方提交额外的 substitution 合同。
-/
theorem formula_forall_iff_at
    (P : GraphPresentation D)
    (sort : σ.SortSymbol) (body : Formula σ)
    (hSource :
      Formula.Admissible
        (Formula.forallE sort body))
    (eigen : FreeVarId)
    (hEigenFresh :
      (sort, eigen) ∉ Formula.freeSupport body) :
    Derives P.theory []
      (Formula.iff
        (formula D (Formula.forallE sort body))
        (Formula.forallE sort
          (Formula.closeFreeAt sort
            (source_id eigen) 0
            (formula D
              (Formula.openAt sort 0
                (.var (.fvar sort eigen)) body))))) := by
  let canonical :=
    FreshVariable.fresh_id sort [body]
  let openedCanonical :=
    Formula.openAt sort 0
      (.var (.fvar sort canonical)) body
  let openedTarget :=
    Formula.openAt sort 0
      (.var (.fvar sort eigen)) body
  have hCanonicalFresh :
      (sort, canonical) ∉
        Formula.freeSupport body := by
    dsimp [canonical]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hEigenTerm :
      Term.Admissible
        (.var (.fvar sort eigen)) sort :=
    ⟨TermWellSorted.fvar sort eigen,
      TermScoped.fvar sort eigen⟩
  have hCanonicalTerm :
      Term.Admissible
        (.var (.fvar sort canonical)) sort :=
    ⟨TermWellSorted.fvar sort canonical,
      TermScoped.fvar sort canonical⟩
  have hOpenedCanonical :
      Formula.Admissible openedCanonical := by
    dsimp [openedCanonical]
    exact Formula.Admissible.forall_openAt
      sort hSource hCanonicalTerm
  have hRename :
      Formula.substituteFree sort canonical
          (.var (.fvar sort eigen))
          openedCanonical =
        openedTarget := by
    calc
      Formula.substituteFree sort canonical
          (.var (.fvar sort eigen))
          openedCanonical =
        Formula.openAt sort 0
          (.var (.fvar sort eigen))
          (Formula.closeFreeAt sort canonical 0
            openedCanonical) := by
              symm
              exact
                Formula.openAt_closeFreeAt_eq_substituteFree
                  sort canonical 0
                  (.var (.fvar sort eigen))
                  openedCanonical
      _ = openedTarget := by
        rw [Formula.closeFreeAt_openAt
          sort canonical 0 body hCanonicalFresh]
  have hOpenedEquivalent :
      Derives P.theory []
        (Formula.iff
          (formula D openedTarget)
          (Formula.substituteFree sort
            (source_id canonical)
            (.var (.fvar sort (source_id eigen)))
            (formula D openedCanonical))) := by
    have hSubstitution :=
      formula_substitute_iff
        P sort canonical hEigenTerm
          openedCanonical hOpenedCanonical
    rw [hRename] at hSubstitution
    simpa [formula_substitution_closure,
      term_flat_closure, term,
      close_witnesses_from,
      condition_conjunction,
      canonical, openedCanonical,
      openedTarget] using hSubstitution
  exact formula_forall_at_iff
    P sort body hSource eigen hEigenFresh <| by
      simpa [canonical, openedCanonical,
        openedTarget] using hOpenedEquivalent

/--
编译有限全称闭包时，源变量编号只发生奇数区重编码。
-/
theorem formula_forall_close_iff
    (P : GraphPresentation D)
    (sort : σ.SortSymbol) (eigen : FreeVarId)
    (source : Formula σ)
    (hSource : Formula.Admissible source) :
    Derives P.theory []
      (Formula.iff
        (formula D
          (Formula.forallE sort
            (Formula.closeFreeAt sort eigen 0 source)))
        (Formula.forallE sort
          (Formula.closeFreeAt sort
            (source_id eigen) 0
            (formula D source)))) := by
  have hClosed :
      Formula.Admissible
        (Formula.forallE sort
          (Formula.closeFreeAt sort eigen 0 source)) :=
    Formula.Admissible.forall_closeFreeAt
      sort eigen hSource
  simpa [Formula.openAt_closeFreeAt] using
    formula_forall_iff_at
      P sort
        (Formula.closeFreeAt sort eigen 0 source)
        hClosed eigen
        (Formula.not_mem_freeSupport_closeFreeAt
          sort eigen 0 source)

/--
函数图编译后的全称公式可直接特化为源层 opening 的编译，不再向调用方暴露
任何求值闭包中间正规形。
-/
theorem formula_forall_elim
    (P : GraphPresentation D)
    (sort : σ.SortSymbol) (body : Formula σ)
    (source : Term σ)
    (hForall :
      Formula.Admissible
        (Formula.forallE sort body))
    (hSource : Term.Admissible source sort) :
    Derives P.theory []
      (Formula.imp
        (formula D
          (Formula.forallE sort body))
        (formula D
          (Formula.openAt sort 0 source body))) := by
  have hOpened :
      Formula.Admissible
        (Formula.openAt sort 0 source body) :=
    Formula.Admissible.forall_openAt
      sort hForall hSource
  apply Derives.imp_intro
    (hAntecedentCheck :=
      Formula.check_certificate_of_admissible
        (formula_admissible D hForall))
  let Γ : Context σ :=
    [formula D (Formula.forallE sort body)]
  let eigen :=
    FreshVariable.fresh_id sort [body]
  let opened :=
    Formula.openAt sort 0
      (.var (.fvar sort eigen)) body
  let compiled := term D 0 source
  have hFresh :
      (sort, eigen) ∉
        Formula.freeSupport body := by
    dsimp [eigen]
    exact FreshVariable.fresh_id_not_mem_m
      (by simp)
  have hOpened :
      Formula.Admissible opened := by
    dsimp [opened]
    exact Formula.Admissible.forall_openAt
      sort hForall
        ⟨TermWellSorted.fvar sort eigen,
          TermScoped.fvar sort eigen⟩
  have hCompiled :
      Term.Admissible compiled.value sort := by
    exact
      ⟨(term_well_formed D 0 hSource.1).1,
        (term_scoped D 0 hSource.2).1⟩
  have hUniversal :
      Derives P.theory Γ
        (Formula.forallE sort
          (Formula.closeFreeAt sort
            (source_id eigen) 0
            (formula D opened))) := by
    exact Derives.formula_cast
      (by simp [formula, eigen, opened])
      (Derives.assumption_of_mem
        (by simp [Γ])
        (hFormulaCheck :=
          Formula.check_certificate_of_admissible
            (formula_admissible D hForall)))
  have hSpecialized :
      Derives P.theory Γ
        (Formula.substituteFree sort
          (source_id eigen) compiled.value
          (formula D opened)) := by
    simpa [Formula.openAt_closeFreeAt_eq_substituteFree,
      compiled] using
        (Derives.forall_elim
          (term := compiled.value) hUniversal)
  have hClosure :
      Derives P.theory Γ
        (formula_substitution_closure
          D 0 source sort (source_id eigen)
          (formula D opened)) := by
    simpa [formula_substitution_closure, compiled] using
      P.term_flat_derives 0 hSource
        (Γ := Γ)
        (fun index hLower hUpper candidate
            hCandidate => by
          rw [List.mem_singleton.mp hCandidate]
          exact formula_witness_fresh
            D (Formula.forallE sort body) index)
        (fun value =>
          Formula.substituteFree sort
            (source_id eigen) value
            (formula D opened))
        (by
          intro value hValue
          exact Formula.Admissible.substituteFree
            sort (source_id eigen)
            (formula_admissible D hOpened)
            hValue)
        (by simpa [compiled] using hSpecialized)
  have hEquivalent :=
    (P.formula_substitute_iff
      sort eigen hSource opened hOpened).context_weaken_cons
        (assumption :=
          formula D (Formula.forallE sort body))
  have hDirect :=
    Derives.iff_elim_left
      hEquivalent hClosure
  have hSubstituteOpen :
      Formula.substituteFree sort eigen
          source opened =
        Formula.openAt sort 0 source body := by
    calc
      Formula.substituteFree sort eigen
          source opened =
        Formula.openAt sort 0 source
          (Formula.closeFreeAt sort eigen 0
            opened) := by
              symm
              exact
                Formula.openAt_closeFreeAt_eq_substituteFree
                  sort eigen 0 source opened
      _ = Formula.openAt sort 0 source body := by
        rw [Formula.closeFreeAt_openAt
          sort eigen 0 body hFresh]
  rw [hSubstituteOpen] at hDirect
  exact hDirect

end GraphPresentation

end FunctionGraphElimination
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
