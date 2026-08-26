import YesMetaZFC.Logic.FirstOrder.Derivation
import YesMetaZFC.Logic.FirstOrder.Admissibility
/-!
# 一阶完备性证明的证明论基础
本模块位于可检查 `Derives` 核之上，只建立后续 Lindenbaum、Henkin 与典范模型构造
需要的证明论接口：
* 有限公式列表诱导的理论；
* 任意 `Derives` 证书所使用的有限理论公理支持；
* 候选理论的有限一致性；
* Henkin 见证扩张所需的良构性边界。
这里不引入模型构造，也不改变底层推导判断。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
namespace Theory
/-- 有限公式列表诱导的理论。列表顺序和重复成员不影响理论成员关系。 -/
def ofList {σ : Signature.{u, v, w}} (formulas : List (Formula σ)) : Theory σ :=
  fun formula => formula ∈ formulas
@[simp]
theorem mem_ofList {σ : Signature.{u, v, w}} {formulas : List (Formula σ)}
    {formula : Formula σ} :
    ofList formulas formula ↔ formula ∈ formulas :=
  Iff.rfl
end Theory

namespace ND_Raw

/-- 原始推导树实际引用的理论公理列表。 -/
def theorySupport
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ} :
    ND_Raw T Γ φ → List (Formula σ)
  | .assumption _ => []
  | .theoryAxiom _ => [φ]
  | .contextWeakening _ hDerives => theorySupport hDerives
  | .theoryWeakening _ hDerives => theorySupport hDerives
  | .truthIntro => []
  | .falsumElim hFalse => theorySupport hFalse
  | .conjIntro hLeft hRight =>
      theorySupport hLeft ++ theorySupport hRight
  | .conjElimLeft hConj => theorySupport hConj
  | .conjElimRight hConj => theorySupport hConj
  | .disjIntroLeft hLeft => theorySupport hLeft
  | .disjIntroRight hRight => theorySupport hRight
  | .disjElim hDisj hLeft hRight =>
      (theorySupport hDisj ++ theorySupport hLeft) ++
        theorySupport hRight
  | .impIntro hBody => theorySupport hBody
  | .impElim hImp hAntecedent =>
      theorySupport hImp ++ theorySupport hAntecedent
  | .iffIntro hForward hBackward =>
      theorySupport hForward ++ theorySupport hBackward
  | .iffElimLeft hIff hRight =>
      theorySupport hIff ++ theorySupport hRight
  | .iffElimRight hIff hLeft =>
      theorySupport hIff ++ theorySupport hLeft
  | .negIntro hFalse => theorySupport hFalse
  | .negElim hBody hNeg =>
      theorySupport hBody ++ theorySupport hNeg
  | .byContradiction hRefute => theorySupport hRefute
  | .forallIntro _ _ hBody => theorySupport hBody
  | .forallElim hForall => theorySupport hForall
  | .existsIntro hBody => theorySupport hBody
  | .existsElim _ _ _ hExists hCase =>
      theorySupport hExists ++ theorySupport hCase
  | .equalityRefl _ => []
  | .equalityElim hEquality hBody =>
      theorySupport hEquality ++ theorySupport hBody

/-- 计算出的每个理论公理确实属于原理论。 -/
theorem theorySupport_subset
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (raw : ND_Raw T Γ φ) :
    ∀ formula, formula ∈ raw.theorySupport → T formula := by
  induction raw with
  | assumption =>
      simp [theorySupport]
  | theoryAxiom hMem =>
      intro formula hFormula
      simp only [theorySupport, List.mem_singleton] at hFormula
      subst formula
      exact hMem
  | contextWeakening _ hDerives ih =>
      simpa [theorySupport] using ih
  | theoryWeakening hSubset hDerives ih =>
      intro formula hFormula
      exact hSubset formula <| ih formula <| by
        simpa [theorySupport] using hFormula
  | truthIntro =>
      simp [theorySupport]
  | falsumElim hFalse ih =>
      simpa [theorySupport] using ih
  | conjIntro hLeft hRight ihLeft ihRight
  | impElim hLeft hRight ihLeft ihRight
  | iffIntro hLeft hRight ihLeft ihRight
  | iffElimLeft hLeft hRight ihLeft ihRight
  | iffElimRight hLeft hRight ihLeft ihRight
  | negElim hLeft hRight ihLeft ihRight
  | equalityElim hLeft hRight ihLeft ihRight =>
      intro formula hFormula
      rcases List.mem_append.mp hFormula with hLeft | hRight
      · exact ihLeft formula hLeft
      · exact ihRight formula hRight
  | conjElimLeft hConj ih
  | conjElimRight hConj ih
  | disjIntroLeft hConj ih
  | disjIntroRight hConj ih
  | impIntro hConj ih
  | negIntro hConj ih
  | byContradiction hConj ih
  | forallElim hConj ih
  | existsIntro hConj ih =>
      simpa [theorySupport] using ih
  | disjElim hDisj hLeft hRight ihDisj ihLeft ihRight =>
      intro formula hFormula
      rcases List.mem_append.mp hFormula with hInitial | hRight
      · rcases List.mem_append.mp hInitial with hDisj | hLeft
        · exact ihDisj formula hDisj
        · exact ihLeft formula hLeft
      · exact ihRight formula hRight
  | forallIntro hTheoryFresh hContextFresh hBody ih =>
      simpa [theorySupport] using ih
  | existsElim hTheoryFresh hContextFresh hConclusionFresh
      hExists hCase ihExists ihCase =>
      intro formula hFormula
      rcases List.mem_append.mp hFormula with hExists | hCase
      · exact ihExists formula hExists
      · exact ihCase formula hCase
  | equalityRefl =>
      simp [theorySupport]

/-- 把原始树重放到其计算出的有限理论支持上。 -/
def restrictTheory
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (raw : ND_Raw T Γ φ) :
    ND_Raw (Theory.ofList raw.theorySupport) Γ φ :=
  match raw with
  | .assumption hMem =>
      .assumption hMem
  | .theoryAxiom hMem =>
      .theoryAxiom (by simp [theorySupport, Theory.ofList])
  | .contextWeakening hSubset hDerives =>
      .contextWeakening hSubset (restrictTheory hDerives)
  | .theoryWeakening hSubset hDerives =>
      restrictTheory hDerives
  | .truthIntro =>
      .truthIntro
  | .falsumElim hFalse =>
      .falsumElim (restrictTheory hFalse)
  | .conjIntro hLeft hRight =>
      .conjIntro
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inl hFormula))
          (restrictTheory hLeft))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inr hFormula))
          (restrictTheory hRight))
  | .conjElimLeft hConj =>
      .conjElimLeft (restrictTheory hConj)
  | .conjElimRight hConj =>
      .conjElimRight (restrictTheory hConj)
  | .disjIntroLeft hLeft =>
      .disjIntroLeft (restrictTheory hLeft)
  | .disjIntroRight hRight =>
      .disjIntroRight (restrictTheory hRight)
  | .disjElim hDisj hLeft hRight =>
      .disjElim
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inl hFormula))))
          (restrictTheory hDisj))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr
              (Or.inl (List.mem_append.mpr (Or.inr hFormula))))
          (restrictTheory hLeft))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inr hFormula))
          (restrictTheory hRight))
  | .impIntro hBody =>
      .impIntro (restrictTheory hBody)
  | .impElim hImp hAntecedent =>
      .impElim
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inl hFormula))
          (restrictTheory hImp))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inr hFormula))
          (restrictTheory hAntecedent))
  | .iffIntro hForward hBackward =>
      .iffIntro
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inl hFormula))
          (restrictTheory hForward))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inr hFormula))
          (restrictTheory hBackward))
  | .iffElimLeft hIff hRight =>
      .iffElimLeft
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inl hFormula))
          (restrictTheory hIff))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inr hFormula))
          (restrictTheory hRight))
  | .iffElimRight hIff hLeft =>
      .iffElimRight
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inl hFormula))
          (restrictTheory hIff))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inr hFormula))
          (restrictTheory hLeft))
  | .negIntro hFalse =>
      .negIntro (restrictTheory hFalse)
  | .negElim hBody hNeg =>
      .negElim
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inl hFormula))
          (restrictTheory hBody))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inr hFormula))
          (restrictTheory hNeg))
  | .byContradiction hRefute =>
      .byContradiction (restrictTheory hRefute)
  | .forallIntro hTheoryFresh hContextFresh hBody =>
      .forallIntro
        (fun formula hFormula =>
          hTheoryFresh formula
            (hBody.theorySupport_subset formula hFormula))
        hContextFresh
        (restrictTheory hBody)
  | .forallElim hForall =>
      .forallElim (restrictTheory hForall)
  | .existsIntro hBody =>
      .existsIntro (restrictTheory hBody)
  | .existsElim hTheoryFresh hContextFresh hConclusionFresh
      hExists hCase =>
      .existsElim
        (fun formula hFormula =>
          hTheoryFresh formula <| by
            rcases List.mem_append.mp hFormula with
              hExistsFormula | hCaseFormula
            · exact hExists.theorySupport_subset
                formula hExistsFormula
            · exact hCase.theorySupport_subset
                formula hCaseFormula)
        hContextFresh hConclusionFresh
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inl hFormula))
          (restrictTheory hExists))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inr hFormula))
          (restrictTheory hCase))
  | .equalityRefl sort =>
      .equalityRefl sort
  | .equalityElim hEquality hBody =>
      .equalityElim
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inl hFormula))
          (restrictTheory hEquality))
        (.theoryWeakening (fun formula hFormula =>
            List.mem_append.mpr (Or.inr hFormula))
          (restrictTheory hBody))

/-- 子树检查成功会给出该子树根公式的检查等式。 -/
theorem root_check_eq_true_of_checked
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (raw : ND_Raw T Γ φ) (hCheck : raw.check = true) :
    Formula.check_admissible φ = true :=
  raw.root_checked hCheck

/-- 原始树检查成功时，有限理论重放树同样检查成功。 -/
theorem restrictTheory_checked
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ}
    (raw : ND_Raw T Γ φ) :
    raw.check = true → raw.restrictTheory.check = true := by
  induction raw <;>
    intro hCheck <;>
    simp only [check, Bool.and_eq_true_iff] at hCheck ⊢ <;>
    simp_all [restrictTheory, theorySupport, check]
  case conjIntro hLeft hRight hLeft_ih hRight_ih =>
    exact ⟨
      ⟨hLeft.root_check_eq_true_of_checked hCheck.1.2, hLeft_ih⟩,
      hRight.root_check_eq_true_of_checked hCheck.2, hRight_ih
    ⟩
  case disjElim hDisj hLeft hRight hDisj_ih hLeft_ih hRight_ih =>
    exact ⟨
      ⟨
        ⟨hDisj.root_check_eq_true_of_checked hCheck.1.1.2, hDisj_ih⟩,
        hLeft_ih
      ⟩,
      hRight_ih
    ⟩
  case impElim hImp hAntecedent hImp_ih hAntecedent_ih =>
    exact ⟨
      ⟨hImp.root_check_eq_true_of_checked hCheck.1.2, hImp_ih⟩,
      hAntecedent.root_check_eq_true_of_checked hCheck.2,
      hAntecedent_ih
    ⟩
  case iffIntro hForward hBackward hForward_ih hBackward_ih =>
    exact ⟨
      ⟨hForward.root_check_eq_true_of_checked hCheck.1.2, hForward_ih⟩,
      hBackward.root_check_eq_true_of_checked hCheck.2,
      hBackward_ih
    ⟩
  case iffElimLeft hIff hRight hIff_ih hRight_ih =>
    exact ⟨
      ⟨hIff.root_check_eq_true_of_checked hCheck.1.2, hIff_ih⟩,
      hRight.root_check_eq_true_of_checked hCheck.2,
      hRight_ih
    ⟩
  case iffElimRight hIff hLeft hIff_ih hLeft_ih =>
    exact ⟨
      ⟨hIff.root_check_eq_true_of_checked hCheck.1.2, hIff_ih⟩,
      hLeft.root_check_eq_true_of_checked hCheck.2,
      hLeft_ih
    ⟩
  case negElim hBody hNeg hBody_ih hNeg_ih =>
    exact ⟨
      ⟨hBody.root_check_eq_true_of_checked hCheck.1.2, hBody_ih⟩,
      hNeg.root_check_eq_true_of_checked hCheck.2, hNeg_ih
    ⟩
  case existsElim hExists hCase hExists_ih hCase_ih =>
    exact ⟨
      ⟨hExists.root_check_eq_true_of_checked hCheck.1.2, hExists_ih⟩,
      hCase_ih
    ⟩
  case equalityElim hEquality hBody hEquality_ih hBody_ih =>
    exact ⟨
      ⟨hEquality.root_check_eq_true_of_checked hCheck.1.2, hEquality_ih⟩,
      hBody.root_check_eq_true_of_checked hCheck.2, hBody_ih
    ⟩

end ND_Raw

namespace Derives
/-- 有限理论列表包含关系允许直接弱化对应的推导。 -/
theorem theory_weaken_ofList {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {small large : List (Formula σ)}
    {Γ : Context σ} {φ : Formula σ} (hSubset : ∀ formula, formula ∈ small → formula ∈ large) (hDerives : Derives (Theory.ofList small) Γ φ) :
    Derives (Theory.ofList large) Γ φ :=
  .theoryWeakening hSubset hDerives
/--
一个推导实际使用的有限理论公理支持。
`formulas` 中每个公式都来自原理论；`derivation` 则只依赖这个有限子理论。
-/
structure FiniteTheorySupport {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (T : Theory σ) (Γ : Context σ) (φ : Formula σ) where
  formulas : List (Formula σ)
  subset : ∀ formula, formula ∈ formulas → T formula
  derivation : Derives (Theory.ofList formulas) Γ φ
namespace FiniteTheorySupport
/-- 有限支持中的推导可以回到原理论。 -/
def toDerives {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {Γ : Context σ} {φ : Formula σ} (support : FiniteTheorySupport T Γ φ) :
    Derives T Γ φ :=
  .theoryWeakening support.subset support.derivation
end FiniteTheorySupport
/--
每个有限 `Derives` 证书只使用原理论中的有限多个公理。
该定理是后续把“理论不一致”还原为有限反证上下文的基础，不依赖理论本身可枚举。
-/
theorem finiteTheorySupport {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} {Γ : Context σ}
    {φ : Formula σ} (hDerives : Derives T Γ φ) :
    Nonempty (FiniteTheorySupport T Γ φ) := by
  rcases hDerives with ⟨cert⟩
  exact ⟨{
    formulas := cert.raw.theorySupport
    subset := cert.raw.theorySupport_subset
    derivation := Derives.of_check cert.raw.restrictTheory
      (cert.raw.restrictTheory_checked cert.checked)
  }⟩
/--
一个公式谓词相对背景理论有限一致：其中任意有限列表都构成一致上下文。
-/
def FinitelyConsistent {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (T Δ : Theory σ) : Prop :=
  ∀ Γ : Context σ, (∀ formula, formula ∈ Γ → Δ formula) →
      Consistent T Γ
namespace FinitelyConsistent
/-- 有限一致性沿候选理论子集向下保持。 -/
theorem mono {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T Δ U : Theory σ} (hConsistent : FinitelyConsistent T Δ) (hSubset : ∀ formula, U formula → Δ formula) :
    FinitelyConsistent T U := by
  intro Γ hΓ
  exact hConsistent Γ fun formula hFormula =>
    hSubset formula (hΓ formula hFormula)
/-- 有限列表理论有限一致，当且仅当整个列表作为上下文一致。 -/
theorem ofList_iff {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {formulas : List (Formula σ)} :
    FinitelyConsistent T (Theory.ofList formulas) ↔
      Consistent T formulas := by
  constructor
  · intro hConsistent
    exact hConsistent formulas (by
      intro formula hFormula
      exact hFormula)
  · intro hConsistent Γ hSubset
    exact Consistent.mono_m hConsistent hSubset
/-- 候选理论不有限一致，当且仅当其中存在一个有限反证上下文。 -/
theorem not_iff_exists_inconsistent_context
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T Δ : Theory σ} :
    ¬ FinitelyConsistent T Δ ↔
      ∃ Γ : Context σ, (∀ formula, formula ∈ Γ → Δ formula) ∧
          Inconsistent T Γ := by
  classical
  constructor
  · intro hNotConsistent
    apply Classical.byContradiction
    intro hNoWitness
    apply hNotConsistent
    intro Γ hΓ hFalse
    exact hNoWitness ⟨Γ, hΓ, hFalse⟩
  · rintro ⟨Γ, hΓ, hFalse⟩ hConsistent
    exact hConsistent Γ hΓ hFalse
/--
若插入单个公式后的候选理论包含一个有限反证上下文，则可以把该公式统一移到
上下文头部，其余公式仍来自原候选理论。
-/
theorem exists_inconsistent_cons_of_insert
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T Δ : Theory σ} {φ : Formula σ} {Γ : Context σ} (hΓ : ∀ formula, formula ∈ Γ → Theory.insert φ Δ formula) (hInconsistent : Inconsistent T Γ) :
    ∃ Γ' : Context σ, (∀ formula, formula ∈ Γ' → Δ formula) ∧
        Inconsistent T (φ :: Γ') := by
  classical
  let Γ' := Γ.filter fun formula => formula ≠ φ
  refine ⟨Γ', ?_, ?_⟩
  · intro formula hFormula
    have hFiltered :
        formula ∈ Γ ∧ formula ≠ φ := by
      simpa [Γ'] using hFormula
    rcases hΓ formula hFiltered.1 with hEq | hMem
    · exact False.elim (hFiltered.2 hEq)
    · exact hMem
  · exact .contextWeakening (by
      intro formula hFormula
      by_cases hEq : formula = φ
      · subst formula
        simp
      · have hFiltered : formula ∈ Γ' := by
          simp [Γ', hFormula, hEq]
        simp [hFiltered]) hInconsistent
/--
经典 Lindenbaum 的全局二分步骤：有限一致候选理论加入 `φ` 或加入 `¬φ`，
至少有一侧仍然有限一致。
-/
theorem extend_or_neg {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T Δ : Theory σ} (hConsistent : FinitelyConsistent T Δ) (φ : Formula σ) (hφ : Formula.Admissible φ) :
    FinitelyConsistent T (Theory.insert φ Δ) ∨
      FinitelyConsistent T (Theory.insert (Formula.neg φ) Δ) := by
  classical
  by_cases hPositive : FinitelyConsistent T (Theory.insert φ Δ)
  · exact Or.inl hPositive
  · right
    apply Classical.byContradiction
    intro hNegative
    rcases not_iff_exists_inconsistent_context.mp hPositive with
      ⟨positiveContext, hPositiveContext, hPositiveFalse⟩
    rcases exists_inconsistent_cons_of_insert
        hPositiveContext hPositiveFalse with
      ⟨positiveBase, hPositiveBase, hPositiveConsFalse⟩
    rcases not_iff_exists_inconsistent_context.mp hNegative with
      ⟨negativeContext, hNegativeContext, hNegativeFalse⟩
    rcases exists_inconsistent_cons_of_insert
        hNegativeContext hNegativeFalse with
      ⟨negativeBase, hNegativeBase, hNegativeConsFalse⟩
    have hNegFormula : Derives T positiveBase (Formula.neg φ) := (incons_cons_iff_m hφ).mp hPositiveConsFalse
    have hDoubleNeg :
        Derives T negativeBase (Formula.neg (Formula.neg φ)) := (incons_cons_iff_m (Formula.Admissible.neg hφ)).mp hNegativeConsFalse
    have hFormula : Derives T negativeBase φ :=
      neg_neg_elim_m hDoubleNeg
    have hCombinedConsistent :
        Consistent T (positiveBase ++ negativeBase) :=
      hConsistent _ (by
        intro formula hFormulaMem
        rcases List.mem_append.mp hFormulaMem with hPositiveMem | hNegativeMem
        · exact hPositiveBase formula hPositiveMem
        · exact hNegativeBase formula hNegativeMem)
    apply hCombinedConsistent
    exact .negElim (.contextWeakening (by
          intro formula hFormulaMem
          simp [hFormulaMem])
        hFormula) (.contextWeakening (by
          intro formula hFormulaMem
          simp [hFormulaMem])
        hNegFormula)
/--
Henkin witness 扩张：候选理论包含相应存在式，且 eigenvariable 对背景理论和候选
理论都新鲜时，加入其 free-variable witness 仍保持有限一致。
-/
theorem insert_henkinWitness {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T Δ : Theory σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hConsistent : FinitelyConsistent T Δ) (hBody : Formula.Admissible body) (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) ∉ Formula.freeSupport formula) (hCandidateFresh :
      ∀ formula, Δ formula → (sort, eigen) ∉ Formula.freeSupport formula) (hExists :
      Δ (Formula.existsE sort (Formula.closeFreeAt sort eigen 0 body))) :
    FinitelyConsistent T (Theory.insert body Δ) := by
  classical
  intro Γ hΓ hInconsistent
  rcases exists_inconsistent_cons_of_insert hΓ hInconsistent with
    ⟨base, hBase, hCaseFalse⟩
  let existential :=
    Formula.existsE sort (Formula.closeFreeAt sort eigen 0 body)
  have hExistential :
      Formula.Admissible existential :=
    Formula.Admissible.exists_closeFreeAt sort eigen hBody
  have hBaseConsistent : Consistent T (existential :: base) :=
    hConsistent _ (by
      intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact hExists
      · exact hBase formula hFormula)
  apply hBaseConsistent
  exact Derives.exists_elim (sort := sort) (eigen := eigen) (body := body) (conclusion := Formula.falsum)
    hTheoryFresh (by
      intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact hCandidateFresh existential hExists
      · exact hCandidateFresh formula (hBase formula hFormula)) (by simp [Formula.freeSupport])
    (.assumption (by simp [existential])) (.contextWeakening (by
        intro formula hFormula
        rcases List.mem_cons.mp hFormula with rfl | hFormula
        · simp
        · simp [hFormula])
      hCaseFalse)
end FinitelyConsistent
/-! ## Proof-carrying 候选理论 -/
/--
完备性构造中的候选理论边界。
背景理论与候选理论仍然使用 raw `Theory`，但结构同时携带双方良构性以及候选理论
相对背景理论的有限一致性证书。
-/
structure WF_Candidate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (T Δ : Theory σ) : Prop where
  wf_background : Theory.Admissible T
  wf_candidate : Theory.Admissible Δ
  wf_consistent : FinitelyConsistent T Δ
namespace WF_Candidate
/-- 良构候选理论的 Lindenbaum 二分扩张。 -/
theorem wf_extend_or_neg {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T Δ : Theory σ} (hCandidate : WF_Candidate T Δ) {φ : Formula σ} (hφ : Formula.Admissible φ) :
    WF_Candidate T (Theory.insert φ Δ) ∨
      WF_Candidate T (Theory.insert (Formula.neg φ) Δ) := by
  rcases FinitelyConsistent.extend_or_neg
      hCandidate.wf_consistent φ hφ with
    hPositive | hNegative
  · exact Or.inl {
      wf_background := hCandidate.wf_background
      wf_candidate :=
        Theory.admissible_insert hφ hCandidate.wf_candidate
      wf_consistent := hPositive
    }
  · exact Or.inr {
      wf_background := hCandidate.wf_background
      wf_candidate :=
        Theory.admissible_insert (Formula.Admissible.neg hφ) hCandidate.wf_candidate
      wf_consistent := hNegative
    }
/-- 良构候选理论的 Henkin witness 扩张。 -/
theorem wf_insert_henkinWitness {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T Δ : Theory σ}
    {sort : σ.SortSymbol} {eigen : FreeVarId} {body : Formula σ} (hCandidate : WF_Candidate T Δ) (hBody : Formula.Admissible body) (hTheoryFresh :
      ∀ formula, T formula → (sort, eigen) ∉ Formula.freeSupport formula) (hCandidateFresh :
      ∀ formula, Δ formula → (sort, eigen) ∉ Formula.freeSupport formula) (hExists :
      Δ (Formula.existsE sort (Formula.closeFreeAt sort eigen 0 body))) :
    WF_Candidate T (Theory.insert body Δ) where
  wf_background := hCandidate.wf_background
  wf_candidate :=
    Theory.admissible_insert hBody hCandidate.wf_candidate
  wf_consistent :=
    FinitelyConsistent.insert_henkinWitness
      hCandidate.wf_consistent hBody
      hTheoryFresh hCandidateFresh hExists
end WF_Candidate
end Derives
end FirstOrder
end Logic
end YesMetaZFC
