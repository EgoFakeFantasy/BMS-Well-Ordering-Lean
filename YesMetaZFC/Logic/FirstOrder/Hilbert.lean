import YesMetaZFC.Logic.FirstOrder.Derivation.Equality
import YesMetaZFC.Logic.FirstOrder.Derivation.Propositional
import YesMetaZFC.Logic.FirstOrder.Derivation.Quantifier
import YesMetaZFC.Logic.FirstOrder.Admissibility
/-!
# 一阶 Hilbert 演绎的标准有限证书
本模块给出与对象集合论内部编码同形的元层 Hilbert 系统。逻辑公理分为十二类
基础模式及其有限次全称闭包；一条证明只能来自逻辑公理、理论成员或两条严格更早
证明行上的 modus ponens。
这里刻意保留标准有限 `List` 证书。它是后续连接 `Derives` 与模型内部证明序列的
中间层：前者通过逻辑公理可靠性映射到自然演绎，后者还需单独处理公式 Gödel 编码
以及模型内 `ω` 的标准性边界。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
universe u v w
/-- 与内部编码十二类基础 Hilbert 模式对应的元层判断。 -/
inductive HilbertBaseAxiom {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] : Formula σ → Prop where
  | implication_distribution (antecedent middle consequent : Formula σ) :
      HilbertBaseAxiom (Formula.imp (Formula.imp antecedent (Formula.imp middle consequent)) (Formula.imp (Formula.imp antecedent middle)
            (Formula.imp antecedent consequent)))
  | self_implication (formula : Formula σ) :
      HilbertBaseAxiom (Formula.imp formula (Formula.imp formula formula))
  | weakening (formula extra : Formula σ) :
      HilbertBaseAxiom (Formula.imp formula (Formula.imp extra formula))
  | contradiction (formula conclusion : Formula σ) :
      HilbertBaseAxiom (Formula.imp formula (Formula.imp (Formula.neg formula) conclusion))
  | classical (formula : Formula σ) :
      HilbertBaseAxiom (Formula.imp (Formula.imp (Formula.neg formula) formula)
          formula)
  | explosion (formula conclusion : Formula σ) :
      HilbertBaseAxiom (Formula.imp (Formula.neg formula) (Formula.imp formula conclusion))
  | case_analysis (formula conclusion : Formula σ) :
      HilbertBaseAxiom (Formula.imp (Formula.imp formula conclusion) (Formula.imp (Formula.imp (Formula.neg formula) conclusion)
            conclusion))
  | forall_specialization (sort : σ.SortSymbol) (body : Formula σ) (term : Term σ) (hTerm : TermWellSorted term sort) (hClosed : Term.BoundClosed term) :
      HilbertBaseAxiom (Formula.imp (Formula.forallE sort body) (Formula.openAt sort 0 term body))
  | forall_distribution (sort : σ.SortSymbol) (antecedent consequent : Formula σ) :
      HilbertBaseAxiom (Formula.imp (Formula.forallE sort (Formula.imp antecedent consequent)) (Formula.imp (Formula.forallE sort antecedent)
            (Formula.forallE sort consequent)))
  | vacuous_forall (sort : σ.SortSymbol) (eigen : FreeVarId) (formula : Formula σ) (hFresh : (sort, eigen) ∉ Formula.freeSupport formula) :
      HilbertBaseAxiom (Formula.imp formula (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 formula)))
  | equality_substitution (sort : σ.SortSymbol) (leftId rightId : FreeVarId) (body : Formula σ) :
      HilbertBaseAxiom (Formula.imp (Formula.equal (Term.var (.fvar sort leftId)) (Term.var (.fvar sort rightId))) (Formula.imp body
            (Formula.substituteFree sort leftId (Term.var (.fvar sort rightId)) body)))
  | equality_reflexivity (sort : σ.SortSymbol) (id : FreeVarId) :
      HilbertBaseAxiom (Formula.equal (Term.var (.fvar sort id)) (Term.var (.fvar sort id)))
/-- 完整逻辑公理是基础模式在具名自由变量上的有限次全称闭包。 -/
inductive HilbertLogicalAxiom {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] : Formula σ → Prop where
  | base {formula : Formula σ} (hBase : HilbertBaseAxiom formula) :
      HilbertLogicalAxiom formula
  | forall_closure
      {formula : Formula σ} (sort : σ.SortSymbol) (eigen : FreeVarId) (hAxiom : HilbertLogicalAxiom formula) :
      HilbertLogicalAxiom (Formula.forallE sort (Formula.closeFreeAt sort eigen 0 formula))
/-- 理论上的 Hilbert 可演绎关系：逻辑公理、理论公理与 MP 的最小闭包。 -/
inductive HilbertDerives {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (theory : Theory σ) : Formula σ → Prop where
  | logical_axiom {formula : Formula σ} (hAxiom : HilbertLogicalAxiom formula) (hAdmissible : Formula.Admissible formula) :
      HilbertDerives theory formula
  | theory_axiom {formula : Formula σ} (hTheory : theory formula) (hAdmissible : Formula.Admissible formula) :
      HilbertDerives theory formula
  | modus_ponens {antecedent consequent : Formula σ} (hAntecedent : HilbertDerives theory antecedent) (hImplication :
        HilbertDerives theory (Formula.imp antecedent consequent)) :
      HilbertDerives theory consequent
/-- 两行在证明列表中按给定顺序严格出现。 -/
def HilbertEarlier {σ : Signature.{u, v, w}} (earlier later : Formula σ) (proof : List (Formula σ)) : Prop :=
  ∃ initial middle suffix,
    proof = initial ++ earlier :: middle ++ later :: suffix
/--
标准有限 Hilbert 证明列表。
每次添加 MP 结论时，前件行必须严格早于蕴含行；两者又都位于新结论之前。这与
内部 `proof_modus_ponens_line_condition` 的索引方向完全一致。
-/
inductive HilbertProof {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] (theory : Theory σ) :
    List (Formula σ) → Prop where
  | nil : HilbertProof theory []
  | logical_axiom {proof : List (Formula σ)} {formula : Formula σ} (hProof : HilbertProof theory proof) (hAxiom : HilbertLogicalAxiom formula)
      (hAdmissible : Formula.Admissible formula) :
      HilbertProof theory (proof ++ [formula])
  | theory_axiom {proof : List (Formula σ)} {formula : Formula σ} (hProof : HilbertProof theory proof) (hTheory : theory formula)
      (hAdmissible : Formula.Admissible formula) :
      HilbertProof theory (proof ++ [formula])
  | modus_ponens
      {proof : List (Formula σ)} {antecedent consequent : Formula σ} (hProof : HilbertProof theory proof) (hEarlier :
        HilbertEarlier antecedent (Formula.imp antecedent consequent) proof) :
      HilbertProof theory (proof ++ [consequent])
namespace HilbertBaseAxiom
/-- 每一类基础 Hilbert 模式都是空理论下的 `Derives` 定理。 -/
theorem derives_empty {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ} (hAxiom : HilbertBaseAxiom formula) (hAdmissible : Formula.Admissible formula) :
    Derives (Theory.empty : Theory σ) [] formula := by
  cases hAxiom with
  | implication_distribution antecedent middle consequent =>
      have hMain :=
        Formula.Admissible.imp_left hAdmissible
      have hAntecedent :=
        Formula.Admissible.imp_left hMain
      have hMiddleConsequent :=
        Formula.Admissible.imp_right hMain
      have hMiddle :=
        Formula.Admissible.imp_left hMiddleConsequent
      have hConsequent :=
        Formula.Admissible.imp_right hMiddleConsequent
      exact Derives.Propositional.imp_distribution
        hAntecedent hMiddle hConsequent
  | self_implication formula =>
      have hFormula :=
        Formula.Admissible.imp_left hAdmissible
      exact Derives.Propositional.imp_const hFormula hFormula
  | weakening formula extra =>
      have hFormula :=
        Formula.Admissible.imp_left hAdmissible
      have hExtra :=
        Formula.Admissible.imp_left (Formula.Admissible.imp_right hAdmissible)
      exact Derives.Propositional.imp_const hFormula hExtra
  | contradiction formula conclusion =>
      have hFormula :=
        Formula.Admissible.imp_left hAdmissible
      have hConclusion :=
        Formula.Admissible.imp_right (Formula.Admissible.imp_right hAdmissible)
      exact Derives.Propositional.imp_neg_elim hFormula hConclusion
  | classical formula =>
      have hFormula :=
        Formula.Admissible.imp_right hAdmissible
      exact Derives.Propositional.classical_reduction hFormula
  | explosion formula conclusion =>
      have hNegFormula :=
        Formula.Admissible.imp_left hAdmissible
      have hFormula :=
        Formula.Admissible.neg_body hNegFormula
      have hConclusion :=
        Formula.Admissible.imp_right (Formula.Admissible.imp_right hAdmissible)
      exact Derives.Propositional.neg_imp_elim hFormula hConclusion
  | case_analysis formula conclusion =>
      have hPositive :=
        Formula.Admissible.imp_left hAdmissible
      have hFormula :=
        Formula.Admissible.imp_left hPositive
      have hConclusion :=
        Formula.Admissible.imp_right hPositive
      have hNegative :=
        Formula.Admissible.imp_left (Formula.Admissible.imp_right hAdmissible)
      nd_apply Derives.impIntro
      nd_apply Derives.impIntro
      nd_apply Derives.byContradiction
      have hPositive :
          Derives (Theory.empty : Theory σ) (Formula.neg conclusion ::
              Formula.imp (Formula.neg formula) conclusion ::
              Formula.imp formula conclusion :: []) (Formula.imp formula conclusion) :=
        .assumption (by simp)
      have hNegative :
          Derives (Theory.empty : Theory σ) (Formula.neg conclusion ::
              Formula.imp (Formula.neg formula) conclusion ::
              Formula.imp formula conclusion :: []) (Formula.imp (Formula.neg formula) conclusion) :=
        .assumption (by simp)
      have hNotConclusion :
          Derives (Theory.empty : Theory σ) (Formula.neg conclusion ::
              Formula.imp (Formula.neg formula) conclusion ::
              Formula.imp formula conclusion :: []) (Formula.neg conclusion) :=
        .assumption (by simp)
      have hNotFormula :
          Derives (Theory.empty : Theory σ) (Formula.neg conclusion ::
              Formula.imp (Formula.neg formula) conclusion ::
              Formula.imp formula conclusion :: []) (Formula.neg formula) := by
        nd_apply Derives.negIntro
        have hFormula :
            Derives (Theory.empty : Theory σ) (formula :: Formula.neg conclusion ::
                Formula.imp (Formula.neg formula) conclusion ::
                Formula.imp formula conclusion :: [])
              formula :=
          .assumption (by simp)
        have hPositive' :=
          Derives.contextWeakening (T := (Theory.empty : Theory σ)) (Γ := Formula.neg conclusion ::
              Formula.imp (Formula.neg formula) conclusion ::
              Formula.imp formula conclusion :: []) (Δ := formula :: Formula.neg conclusion ::
              Formula.imp (Formula.neg formula) conclusion ::
              Formula.imp formula conclusion :: []) (φ := Formula.imp formula conclusion) (by simp) hPositive
        have hNotConclusion' :=
          Derives.contextWeakening (T := (Theory.empty : Theory σ)) (Γ := Formula.neg conclusion ::
              Formula.imp (Formula.neg formula) conclusion ::
              Formula.imp formula conclusion :: []) (Δ := formula :: Formula.neg conclusion ::
              Formula.imp (Formula.neg formula) conclusion ::
              Formula.imp formula conclusion :: []) (φ := Formula.neg conclusion) (by simp) hNotConclusion
        exact Derives.negElim (Derives.impElim hPositive' hFormula)
          hNotConclusion'
      exact Derives.negElim (Derives.impElim hNegative hNotFormula)
        hNotConclusion
  | forall_specialization sort body term hTerm hClosed =>
      exact Derives.forall_specialization
  | forall_distribution sort antecedent consequent =>
      have hForallImp :=
        Formula.Admissible.imp_left hAdmissible
      have hForallAntecedent :=
        Formula.Admissible.imp_left (Formula.Admissible.imp_right hAdmissible)
      exact Derives.forall_imp_distribution sort antecedent consequent
  | vacuous_forall sort eigen formula hFresh =>
      have hFormula :=
        Formula.Admissible.imp_left hAdmissible
      exact Derives.forall_vacuous_intro hFresh
  | equality_substitution sort leftId rightId body =>
      have hBody :=
        Formula.Admissible.imp_left (Formula.Admissible.imp_right hAdmissible)
      simpa [Formula.substituteFree_self sort leftId body] using (Derives.eq_subst_imp_m (T := (Theory.empty : Theory σ)) (Γ := [])
          (sort := sort) (eigen := leftId)
          (left := Term.var (.fvar sort leftId))
          (right := Term.var (.fvar sort rightId))
          (body := body))
  | equality_reflexivity sort id =>
      exact Derives.eq_refl_m (Term.var (.fvar sort id))
end HilbertBaseAxiom
namespace HilbertLogicalAxiom
/-- 有限次全称闭包后的逻辑公理仍是空理论定理。 -/
theorem derives_empty {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {formula : Formula σ} (hAxiom : HilbertLogicalAxiom formula) (hAdmissible : Formula.Admissible formula) :
    Derives (Theory.empty : Theory σ) [] formula := by
  induction hAxiom with
  | base hBase =>
      exact hBase.derives_empty hAdmissible
  | @forall_closure formula sort eigen hAxiom ih =>
      have hFormula :
          Formula.Admissible formula := by
        have hOpened :=
          Formula.Admissible.forall_openAt
            sort hAdmissible
            ⟨TermWellSorted.fvar sort eigen,
              TermScoped.fvar sort eigen⟩
        simpa [Formula.openAt_closeFreeAt] using hOpened
      exact Derives.forall_intro (by
          intro candidate hCandidate
          cases hCandidate) (by simp) (ih hFormula)
end HilbertLogicalAxiom
namespace HilbertDerives
/-- 标准 Hilbert 推导的结论始终落在 proof-layer admissibility 边界内。 -/
theorem admissible {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {formula : Formula σ} (hDerives : HilbertDerives theory formula) :
    Formula.Admissible formula := by
  induction hDerives with
  | logical_axiom _ hAdmissible =>
      exact hAdmissible
  | theory_axiom _ hAdmissible =>
      exact hAdmissible
  | modus_ponens _ _ _ ihImplication =>
      exact Formula.Admissible.imp_right ihImplication
/-- 标准 Hilbert 推导可以可靠地回放为公共自然演绎 `Derives`。 -/
theorem to_derives {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {formula : Formula σ} (hDerives : HilbertDerives theory formula) :
    Derives theory [] formula := by
  induction hDerives with
  | logical_axiom hAxiom hAdmissible =>
      exact Derives.theoryWeakening (T := (Theory.empty : Theory σ)) (U := theory) (by simp [Theory.empty]) (hAxiom.derives_empty hAdmissible)
  | theory_axiom hTheory hAdmissible =>
      exact Derives.theoryAxiom hTheory
  | modus_ponens hAntecedent hImplication ihAntecedent ihImplication =>
      exact Derives.impElim ihImplication ihAntecedent
end HilbertDerives
namespace HilbertEarlier
/-- 在证明前方追加一段列表不会改变两条既有行的先后关系。 -/
theorem prepend {σ : Signature.{u, v, w}}
    {earlier later : Formula σ} {proof : List (Formula σ)} (hEarlier : HilbertEarlier earlier later proof) (initial : List (Formula σ)) :
    HilbertEarlier earlier later (initial ++ proof) := by
  rcases hEarlier with ⟨before, middle, after, rfl⟩
  exact ⟨initial ++ before, middle, after, by simp [List.append_assoc]⟩
/-- 严格较早的两条行都属于同一证明列表。 -/
theorem mem {σ : Signature.{u, v, w}}
    {earlier later : Formula σ} {proof : List (Formula σ)} (hEarlier : HilbertEarlier earlier later proof) :
    earlier ∈ proof ∧ later ∈ proof := by
  rcases hEarlier with ⟨initial, middle, suffix, rfl⟩
  simp
end HilbertEarlier
namespace HilbertProof
/-- 两条标准证明可以顺次拼接；第二条证明中的索引次序保持不变。 -/
theorem append {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {left right : List (Formula σ)} (hLeft : HilbertProof theory left) (hRight : HilbertProof theory right) :
    HilbertProof theory (left ++ right) := by
  induction hRight with
  | nil =>
      simpa using hLeft
  | logical_axiom hProof hAxiom hAdmissible ih =>
      simpa [List.append_assoc] using (HilbertProof.logical_axiom ih hAxiom hAdmissible)
  | theory_axiom hProof hTheory hAdmissible ih =>
      simpa [List.append_assoc] using (HilbertProof.theory_axiom ih hTheory hAdmissible)
  | modus_ponens hProof hEarlier ih =>
      simpa [List.append_assoc] using (HilbertProof.modus_ponens ih (hEarlier.prepend left))
/-- 标准证明列表中的每一行都给出一个归纳式 Hilbert 推导。 -/
theorem derives_of_mem {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {proof : List (Formula σ)} (hProof : HilbertProof theory proof)
    {formula : Formula σ} (hFormula : formula ∈ proof) :
    HilbertDerives theory formula := by
  induction hProof generalizing formula with
  | nil =>
      simp at hFormula
  | @logical_axiom proof formula hProof hAxiom hAdmissible ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · exact HilbertDerives.logical_axiom hAxiom hAdmissible
  | @theory_axiom proof formula hProof hTheory hAdmissible ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · exact HilbertDerives.theory_axiom hTheory hAdmissible
  | @modus_ponens proof antecedent consequent hProof hEarlier ih =>
      simp only [List.mem_append, List.mem_singleton] at hFormula
      rcases hFormula with hFormula | rfl
      · exact ih hFormula
      · have hPremises := hEarlier.mem
        exact HilbertDerives.modus_ponens (ih hPremises.1) (ih hPremises.2)
/-- 归纳式 Hilbert 推导可线性化为一条以目标为末行的标准有限证明。 -/
theorem exists_finite {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {theory : Theory σ}
    {formula : Formula σ} (hDerives : HilbertDerives theory formula) :
    ∃ initial, HilbertProof theory (initial ++ [formula]) := by
  induction hDerives with
  | logical_axiom hAxiom hAdmissible =>
      exact ⟨[],
        HilbertProof.logical_axiom HilbertProof.nil hAxiom hAdmissible⟩
  | theory_axiom hTheory hAdmissible =>
      exact ⟨[],
        HilbertProof.theory_axiom HilbertProof.nil hTheory hAdmissible⟩
  | @modus_ponens antecedent consequent hAntecedent hImplication
      ihAntecedent ihImplication =>
      rcases ihAntecedent with ⟨antecedentPrefix, hAntecedentProof⟩
      rcases ihImplication with ⟨implicationPrefix, hImplicationProof⟩
      let antecedentProof :=
        antecedentPrefix ++ [antecedent]
      let implicationProof :=
        implicationPrefix ++ [Formula.imp antecedent consequent]
      have hCombined :
          HilbertProof theory (antecedentProof ++ implicationProof) :=
        hAntecedentProof.append hImplicationProof
      have hEarlier :
          HilbertEarlier antecedent (Formula.imp antecedent consequent) (antecedentProof ++ implicationProof) := by
        refine ⟨antecedentPrefix, implicationPrefix, [], ?_⟩
        simp [antecedentProof, implicationProof, List.append_assoc]
      exact ⟨antecedentProof ++ implicationProof,
        HilbertProof.modus_ponens hCombined hEarlier⟩
end HilbertProof
/-- 归纳闭包与“存在以目标为末行的标准有限 Hilbert 证明”完全等价。 -/
theorem hilbert_derives_iff_finite_proof
    {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {theory : Theory σ} {formula : Formula σ} :
    HilbertDerives theory formula ↔
      ∃ initial, HilbertProof theory (initial ++ [formula]) := by
  constructor
  · exact HilbertProof.exists_finite
  · rintro ⟨initial, hProof⟩
    exact hProof.derives_of_mem (by simp)
end FirstOrder
end Logic
end YesMetaZFC
