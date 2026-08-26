import YesMetaZFC.Logic.FirstOrder.Completeness.ProofTheory
import YesMetaZFC.Logic.FirstOrder.FreshVariable
/-!
# 一阶 Henkin 完成构造
本模块在 `WF_Candidate` 之上实现当前 locally nameless 语法核适用的 Henkin 完成。
任意大签名并不自动可数，因此核心构造显式消费一个公平公式调度；调度只负责覆盖
全部 admissible 公式，所有一致性、良构性和见证性质仍由 Lean 证明。
背景理论要求由句子组成。这个条件只用于保证每一步都能从 `Nat` 编号的自由变量中
选择对背景理论新鲜的 Henkin 参数，不把可数性或有限级别护栏传播到 `Derives` 核。
-/
namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace Completeness
namespace Henkin
universe u v w
/--
公平公式调度。
`cofinal` 比普通满射更强：每个 admissible 公式在任意给定阶段之后仍会再次出现。
这使较早阶段后来加入的存在公式最终一定获得见证。
-/
structure Schedule (σ : Signature.{u, v, w}) [DecidableEq σ.SortSymbol] where
  formula : Nat → Formula σ
  admissible : ∀ index, Formula.Admissible (formula index)
  cofinal :
    ∀ target, Formula.Admissible target →
      ∀ start, ∃ index, start ≤ index ∧ formula index = target
/-- Henkin 构造消费的句子背景理论。 -/
structure Background {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (T : Theory σ) : Prop where
  admissible : Theory.Admissible T
  sentence : ∀ formula, T formula → Formula.Sentence formula
  consistent : Derives.Consistent T []
namespace Background
/-- 背景理论中的句子不含任何自由变量。 -/
theorem free_fresh {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} (background : Background T)
    {sort : σ.SortSymbol} {id : FreeVarId}
    {formula : Formula σ} (hFormula : T formula) : (sort, id) ∉ Formula.freeSupport formula := by
  have hSentence := background.sentence formula hFormula
  rw [hSentence.2]
  simp
end Background
/-! ## 有限阶段 -/
/-- Henkin 构造的一个有限候选阶段。 -/
structure Stage {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} (background : Background T) where
  formulas : List (Formula σ)
  wf : Derives.WF_Candidate T (Theory.ofList formulas)
namespace Stage
/-- 任意 admissible 且一致的有限上下文都可以作为 Henkin 构造的种子。 -/
def seed {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} (background : Background T) (formulas : List (Formula σ)) (hAdmissible : Context.Admissible formulas)
    (hConsistent : Derives.Consistent T formulas) :
    Stage background where
  formulas := formulas
  wf := {
    wf_background := background.admissible
    wf_candidate := Theory.admissible_ofList hAdmissible
    wf_consistent :=
      Derives.FinitelyConsistent.ofList_iff.mpr hConsistent
  }
/-- 空候选是每个一致句子背景上的默认初始阶段。 -/
def initial {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} (background : Background T) :
    Stage background :=
  seed background [] Context.admissible_nil background.consistent
/--
若 `formula` 尚不可由背景理论推出，则其否定构成一个一致的单公式反例种子。
-/
def refutation_seed {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ} (background : Background T) (formula : Formula σ) (hFormula : Formula.Admissible formula)
    (hNotDerives : ¬ Derives T [] formula) :
    Stage background :=
  seed background [Formula.neg formula] (Context.admissible_cons hFormula.neg Context.admissible_nil) (by
      intro hFalse
      exact hNotDerives (.byContradiction hFalse))
/-- 列表头插入与理论插入给出同一个候选理论。 -/
theorem ofList_cons {σ : Signature.{u, v, w}}
    {formula : Formula σ} {formulas : List (Formula σ)} :
    Theory.ofList (formula :: formulas) =
      Theory.insert formula (Theory.ofList formulas) := by
  funext target
  simp [Theory.ofList, Theory.insert]
/-- 把理论插入后的候选证书搬回列表头插入表示。 -/
def of_insert {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {background : Background T} (current : Stage background) {formula : Formula σ} (hCandidate :
      Derives.WF_Candidate T (Theory.insert formula (Theory.ofList current.formulas))) :
    Stage background where
  formulas := formula :: current.formulas
  wf := by
    rw [ofList_cons]
    exact hCandidate
/-- 阶段中的公式都 admissible。 -/
theorem formula_admissible {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (stage : Stage background)
    {formula : Formula σ} (hFormula : formula ∈ stage.formulas) :
    Formula.Admissible formula :=
  stage.wf.wf_candidate formula hFormula
end Stage
/-! ## 单步完成 -/
/-- 一个阶段对指定公式完成一次 Lindenbaum/Henkin 扩张的全部可审计结果。 -/
structure Extension {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {background : Background T} (current : Stage background) (formula : Formula σ) where
  next : Stage background
  subset :
    ∀ target, target ∈ current.formulas → target ∈ next.formulas
  decision :
    formula ∈ next.formulas ∨ Formula.neg formula ∈ next.formulas
  witness :
    ∀ sort body,
      formula = Formula.existsE sort body →
        formula ∈ current.formulas →
          ∃ eigen,
            Formula.openAt sort 0 (Term.var (.fvar sort eigen)) body ∈
              next.formulas
namespace Extension
/-- 若负分支保持有限一致，则当前阶段尚未包含被否定的公式。 -/
theorem not_mem_of_negative {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (current : Stage background)
    {formula : Formula σ} (hNegative :
      Derives.WF_Candidate T (Theory.insert (Formula.neg formula) (Theory.ofList current.formulas))) :
    formula ∉ current.formulas := by
  intro hFormula
  have hFormulaAdmissible :
      Formula.Admissible formula :=
    current.formula_admissible hFormula
  have hConsistent :
      Derives.Consistent T [formula, Formula.neg formula] :=
    hNegative.wf_consistent _ (by
      intro target hTarget
      rcases List.mem_cons.mp hTarget with rfl | hTarget
      · exact Or.inr hFormula
      · have hNeg : target = Formula.neg formula := by
          simpa using hTarget
        subst target
        exact Or.inl rfl)
  apply hConsistent
  have hPositive :
      Derives T [formula, Formula.neg formula] formula :=
    .assumption (by simp)
  have hNegated :
      Derives T [formula, Formula.neg formula] (Formula.neg formula) :=
    .assumption (by simp)
  exact .negElim hPositive hNegated
/-- 一个 admissible 公式总能完成一次保持良构和有限一致的扩张。 -/
theorem nonempty {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (current : Stage background) (formula : Formula σ) (hFormula : Formula.Admissible formula) :
    Nonempty (Extension current formula) := by
  classical
  rcases current.wf.wf_extend_or_neg hFormula with hPositive | hNegative
  · cases formula with
    | falsum =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort body hShape
            cases hShape
        }⟩
    | truth =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort body hShape
            cases hShape
        }⟩
    | rel relation arguments =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort body hShape
            cases hShape
        }⟩
    | equal left right =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort body hShape
            cases hShape
        }⟩
    | neg body =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort quantifiedBody hShape
            cases hShape
        }⟩
    | conj left right =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort body hShape
            cases hShape
        }⟩
    | disj left right =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort body hShape
            cases hShape
        }⟩
    | imp left right =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort body hShape
            cases hShape
        }⟩
    | iff left right =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort body hShape
            cases hShape
        }⟩
    | forallE binder body =>
        let next := Stage.of_insert current hPositive
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, Stage.of_insert, hTarget]
          decision := Or.inl (by simp [next, Stage.of_insert])
          witness := by
            intro sort quantifiedBody hShape
            cases hShape
        }⟩
    | existsE sort body =>
        let existential := Formula.existsE sort body
        let positive : Stage background :=
          Stage.of_insert current hPositive
        let eigen :=
          FreshVariable.fresh_id sort (existential :: current.formulas)
        let witness :=
          Formula.openAt sort 0 (Term.var (.fvar sort eigen)) body
        have hEigenFresh : (sort, eigen) ∉ Formula.freeSupport existential :=
          FreshVariable.fresh_id_not_mem_m (by simp [existential])
        have hBodyFresh : (sort, eigen) ∉ Formula.freeSupport body := by
          simpa [existential, Formula.freeSupport] using hEigenFresh
        have hTerm :
            Term.Admissible (Term.var (.fvar sort eigen)) sort :=
          ⟨.fvar sort eigen, .fvar sort eigen⟩
        have hWitnessAdmissible :
            Formula.Admissible witness := by
          exact Formula.Admissible.exists_openAt sort hFormula hTerm
        have hClosed :
            Formula.closeFreeAt sort eigen 0 witness = body := by
          exact Formula.closeFreeAt_openAt sort eigen 0 body hBodyFresh
        have hExists :
            Theory.ofList positive.formulas (Formula.existsE sort (Formula.closeFreeAt sort eigen 0 witness)) := by
          change
            Formula.existsE sort (Formula.closeFreeAt sort eigen 0 witness) ∈
              positive.formulas
          simp [positive, Stage.of_insert, hClosed]
        have hPositiveFresh :
            ∀ target, Theory.ofList positive.formulas target → (sort, eigen) ∉ Formula.freeSupport target := by
          intro target hTarget
          apply FreshVariable.fresh_id_not_mem_m (sort := sort) (formulas := existential :: current.formulas)
          simpa [positive, Stage.of_insert, existential] using hTarget
        have hWitnessCandidate :
            Derives.WF_Candidate T (Theory.insert witness (Theory.ofList positive.formulas)) :=
          positive.wf.wf_insert_henkinWitness
            hWitnessAdmissible (fun target hTarget =>
              background.free_fresh hTarget)
            hPositiveFresh hExists
        let next : Stage background :=
          Stage.of_insert positive hWitnessCandidate
        exact ⟨{
          next := next
          subset := by
            intro target hTarget
            simp [next, positive, Stage.of_insert, hTarget]
          decision := Or.inl (by
            simp [next, positive, Stage.of_insert])
          witness := by
            intro witnessSort witnessBody hShape hCurrent
            cases hShape
            exact ⟨eigen, by
              simp [next, positive, Stage.of_insert, witness]⟩
        }⟩
  · let next := Stage.of_insert current hNegative
    have hNotCurrent :
        formula ∉ current.formulas :=
      not_mem_of_negative current hNegative
    exact ⟨{
      next := next
      subset := by
        intro target hTarget
        simp [next, Stage.of_insert, hTarget]
      decision := Or.inr (by simp [next, Stage.of_insert])
      witness := by
        intro sort body hShape hCurrent
        exact False.elim (hNotCurrent hCurrent)
    }⟩
/-- 经典选择固定一个确定的扩张结果；可信性质来自 `nonempty`。 -/
noncomputable def choose {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (current : Stage background) (formula : Formula σ) (hFormula : Formula.Admissible formula) :
    Extension current formula :=
  Classical.choice (nonempty current formula hFormula)
end Extension
/-! ## 公平迭代与极限候选 -/
/-- 候选理论决定每个 admissible 公式或其否定。 -/
def Decides {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (candidate : Theory σ) : Prop :=
  ∀ formula, Formula.Admissible formula →
    candidate formula ∨ candidate (Formula.neg formula)
/-- 候选理论中的每个存在公式都有一个自由变量项见证。 -/
def Witnessed {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (candidate : Theory σ) : Prop :=
  ∀ sort body,
    candidate (Formula.existsE sort body) →
      ∃ eigen,
        candidate (Formula.openAt sort 0 (Term.var (.fvar sort eigen)) body)
/-- Henkin 完成的公开 proof-carrying 结果。 -/
structure Result {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} (background : Background T) where
  candidate : Theory σ
  wf : Derives.WF_Candidate T candidate
  decides : Decides candidate
  witnessed : Witnessed candidate
namespace Construction
noncomputable section
/-- 按公平调度递归生成有限阶段。 -/
def stage {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {background : Background T} (initial : Stage background) (schedule : Schedule σ) :
    Nat → Stage background
  | 0 => initial
  | index + 1 =>
      (Extension.choose (stage initial schedule index) (schedule.formula index) (schedule.admissible index)).next
@[simp]
theorem stage_zero {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (initial : Stage background) (schedule : Schedule σ) :
    stage initial schedule 0 = initial :=
  rfl
@[simp]
theorem stage_succ {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (initial : Stage background) (schedule : Schedule σ) (index : Nat) :
    stage initial schedule (index + 1) = (Extension.choose (stage initial schedule index) (schedule.formula index) (schedule.admissible index)).next :=
  rfl
/-- 每个阶段的公式都保留到下一阶段。 -/
theorem subset_succ {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ} (index : Nat) {formula : Formula σ} (hFormula : formula ∈ (stage initial schedule index).formulas) :
    formula ∈ (stage initial schedule (index + 1)).formulas := by
  exact (Extension.choose (stage initial schedule index) (schedule.formula index) (schedule.admissible index)).subset formula hFormula
/-- 阶段公式沿任意自然数序单调保留。 -/
theorem subset_of_le {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ}
    {small large : Nat} (hLe : small ≤ large)
    {formula : Formula σ} (hFormula : formula ∈ (stage initial schedule small).formulas) :
    formula ∈ (stage initial schedule large).formulas := by
  induction hLe with
  | refl =>
      exact hFormula
  | step hPrevious ih =>
      exact subset_succ _ ih
/-- 第 `index` 步决定调度到的公式。 -/
theorem decision_at {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ} (index : Nat) :
    schedule.formula index ∈ (stage initial schedule (index + 1)).formulas ∨
      Formula.neg (schedule.formula index) ∈ (stage initial schedule (index + 1)).formulas := by
  exact (Extension.choose (stage initial schedule index) (schedule.formula index) (schedule.admissible index)).decision
/-- 已在当前阶段出现的存在式在调度步骤后获得见证。 -/
theorem witness_at {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ} (index : Nat) {sort : σ.SortSymbol} {body : Formula σ} (hShape : schedule.formula index = Formula.existsE sort body) (hMember :
      schedule.formula index ∈ (stage initial schedule index).formulas) :
    ∃ eigen,
      Formula.openAt sort 0 (Term.var (.fvar sort eigen)) body ∈ (stage initial schedule (index + 1)).formulas := by
  exact (Extension.choose (stage initial schedule index) (schedule.formula index) (schedule.admissible index)).witness
        sort body hShape hMember
/-- 极限候选是全部有限阶段的并。 -/
def candidate {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} (initial : Stage background) (schedule : Schedule σ) :
    Theory σ :=
  fun formula =>
    ∃ index, formula ∈ (stage initial schedule index).formulas
/-- 任意阶段成员进入极限候选。 -/
theorem candidate_of_stage {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ}
    {index : Nat} {formula : Formula σ} (hFormula : formula ∈ (stage initial schedule index).formulas) :
    candidate initial schedule formula :=
  ⟨index, hFormula⟩
/-- 初始种子中的每个公式都保留到极限候选。 -/
theorem candidate_of_initial {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ} {formula : Formula σ} (hFormula : formula ∈ initial.formulas) :
    candidate initial schedule formula := by
  exact candidate_of_stage (index := 0) (by simpa using hFormula)
/-- 极限候选只包含 admissible 公式。 -/
theorem candidate_admissible {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ} :
    Theory.Admissible (candidate initial schedule) := by
  intro formula hFormula
  rcases hFormula with ⟨index, hMember⟩
  exact (stage initial schedule index).formula_admissible hMember
/-- 极限候选中的有限上下文总能同时落入一个有限阶段。 -/
theorem context_in_stage {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ} (context : Context σ) (hContext :
      ∀ formula, formula ∈ context →
        candidate initial schedule formula) :
    ∃ index,
      ∀ formula, formula ∈ context →
        formula ∈ (stage initial schedule index).formulas := by
  induction context with
  | nil =>
      exact ⟨0, by
        intro formula hFormula
        cases hFormula⟩
  | cons head tail ih =>
      rcases hContext head (by simp) with ⟨headIndex, hHead⟩
      have hTail :
          ∀ formula, formula ∈ tail →
            candidate initial schedule formula := by
        intro formula hFormula
        exact hContext formula (by simp [hFormula])
      rcases ih hTail with ⟨tailIndex, hTailAt⟩
      refine ⟨Nat.max headIndex tailIndex, ?_⟩
      intro formula hFormula
      rcases List.mem_cons.mp hFormula with rfl | hFormula
      · exact subset_of_le (Nat.le_max_left headIndex tailIndex) hHead
      · exact subset_of_le (Nat.le_max_right headIndex tailIndex) (hTailAt formula hFormula)
/-- 极限候选相对背景理论仍然有限一致。 -/
theorem candidate_finitelyConsistent {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ} :
    Derives.FinitelyConsistent T (candidate initial schedule) := by
  intro context hContext
  rcases context_in_stage context hContext with ⟨index, hAtStage⟩
  exact (stage initial schedule index).wf.wf_consistent
      context hAtStage
/-- 公平调度保证极限候选决定每个 admissible 公式。 -/
theorem candidate_decides {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ} :
    Decides (candidate initial schedule) := by
  intro formula hFormula
  rcases schedule.cofinal formula hFormula 0 with
    ⟨index, hStart, hScheduled⟩
  rcases decision_at (initial := initial) (schedule := schedule) index with
    hPositive | hNegative
  · left
    refine candidate_of_stage (index := index + 1) ?_
    simpa [hScheduled] using hPositive
  · right
    refine candidate_of_stage (index := index + 1) ?_
    simpa [hScheduled] using hNegative
/-- 公平调度保证极限候选中的每个存在式最终获得见证。 -/
theorem candidate_witnessed {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {T : Theory σ}
    {background : Background T} {initial : Stage background}
    {schedule : Schedule σ} :
    Witnessed (candidate initial schedule) := by
  intro sort body hExists
  rcases hExists with ⟨memberIndex, hMember⟩
  have hAdmissible :
      Formula.Admissible (Formula.existsE sort body) := (stage initial schedule memberIndex).formula_admissible hMember
  rcases schedule.cofinal (Formula.existsE sort body) hAdmissible memberIndex with
    ⟨index, hMemberIndex, hScheduled⟩
  have hAtIndex :
      schedule.formula index ∈ (stage initial schedule index).formulas := by
    rw [hScheduled]
    exact subset_of_le hMemberIndex hMember
  rcases witness_at (initial := initial) (schedule := schedule)
      index hScheduled hAtIndex with
    ⟨eigen, hWitness⟩
  exact ⟨eigen, candidate_of_stage hWitness⟩
/-- 公平调度生成的完整 Henkin 候选。 -/
def result {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Theory σ} {background : Background T} (initial : Stage background) (schedule : Schedule σ) :
    Result background where
  candidate := candidate initial schedule
  wf := {
    wf_background := background.admissible
    wf_candidate := candidate_admissible
    wf_consistent := candidate_finitelyConsistent
  }
  decides := candidate_decides
  witnessed := candidate_witnessed
end
end Construction
end Henkin
end Completeness
end FirstOrder
end Logic
end YesMetaZFC
