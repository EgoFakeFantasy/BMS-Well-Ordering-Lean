import YesMetaZFC.Automation.CoreNormalForm.LocalSkolemSoundness
import YesMetaZFC.Automation.CoreNormalForm.DefinitionalCnfSoundness
import YesMetaZFC.Automation.CoreNormalForm.NormalizationSoundness
import YesMetaZFC.Automation.CoreNormalForm.FoolTraceSoundness
/-!
# Core normal form checked preprocessing
本模块把当前新预处理主线串成一个 checked payload：
1. core normalizer trace；
2. dependency-driven anti-prenex / mini-scoping；
3. local Skolem trace；
4. equality-visible definitional CNF。
这里的 `CheckedPreprocessing.sound` 先给出结构 soundness 骨架：checked 总证书确实钉住
每个阶段的 checker 和相邻阶段的输入输出。真正的语义等价、Skolem 保守性和定义性
CNF 保守性将后续作为各 phase 的 theorem 接入。
-/
namespace YesMetaZFC.Automation.CoreSyntax.NormalForm.CheckedPreprocessing
universe x
structure Settings where
  normalForm : _root_.YesMetaZFC.Automation.CoreSyntax.NormalForm.Config := {}
  antiPrenex : AntiPrenex.Config := {}
  localSkolem : LocalSkolem.Config := {}
  definitionalCnf : DefinitionalCnf.Config := {}
  deriving Repr, Inhabited, BEq, DecidableEq, Lean.ToExpr
def statsEq (left right : Certificate.Stats) : Bool :=
  left.steps == right.steps &&
    left.clauses == right.clauses &&
      left.literals == right.literals &&
        left.generated == right.generated &&
          left.retained == right.retained &&
            left.verified == right.verified &&
              left.residuals == right.residuals &&
                left.fuel == right.fuel
def statsOf (settings : Settings) (source : Formula) (normalizationTrace : Trace) (antiPrenex : AntiPrenexPayload) (localSkolem : LocalSkolemPayload) (cnf : DefinitionalCnfPayload) : Certificate.Stats :=
  {
    steps :=
      normalizationTrace.steps.size +
        antiPrenex.steps +
          localSkolem.steps +
            cnf.definitionCount
    clauses := cnf.clauseCount
    literals := cnf.literalCount
    generated := source.size
    retained := cnf.clauseCount
    verified :=
      normalizationTrace.steps.size +
        antiPrenex.steps +
          localSkolem.steps +
            cnf.definitionCount
    residuals := (if antiPrenex.fuelExhausted then 1 else 0) + (if localSkolem.budgetSatisfied then 0 else 1) + (if cnf.budgetSatisfied then 0 else 1)
    fuel :=
      settings.normalForm.fuel +
        settings.antiPrenex.maxSteps +
          settings.localSkolem.maxSteps +
            settings.definitionalCnf.maxDefinitions
  }
structure Payload where
  settings : Settings
  source : Formula
  normalized : Formula
  normalizationTrace : Trace
  initialNnf : Nnf
  antiPrenex : AntiPrenexPayload
  localSkolem : LocalSkolemPayload
  definitionalCnf : DefinitionalCnfPayload
  clauses : ClauseSet
  stats : Certificate.Stats
  deriving Repr, Lean.ToExpr
namespace Payload
def build (settings : Settings) (source : Formula) : Payload :=
  let normalized := normalizeFormula source (config := settings.normalForm)
  let normalizationTrace := Trace.ofFormula source (config := settings.normalForm)
  let initialNnf := toNnfWith Polarity.positive normalized
  let antiPrenex := AntiPrenexPayload.build settings.antiPrenex initialNnf
  let localSkolem := LocalSkolemPayload.build settings.localSkolem antiPrenex.result
  let definitionalCnf :=
    DefinitionalCnfPayload.build settings.definitionalCnf [] localSkolem.result
  {
    settings := settings
    source := source
    normalized := normalized
    normalizationTrace := normalizationTrace
    initialNnf := initialNnf
    antiPrenex := antiPrenex
    localSkolem := localSkolem
    definitionalCnf := definitionalCnf
    clauses := definitionalCnf.clauses
    stats := statsOf settings source normalizationTrace antiPrenex localSkolem definitionalCnf
  }
def phaseCheck (payload : Payload) : Bool :=
  payload.source.check? &&
    payload.normalized.check? &&
      Trace.check payload.settings.normalForm payload.normalizationTrace &&
        AntiPrenexPayload.check payload.antiPrenex &&
          LocalSkolemPayload.check payload.localSkolem &&
            DefinitionalCnfPayload.check payload.definitionalCnf
def linkCheck (payload : Payload) : Bool :=
  TraceExpr.eq payload.normalizationTrace.source (TraceExpr.formula payload.source) &&
    TraceExpr.eq payload.normalizationTrace.target (TraceExpr.formula payload.normalized) &&
      SyntaxEq.nnfEq payload.initialNnf (toNnfWith Polarity.positive payload.normalized) &&
        SyntaxEq.nnfEq payload.antiPrenex.source payload.initialNnf &&
          SyntaxEq.nnfEq payload.localSkolem.source payload.antiPrenex.result &&
            SyntaxEq.nnfEq payload.definitionalCnf.source payload.localSkolem.result &&
              ClauseSet.eq payload.clauses payload.definitionalCnf.clauses
theorem linkCheck_eq_true_of_components (payload : Payload) (hTraceSource : TraceExpr.eq payload.normalizationTrace.source (TraceExpr.formula payload.source) = true) (hTraceTarget : TraceExpr.eq
    payload.normalizationTrace.target (TraceExpr.formula payload.normalized) = true) (hInitialNnf : SyntaxEq.nnfEq payload.initialNnf (toNnfWith Polarity.positive payload.normalized) = true) (hAntiPrenex : SyntaxEq.nnfEq
    payload.antiPrenex.source payload.initialNnf = true) (hLocalSkolem : SyntaxEq.nnfEq payload.localSkolem.source payload.antiPrenex.result = true) (hDefinitionalCnf : SyntaxEq.nnfEq payload.definitionalCnf.source
    payload.localSkolem.result = true) (hClauses : ClauseSet.eq payload.clauses payload.definitionalCnf.clauses = true) : linkCheck payload = true :=
  Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨hTraceSource, hTraceTarget⟩, hInitialNnf⟩,
            hAntiPrenex⟩,
          hLocalSkolem⟩,
        hDefinitionalCnf⟩,
      hClauses⟩
def metricCheck (payload : Payload) : Bool :=
  statsEq payload.stats (statsOf payload.settings payload.source payload.normalizationTrace payload.antiPrenex payload.localSkolem payload.definitionalCnf)
def check (payload : Payload) : Bool :=
  phaseCheck payload && linkCheck payload
def auditCheck (payload : Payload) : Bool :=
  check payload && (metricCheck payload && AntiPrenexPayload.auditCheck payload.antiPrenex && DefinitionalCnfPayload.auditCheck payload.definitionalCnf)
def mk? (settings : Settings) (source : Formula) : Option (Certificate.Checked Payload Payload.check) :=
  Certificate.Checked.mk? (check := Payload.check) (build settings source)
end Payload
abbrev Checked := Certificate.Checked Payload Payload.check
structure Sound (payload : Payload) : Prop where
  checked : Payload.check payload = true
  phasesChecked : Payload.phaseCheck payload = true
  linksChecked : Payload.linkCheck payload = true
theorem sound_of_check {payload : Payload} (h : Payload.check payload = true) : Sound payload := by
  unfold Payload.check at h
  rcases Bool.and_eq_true_iff.mp h with ⟨hPhase, hLink⟩
  exact {
    checked := h
    phasesChecked := hPhase
    linksChecked := hLink
  }
theorem sound (checked : Checked) : Sound checked.payload :=
  sound_of_check checked.checked
theorem satisfies_source_iff_normalized (checked : Checked) {M : Semantics.Model} (contract : Semantics.FoolLambdaContract M) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) : Semantics.Formula.Satisfies env checked.payload.source ↔ Semantics.Formula.Satisfies env checked.payload.normalized := by
  have hSound := sound checked
  have hPhases := hSound.phasesChecked
  have hLinks := hSound.linksChecked
  simp only [Payload.phaseCheck, Bool.and_eq_true_iff] at hPhases
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  have hTrace :
      Trace.check checked.payload.settings.normalForm
        checked.payload.normalizationTrace = true :=
    hPhases.1.1.1.2
  have hSourceLink :
      TraceExpr.eq checked.payload.normalizationTrace.source (TraceExpr.formula checked.payload.source) = true :=
    hLinks.1.1.1.1.1.1
  have hTargetLink :
      TraceExpr.eq checked.payload.normalizationTrace.target (TraceExpr.formula checked.payload.normalized) = true :=
    hLinks.1.1.1.1.1.2
  have hTraceSem :=
    Semantics.Trace.sound_of_check contract
      checked.payload.settings.normalForm env hFree
        checked.payload.normalizationTrace hTrace
  have hSourceEq :
      checked.payload.normalizationTrace.source =
        TraceExpr.formula checked.payload.source :=
    Semantics.TraceExpr.eq_eq_true.mp hSourceLink
  have hTargetEq :
      checked.payload.normalizationTrace.target =
        TraceExpr.formula checked.payload.normalized :=
    Semantics.TraceExpr.eq_eq_true.mp hTargetLink
  rw [hSourceEq, hTargetEq] at hTraceSem
  exact hTraceSem
theorem satisfies_source_iff_normalized_fool (checked : Checked) (hFoolTrace : checked.payload.normalizationTrace.foolCheck = true) {M : Semantics.Model} (contract : Semantics.FoolContract M) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) : Semantics.Formula.Satisfies env checked.payload.source ↔ Semantics.Formula.Satisfies env checked.payload.normalized := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  have hSourceLink :
      TraceExpr.eq checked.payload.normalizationTrace.source (TraceExpr.formula checked.payload.source) = true :=
    hLinks.1.1.1.1.1.1
  have hTargetLink :
      TraceExpr.eq checked.payload.normalizationTrace.target (TraceExpr.formula checked.payload.normalized) = true :=
    hLinks.1.1.1.1.1.2
  have hTraceSem :=
    Semantics.Trace.sound_of_foolCheck contract env hFree
      checked.payload.normalizationTrace hFoolTrace
  have hSourceEq :
      checked.payload.normalizationTrace.source =
        TraceExpr.formula checked.payload.source :=
    Semantics.TraceExpr.eq_eq_true.mp hSourceLink
  have hTargetEq :
      checked.payload.normalizationTrace.target =
        TraceExpr.formula checked.payload.normalized :=
    Semantics.TraceExpr.eq_eq_true.mp hTargetLink
  rw [hSourceEq, hTargetEq] at hTraceSem
  exact hTraceSem
theorem satisfies_normalized_iff_initialNnf (checked : Checked) {M : Semantics.Model} (env : Semantics.Env M) : Semantics.Formula.Satisfies env checked.payload.normalized ↔ Semantics.Nnf.Satisfies env checked.payload.initialNnf := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  have hInitialNnf :
      SyntaxEq.nnfEq checked.payload.initialNnf (toNnfWith Polarity.positive checked.payload.normalized) = true :=
    hLinks.1.1.1.1.2
  have hInitialNnfEq :
      checked.payload.initialNnf =
        toNnfWith Polarity.positive checked.payload.normalized :=
    SyntaxEq.nnfEq_eq_true.mp hInitialNnf
  rw [hInitialNnfEq]
  exact (Semantics.Nnf.satisfies_toNnfWith_positive env checked.payload.normalized).symm
theorem satisfies_initialNnf_iff_antiPrenexResult (checked : Checked) {M : Semantics.Model} (env : Semantics.Env M) : Semantics.Nnf.Satisfies env checked.payload.initialNnf ↔ Semantics.Nnf.Satisfies env checked.payload.antiPrenex.result := by
  have hSound := sound checked
  have hPhases := hSound.phasesChecked
  have hLinks := hSound.linksChecked
  simp only [Payload.phaseCheck, Bool.and_eq_true_iff] at hPhases
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  have hAntiPrenex :
      AntiPrenexPayload.check checked.payload.antiPrenex = true :=
    hPhases.1.1.2
  have hAntiPrenexSource :
      SyntaxEq.nnfEq checked.payload.antiPrenex.source
        checked.payload.initialNnf = true :=
    hLinks.1.1.1.2
  have hAntiPrenexSourceEq :
      checked.payload.antiPrenex.source = checked.payload.initialNnf :=
    SyntaxEq.nnfEq_eq_true.mp hAntiPrenexSource
  rw [← hAntiPrenexSourceEq]
  exact AntiPrenexPayload.semanticEquivalent_of_check hAntiPrenex env
theorem satisfies_source_iff_antiPrenexResult (checked : Checked) {M : Semantics.Model} (contract : Semantics.FoolLambdaContract M) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) : Semantics.Formula.Satisfies env checked.payload.source ↔ Semantics.Nnf.Satisfies env checked.payload.antiPrenex.result :=
  (satisfies_source_iff_normalized checked contract env hFree).trans
    ((satisfies_normalized_iff_initialNnf checked env).trans (satisfies_initialNnf_iff_antiPrenexResult checked env))
theorem satisfies_source_iff_antiPrenexResult_fool (checked : Checked) (hFoolTrace : checked.payload.normalizationTrace.foolCheck = true) {M : Semantics.Model} (contract : Semantics.FoolContract M) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) : Semantics.Formula.Satisfies env checked.payload.source ↔ Semantics.Nnf.Satisfies env checked.payload.antiPrenex.result :=
  (satisfies_source_iff_normalized_fool checked hFoolTrace contract env hFree).trans
      ((satisfies_normalized_iff_initialNnf checked env).trans (satisfies_initialNnf_iff_antiPrenexResult checked env))
theorem satisfies_source_iff_antiPrenexResult_of_normalized_eq (checked : Checked) (hNormalized : checked.payload.normalized = checked.payload.source) {M : Semantics.Model} (env : Semantics.Env M) : Semantics.Formula.Satisfies env checked.payload.source ↔ Semantics.Nnf.Satisfies env checked.payload.antiPrenex.result := by
  rw [← hNormalized]
  exact (satisfies_normalized_iff_initialNnf checked env).trans (satisfies_initialNnf_iff_antiPrenexResult checked env)
theorem localSkolem_checked (checked : Checked) : LocalSkolemPayload.check checked.payload.localSkolem = true := by
  have hPhases := (sound checked).phasesChecked
  simp only [Payload.phaseCheck, Bool.and_eq_true_iff] at hPhases
  exact hPhases.1.2
theorem localSkolem_source_eq_antiPrenexResult (checked : Checked) : checked.payload.localSkolem.source = checked.payload.antiPrenex.result := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  exact SyntaxEq.nnfEq_eq_true.mp hLinks.1.1.2
theorem definitionalCnf_checked (checked : Checked) : DefinitionalCnfPayload.check checked.payload.definitionalCnf = true := by
  have hPhases := (sound checked).phasesChecked
  simp only [Payload.phaseCheck, Bool.and_eq_true_iff] at hPhases
  exact hPhases.2
theorem definitionalCnf_source_eq_localSkolemResult (checked : Checked) : checked.payload.definitionalCnf.source = checked.payload.localSkolem.result := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  exact SyntaxEq.nnfEq_eq_true.mp hLinks.1.2
theorem clauses_eq_definitionalCnfClauses (checked : Checked) : checked.payload.clauses = checked.payload.definitionalCnf.clauses := by
  have hLinks := (sound checked).linksChecked
  simp only [Payload.linkCheck, Bool.and_eq_true_iff] at hLinks
  exact Semantics.ClauseSet.eq_eq_true.mp hLinks.2
structure ModelExtension (checked : Checked) (M : Semantics.Model) (base : Semantics.Env M) where
  sourceSupported :
    Semantics.FreeSupport.NnfSupportedBy []
      checked.payload.antiPrenex.result
  localSkolem :
    Semantics.LocalSkolemSoundness.UniformSoundExtension (LocalSkolem.initialState checked.payload.antiPrenex.result)
      checked.payload.antiPrenex.result
      checked.payload.localSkolem.result M base
  definitionalCnf :
    Semantics.DefinitionalCnf.UniformSoundExtension
      checked.payload.definitionalCnf.contextSorts
      checked.payload.definitionalCnf.source
      checked.payload.definitionalCnf.root
      checked.payload.definitionalCnf.clauses
      checked.payload.definitionalCnf.definitions
      localSkolem.extension.target (localSkolem.extension.rebase base)
namespace ModelExtension
@[implicit_reducible]
def target {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) : Semantics.Model :=
  Semantics.Model.overrideDefinitions
    extension.localSkolem.extension.target (extension.localSkolem.extension.rebase base)
    checked.payload.definitionalCnf.definitions
def rebase {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (env : Semantics.Env M) : Semantics.Env extension.target :=
  Semantics.Env.rebaseOverrideDefinitions (extension.localSkolem.extension.rebase base)
    checked.payload.definitionalCnf.definitions (extension.localSkolem.extension.rebase env)
def unbase {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (env : Semantics.Env extension.target) : Semantics.Env M :=
  extension.localSkolem.extension.unbase <|
    Semantics.Env.unbaseOverrideDefinitions env
theorem rebase_unbase {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (env : Semantics.Env extension.target) : extension.rebase (extension.unbase env) = env := by
  unfold rebase unbase
  rw [extension.localSkolem.extension.rebase_unbase, Semantics.Env.rebaseOverrideDefinitions_unbaseOverrideDefinitions]
theorem unbase_rebase {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (env : Semantics.Env M) : extension.unbase (extension.rebase env) = env := by
  unfold rebase unbase
  rw [Semantics.Env.unbaseOverrideDefinitions_rebaseOverrideDefinitions, extension.localSkolem.extension.unbase_rebase]
theorem unbaseRespectsFree {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) {env : Semantics.Env extension.target} (hFree : Semantics.Env.RespectsFree env) : Semantics.Env.RespectsFree (extension.unbase env) :=
  extension.localSkolem.extension.unbaseRespectsFree _ <|
    Semantics.Env.respectsFree_unbaseOverrideDefinitions hFree
theorem unbaseSameBound {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) {left right : Semantics.Env extension.target} (hBound : Semantics.LocalSkolemChoice.SameBoundStack left right) : Semantics.LocalSkolemChoice.SameBoundStack (extension.unbase left) (extension.unbase right) :=
  extension.localSkolem.extension.unbaseSameBound <|
    Semantics.Env.sameBoundStack_unbaseOverrideDefinitions hBound
theorem functionSort {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (contract : Semantics.FoolLambdaContract M) : ∀ symbol arguments, extension.target.sortInterp symbol.outputSort (extension.target.functionInterp symbol arguments) := by
  intro symbol arguments
  exact
    extension.localSkolem.extension.functionSort contract.function_sort
      symbol arguments
theorem functionSort_of {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (hFunctionSort : ∀ symbol arguments, M.sortInterp symbol.outputSort (M.functionInterp symbol arguments)) : ∀ symbol arguments, extension.target.sortInterp symbol.outputSort (extension.target.functionInterp symbol arguments) := by
  intro symbol arguments
  exact
    extension.localSkolem.extension.functionSort hFunctionSort
      symbol arguments
theorem foolContract {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (source : Semantics.FoolContract M) : Semantics.FoolContract extension.target :=
  Semantics.FoolContract.overrideDefinitions (extension.localSkolem.extension.foolContract source) (extension.localSkolem.extension.rebase base)
    checked.payload.definitionalCnf.definitions
theorem contract {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (source : Semantics.FoolLambdaContract M) : Semantics.FoolLambdaContract extension.target :=
  Semantics.FoolLambdaContract.overrideDefinitions (extension.localSkolem.extension.contract source) (extension.localSkolem.extension.rebase base)
    checked.payload.definitionalCnf.definitions
theorem respectsFree {checked : Checked} {M : Semantics.Model} {base env : Semantics.Env M} (extension : ModelExtension checked M base) (hFree : Semantics.Env.RespectsFree env) : Semantics.Env.RespectsFree (extension.rebase env) := by
  apply Semantics.Env.respectsFree_rebaseOverrideDefinitions
  exact extension.localSkolem.extension.respectsFree env hFree
theorem sameBound {checked : Checked} {M : Semantics.Model} {base left right : Semantics.Env M} (extension : ModelExtension checked M base) (hBound : Semantics.LocalSkolemChoice.SameBoundStack left right) : Semantics.LocalSkolemChoice.SameBoundStack (extension.rebase left) (extension.rebase right) := by
  apply Semantics.Env.sameBoundStack_rebaseOverrideDefinitions
  exact extension.localSkolem.extension.sameBound hBound
theorem clausesSatisfied {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (contract : Semantics.FoolLambdaContract M) (hBaseFree : Semantics.Env.RespectsFree
    base) (hSource : Semantics.Formula.Satisfies base checked.payload.source) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) (hBound : Semantics.LocalSkolemChoice.SameBoundStack env base) :
    Semantics.ClauseSet.Satisfies (extension.rebase env) checked.payload.clauses := by
  have hAntiPrenex :
      Semantics.Nnf.Satisfies base checked.payload.antiPrenex.result := (satisfies_source_iff_antiPrenexResult checked contract base hBaseFree).mp hSource
  have hLocalResult :
      Semantics.Nnf.Satisfies (extension.localSkolem.extension.rebase env)
        checked.payload.localSkolem.result :=
    extension.localSkolem.resultSat_of_source
      extension.sourceSupported hAntiPrenex env hFree hBound
  have hCnfSource :
      Semantics.Nnf.Satisfies (extension.localSkolem.extension.rebase env)
        checked.payload.definitionalCnf.source := by
    rw [definitionalCnf_source_eq_localSkolemResult checked]
    exact hLocalResult
  rw [clauses_eq_definitionalCnfClauses checked]
  exact extension.definitionalCnf.clausesSatisfied (extension.localSkolem.extension.rebase env) hCnfSource
theorem clausesSatisfied_fool {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (hFoolTrace : checked.payload.normalizationTrace.foolCheck = true) (contract :
    Semantics.FoolContract M) (hBaseFree : Semantics.Env.RespectsFree base) (hSource : Semantics.Formula.Satisfies base checked.payload.source) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) (hBound :
    Semantics.LocalSkolemChoice.SameBoundStack env base) : Semantics.ClauseSet.Satisfies (extension.rebase env) checked.payload.clauses := by
  have hAntiPrenex :
      Semantics.Nnf.Satisfies base checked.payload.antiPrenex.result :=
    (satisfies_source_iff_antiPrenexResult_fool checked hFoolTrace contract base hBaseFree).mp hSource
  have hLocalResult :
      Semantics.Nnf.Satisfies (extension.localSkolem.extension.rebase env)
        checked.payload.localSkolem.result :=
    extension.localSkolem.resultSat_of_source
      extension.sourceSupported hAntiPrenex env hFree hBound
  have hCnfSource :
      Semantics.Nnf.Satisfies (extension.localSkolem.extension.rebase env)
        checked.payload.definitionalCnf.source := by
    rw [definitionalCnf_source_eq_localSkolemResult checked]
    exact hLocalResult
  rw [clauses_eq_definitionalCnfClauses checked]
  exact extension.definitionalCnf.clausesSatisfied (extension.localSkolem.extension.rebase env) hCnfSource
theorem clausesSatisfied_of_normalized_eq {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (hNormalized : checked.payload.normalized = checked.payload.source)
    (hSource : Semantics.Formula.Satisfies base checked.payload.source) (env : Semantics.Env M) (hFree : Semantics.Env.RespectsFree env) (hBound : Semantics.LocalSkolemChoice.SameBoundStack env base) :
    Semantics.ClauseSet.Satisfies (extension.rebase env) checked.payload.clauses := by
  have hAntiPrenex :
      Semantics.Nnf.Satisfies base checked.payload.antiPrenex.result :=
    (satisfies_source_iff_antiPrenexResult_of_normalized_eq checked hNormalized base).mp hSource
  have hLocalResult :
      Semantics.Nnf.Satisfies (extension.localSkolem.extension.rebase env)
        checked.payload.localSkolem.result :=
    extension.localSkolem.resultSat_of_source
      extension.sourceSupported hAntiPrenex env hFree hBound
  have hCnfSource :
      Semantics.Nnf.Satisfies (extension.localSkolem.extension.rebase env)
        checked.payload.definitionalCnf.source := by
    rw [definitionalCnf_source_eq_localSkolemResult checked]
    exact hLocalResult
  rw [clauses_eq_definitionalCnfClauses checked]
  exact extension.definitionalCnf.clausesSatisfied (extension.localSkolem.extension.rebase env) hCnfSource
theorem clausesSatisfiedTarget {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (contract : Semantics.FoolLambdaContract M) (hBaseFree :
    Semantics.Env.RespectsFree base) (hSource : Semantics.Formula.Satisfies base checked.payload.source) (env : Semantics.Env extension.target) (hFree : Semantics.Env.RespectsFree env) (hBound :
    Semantics.LocalSkolemChoice.SameBoundStack env (extension.rebase base)) : Semantics.ClauseSet.Satisfies env checked.payload.clauses := by
  let sourceEnv := extension.unbase env
  have hSourceFree : Semantics.Env.RespectsFree sourceEnv :=
    extension.unbaseRespectsFree hFree
  have hSourceBound :
      Semantics.LocalSkolemChoice.SameBoundStack sourceEnv base := by
    have hPulled := extension.unbaseSameBound hBound
    simpa [sourceEnv, extension.unbase_rebase] using hPulled
  have hClauses :=
    extension.clausesSatisfied contract hBaseFree hSource
      sourceEnv hSourceFree hSourceBound
  simpa [sourceEnv, extension.rebase_unbase] using hClauses
theorem clausesSatisfiedTarget_fool {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (hFoolTrace : checked.payload.normalizationTrace.foolCheck = true)
    (contract : Semantics.FoolContract M) (hBaseFree : Semantics.Env.RespectsFree base) (hSource : Semantics.Formula.Satisfies base checked.payload.source) (env : Semantics.Env extension.target) (hFree :
    Semantics.Env.RespectsFree env) (hBound : Semantics.LocalSkolemChoice.SameBoundStack env (extension.rebase base)) : Semantics.ClauseSet.Satisfies env checked.payload.clauses := by
  let sourceEnv := extension.unbase env
  have hSourceFree : Semantics.Env.RespectsFree sourceEnv :=
    extension.unbaseRespectsFree hFree
  have hSourceBound :
      Semantics.LocalSkolemChoice.SameBoundStack sourceEnv base := by
    have hPulled := extension.unbaseSameBound hBound
    simpa [sourceEnv, extension.unbase_rebase] using hPulled
  have hClauses :=
    extension.clausesSatisfied_fool hFoolTrace contract hBaseFree hSource
      sourceEnv hSourceFree hSourceBound
  simpa [sourceEnv, extension.rebase_unbase] using hClauses
theorem clausesSatisfiedTarget_of_normalized_eq {checked : Checked} {M : Semantics.Model} {base : Semantics.Env M} (extension : ModelExtension checked M base) (hNormalized : checked.payload.normalized =
    checked.payload.source) (hSource : Semantics.Formula.Satisfies base checked.payload.source) (env : Semantics.Env extension.target) (hFree : Semantics.Env.RespectsFree env) (hBound :
    Semantics.LocalSkolemChoice.SameBoundStack env (extension.rebase base)) : Semantics.ClauseSet.Satisfies env checked.payload.clauses := by
  let sourceEnv := extension.unbase env
  have hSourceFree : Semantics.Env.RespectsFree sourceEnv :=
    extension.unbaseRespectsFree hFree
  have hSourceBound :
      Semantics.LocalSkolemChoice.SameBoundStack sourceEnv base := by
    have hPulled := extension.unbaseSameBound hBound
    simpa [sourceEnv, extension.unbase_rebase] using hPulled
  have hClauses :=
    extension.clausesSatisfied_of_normalized_eq
      hNormalized hSource sourceEnv hSourceFree hSourceBound
  simpa [sourceEnv, extension.rebase_unbase] using hClauses
end ModelExtension
theorem modelExtension (checked : Checked) (hSupported : Semantics.FreeSupport.NnfSupportedBy [] checked.payload.antiPrenex.result) (M : Semantics.Model) (base : Semantics.Env M) : Nonempty (ModelExtension checked M base) := by
  have hLocalSourceEq := localSkolem_source_eq_antiPrenexResult checked
  have hLocalSupported :
      Semantics.FreeSupport.NnfSupportedBy []
        checked.payload.localSkolem.source := by
    simpa [hLocalSourceEq] using hSupported
  rcases LocalSkolemPayload.uniformSoundExtension_of_check (localSkolem_checked checked) hLocalSupported M base with ⟨localSkolem⟩
  have localSkolem' :
      Semantics.LocalSkolemSoundness.UniformSoundExtension (LocalSkolem.initialState checked.payload.antiPrenex.result)
        checked.payload.antiPrenex.result
        checked.payload.localSkolem.result M base := by
    simpa [hLocalSourceEq] using localSkolem
  exact ⟨{
    sourceSupported := hSupported
    localSkolem := localSkolem'
    definitionalCnf := Semantics.DefinitionalCnfPayload.uniformSoundExtension_of_check (definitionalCnf_checked checked) (localSkolem'.extension.rebase base)
  }⟩
end CheckedPreprocessing
end NormalForm
end CoreSyntax
end Automation
end YesMetaZFC
