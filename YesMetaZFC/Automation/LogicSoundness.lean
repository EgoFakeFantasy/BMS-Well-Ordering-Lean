import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Logic.Shallow.Soundness
import YesMetaZFC.Logic.FirstOrder.Admissibility
/-!
# 新语义核自动化 soundness 边界
本文件是新 `Logic` 语义核和自动化层之间的第一层可信合同。它不导入旧
`Automation.Core` / `LCF` replay，也不复用旧 MF1 soundness。搜索器后续只需要把
自己的可检查证书落到这里的 `SemanticCertificate` / `DeepProblem` 合同上。自动化主线
保持 `SetLevel` 语法与可计算 payload 位于 `Type 0`，同时允许 provider 与语义证书消费
任意 universe 的模型载体；无后缀 API 仅是现有 tactic 使用的 `x = 0` 特化。
-/
namespace YesMetaZFC
namespace Automation
namespace LogicSoundness
universe u v w x
open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder
open _root_.YesMetaZFC.Logic.Shallow.FirstOrder
/--
自动化搜索器进入可信边界后必须交出的最小语义合同。
注意：这里故意只说“前提语义蕴涵目标”，不提旧 Hilbert/LCF replay。DAG、
CDCL residual、叠加演算和后续二阶/Henkin checker 都应各自证明能产生这个合同。
-/
structure SemanticCertificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (premises : Theory σ) (target : Formula σ) where
  entails : Theory.SemanticallyEntails.{u, v, w, x} premises target
namespace SemanticCertificate
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {premises : Theory σ} {target : Formula σ} (cert : SemanticCertificate.{u, v, w, x} premises target) :
    Theory.SemanticallyEntails.{u, v, w, x} premises target :=
  cert.entails
def weaken {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {strong weak : Theory σ} {target : Formula σ} (hSub : ∀ φ, weak φ → strong φ) (cert : SemanticCertificate.{u, v, w, x} weak target) :
    SemanticCertificate.{u, v, w, x} strong target where
  entails := Theory.entails_weaken hSub cert.entails
end SemanticCertificate
structure DeepProblem (σ : Signature.{u, v, w}) where
  premises : List (Formula σ) := []
  target : Formula σ
namespace DeepProblem
def theory {σ : Signature.{u, v, w}} (problem : DeepProblem σ) : Theory σ :=
  fun φ => φ ∈ problem.premises
def refutationFormula {σ : Signature.{u, v, w}} (problem : DeepProblem σ) : Formula σ :=
  Formula.conjunctionList (problem.premises ++ [Formula.neg problem.target])
theorem satisfies_refutationFormula_iff {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (problem : DeepProblem σ) (env : Env M) :
    Theory.Models problem.theory env ∧
        ¬ Formula.satisfies env problem.target ↔
      Formula.satisfies env problem.refutationFormula := by
  unfold refutationFormula
  rw [Formula.satisfies_conjunctionList_iff]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hModels, hTarget⟩ formula (hPremise | hTargetFormula)
    · exact hModels formula hPremise
    · subst formula
      simpa [Formula.satisfies] using hTarget
  · intro h
    constructor
    · intro formula hPremise
      exact h formula (Or.inl hPremise)
    · have hNeg := h (Formula.neg problem.target) (Or.inr rfl)
      simpa [Formula.satisfies] using hNeg
def empty {σ : Signature.{u, v, w}} (target : Formula σ) : DeepProblem σ where
  premises := []
  target := target
abbrev Certificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) :=
  SemanticCertificate.{u, v, w, x} problem.theory problem.target
def premiseCertificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) {φ : Formula σ} (hMem : φ ∈ problem.premises) :
    SemanticCertificate.{u, v, w, x} problem.theory φ where
  entails := Theory.entails_of_mem hMem
end DeepProblem
structure CheckedCertificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] where
  problem : DeepProblem σ
  cert : DeepProblem.Certificate.{u, v, w, x} problem
namespace CheckedCertificate
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (checked : CheckedCertificate.{u, v, w, x} (σ := σ)) :
    Theory.SemanticallyEntails.{u, v, w, x} checked.problem.theory checked.problem.target :=
  checked.cert.entails
end CheckedCertificate
structure CheckedValidCertificate {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] where
  target : Formula σ
  cert : SemanticCertificate.{u, v, w, x} Theory.empty target
namespace CheckedValidCertificate
theorem sound {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (checked : CheckedValidCertificate.{u, v, w, x} (σ := σ)) :
    Theory.SemanticallyEntails.{u, v, w, x} Theory.empty checked.target :=
  checked.cert.entails
end CheckedValidCertificate
/- 集合层语法固定在 `Type 0`；模型载体可独立处于任意 universe。 -/
namespace SetLevel
abbrev Signature := Logic.Signature.{0, 0, 0}
abbrev Term (σ : Signature) := Logic.FirstOrder.Term σ
abbrev Formula (σ : Signature) := Logic.FirstOrder.Formula σ
abbrev Theory (σ : Signature) := Logic.FirstOrder.Theory σ
abbrev StructureAt (σ : Signature) :=
  Logic.FirstOrder.Structure.{0, 0, 0, x} σ
abbrev EnvAt {σ : Signature} (M : StructureAt.{x} σ) :=
  Logic.FirstOrder.Env M
abbrev SemanticallyEntailsAt
    {σ : Signature} [DecidableEq σ.SortSymbol] (T : Theory σ) (φ : Formula σ) :=
  Logic.FirstOrder.Theory.SemanticallyEntails.{0, 0, 0, x} T φ
abbrev Structure (σ : Signature) := StructureAt.{0} σ
abbrev Env {σ : Signature} (M : Structure σ) := EnvAt.{0} M
abbrev SemanticallyEntails {σ : Signature} [DecidableEq σ.SortSymbol] (T : Theory σ) (φ : Formula σ) :=
  SemanticallyEntailsAt.{0} T φ
namespace Theory
def empty {σ : Signature} : Theory σ :=
  Logic.FirstOrder.Theory.empty
def singleton {σ : Signature} (φ : Formula σ) : Theory σ :=
  Logic.FirstOrder.Theory.singleton φ
def insert {σ : Signature} (φ : Formula σ) (T : Theory σ) : Theory σ :=
  Logic.FirstOrder.Theory.insert φ T
def union {σ : Signature} (T U : Theory σ) : Theory σ :=
  Logic.FirstOrder.Theory.union T U
end Theory
abbrev SemanticCertificateAt
    {σ : Signature} [DecidableEq σ.SortSymbol] (premises : Theory σ) (target : Formula σ) :=
  LogicSoundness.SemanticCertificate.{0, 0, 0, x} premises target
abbrev SemanticCertificate {σ : Signature} [DecidableEq σ.SortSymbol] (premises : Theory σ) (target : Formula σ) :=
  SemanticCertificateAt.{0} premises target
namespace SemanticCertificate
theorem soundAt {σ : Signature} [DecidableEq σ.SortSymbol]
    {premises : Theory σ} {target : Formula σ} (cert : SemanticCertificateAt.{x} premises target) :
    SemanticallyEntailsAt.{x} premises target :=
  cert.entails
theorem sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {premises : Theory σ} {target : Formula σ} (cert : SemanticCertificate premises target) :
    SemanticallyEntails premises target :=
  cert.entails
def weakenAt {σ : Signature} [DecidableEq σ.SortSymbol]
    {strong weak : Theory σ} {target : Formula σ} (hSub : ∀ φ, weak φ → strong φ) (cert : SemanticCertificateAt.{x} weak target) :
    SemanticCertificateAt.{x} strong target :=
  LogicSoundness.SemanticCertificate.weaken hSub cert
def weaken {σ : Signature} [DecidableEq σ.SortSymbol]
    {strong weak : Theory σ} {target : Formula σ} (hSub : ∀ φ, weak φ → strong φ) (cert : SemanticCertificate weak target) :
    SemanticCertificate strong target :=
  weakenAt hSub cert
end SemanticCertificate
structure DeepProblem (σ : Signature) where
  premises : List (Formula σ) := []
  target : Formula σ
namespace DeepProblem
def theory {σ : Signature} (problem : DeepProblem σ) : Theory σ :=
  fun φ => φ ∈ problem.premises
def refutationFormula {σ : Signature} (problem : DeepProblem σ) : Formula σ :=
  Formula.conjunctionList (problem.premises ++ [Formula.neg problem.target])
theorem satisfies_refutationFormula_iff_at {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : StructureAt.{x} σ} (problem : DeepProblem σ) (env : EnvAt.{x} M) :
    Logic.FirstOrder.Theory.Models problem.theory env ∧
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target ↔
      Logic.FirstOrder.Formula.satisfies env problem.refutationFormula := by
  unfold refutationFormula
  rw [Logic.FirstOrder.Formula.satisfies_conjunctionList_iff]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hModels, hTarget⟩ formula (hPremise | hTargetFormula)
    · exact hModels formula hPremise
    · subst formula
      simpa [Logic.FirstOrder.Formula.satisfies] using hTarget
  · intro h
    constructor
    · intro formula hPremise
      exact h formula (Or.inl hPremise)
    · have hNeg := h (Formula.neg problem.target) (Or.inr rfl)
      simpa [Logic.FirstOrder.Formula.satisfies] using hNeg
theorem satisfies_refutationFormula_iff {σ : Signature}
    [DecidableEq σ.SortSymbol] {M : Structure σ} (problem : DeepProblem σ) (env : Env M) :
    Logic.FirstOrder.Theory.Models problem.theory env ∧
        ¬ Logic.FirstOrder.Formula.satisfies env problem.target ↔
      Logic.FirstOrder.Formula.satisfies env problem.refutationFormula :=
  satisfies_refutationFormula_iff_at problem env
/-! ## proof-carrying 良构性边界 -/
def Admissible {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) : Prop :=
  Logic.FirstOrder.Formula.Admissible problem.target ∧
    ∀ premise, premise ∈ problem.premises →
      Logic.FirstOrder.Formula.Admissible premise
def check_admissible {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) : Bool :=
  Logic.FirstOrder.Formula.check_admissible problem.target &&
    problem.premises.all Logic.FirstOrder.Formula.check_admissible
theorem check_admissible_sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (hCheck : problem.check_admissible = true) :
    Admissible problem := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hTarget, hPremises⟩
  constructor
  · exact Logic.FirstOrder.Formula.check_admissible_sound hTarget
  · intro premise hPremise
    have hAll :
        ∀ formula, formula ∈ problem.premises →
          Logic.FirstOrder.Formula.check_admissible formula = true :=
      List.all_eq_true.mp hPremises
    exact Logic.FirstOrder.Formula.check_admissible_sound (hAll premise hPremise)
def empty {σ : Signature} (target : Formula σ) : DeepProblem σ where
  premises := []
  target := target
abbrev CertificateAt {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) :=
  SemanticCertificateAt.{x} problem.theory problem.target
abbrev Certificate {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) :=
  CertificateAt.{0} problem
def premiseCertificateAt {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) {φ : Formula σ} (hMem : φ ∈ problem.premises) :
    SemanticCertificateAt.{x} problem.theory φ where
  entails := Logic.FirstOrder.Theory.entails_of_mem hMem
def premiseCertificate {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) {φ : Formula σ} (hMem : φ ∈ problem.premises) :
    SemanticCertificate problem.theory φ :=
  premiseCertificateAt problem hMem
end DeepProblem
structure CheckedCertificateAt
    {σ : Signature} [DecidableEq σ.SortSymbol] where
  problem : DeepProblem σ
  cert : DeepProblem.CertificateAt.{x} problem
abbrev CheckedCertificate {σ : Signature} [DecidableEq σ.SortSymbol] :=
  CheckedCertificateAt.{0} (σ := σ)
namespace CheckedCertificate
theorem soundAt {σ : Signature} [DecidableEq σ.SortSymbol] (checked : CheckedCertificateAt.{x} (σ := σ)) :
    SemanticallyEntailsAt.{x}
      checked.problem.theory checked.problem.target :=
  checked.cert.entails
theorem sound {σ : Signature} [DecidableEq σ.SortSymbol] (checked : CheckedCertificate (σ := σ)) :
    SemanticallyEntails checked.problem.theory checked.problem.target :=
  soundAt checked
end CheckedCertificate
/-! ### 自动化后端消费协议 -/
/--
已经在可信边界内闭合的一个自动化后端结果。
搜索器本身仍是不可信的；它只能通过自己的 checker/soundness 定理构造这里的
`cert` 字段。`audit?` 只保存压缩证书图和统计信息，不参与 soundness。
-/
structure BackendSuccessAt {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) where
  admissible : DeepProblem.Admissible problem
  backend : Certificate.Backend
  phase : Certificate.Phase := .replay
  cert : DeepProblem.CertificateAt.{x} problem
  audit? : Option Certificate.Composite := none
  note : String := ""
abbrev BackendSuccess {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) :=
  BackendSuccessAt.{0} problem
namespace BackendSuccessAt
theorem sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccessAt.{x} problem) :
    SemanticallyEntailsAt.{x} problem.theory problem.target :=
  success.cert.entails
def toCheckedCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccessAt.{x} problem) :
    CheckedCertificateAt.{x} (σ := σ) where
  problem := problem
  cert := success.cert
def summary {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccessAt.{x} problem) : String :=
  let note := if success.note.isEmpty then "" else s!"; note={success.note}"
  let audit :=
    match success.audit? with
    | some cert => s!"; auditNodes={cert.nodes.size}; root={cert.root}"
    | none => ""
  s!"{success.backend.label}/{success.phase.label}: closed{audit}{note}"
def ofCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (backend : Certificate.Backend) (phase : Certificate.Phase) (cert : DeepProblem.CertificateAt.{x} problem)
    (admissible : DeepProblem.Admissible problem) (audit? : Option Certificate.Composite := none) (note : String := "") :
    BackendSuccessAt.{x} problem where
  admissible := admissible
  backend := backend
  phase := phase
  cert := cert
  audit? := audit?
  note := note
end BackendSuccessAt
namespace BackendSuccess
theorem sound {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccess problem) :
    SemanticallyEntails problem.theory problem.target :=
  BackendSuccessAt.sound success
def toCheckedCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccess problem) :
    CheckedCertificate (σ := σ) :=
  BackendSuccessAt.toCheckedCertificate success
def summary {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (success : BackendSuccess problem) : String :=
  BackendSuccessAt.summary success
def ofCertificate {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (backend : Certificate.Backend) (phase : Certificate.Phase) (cert : DeepProblem.Certificate problem)
    (admissible : DeepProblem.Admissible problem) (audit? : Option Certificate.Composite := none) (note : String := "") :
    BackendSuccess problem :=
  BackendSuccessAt.ofCertificate backend phase cert admissible audit? note
end BackendSuccess
inductive BackendAttemptAt {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) where
  | success (success : BackendSuccessAt.{x} problem)
  | failure (diagnostic : Certificate.Diagnostic)
abbrev BackendAttempt {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) :=
  BackendAttemptAt.{0} problem
namespace BackendAttemptAt
def closed {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} : BackendAttemptAt.{x} problem → Bool
  | .success _ => true
  | .failure _ => false
def success? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} :
    BackendAttemptAt.{x} problem → Option (BackendSuccessAt.{x} problem)
  | .success result => some result
  | .failure _ => none
def diagnostic? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} :
    BackendAttemptAt.{x} problem → Option Certificate.Diagnostic
  | .success _ => none
  | .failure diagnostic => some diagnostic
def summary {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} : BackendAttemptAt.{x} problem → String
  | .success result => BackendSuccessAt.summary result
  | .failure diagnostic => diagnostic.label
theorem sound_of_success {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} {attempt : BackendAttemptAt.{x} problem}
    {success : BackendSuccessAt.{x} problem} (_hSuccess : success? attempt = some success) :
    SemanticallyEntailsAt.{x} problem.theory problem.target :=
  BackendSuccessAt.sound success
end BackendAttemptAt
abbrev BackendResult (α : Type u) :=
  Except Certificate.Diagnostic α
namespace BackendAttempt
def closed {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) : Bool :=
  BackendAttemptAt.closed attempt
def success? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) :
    Option (BackendSuccess problem) :=
  BackendAttemptAt.success? attempt
def diagnostic? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) :
    Option Certificate.Diagnostic :=
  BackendAttemptAt.diagnostic? attempt
def summary {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) : String :=
  BackendAttemptAt.summary attempt
theorem sound_of_success {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} {attempt : BackendAttempt problem}
    {success : BackendSuccess problem} (hSuccess : BackendAttempt.success? attempt = some success) :
    SemanticallyEntails problem.theory problem.target :=
  BackendAttemptAt.sound_of_success hSuccess
end BackendAttempt
structure PortfolioAt {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) where
  attempts : Array (BackendAttemptAt.{x} problem) := #[]
abbrev Portfolio {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) :=
  PortfolioAt.{0} problem
namespace PortfolioAt
def empty {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) : PortfolioAt.{x} problem where
  attempts := #[]
def push {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) (attempt : BackendAttemptAt.{x} problem) : PortfolioAt.{x} problem where
  attempts := portfolio.attempts.push attempt
def firstSuccess? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) :
    Option (BackendSuccessAt.{x} problem) := Id.run do
  for attempt in portfolio.attempts do
    match BackendAttemptAt.success? attempt with
    | some success => return some success
    | none => pure ()
  return none
def diagnostics {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) :
    Array Certificate.Diagnostic := Id.run do
  let mut out := #[]
  for attempt in portfolio.attempts do
    match BackendAttemptAt.diagnostic? attempt with
    | some diagnostic => out := out.push diagnostic
    | none => pure ()
  return out
def closed {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) : Bool := (firstSuccess? portfolio).isSome
def checkedCertificate? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) :
    Option (CheckedCertificateAt.{x} (σ := σ)) := do
  let success ← firstSuccess? portfolio
  pure (BackendSuccessAt.toCheckedCertificate success)
theorem sound_of_firstSuccess {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} {portfolio : PortfolioAt.{x} problem}
    {success : BackendSuccessAt.{x} problem} (_hSuccess : firstSuccess? portfolio = some success) :
    SemanticallyEntailsAt.{x} problem.theory problem.target :=
  BackendSuccessAt.sound success
end PortfolioAt
namespace Portfolio
def empty {σ : Signature} [DecidableEq σ.SortSymbol] (problem : DeepProblem σ) : Portfolio problem :=
  PortfolioAt.empty problem
def push {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem) (attempt : BackendAttempt problem) : Portfolio problem :=
  PortfolioAt.push portfolio attempt
def firstSuccess? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem) :
    Option (BackendSuccess problem) :=
  PortfolioAt.firstSuccess? portfolio
def diagnostics {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem) :
    Array Certificate.Diagnostic :=
  PortfolioAt.diagnostics portfolio
def closed {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem) : Bool :=
  PortfolioAt.closed portfolio
def checkedCertificate? {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} (portfolio : Portfolio problem) :
    Option (CheckedCertificate (σ := σ)) :=
  PortfolioAt.checkedCertificate? portfolio
theorem sound_of_firstSuccess {σ : Signature} [DecidableEq σ.SortSymbol]
    {problem : DeepProblem σ} {portfolio : Portfolio problem}
    {success : BackendSuccess problem} (hSuccess : Portfolio.firstSuccess? portfolio = some success) :
    SemanticallyEntails problem.theory problem.target :=
  PortfolioAt.sound_of_firstSuccess hSuccess
end Portfolio
/--
自动化搜索器的 proof-carrying provider 接口。
`run` 可以做任意搜索，但返回 `.success` 时必须已经携带 `BackendSuccess`，因此可信边界
仍然只依赖语义证书本身。
-/
structure ProviderAt (σ : Signature) [DecidableEq σ.SortSymbol] where
  name : String
  backend : Certificate.Backend
  run : (problem : DeepProblem σ) → BackendAttemptAt.{x} problem
abbrev Provider (σ : Signature) [DecidableEq σ.SortSymbol] :=
  ProviderAt.{0} σ
namespace ProviderAt
def solve? {σ : Signature} [DecidableEq σ.SortSymbol] (provider : ProviderAt.{x} σ) (problem : DeepProblem σ) : Option (BackendSuccessAt.{x} problem) :=
  BackendAttemptAt.success? (provider.run problem)
def runAll {σ : Signature} [DecidableEq σ.SortSymbol] (providers : Array (ProviderAt.{x} σ)) (problem : DeepProblem σ) :
    PortfolioAt.{x} problem := Id.run do
  let mut attempts := #[]
  for provider in providers do
    attempts := attempts.push (provider.run problem)
  return { attempts := attempts }
end ProviderAt
namespace Provider
def solve? {σ : Signature} [DecidableEq σ.SortSymbol] (provider : Provider σ) (problem : DeepProblem σ) : Option (BackendSuccess problem) :=
  ProviderAt.solve? provider problem
def runAll {σ : Signature} [DecidableEq σ.SortSymbol] (providers : Array (Provider σ)) (problem : DeepProblem σ) :
    Portfolio problem :=
  ProviderAt.runAll providers problem
end Provider
structure CheckedValidCertificateAt
    {σ : Signature} [DecidableEq σ.SortSymbol] where
  target : Formula σ
  cert : SemanticCertificateAt.{x} Theory.empty target
abbrev CheckedValidCertificate
    {σ : Signature} [DecidableEq σ.SortSymbol] :=
  CheckedValidCertificateAt.{0} (σ := σ)
namespace CheckedValidCertificate
theorem soundAt {σ : Signature} [DecidableEq σ.SortSymbol] (checked : CheckedValidCertificateAt.{x} (σ := σ)) :
    SemanticallyEntailsAt.{x} Theory.empty checked.target :=
  checked.cert.entails
theorem sound {σ : Signature} [DecidableEq σ.SortSymbol] (checked : CheckedValidCertificate (σ := σ)) :
    SemanticallyEntails Theory.empty checked.target :=
  soundAt checked
end CheckedValidCertificate
end SetLevel
structure BridgeProblem {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol] (M : Structure.{u, v, w, x} σ) where
  premises : List (BridgeResult M) := []
  target : BridgeResult M
namespace BridgeProblem
def toDeep {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M) :
    DeepProblem σ where
  premises := problem.premises.map (fun premise => premise.deep)
  target := problem.target.deep
def ShallowModels {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M) (env : Env M) : Prop :=
  ∀ premise, premise ∈ problem.premises → premise.prop env
theorem models_of_shallowModels {σ : Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M)
    {env : Env M} (hPremises : problem.ShallowModels env) :
    Theory.Models problem.toDeep.theory env := by
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨premise, hMem, hDeep⟩
  rw [← hDeep]
  exact (premise.sound env).mp (hPremises premise hMem)
theorem target_satisfies_of_certificate {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M) (cert : DeepProblem.Certificate.{u, v, w, x} problem.toDeep)
    {env : Env M} (hPremises : problem.ShallowModels env) :
    Formula.satisfies env problem.target.deep :=
  cert.entails env (problem.models_of_shallowModels hPremises)
theorem target_prop_of_certificate {σ : Signature.{u, v, w}}
    [DecidableEq σ.SortSymbol] {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M) (cert : DeepProblem.Certificate.{u, v, w, x} problem.toDeep)
    {env : Env M} (hPremises : problem.ShallowModels env) :
    problem.target.prop env := (problem.target.sound env).mpr (problem.target_satisfies_of_certificate cert hPremises)
end BridgeProblem
end LogicSoundness
end Automation
end YesMetaZFC
