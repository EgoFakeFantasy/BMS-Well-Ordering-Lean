import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Logic.Shallow.Soundness

/-!
# 自动化的闭句语义可信边界

自动化搜索器可以在边界外使用适合计算的证书语法，但进入可信层时必须已经编译为
内在排序、内在作用域正确的闭句。由此，可信接口不再携带自由变量环境、良构证明或
闭合性桥接；这些义务只能存在于证书语法到内在语法的单次检查编译中。
-/

namespace YesMetaZFC
namespace Automation
namespace LogicSoundness

universe u v w x

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder
open _root_.YesMetaZFC.Logic.Shallow.FirstOrder

/-- 自动化后端进入可信边界后交出的最小语义合同。 -/
structure SemanticCertificate {σ : Signature.{u, v, w}}
    (premises : Theory σ) (target : Sentence σ) where
  entails : Theory.SemanticallyEntails.{u, v, w, x} premises target

namespace SemanticCertificate

theorem sound {σ : Signature.{u, v, w}}
    {premises : Theory σ} {target : Sentence σ}
    (cert : SemanticCertificate.{u, v, w, x} premises target) :
    Theory.SemanticallyEntails.{u, v, w, x} premises target :=
  cert.entails

theorem weaken {σ : Signature.{u, v, w}}
    {strong weak : Theory σ} {target : Sentence σ}
    (hSub : ∀ φ, weak φ → strong φ)
    (cert : SemanticCertificate.{u, v, w, x} weak target) :
    SemanticCertificate.{u, v, w, x} strong target where
  entails := Theory.entails_weaken hSub cert.entails

end SemanticCertificate

/-- 可信自动化问题只含闭句。 -/
structure DeepProblem (σ : Signature.{u, v, w}) where
  premises : List (Sentence σ) := []
  target : Sentence σ

namespace DeepProblem

def theory {σ : Signature.{u, v, w}}
    (problem : DeepProblem σ) : Theory σ :=
  fun φ => φ ∈ problem.premises

def refutationFormula {σ : Signature.{u, v, w}}
    (problem : DeepProblem σ) : Sentence σ :=
  Formula.conjunctionList
    (problem.premises ++ [Formula.neg problem.target])

theorem satisfies_refutationFormula_iff {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (problem : DeepProblem σ) :
    Theory.Models M problem.theory ∧
        ¬ problem.target.TrueIn M ↔
      problem.refutationFormula.TrueIn M := by
  unfold refutationFormula Formula.TrueIn
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

def empty {σ : Signature.{u, v, w}}
    (target : Sentence σ) : DeepProblem σ where
  target := target

abbrev Certificate {σ : Signature.{u, v, w}}
    (problem : DeepProblem σ) :=
  SemanticCertificate.{u, v, w, x} problem.theory problem.target

theorem premiseCertificate {σ : Signature.{u, v, w}}
    (problem : DeepProblem σ) {φ : Sentence σ}
    (hMem : φ ∈ problem.premises) :
    SemanticCertificate.{u, v, w, x} problem.theory φ where
  entails := Theory.entails_of_mem hMem

end DeepProblem

structure CheckedCertificate {σ : Signature.{u, v, w}} where
  problem : DeepProblem σ
  cert : DeepProblem.Certificate.{u, v, w, x} problem

namespace CheckedCertificate

theorem sound {σ : Signature.{u, v, w}}
    (checked : CheckedCertificate.{u, v, w, x} (σ := σ)) :
    Theory.SemanticallyEntails.{u, v, w, x}
      checked.problem.theory checked.problem.target :=
  checked.cert.entails

end CheckedCertificate

structure CheckedValidCertificate {σ : Signature.{u, v, w}} where
  target : Sentence σ
  cert : SemanticCertificate.{u, v, w, x} Theory.empty target

namespace CheckedValidCertificate

theorem sound {σ : Signature.{u, v, w}}
    (checked : CheckedValidCertificate.{u, v, w, x} (σ := σ)) :
    Theory.SemanticallyEntails.{u, v, w, x} Theory.empty checked.target :=
  checked.cert.entails

end CheckedValidCertificate

/-! ## Type 0 自动化接口 -/

namespace SetLevel

abbrev Signature := Logic.Signature.{0, 0, 0}
abbrev Sentence (σ : Signature) := Logic.FirstOrder.Sentence σ
abbrev Formula (σ : Signature) := Sentence σ
abbrev Term (σ : Signature) (sort : σ.SortSymbol) :=
  Logic.FirstOrder.Term σ [] [] sort
abbrev Theory (σ : Signature) := Logic.FirstOrder.Theory σ

abbrev StructureAt (σ : Signature) :=
  Logic.FirstOrder.Structure.{0, 0, 0, x} σ

abbrev EnvAt {σ : Signature} (M : StructureAt.{x} σ) :=
  Logic.FirstOrder.Env M [] []

abbrev SemanticallyEntailsAt
    {σ : Signature} (T : Theory σ) (φ : Sentence σ) :=
  Logic.FirstOrder.Theory.SemanticallyEntails.{0, 0, 0, x} T φ

abbrev Structure (σ : Signature) := StructureAt.{0} σ
abbrev Env {σ : Signature} (M : Structure σ) := EnvAt.{0} M

abbrev SemanticallyEntails
    {σ : Signature} (T : Theory σ) (φ : Sentence σ) :=
  SemanticallyEntailsAt.{0} T φ

namespace Theory

def empty {σ : Signature} : Theory σ :=
  Logic.FirstOrder.Theory.empty

def singleton {σ : Signature} (φ : Sentence σ) : Theory σ :=
  Logic.FirstOrder.Theory.singleton φ

def insert {σ : Signature} (φ : Sentence σ) (T : Theory σ) : Theory σ :=
  Logic.FirstOrder.Theory.insert φ T

def union {σ : Signature} (T U : Theory σ) : Theory σ :=
  Logic.FirstOrder.Theory.union T U

end Theory

abbrev SemanticCertificateAt
    {σ : Signature} (premises : Theory σ) (target : Sentence σ) :=
  LogicSoundness.SemanticCertificate.{0, 0, 0, x} premises target

abbrev SemanticCertificate
    {σ : Signature} (premises : Theory σ) (target : Sentence σ) :=
  SemanticCertificateAt.{0} premises target

namespace SemanticCertificate

theorem soundAt {σ : Signature}
    {premises : Theory σ} {target : Sentence σ}
    (cert : SemanticCertificateAt.{x} premises target) :
    SemanticallyEntailsAt.{x} premises target :=
  cert.entails

theorem sound {σ : Signature}
    {premises : Theory σ} {target : Sentence σ}
    (cert : SemanticCertificate premises target) :
    SemanticallyEntails premises target :=
  cert.entails

theorem weakenAt {σ : Signature}
    {strong weak : Theory σ} {target : Sentence σ}
    (hSub : ∀ φ, weak φ → strong φ)
    (cert : SemanticCertificateAt.{x} weak target) :
    SemanticCertificateAt.{x} strong target :=
  LogicSoundness.SemanticCertificate.weaken hSub cert

theorem weaken {σ : Signature}
    {strong weak : Theory σ} {target : Sentence σ}
    (hSub : ∀ φ, weak φ → strong φ)
    (cert : SemanticCertificate weak target) :
    SemanticCertificate strong target :=
  weakenAt hSub cert

end SemanticCertificate

abbrev DeepProblem (σ : Signature) :=
  LogicSoundness.DeepProblem σ

namespace DeepProblem

def theory {σ : Signature} (problem : DeepProblem σ) : Theory σ :=
  LogicSoundness.DeepProblem.theory problem

def refutationFormula {σ : Signature}
    (problem : DeepProblem σ) : Sentence σ :=
  LogicSoundness.DeepProblem.refutationFormula problem

theorem satisfies_refutationFormula_iff_at {σ : Signature}
    {M : StructureAt.{x} σ} (problem : DeepProblem σ) :
    Logic.FirstOrder.Theory.Models M problem.theory ∧
        ¬ problem.target.TrueIn M ↔
      problem.refutationFormula.TrueIn M :=
  LogicSoundness.DeepProblem.satisfies_refutationFormula_iff problem

theorem satisfies_refutationFormula_iff {σ : Signature}
    {M : Structure σ} (problem : DeepProblem σ) :
    Logic.FirstOrder.Theory.Models M problem.theory ∧
        ¬ problem.target.TrueIn M ↔
      problem.refutationFormula.TrueIn M :=
  satisfies_refutationFormula_iff_at problem

def empty {σ : Signature} (target : Sentence σ) : DeepProblem σ :=
  LogicSoundness.DeepProblem.empty target

abbrev CertificateAt {σ : Signature} (problem : DeepProblem σ) :=
  SemanticCertificateAt.{x} problem.theory problem.target

abbrev Certificate {σ : Signature} (problem : DeepProblem σ) :=
  CertificateAt.{0} problem

theorem premiseCertificateAt {σ : Signature}
    (problem : DeepProblem σ) {φ : Sentence σ}
    (hMem : φ ∈ problem.premises) :
    SemanticCertificateAt.{x} problem.theory φ :=
  LogicSoundness.DeepProblem.premiseCertificate problem hMem

theorem premiseCertificate {σ : Signature}
    (problem : DeepProblem σ) {φ : Sentence σ}
    (hMem : φ ∈ problem.premises) :
    SemanticCertificate problem.theory φ :=
  premiseCertificateAt problem hMem

end DeepProblem

abbrev CheckedCertificateAt {σ : Signature} :=
  LogicSoundness.CheckedCertificate.{0, 0, 0, x} (σ := σ)

abbrev CheckedCertificate {σ : Signature} :=
  CheckedCertificateAt.{0} (σ := σ)

namespace CheckedCertificate

theorem soundAt {σ : Signature}
    (checked : CheckedCertificateAt.{x} (σ := σ)) :
    SemanticallyEntailsAt.{x}
      checked.problem.theory checked.problem.target :=
  checked.cert.entails

theorem sound {σ : Signature}
    (checked : CheckedCertificate (σ := σ)) :
    SemanticallyEntails checked.problem.theory checked.problem.target :=
  soundAt checked

end CheckedCertificate

/-! ### 自动化后端消费协议 -/

/--
后端成功结果只携带闭句问题的语义证书。搜索审计数据不参与可靠性证明。
-/
structure BackendSuccessAt {σ : Signature}
    (problem : DeepProblem σ) where
  backend : Certificate.Backend
  phase : Certificate.Phase := .replay
  cert : DeepProblem.CertificateAt.{x} problem
  audit? : Option Certificate.Composite := none
  note : String := ""

abbrev BackendSuccess {σ : Signature} (problem : DeepProblem σ) :=
  BackendSuccessAt.{0} problem

namespace BackendSuccessAt

theorem sound {σ : Signature}
    {problem : DeepProblem σ} (success : BackendSuccessAt.{x} problem) :
    SemanticallyEntailsAt.{x} problem.theory problem.target :=
  success.cert.entails

def toCheckedCertificate {σ : Signature}
    {problem : DeepProblem σ} (success : BackendSuccessAt.{x} problem) :
    CheckedCertificateAt.{x} (σ := σ) where
  problem := problem
  cert := success.cert

def summary {σ : Signature}
    {problem : DeepProblem σ} (success : BackendSuccessAt.{x} problem) :
    String :=
  let note := if success.note.isEmpty then "" else s!"; note={success.note}"
  let audit :=
    match success.audit? with
    | some cert => s!"; auditNodes={cert.nodes.size}; root={cert.root}"
    | none => ""
  s!"{success.backend.label}/{success.phase.label}: closed{audit}{note}"

def ofCertificate {σ : Signature}
    {problem : DeepProblem σ}
    (backend : Certificate.Backend) (phase : Certificate.Phase)
    (cert : DeepProblem.CertificateAt.{x} problem)
    (audit? : Option Certificate.Composite := none) (note : String := "") :
    BackendSuccessAt.{x} problem where
  backend := backend
  phase := phase
  cert := cert
  audit? := audit?
  note := note

end BackendSuccessAt

namespace BackendSuccess

theorem sound {σ : Signature}
    {problem : DeepProblem σ} (success : BackendSuccess problem) :
    SemanticallyEntails problem.theory problem.target :=
  BackendSuccessAt.sound success

def toCheckedCertificate {σ : Signature}
    {problem : DeepProblem σ} (success : BackendSuccess problem) :
    CheckedCertificate (σ := σ) :=
  BackendSuccessAt.toCheckedCertificate success

def summary {σ : Signature}
    {problem : DeepProblem σ} (success : BackendSuccess problem) :
    String :=
  BackendSuccessAt.summary success

def ofCertificate {σ : Signature}
    {problem : DeepProblem σ}
    (backend : Certificate.Backend) (phase : Certificate.Phase)
    (cert : DeepProblem.Certificate problem)
    (audit? : Option Certificate.Composite := none) (note : String := "") :
    BackendSuccess problem :=
  BackendSuccessAt.ofCertificate backend phase cert audit? note

end BackendSuccess

inductive BackendAttemptAt {σ : Signature}
    (problem : DeepProblem σ) where
  | success (success : BackendSuccessAt.{x} problem)
  | failure (diagnostic : Certificate.Diagnostic)

abbrev BackendAttempt {σ : Signature} (problem : DeepProblem σ) :=
  BackendAttemptAt.{0} problem

namespace BackendAttemptAt

def closed {σ : Signature}
    {problem : DeepProblem σ} : BackendAttemptAt.{x} problem → Bool
  | .success _ => true
  | .failure _ => false

def success? {σ : Signature}
    {problem : DeepProblem σ} :
    BackendAttemptAt.{x} problem → Option (BackendSuccessAt.{x} problem)
  | .success result => some result
  | .failure _ => none

def diagnostic? {σ : Signature}
    {problem : DeepProblem σ} :
    BackendAttemptAt.{x} problem → Option Certificate.Diagnostic
  | .success _ => none
  | .failure diagnostic => some diagnostic

def summary {σ : Signature}
    {problem : DeepProblem σ} : BackendAttemptAt.{x} problem → String
  | .success result => BackendSuccessAt.summary result
  | .failure diagnostic => diagnostic.label

theorem sound_of_success {σ : Signature}
    {problem : DeepProblem σ} {attempt : BackendAttemptAt.{x} problem}
    {success : BackendSuccessAt.{x} problem}
    (_hSuccess : success? attempt = some success) :
    SemanticallyEntailsAt.{x} problem.theory problem.target :=
  BackendSuccessAt.sound success

end BackendAttemptAt

abbrev BackendResult (α : Type u) :=
  Except Certificate.Diagnostic α

namespace BackendAttempt

def closed {σ : Signature}
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) : Bool :=
  BackendAttemptAt.closed attempt

def success? {σ : Signature}
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) :
    Option (BackendSuccess problem) :=
  BackendAttemptAt.success? attempt

def diagnostic? {σ : Signature}
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) :
    Option Certificate.Diagnostic :=
  BackendAttemptAt.diagnostic? attempt

def summary {σ : Signature}
    {problem : DeepProblem σ} (attempt : BackendAttempt problem) :
    String :=
  BackendAttemptAt.summary attempt

theorem sound_of_success {σ : Signature}
    {problem : DeepProblem σ} {attempt : BackendAttempt problem}
    {success : BackendSuccess problem}
    (hSuccess : BackendAttempt.success? attempt = some success) :
    SemanticallyEntails problem.theory problem.target :=
  BackendAttemptAt.sound_of_success hSuccess

end BackendAttempt

structure PortfolioAt {σ : Signature}
    (problem : DeepProblem σ) where
  attempts : Array (BackendAttemptAt.{x} problem) := #[]

abbrev Portfolio {σ : Signature} (problem : DeepProblem σ) :=
  PortfolioAt.{0} problem

namespace PortfolioAt

def empty {σ : Signature}
    (problem : DeepProblem σ) : PortfolioAt.{x} problem where
  attempts := #[]

def push {σ : Signature}
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem)
    (attempt : BackendAttemptAt.{x} problem) : PortfolioAt.{x} problem where
  attempts := portfolio.attempts.push attempt

def firstSuccess? {σ : Signature}
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) :
    Option (BackendSuccessAt.{x} problem) := Id.run do
  for attempt in portfolio.attempts do
    match BackendAttemptAt.success? attempt with
    | some success => return some success
    | none => pure ()
  return none

def diagnostics {σ : Signature}
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) :
    Array Certificate.Diagnostic := Id.run do
  let mut out := #[]
  for attempt in portfolio.attempts do
    match BackendAttemptAt.diagnostic? attempt with
    | some diagnostic => out := out.push diagnostic
    | none => pure ()
  return out

def closed {σ : Signature}
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) : Bool :=
  (firstSuccess? portfolio).isSome

def checkedCertificate? {σ : Signature}
    {problem : DeepProblem σ} (portfolio : PortfolioAt.{x} problem) :
    Option (CheckedCertificateAt.{x} (σ := σ)) := do
  let success ← firstSuccess? portfolio
  pure (BackendSuccessAt.toCheckedCertificate success)

theorem sound_of_firstSuccess {σ : Signature}
    {problem : DeepProblem σ} {portfolio : PortfolioAt.{x} problem}
    {success : BackendSuccessAt.{x} problem}
    (_hSuccess : firstSuccess? portfolio = some success) :
    SemanticallyEntailsAt.{x} problem.theory problem.target :=
  BackendSuccessAt.sound success

end PortfolioAt

namespace Portfolio

def empty {σ : Signature}
    (problem : DeepProblem σ) : Portfolio problem :=
  PortfolioAt.empty problem

def push {σ : Signature}
    {problem : DeepProblem σ} (portfolio : Portfolio problem)
    (attempt : BackendAttempt problem) : Portfolio problem :=
  PortfolioAt.push portfolio attempt

def firstSuccess? {σ : Signature}
    {problem : DeepProblem σ} (portfolio : Portfolio problem) :
    Option (BackendSuccess problem) :=
  PortfolioAt.firstSuccess? portfolio

def diagnostics {σ : Signature}
    {problem : DeepProblem σ} (portfolio : Portfolio problem) :
    Array Certificate.Diagnostic :=
  PortfolioAt.diagnostics portfolio

def closed {σ : Signature}
    {problem : DeepProblem σ} (portfolio : Portfolio problem) : Bool :=
  PortfolioAt.closed portfolio

def checkedCertificate? {σ : Signature}
    {problem : DeepProblem σ} (portfolio : Portfolio problem) :
    Option (CheckedCertificate (σ := σ)) :=
  PortfolioAt.checkedCertificate? portfolio

theorem sound_of_firstSuccess {σ : Signature}
    {problem : DeepProblem σ} {portfolio : Portfolio problem}
    {success : BackendSuccess problem}
    (hSuccess : Portfolio.firstSuccess? portfolio = some success) :
    SemanticallyEntails problem.theory problem.target :=
  PortfolioAt.sound_of_firstSuccess hSuccess

end Portfolio

/-- 能返回成功时已经携带语义证书的后端接口。 -/
structure ProviderAt (σ : Signature) where
  name : String
  backend : Certificate.Backend
  run : (problem : DeepProblem σ) → BackendAttemptAt.{x} problem

abbrev Provider (σ : Signature) :=
  ProviderAt.{0} σ

namespace ProviderAt

def solve? {σ : Signature}
    (provider : ProviderAt.{x} σ) (problem : DeepProblem σ) :
    Option (BackendSuccessAt.{x} problem) :=
  BackendAttemptAt.success? (provider.run problem)

def runAll {σ : Signature}
    (providers : Array (ProviderAt.{x} σ)) (problem : DeepProblem σ) :
    PortfolioAt.{x} problem := Id.run do
  let mut attempts := #[]
  for provider in providers do
    attempts := attempts.push (provider.run problem)
  return { attempts := attempts }

end ProviderAt

namespace Provider

def solve? {σ : Signature}
    (provider : Provider σ) (problem : DeepProblem σ) :
    Option (BackendSuccess problem) :=
  ProviderAt.solve? provider problem

def runAll {σ : Signature}
    (providers : Array (Provider σ)) (problem : DeepProblem σ) :
    Portfolio problem :=
  ProviderAt.runAll providers problem

end Provider

abbrev CheckedValidCertificateAt {σ : Signature} :=
  LogicSoundness.CheckedValidCertificate.{0, 0, 0, x} (σ := σ)

abbrev CheckedValidCertificate {σ : Signature} :=
  CheckedValidCertificateAt.{0} (σ := σ)

namespace CheckedValidCertificate

theorem soundAt {σ : Signature}
    (checked : CheckedValidCertificateAt.{x} (σ := σ)) :
    SemanticallyEntailsAt.{x} Theory.empty checked.target :=
  checked.cert.entails

theorem sound {σ : Signature}
    (checked : CheckedValidCertificate (σ := σ)) :
    SemanticallyEntails Theory.empty checked.target :=
  soundAt checked

end CheckedValidCertificate

end SetLevel

/-! ## 闭句浅嵌入桥接 -/

structure BridgeProblem {σ : Signature.{u, v, w}}
    (M : Structure.{u, v, w, x} σ) where
  premises : List (BridgeResult M []) := []
  target : BridgeResult M []

namespace BridgeProblem

def toDeep {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M) :
    DeepProblem σ where
  premises := problem.premises.map BridgeResult.deep
  target := problem.target.deep

def ShallowModels {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M) : Prop :=
  ∀ premise, premise ∈ problem.premises →
    premise.prop (Env.empty (M := M))

theorem models_of_shallowModels {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M)
    (hPremises : problem.ShallowModels) :
    Theory.Models M problem.toDeep.theory := by
  intro φ hφ
  rcases List.mem_map.mp hφ with ⟨premise, hMem, hDeep⟩
  rw [← hDeep]
  exact
    (premise.sound (Env.empty (M := M))).mp
      (hPremises premise hMem)

theorem target_satisfies_of_certificate {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M)
    (cert : DeepProblem.Certificate.{u, v, w, x} problem.toDeep)
    (hPremises : problem.ShallowModels) :
    problem.target.deep.TrueIn M :=
  cert.entails M (problem.models_of_shallowModels hPremises)

theorem target_prop_of_certificate {σ : Signature.{u, v, w}}
    {M : Structure.{u, v, w, x} σ} (problem : BridgeProblem M)
    (cert : DeepProblem.Certificate.{u, v, w, x} problem.toDeep)
    (hPremises : problem.ShallowModels) :
    problem.target.prop (Env.empty (M := M)) :=
  (problem.target.sound (Env.empty (M := M))).mpr
    (problem.target_satisfies_of_certificate cert hPremises)

end BridgeProblem

end LogicSoundness
end Automation
end YesMetaZFC
