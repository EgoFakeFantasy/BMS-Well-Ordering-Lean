import YesMetaZFC.Automation.KernelReplay
import YesMetaZFC.Automation.SourcePreprocessing
import YesMetaZFC.Automation.HOSearchMaterialization
import YesMetaZFC.Automation.HODAGCertificate
import YesMetaZFC.Automation.HOExtensionalWitnessRegistry
import YesMetaZFC.Automation.HORefutationProvider
import YesMetaZFC.Automation.CoreNormalForm.HigherOrderProjectionSoundness

/-!
# 高阶宿主 replay 表达式构造器

把高阶 provider 的大段元层 quotation 从宿主重化文件移出。这里不依赖宿主私有
结构，只消费闭合 source snapshot、`FoolReplay` 与 HO provider artifact；最终宿主
构造器以 `Name` 注入，避免形成模块环。
-/
namespace YesMetaZFC
namespace Automation
namespace HigherOrderReplayBuilder

open Lean Meta

def buildAttempt
    (finalAttemptConstructor : Name)
    (input sourceProblem hSource : Expr)
    (sourceProblemValue : SourcePreprocessing.Problem)
    (replay : SourcePreprocessing.FoolReplay sourceProblemValue)
    (artifact :
      HORefutationProvider.CheckedReplayArtifact replay.payload.clauses) : MetaM Expr := do
  let settingsExpr :=
    toExpr (({} : SourcePreprocessing.FoolSettings).toSettings)
  let payloadExpr ←
    KernelReplay.preprocessingPayloadExpr
      (toExpr replay.payload.source)
      (toExpr replay.payload.normalized)
      settingsExpr replay.payload.normalizationTrace
      replay.payload.initialNnf
  let payloadCheck ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.check
      #[payloadExpr]
  let payloadSource ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.source
      #[payloadExpr]
  let refutationSource ←
    mkAppM ``SourcePreprocessing.Problem.refutationSource
      #[sourceProblem]
  let sourceCheck ←
    mkAppM ``CoreSyntax.NormalForm.SyntaxEq.formulaEq
      #[payloadSource, refutationSource]
  let antiPrenex ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.antiPrenex
      #[payloadExpr]
  let antiPrenexResult ←
    mkAppM ``CoreSyntax.NormalForm.AntiPrenexPayload.result
      #[antiPrenex]
  let freeCheck ←
    mkAppM
      ``CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      #[antiPrenexResult]
  let payloadClauses ←
    mkAppM
      ``CoreSyntax.NormalForm.CheckedPreprocessing.Payload.clauses
      #[payloadExpr]
  let replayCheck ←
    mkAppM ``SourcePreprocessing.FoolReplay.check
      #[sourceProblem, payloadExpr]
  let nativeReplayCheck :=
    toExpr (SourcePreprocessing.FoolReplay.check
      sourceProblemValue replay.payload)
  let hReplay ←
    KernelReplay.erasableBoolTrueProof
      `prove_auto_native_ho_replay
      "higher-order preprocessing replay"
      nativeReplayCheck replayCheck
  let nativeCheck ←
    mkAppM
      ``HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
      #[payloadClauses]
  let coreProblem :=
    HOSearchMaterialization.CoreProjectionSoundness.coreProblem
      replay.payload.clauses
  let coreProblemExpr := toExpr coreProblem
  let dagExpr :=
    HOSearchMaterialization.ReplayQuotation.dagExprWithProblem
      coreProblemExpr artifact.checked.checked.dag
  let selectorRegistryCheck ←
    mkAppM
      ``HODAGCertificate.DAG.avatarSelectorRegistryChecked
      #[dagExpr]
  let nativeWitnessRegistryExpr ←
    mkAppM ``HOExtensionalWitnessRegistry.Registry.ofDAG
      #[dagExpr]
  let witnessRegistryCheck ←
    mkAppM ``HOExtensionalWitnessRegistry.Registry.check
      #[dagExpr, nativeWitnessRegistryExpr]
  let initialClauses ←
    mkAppM ``HODAGCertificate.Problem.initialClauses
      #[coreProblemExpr]
  let initialClauseCheck ←
    mkAppOptM ``HODAGCertificate.Clause.check
      #[some (mkConst ``HOSearchMaterialization.SearchSignature), none]
  let initialClauseCount ←
    mkAppM ``Array.size #[initialClauses]
  let initialChecks ←
    mkAppM ``Array.all
      #[initialClauses, initialClauseCheck, toExpr 0, initialClauseCount]
  let supportedCheck ←
    mkAppM ``HODAGCertificate.DAG.avatarSoundnessSupported
      #[dagExpr]
  let replayChecks ←
    KernelReplay.erasableBoolTrueProofs
      `prove_auto_native_ho_replay
      #["higher-order preprocessing payload",
        "higher-order preprocessing source",
        "higher-order preprocessing free closure",
        "higher-order native clause projection",
        "higher-order selector registry",
        "higher-order extensional witness registry",
        "higher-order initial clause checks",
        "higher-order AVATAR soundness capability"]
      #[payloadCheck, sourceCheck, freeCheck, nativeCheck,
        selectorRegistryCheck, witnessRegistryCheck,
        initialChecks, supportedCheck]
      #[payloadCheck, sourceCheck, freeCheck, nativeCheck,
        selectorRegistryCheck, witnessRegistryCheck,
        initialChecks, supportedCheck]
  let dagContract ←
    KernelReplay.higherOrderDagContractProof
      dagExpr artifact.checked.checked.dag
  let hNativeRaw := replayChecks[3]!
  let hSelectorRegistry := replayChecks[4]!
  let hNativeWitnessRegistry := replayChecks[5]!
  let hInitialRaw := replayChecks[6]!
  let hSupported := replayChecks[7]!
  let expectedNativeCheck ←
    mkAppM
      ``HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
      #[payloadClauses]
  let hNativeExpr ←
    KernelReplay.retargetBoolTrueProof
      "higher-order native clause projection"
      expectedNativeCheck hNativeRaw
  let expectedCoreProblemExpr ←
    mkAppM
      ``HOSearchMaterialization.CoreProjectionSoundness.coreProblem
      #[payloadClauses]
  let hInitialChecks ←
    KernelReplay.retargetBoolTrueProof
      "higher-order initial clause checks" initialChecks hInitialRaw
  let checkedDag ←
    mkAppM ``HODAGCertificate.CheckedDAG.ofContract
      #[dagExpr, dagContract]
  let checkedDagExpr ←
    mkAppM ``HODAGCertificate.CheckedDAG.dag #[checkedDag]
  let checkedAvatar ←
    mkAppM ``HODAGCertificate.CheckedAvatarDAG.mk
      #[checkedDag, hSelectorRegistry]
  let witnessRegistryExpr ←
    mkAppM ``HOExtensionalWitnessRegistry.Registry.ofDAG
      #[checkedDagExpr]
  let checkedWitnessRegistryCheck ←
    mkAppM ``HOExtensionalWitnessRegistry.Registry.check
      #[checkedDagExpr, witnessRegistryExpr]
  let hWitnessRegistry ←
    KernelReplay.retargetBoolTrueProof
      "higher-order checked extensional witness registry"
      checkedWitnessRegistryCheck hNativeWitnessRegistry
  let hWitnessExtracted ← mkEqRefl witnessRegistryExpr
  let checkedWitnessRegistry ←
    mkAppM ``HOExtensionalWitnessRegistry.CheckedRegistry.mk
      #[witnessRegistryExpr, hWitnessExtracted, hWitnessRegistry]
  let checkedProblem ←
    mkAppM ``HODAGCertificate.DAG.problem #[checkedDagExpr]
  let hCheckedProblem ←
    KernelReplay.equalityProof
      "higher-order DAG problem alignment"
      checkedProblem coreProblemExpr
  let hCoreProblem ←
    KernelReplay.equalityProof
      "higher-order core problem quotation"
      coreProblemExpr expectedCoreProblemExpr
  let hProblemEq ←
    mkAppM ``Eq.trans #[hCheckedProblem, hCoreProblem]
  let hExpectedInitialChecks ←
    mkAppM ``HORefutationProvider.initialChecks_of_problem_eq
      #[hCoreProblem, hInitialChecks]
  let replayArtifact ←
    mkAppM ``HORefutationProvider.CheckedReplayArtifact.mk
      #[checkedAvatar, checkedWitnessRegistry, hProblemEq,
        hNativeExpr, hExpectedInitialChecks, hSupported]
  let replayExpr ←
    mkAppM ``SourcePreprocessing.FoolReplay.ofCheck
      #[sourceProblem, payloadExpr, hReplay]
  mkAppM finalAttemptConstructor
    #[input, sourceProblem, hSource, replayExpr, replayArtifact]

end HigherOrderReplayBuilder
end Automation
end YesMetaZFC
