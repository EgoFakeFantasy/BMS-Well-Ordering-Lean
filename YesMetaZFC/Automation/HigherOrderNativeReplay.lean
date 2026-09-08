import YesMetaZFC.Automation.CoreNormalForm.HigherOrderProjectionSoundness
import YesMetaZFC.Automation.HOAvatarSoundness
import YesMetaZFC.Automation.SourcePreprocessing
import YesMetaZFC.Automation.HOExtensionalWitnessRegistry
import YesMetaZFC.Automation.HODAGCertificate.LinearReplay

/-!
# 高阶回放的单次 native 检查票据

默认路径把同一份 payload、HO-DAG 与初始问题放进一张闭合 Bool ticket，避免
富 DAG 因多个局部检查被重复编译。严格审计路径不消费这个 ticket，只消费现有
HODAG 分块完备性和各局部 checker 的普通 Lean 证明。
-/
namespace YesMetaZFC
namespace Automation
namespace HigherOrderNativeReplay

abbrev Payload := CoreSyntax.NormalForm.CheckedPreprocessing.Payload
abbrev DAG := HOSearchMaterialization.DAG

def check (sourceProblem : SourcePreprocessing.Problem)
    (payload : Payload) (dag : DAG) : Bool :=
  payload.check && (CoreSyntax.NormalForm.SyntaxEq.formulaEq
    payload.source sourceProblem.refutationSource && (
      CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
        payload.antiPrenex.result && (
        HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
          payload.clauses && (
          HODAGCertificate.DAG.LinearReplay.coreCheck dag && (
          dag.avatarSelectorRegistryChecked && (
          let registry :=
            HOExtensionalWitnessRegistry.Registry.ofDAG dag
          HOExtensionalWitnessRegistry.Registry.check dag registry && (
          let problem :=
            HOSearchMaterialization.CoreProjectionSoundness.coreProblem
              payload.clauses
          problem.initialClauses.all HODAGCertificate.Clause.check && (
          dag.avatarSoundnessSupported))))))))

structure Checked (sourceProblem : SourcePreprocessing.Problem)
    (payload : Payload) (dag : DAG) : Prop where
  h_payload : payload.check = true
  h_source :
    CoreSyntax.NormalForm.SyntaxEq.formulaEq
      payload.source sourceProblem.refutationSource = true
  h_free :
    CoreSyntax.NormalForm.Semantics.FreeSupport.nnfFreeClosed
      payload.antiPrenex.result = true
  h_native :
    HOSearchMaterialization.CoreProjectionSoundness.Native.clauseSet
      payload.clauses = true
  h_dag : HODAGCertificate.DAG.LinearReplay.coreCheck dag = true
  h_selector : dag.avatarSelectorRegistryChecked = true
  h_witness :
    HOExtensionalWitnessRegistry.Registry.check dag
      (HOExtensionalWitnessRegistry.Registry.ofDAG dag) = true
  h_initial :
    (HOSearchMaterialization.CoreProjectionSoundness.coreProblem
      payload.clauses).initialClauses.all HODAGCertificate.Clause.check = true
  h_supported : dag.avatarSoundnessSupported = true

theorem Checked.ofCheck
    {sourceProblem : SourcePreprocessing.Problem}
    {payload : Payload} {dag : DAG}
    (hCheck : check sourceProblem payload dag = true) :
    Checked sourceProblem payload dag := by
  simp only [check, Bool.and_eq_true_iff] at hCheck
  exact {
    h_payload := hCheck.1
    h_source := hCheck.2.1
    h_free := hCheck.2.2.1
    h_native := hCheck.2.2.2.1
    h_dag := hCheck.2.2.2.2.1
    h_selector := hCheck.2.2.2.2.2.1
    h_witness := hCheck.2.2.2.2.2.2.1
    h_initial := hCheck.2.2.2.2.2.2.2.1
    h_supported := hCheck.2.2.2.2.2.2.2.2
  }

end HigherOrderNativeReplay
end Automation
end YesMetaZFC
