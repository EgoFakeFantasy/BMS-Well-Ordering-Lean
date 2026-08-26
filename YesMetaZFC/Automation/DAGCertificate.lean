import YesMetaZFC.Automation.DAGCertificate.Payload
namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
universe x
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.Automation.LogicSoundness
section DAGCertificateSignature
variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]
namespace DAG
/--
整张 DAG 的反证语义不变量。
它要求每个节点都满足 `Node.RefutationInvariant`；后续拓扑归纳将把 source / local /
ground / residual 的局部 soundness 统一接到这里。
-/
def RefutationInvariant  (dag : DAG σ) : Prop :=
  ∀ index (hIndex : index < dag.nodes.size),
    Node.RefutationInvariant.{x} (σ := σ) dag.problem (dag.nodeAt index hIndex)
def GuardedRefutationInvariant (dag : DAG σ) (valuation : PropResolution.Valuation) : Prop :=
  ∀ index (hIndex : index < dag.nodes.size),
    Node.GuardedRefutationInvariant.{x} (σ := σ) dag.problem valuation (dag.nodeAt index hIndex)
end DAG
structure CheckedDAG
     where
  private mkInternal ::
  dag : DAG σ
  contract : DAG.Contract dag
namespace CheckedDAG
section CheckedDAGEnvironment
variable (cert : CheckedDAG (σ := σ))
variable (valuation : PropResolution.Valuation)
variable (index : Nat) (hIndex : index < cert.dag.nodes.size)
/-- 已有完整结构契约时直接进入 checked DAG，不重复计算布尔总检查。 -/
def ofContract (dag : DAG σ) (contract : DAG.Contract dag) :
    CheckedDAG (σ := σ) :=
  ⟨dag, contract⟩
def problem : ClauseProblem σ :=
  cert.dag.problem
def toComposite : Certificate.Composite :=
  cert.dag.toComposite
private theorem parentGuardsHold_of_union_check (hGuardCheck : (match cert.dag.parentGuardUnion? (cert.dag.nodeAt index hIndex).parents with
      | some unionGuards =>
          Guards.eq (cert.dag.nodeAt index hIndex).guards unionGuards
      | none => false) = true) (parent : NodeId) (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentSize : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation} :
    Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
    Node.GuardsHold valuation (cert.dag.nodeAt parent hParentSize).guards := by
  cases hUnion :
      cert.dag.parentGuardUnion? (cert.dag.nodeAt index hIndex).parents with
  | none =>
      simp [hUnion] at hGuardCheck
  | some unionGuards =>
      have hEq :
          Guards.eq (cert.dag.nodeAt index hIndex).guards unionGuards = true := by
        simpa [hUnion] using hGuardCheck
      intro hCurrentGuards
      have hUnionGuards : Node.GuardsHold valuation unionGuards :=
        Node.GuardsHold.of_guardSetEq hEq hCurrentGuards
      intro lit hLit
      exact hUnionGuards lit (DAG.mem_parentGuardUnionList_of_parent_mem (dag := cert.dag) (parents := (cert.dag.nodeAt index hIndex).parents.toList)
          (parent := parent) (parentNode := cert.dag.nodeAt parent hParentSize) (guards := unionGuards) (lit := lit)
          (by simpa [DAG.parentGuardUnion?] using hUnion)
          hParentMem (cert.dag.node?_eq_some_nodeAt hParentSize)
          hLit)
theorem parentGuardsHold_of_localNodeGuardsOk (payload : LocalRulePayload σ) (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (parent : NodeId) (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList) (hParentSize : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation} :
    Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
      Node.GuardsHold valuation (cert.dag.nodeAt parent hParentSize).guards := by
  have hGuardCheck := (cert.contract.node_contract index hIndex).guards_checked
  unfold DAG.localNodeGuardsOk at hGuardCheck
  have hGuardCheck' : (match cert.dag.parentGuardUnion? (cert.dag.nodeAt index hIndex).parents with
      | some unionGuards =>
          Guards.eq (cert.dag.nodeAt index hIndex).guards unionGuards
      | none => false) = true := by
    simpa [hLocal] using hGuardCheck
  exact parentGuardsHold_of_union_check cert index hIndex hGuardCheck'
    parent hParentMem hParentSize
theorem parentGuardsHold_of_theoryConflictNodeGuardsOk (payload : TheoryConflictPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload) (parent : NodeId)
    (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList) (hParentSize : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation} :
    Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
      Node.GuardsHold valuation (cert.dag.nodeAt parent hParentSize).guards := by
  have hGuardCheck := (cert.contract.node_contract index hIndex).guards_checked
  unfold DAG.localNodeGuardsOk at hGuardCheck
  have hGuardCheck' : (match cert.dag.parentGuardUnion? (cert.dag.nodeAt index hIndex).parents with
      | some unionGuards =>
          Guards.eq (cert.dag.nodeAt index hIndex).guards unionGuards
      | none => false) = true := by
    simpa [hPayload] using hGuardCheck
  exact parentGuardsHold_of_union_check cert index hIndex hGuardCheck'
    parent hParentMem hParentSize
/--
固定当前本地规则节点的 guards 后，把整族 guarded 父不变量统一退化为普通父不变量，
从而让 guarded 回放直接复用普通拓扑 step。
-/
private theorem localGuardedTopologicalStep_of_topologicalStep (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : LocalRulePayload σ)
    (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload) (hStep :
      (∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) →
        Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex)) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt index hIndex) := by
  intro M env hProblem hGuards
  exact (hStep fun parent hParent =>
    Node.refutationInvariant_of_guardedRefutationInvariant (hParents parent hParent) (cert.parentGuardsHold_of_localNodeGuardsOk
        index hIndex payload hLocal parent hParent (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex)
        hGuards)) env hProblem
/--
checked DAG 拓扑 step 的 source 分支。
父节点不变量在 source 分支中不会被使用；保留该参数是为了让本定理能直接嵌入后续
统一 `topologicalInduction` 的 step 形状。
-/
theorem sourceTopologicalStep (_hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt parent (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex)))
    (initialIndex : Nat) (hSource : (cert.dag.nodeAt index hIndex).payload = .source initialIndex) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) :=
  Node.sourceRefutationInvariant_of_payload_check hSource ((cert.contract.node_contract index hIndex).payload_checked)
theorem localRuleParentSnapshotChecked (payload : LocalRulePayload σ) (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (parent : ParentClause σ) (hParent : parent ∈ payload.evidence.parentClauses.toList) :
    cert.dag.parentSnapshotChecked parent = true := by
  have hAllNodes := Array.all_eq_true.mp cert.contract.parent_snapshots_checked
  have hCurrent : ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun current =>
        cert.dag.parentSnapshotChecked current) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hLocal] at hCurrent
  have hNode :
      payload.evidence.parentClauses.all (fun current => cert.dag.parentSnapshotChecked current) = true := by
    simpa [Payload.parentClauses, LocalRulePayload.parentClauses] using hCurrent
  exact array_check_of_mem hNode hParent
theorem theoryConflictSnapshotChecked (payload : TheoryConflictPayload σ) (hPayload : (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload) :
    cert.dag.parentSnapshotChecked payload.conflict = true := by
  have hAllNodes := Array.all_eq_true.mp cert.contract.parent_snapshots_checked
  have hNode : ((cert.dag.nodeAt index hIndex).payload.parentClauses.all fun parent =>
        cert.dag.parentSnapshotChecked parent) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked, DAG.nodeAt] using
      hAllNodes index hIndex
  rw [hPayload] at hNode
  simpa [Payload.parentClauses, TheoryConflictPayload.parentClauses] using hNode
theorem parentClause_eq_nodeAt_of_snapshot (parent : ParentClause σ) (hParentSize : parent.id < cert.dag.nodes.size)
    (hSnapshot : cert.dag.parentSnapshotChecked parent = true) :
    parent.clause = (cert.dag.nodeAt parent.id hParentSize).conclusion := by
  rcases DAG.parentSnapshotChecked_sound hSnapshot with
    ⟨snapshotNode, hSnapshotNode, hSnapshotClause⟩
  have hSnapshotNodeEq : snapshotNode = cert.dag.nodeAt parent.id hParentSize := by
    rw [cert.dag.node?_eq_some_nodeAt hParentSize] at hSnapshotNode
    cases hSnapshotNode
    rfl
  have hSnapshotClause' : (cert.dag.nodeAt parent.id hParentSize).conclusion = parent.clause := by
    simpa [hSnapshotNodeEq] using hSnapshotClause
  exact hSnapshotClause'.symm
theorem parentObject_satisfies_of_snapshot (parent : ParentClause σ) {objectClause : Clause σ} (hParentSize : parent.id < cert.dag.nodes.size)
    (hSnapshot : cert.dag.parentSnapshotChecked parent = true) (hObjectEq : parent.clause = objectClause)
    {base : PropResolution.Valuation} (hInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem base (cert.dag.nodeAt parent.id hParentSize))
    {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M) (hProblem : cert.dag.problem.Valid env) (hGuards :
      Node.GuardsHold base (cert.dag.nodeAt parent.id hParentSize).guards) :
    Clause.Satisfies env objectClause := by
  rw [← hObjectEq,
    cert.parentClause_eq_nodeAt_of_snapshot parent hParentSize hSnapshot]
  exact hInvariant env hProblem hGuards
theorem propParentInitialLink_fields (link : PropParentClauseLink σ) (hLink :
      cert.dag.propParentInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true) (hParentSize : link.parent.id < cert.dag.nodes.size) :
    cert.dag.parentSnapshotChecked link.parent = true ∧ (cert.dag.nodeAt link.parent.id hParentSize).unguarded = true := by
  unfold DAG.propParentInitialLinkOk at hLink
  rw [cert.dag.node?_eq_some_nodeAt hParentSize] at hLink
  rcases Bool.and_eq_true_iff.mp hLink with ⟨hPrefix, hUnguarded⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨_, hSnapshot⟩
  exact ⟨hSnapshot, hUnguarded⟩
theorem propGuardActivationInitialLink_fields (link : PropGuardActivationLink σ) (hLink :
      cert.dag.propGuardActivationInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true) (hParentSize : link.parent.id < cert.dag.nodes.size) :
    cert.dag.parentSnapshotChecked link.parent = true ∧ (cert.dag.nodeAt link.parent.id hParentSize).unguarded = false ∧
        Guards.eq link.guards (cert.dag.nodeAt link.parent.id hParentSize).guards = true := by
  unfold DAG.propGuardActivationInitialLinkOk at hLink
  rw [cert.dag.node?_eq_some_nodeAt hParentSize] at hLink
  rcases Bool.and_eq_true_iff.mp hLink with ⟨hPrefix, hFields⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨_, hSnapshot⟩
  rcases Bool.and_eq_true_iff.mp hFields with ⟨hUnguarded, hGuardEq⟩
  exact ⟨hSnapshot, by simpa using hUnguarded, hGuardEq⟩
theorem propLearnedInitialLink_fields (link : PropLearnedClauseLink) (hLink :
      cert.dag.propLearnedInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true) (hParentSize : link.parent < cert.dag.nodes.size) :
    ∃ learnedPayload, (cert.dag.nodeAt link.parent hParentSize).payload =
        .propositionalLearnedClause learnedPayload ∧
      link.clause = learnedPayload.learned := by
  unfold DAG.propLearnedInitialLinkOk at hLink
  rw [cert.dag.node?_eq_some_nodeAt hParentSize] at hLink
  rcases Bool.and_eq_true_iff.mp hLink with ⟨_, hMatch⟩
  cases hPayload : (cert.dag.nodeAt link.parent hParentSize).payload with
  | propositionalLearnedClause learnedPayload =>
      refine ⟨learnedPayload, rfl, ?_⟩
      exact PropResolution.clauseEq_eq.mp (by simpa [hPayload] using hMatch)
  | _ =>
      simp [hPayload] at hMatch
theorem propLearnedNode_fields (payload : PropositionalLearnedClausePayload) (hPayload : (cert.dag.nodeAt index hIndex).payload =
        .propositionalLearnedClause payload) :
    payload.conflict ∈ (cert.dag.nodeAt index hIndex).parents.toList ∧ (cert.dag.nodeAt index hIndex).conclusion.isEmpty = true ∧
      ∃ conflictNode,
        cert.dag.node? payload.conflict = some conflictNode ∧
        conflictNode.theoryConflict = true ∧
        Guards.eq (cert.dag.nodeAt index hIndex).guards
          conflictNode.guards = true ∧
        payload.learned = Guards.learnedClause conflictNode.guards := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hPayload] at hPayloadCheck
  have hLearnedCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold PropositionalLearnedClausePayload.check at hLearnedCheck
  rcases Bool.and_eq_true_iff.mp hLearnedCheck with
    ⟨hParentIn, hConclusionEmpty⟩
  have hParentMem :
      payload.conflict ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
    exact Array.mem_def.mp (by simpa using hParentIn)
  have hGuardCheck := (cert.contract.node_contract index hIndex).guards_checked
  unfold DAG.localNodeGuardsOk at hGuardCheck
  simp [hPayload] at hGuardCheck
  rcases hGuardCheck with ⟨_, hConflictMatch⟩
  cases hConflictNode : cert.dag.node? payload.conflict with
  | none =>
      simp [hConflictNode] at hConflictMatch
  | some conflictNode =>
      have hConflictFields :
          conflictNode.theoryConflict &&
            Guards.eq (cert.dag.nodeAt index hIndex).guards
              conflictNode.guards && (match conflictNode.payload with
            | .theoryConflict _ =>
                PropResolution.clauseEq payload.learned (Guards.learnedClause conflictNode.guards)
            | _ => false) = true := by
        simpa [hConflictNode] using hConflictMatch
      rcases Bool.and_eq_true_iff.mp hConflictFields with
        ⟨hConflictPrefix, hLearnedEq⟩
      rcases Bool.and_eq_true_iff.mp hConflictPrefix with
        ⟨hConflictTheory, hGuardEq⟩
      cases hConflictPayload : conflictNode.payload with
      | theoryConflict _ =>
          rw [hConflictPayload] at hLearnedEq
          exact ⟨hParentMem, hConclusionEmpty, conflictNode, rfl,
            hConflictTheory, hGuardEq,
            PropResolution.clauseEq_eq.mp (by simpa using hLearnedEq)⟩
      | _ =>
          simp [hConflictPayload] at hLearnedEq
/--
checked DAG 的统一本地规则拓扑 step。
父快照、父边与三种环境搬运在这里统一处理；具体 evidence 的 checker 语义交给
`LocalRuleEvidence.satisfies_of_check`。
-/
theorem localRuleTopologicalStep (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt parent (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex)))
    (payload : LocalRulePayload σ) (hLocal : (cert.dag.nodeAt index hIndex).payload = .localRule payload) :
    Node.RefutationInvariant.{x} cert.dag.problem (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hLocal] at hPayloadCheck
  have hLocalCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold LocalRulePayload.check at hLocalCheck
  rcases Bool.and_eq_true_iff.mp hLocalCheck with
    ⟨hLocalPrefix, _hFamily⟩
  rcases Bool.and_eq_true_iff.mp hLocalPrefix with
    ⟨_hParentsNonempty, hEvidenceCheck⟩
  have hParentSat :
      ∀ (parent : ParentClause σ),
        parent ∈ payload.evidence.parentClauses.toList →
          parent.idIn (cert.dag.nodeAt index hIndex).parents = true →
            ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
              cert.dag.problem.Valid env → Clause.Satisfies env parent.clause := by
    intro parent hPayloadMem hParentIn M env hProblem
    have hParentMem :
        parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
      ParentClause.mem_toList_of_idIn hParentIn
    let hParentSize := Nat.lt_trans (cert.contract.parents_before index hIndex parent.id hParentMem) hIndex
    have hSnapshot :=
      cert.localRuleParentSnapshotChecked index hIndex payload hLocal
        parent hPayloadMem
    have hParentClause :=
      cert.parentClause_eq_nodeAt_of_snapshot parent hParentSize hSnapshot
    simpa only [hParentClause] using (hParents parent.id hParentMem) env hProblem
  have hSubstitutedParentSat :
      ∀ (parent : ParentClause σ),
        parent ∈ payload.evidence.parentClauses.toList →
          parent.idIn (cert.dag.nodeAt index hIndex).parents = true →
            ∀ (subst : TermSubstitution σ),
              TermSubstitution.BoundClosed subst ∧
                TermSubstitution.WellSorted subst →
                  ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
                    cert.dag.problem.Valid env →
                      Clause.Satisfies env (Clause.applySubstitution subst parent.clause) := by
    intro parent hPayloadMem hParentIn subst hAdmissible M env hProblem
    let targetEnv := TermSubstitution.semanticEnv subst env hAdmissible.2
    have hEnvMatches :=
      TermSubstitution.semanticEnv_matches (subst := subst) (env := env) (hAdmissible := hAdmissible.2)
    have hProblem' : cert.dag.problem.Valid targetEnv :=
      hProblem.of_sameBoundStack hEnvMatches.1
    have hSatTarget :=
      hParentSat parent hPayloadMem hParentIn targetEnv hProblem'
    exact (Clause.satisfies_applySubstitution_iff_of_envMatches (subst := subst) (env := env) (targetEnv := targetEnv)
      hAdmissible.1 hEnvMatches parent.clause).mpr hSatTarget
  have hStandardizedParentSat :
      ∀ (parent : ParentClause σ),
        parent ∈ payload.evidence.parentClauses.toList →
          parent.idIn (cert.dag.nodeAt index hIndex).parents = true →
            ∀ (offset : Nat) (subst : TermSubstitution σ),
              TermSubstitution.BoundClosed subst ∧
                TermSubstitution.WellSorted subst →
                  ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
                    cert.dag.problem.Valid env →
                      Clause.Satisfies env (Clause.applySubstitution subst (Clause.renameFreeVars offset parent.clause)) := by
    intro parent hPayloadMem hParentIn offset subst hAdmissible M env hProblem
    let substitutionEnv := TermSubstitution.semanticEnv subst env hAdmissible.2
    have hSubstitutionEnv :=
      TermSubstitution.semanticEnv_matches (subst := subst) (env := env) (hAdmissible := hAdmissible.2)
    let renamedEnv := FreeVarRenaming.semanticEnv offset substitutionEnv
    have hRenamedEnv :=
      FreeVarRenaming.semanticEnv_matches (offset := offset) (sourceEnv := substitutionEnv)
    have hProblem' : cert.dag.problem.Valid substitutionEnv :=
      hProblem.of_sameBoundStack hSubstitutionEnv.1
    have hProblem'' : cert.dag.problem.Valid renamedEnv :=
      hProblem'.of_sameBoundStack hRenamedEnv.1
    have hSatOriginal :=
      hParentSat parent hPayloadMem hParentIn renamedEnv hProblem''
    have hSatRenamed :
        Clause.Satisfies substitutionEnv (Clause.renameFreeVars offset parent.clause) := (Clause.satisfies_renameFreeVars_iff_of_envMatches
        (offset := offset) (sourceEnv := substitutionEnv) (targetEnv := renamedEnv) hRenamedEnv parent.clause).mpr hSatOriginal
    exact (Clause.satisfies_applySubstitution_iff_of_envMatches (subst := subst) (env := env) (targetEnv := substitutionEnv)
      hAdmissible.1 hSubstitutionEnv (Clause.renameFreeVars offset parent.clause)).mpr hSatRenamed
  intro M env hProblem
  exact LocalRuleEvidence.satisfies_of_check (M := M) (fun currentEnv => cert.dag.problem.Valid currentEnv)
    hEvidenceCheck (fun parent hPayloadMem hParentIn currentEnv hCurrent =>
      hParentSat parent hPayloadMem hParentIn currentEnv hCurrent) (fun parent hPayloadMem hParentIn subst hAdmissible currentEnv hCurrent =>
      hSubstitutedParentSat parent hPayloadMem hParentIn subst hAdmissible
        currentEnv hCurrent) (fun parent hPayloadMem hParentIn offset subst hAdmissible currentEnv hCurrent =>
      hStandardizedParentSat parent hPayloadMem hParentIn offset subst hAdmissible
        currentEnv hCurrent)
    env hProblem
theorem sourceGuardedTopologicalStep (_hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) (initialIndex : Nat)
    (hSource : (cert.dag.nodeAt index hIndex).payload = .source initialIndex) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt index hIndex) :=
  Node.guardedRefutationInvariant_of_refutationInvariant (Node.sourceRefutationInvariant_of_payload_check hSource
      ((cert.contract.node_contract index hIndex).payload_checked))
theorem theoryConflictGuardedTopologicalStep (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : TheoryConflictPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .theoryConflict payload) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hPayload] at hPayloadCheck
  have hTheoryCheck :
      payload.check (cert.dag.nodeAt index hIndex).parents (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hPayloadCheck
  unfold TheoryConflictPayload.check at hTheoryCheck
  rcases Bool.and_eq_true_iff.mp hTheoryCheck with ⟨hPrefix, _hConclusionEmpty⟩
  rcases Bool.and_eq_true_iff.mp hPrefix with ⟨hParentIn, _hConflictEmpty⟩
  have hParentMem :
      payload.conflict.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIn
  let hParentLt := cert.contract.parents_before index hIndex payload.conflict.id hParentMem
  let hParentSize := Nat.lt_trans hParentLt hIndex
  have hConflictInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt payload.conflict.id hParentSize) :=
    hParents payload.conflict.id hParentMem
  have hSnapshot :=
    cert.theoryConflictSnapshotChecked index hIndex payload hPayload
  have hConflictClause :=
    cert.parentClause_eq_nodeAt_of_snapshot payload.conflict hParentSize hSnapshot
  have hConflictGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt index hIndex).guards →
        Node.GuardsHold valuation (cert.dag.nodeAt payload.conflict.id hParentSize).guards :=
    cert.parentGuardsHold_of_theoryConflictNodeGuardsOk index hIndex payload hPayload
      payload.conflict.id hParentMem hParentSize
  intro M env hProblem hGuards
  exact (Node.theoryConflictGuardedRefutationInvariant_of_payload_check (problem := cert.dag.problem) (node := cert.dag.nodeAt index hIndex)
    (conflictNode := cert.dag.nodeAt payload.conflict.id hParentSize)
    hPayload hConflictClause hConflictGuards hConflictInvariant ((cert.contract.node_contract index hIndex).payload_checked)) (env := env) hProblem hGuards
theorem propositionalLearnedClauseGuardedTopologicalStep (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : PropositionalLearnedClausePayload) (hPayload :
      (cert.dag.nodeAt index hIndex).payload = .propositionalLearnedClause payload) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt index hIndex) := by
  rcases cert.propLearnedNode_fields index hIndex payload hPayload with
    ⟨hParentMem, _, conflictNode, hConflictNode,
      hConflictTheory, hGuardEq, _⟩
  let hParentSize := Nat.lt_trans (cert.contract.parents_before index hIndex payload.conflict hParentMem) hIndex
  rw [cert.dag.node?_eq_some_nodeAt hParentSize] at hConflictNode
  cases hConflictNode
  intro M env hProblem hGuards
  exact False.elim (Clause.not_satisfies_of_isEmpty (Node.theoryConflict_fields hConflictTheory).2 ((hParents payload.conflict hParentMem) env hProblem
      (Node.GuardsHold.of_guardSetEq hGuardEq hGuards)))
private theorem propClosureJustificationCheckAt
    {parents : Array NodeId} {payload : PropositionalClosurePayload σ} (hCheck : payload.justificationsCheck parents = true)
    {slot : Nat} (hSlot : slot < payload.initialClauses.size) :
    ∃ hJust : slot < payload.initialJustifications.size, (payload.initialJustifications[slot]).check parents payload.atomMap
        payload.initialClauses[slot] = true := by
  have hListCheck :=
    PropositionalClosurePayload.justificationsListCheck_eq_true_of_check hCheck
  unfold PropositionalClosurePayload.justificationsCheck at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hSizeBool, _hBody⟩
  have hSizeEq :
      payload.initialClauses.size = payload.initialJustifications.size := by
    simpa using hSizeBool
  have hJust : slot < payload.initialJustifications.size := by
    simpa [hSizeEq] using hSlot
  refine ⟨hJust, ?_⟩
  have hAt :=
    PropositionalClosurePayload.justificationsListCheck_at
      parents payload.atomMap hListCheck slot (by simpa using hSlot) (by simpa using hJust)
  simpa using hAt
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
private theorem propClosureJustificationSupportedAt
    {payload : PropositionalClosurePayload σ} (hSupported : payload.guardedSoundnessSupported = true)
    {slot : Nat} (hSlot : slot < payload.initialJustifications.size) : (payload.initialJustifications[slot]).guardedSoundnessSupported = true := by
  have hAll := Array.all_eq_true.mp hSupported
  simpa [PropositionalClosurePayload.guardedSoundnessSupported] using hAll slot hSlot
theorem residualCdclGuardedTopologicalStep (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) (payload : PropositionalClosurePayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .residualCdcl payload) (hPayloadSupported : payload.guardedSoundnessSupported = true) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt index hIndex) := by
  have hPayloadCheck := (cert.contract.node_contract index hIndex).payload_checked
  rw [hPayload] at hPayloadCheck
  have hResidualCheck : (!((cert.dag.nodeAt index hIndex).parents.isEmpty) && (cert.dag.nodeAt index hIndex).conclusion.isEmpty &&
            payload.check (cert.dag.nodeAt index hIndex).parents) = true := by
    simpa [Payload.check] using hPayloadCheck
  rcases Bool.and_eq_true_iff.mp hResidualCheck with
    ⟨_hResidualPrefix, hClosureCheck⟩
  have hClosureParts := hClosureCheck
  unfold PropositionalClosurePayload.check at hClosureParts
  simp at hClosureParts
  rcases hClosureParts with ⟨hClosureParts, _hVerifiedStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hRetainedStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hGeneratedStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hClauseStats⟩
  rcases hClosureParts with ⟨hClosureParts, _hStepsStats⟩
  rcases hClosureParts with ⟨hCheckedUnsatProof, hJustificationsCheckProof⟩
  have hCheckedUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof = true :=
    hCheckedUnsatProof
  have hJustificationsCheck :
      payload.justificationsCheck (cert.dag.nodeAt index hIndex).parents = true :=
    hJustificationsCheckProof
  have hInitialLinks := (cert.contract.node_contract index hIndex).prop_initial_links_checked
  have hDagInitials :
      payload.initialJustifications.all (fun justification =>
          cert.dag.propInitialJustificationDagOk (cert.dag.nodeAt index hIndex).parents justification) = true := by
    simpa [DAG.propInitialLinksOk, hPayload] using hInitialLinks
  intro M env hProblem _hGuards
  have hInitialSatisfies :
      ∀ initial, initial ∈ payload.initialClauses.toList →
        PropResolution.Clause.Satisfies (PropLiteralLink.valuation valuation payload.atomMap env) initial.clause := by
    intro initial hInitialMem
    have hInitialArray : initial ∈ payload.initialClauses :=
      Array.mem_def.mpr hInitialMem
    rcases Array.mem_iff_getElem.mp hInitialArray with
      ⟨slot, hSlot, hInitialGet⟩
    rcases propClosureJustificationCheckAt hJustificationsCheck hSlot with
      ⟨hJustSlot, hJustificationCheck⟩
    have hJustificationSupported :=
      propClosureJustificationSupportedAt hPayloadSupported hJustSlot
    have hDagOk := (Array.all_eq_true.mp hDagInitials) slot hJustSlot
    cases hJustification :
        payload.initialJustifications[slot] with
    | parentClause link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropParentClauseLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hCheckPrefix, hLiteralChecks⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentInBool, hObjectEqBool⟩
        have hInitialEq : initial.clause = link.encodedClause :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hObjectEq : link.parent.clause = link.objectClause :=
          Clause.eq_sound link.parent.clause link.objectClause hObjectEqBool
        have hDagParent :
            cert.dag.propParentInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
          ParentClause.mem_toList_of_idIn hParentInBool
        let hParentLt := cert.contract.parents_before index hIndex link.parent.id hParentMem
        let hParentSize := Nat.lt_trans hParentLt hIndex
        have hParentFields :=
          cert.propParentInitialLink_fields index hIndex link
            hDagParent hParentSize
        rcases hParentFields with ⟨hSnapshot, hParentUnguarded⟩
        have hObjectSat :=
          cert.parentObject_satisfies_of_snapshot link.parent hParentSize
            hSnapshot hObjectEq (hParents link.parent.id hParentMem)
            env hProblem (Node.GuardsHold.of_isEmpty (by
              simpa [Node.unguarded] using hParentUnguarded))
        have hEncodedSat :=
          PropParentClauseLink.encodedClause_satisfies_of_object (base := valuation) (atomMap := payload.atomMap)
            hLiteralChecks hObjectSat
        simpa [hInitialEq] using hEncodedSat
    | guardActivationClause link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropGuardActivationLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hCheckPrefix, hLiteralChecks⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hCheckPrefix, hGuardChecks⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentInBool, hObjectEqBool⟩
        have hInitialEq : initial.clause = link.encodedClause :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hObjectEq : link.parent.clause = link.objectClause :=
          Clause.eq_sound link.parent.clause link.objectClause hObjectEqBool
        have hDagActivation :
            cert.dag.propGuardActivationInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent.id ∈ (cert.dag.nodeAt index hIndex).parents.toList :=
          ParentClause.mem_toList_of_idIn hParentInBool
        let hParentLt := cert.contract.parents_before index hIndex link.parent.id hParentMem
        let hParentSize := Nat.lt_trans hParentLt hIndex
        have hGuardFields :=
          cert.propGuardActivationInitialLink_fields index hIndex link
            hDagActivation hParentSize
        rcases hGuardFields with ⟨hSnapshot, _hParentUnguarded, hGuardEq⟩
        have hObjectOfGuards : (∀ lit, lit ∈ (Guards.canonical link.guards).toList →
              lit.Holds valuation) → Clause.Satisfies env link.objectClause := by
          intro hLinkGuards
          exact cert.parentObject_satisfies_of_snapshot link.parent hParentSize
            hSnapshot hObjectEq (hParents link.parent.id hParentMem)
            env hProblem (Node.GuardsHold.of_guardSetEq hGuardEq hLinkGuards)
        have hEncodedSat :=
          PropGuardActivationLink.encodedClause_satisfies (base := valuation) (atomMap := payload.atomMap)
            hGuardChecks hLiteralChecks hObjectOfGuards
        simpa [hInitialEq] using hEncodedSat
    | propLearnedClause link =>
        have hCheck :
            link.check (cert.dag.nodeAt index hIndex).parents
              payload.atomMap initial = true := by
          simpa [PropInitialJustification.check, hJustification, hInitialGet]
            using hJustificationCheck
        unfold PropLearnedClauseLink.check at hCheck
        rcases Bool.and_eq_true_iff.mp hCheck with
          ⟨hCheckPrefix, hInitialEqBool⟩
        rcases Bool.and_eq_true_iff.mp hCheckPrefix with
          ⟨hParentContains, hOutside⟩
        have hInitialEq : initial.clause = link.clause :=
          PropResolution.clauseEq_eq.mp hInitialEqBool
        have hDagLearned :
            cert.dag.propLearnedInitialLinkOk (cert.dag.nodeAt index hIndex).parents link = true := by
          simpa [DAG.propInitialJustificationDagOk, hJustification] using hDagOk
        have hParentMem :
            link.parent ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
          have hArray :
              link.parent ∈ (cert.dag.nodeAt index hIndex).parents := by
            simpa using hParentContains
          exact Array.mem_def.mp hArray
        let hParentLt := cert.contract.parents_before index hIndex link.parent hParentMem
        let hParentSize := Nat.lt_trans hParentLt hIndex
        rcases cert.propLearnedInitialLink_fields index hIndex link
            hDagLearned hParentSize with
          ⟨learnedPayload, hParentPayload, hLinkLearnedEq⟩
        rcases cert.propLearnedNode_fields link.parent hParentSize
            learnedPayload hParentPayload with
          ⟨_, hParentConclusionEmpty, conflictNode, _,
            _, hGuardEq, hLearnedEqConflict⟩
        by_cases hParentGuards :
            Node.GuardsHold valuation (cert.dag.nodeAt link.parent hParentSize).guards
        · exact False.elim (Clause.not_satisfies_of_isEmpty hParentConclusionEmpty ((hParents link.parent hParentMem) env hProblem hParentGuards))
        · have hNotConflictGuards :
              ¬ Node.GuardsHold valuation conflictNode.guards := by
            intro hConflictGuards
            apply hParentGuards
            intro lit hLit
            have hCanonical :
                Guards.canonical (cert.dag.nodeAt link.parent hParentSize).guards =
                  Guards.canonical conflictNode.guards :=
              PropResolution.clauseEq_eq.mp (by simpa [Guards.eq] using hGuardEq)
            exact hConflictGuards lit (by simpa [hCanonical] using hLit)
          have hLearnedSat :=
            PropLearnedClauseLink.satisfies_of_not_guards (base := valuation) (atomMap := payload.atomMap)
              (env := env) (link := link) (guards := conflictNode.guards) (hLinkLearnedEq.trans hLearnedEqConflict)
              hOutside hNotConflictGuards
          simpa [hInitialEq] using hLearnedSat
    | avatarSkeleton link =>
        have hUnsupported : (PropInitialJustification.avatarSkeleton link :
              PropInitialJustification σ).guardedSoundnessSupported = true := by
          simpa [hJustification] using hJustificationSupported
        simp [PropInitialJustification.guardedSoundnessSupported] at hUnsupported
  exact False.elim (PropResolution.checkedUnsat_sound hInitialSatisfies hCheckedUnsat)
theorem topologicalInduction
    {P : ∀ index, index < cert.dag.nodes.size → Node σ → Prop} (hStep :
      ∀ index (hIndex : index < cert.dag.nodes.size), (∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex) (cert.dag.nodeAt parent
                (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) →
          P index hIndex (cert.dag.nodeAt index hIndex)) :
    ∀ index (hIndex : index < cert.dag.nodes.size),
      P index hIndex (cert.dag.nodeAt index hIndex) :=
  cert.dag.topologicalInduction cert.contract.parents_before hStep
theorem rootByTopologicalInduction
    {P : ∀ index, index < cert.dag.nodes.size → Node σ → Prop} (hStep :
      ∀ index (hIndex : index < cert.dag.nodes.size), (∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex) (cert.dag.nodeAt parent
                (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) →
          P index hIndex (cert.dag.nodeAt index hIndex)) :
    P cert.dag.root cert.contract.root_exists (cert.dag.nodeAt cert.dag.root cert.contract.root_exists) :=
  cert.dag.rootByTopologicalInduction cert.contract.root_exists cert.contract.parents_before hStep
theorem guardedSoundnessSupportedTopologicalStep (hSupported : cert.dag.guardedSoundnessSupported = true) (hParents :
      ∀ parent (hParent : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList),
        Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt parent
            (Nat.lt_trans (cert.contract.parents_before index hIndex parent hParent) hIndex))) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt index hIndex) := by
  have hNodeSupported := (cert.contract.node_contract index hIndex).guarded_soundness_supported hSupported
  cases hPayload : (cert.dag.nodeAt index hIndex).payload with
  | source initialIndex =>
      intro M env hProblem hGuards
      exact (cert.sourceGuardedTopologicalStep valuation index hIndex hParents
        initialIndex hPayload) (env := env) hProblem hGuards
  | avatarSplit payload =>
      simp [hPayload, Payload.guardedSoundnessSupported] at hNodeSupported
  | avatarComponent payload =>
      simp [hPayload, Payload.guardedSoundnessSupported] at hNodeSupported
  | localRule payload =>
      intro M env hProblem hGuards
      exact (cert.localGuardedTopologicalStep_of_topologicalStep valuation
        index hIndex hParents payload hPayload fun hOrdinaryParents =>
          cert.localRuleTopologicalStep index hIndex hOrdinaryParents payload hPayload) (env := env) hProblem hGuards
  | theoryConflict payload =>
      intro M env hProblem hGuards
      exact (cert.theoryConflictGuardedTopologicalStep valuation index hIndex hParents
        payload hPayload) (env := env) hProblem hGuards
  | propositionalLearnedClause payload =>
      intro M env hProblem hGuards
      exact (cert.propositionalLearnedClauseGuardedTopologicalStep valuation
        index hIndex hParents payload hPayload) (env := env) hProblem hGuards
  | residualCdcl payload =>
      have hPayloadSupported : payload.guardedSoundnessSupported = true := by
        simpa [hPayload, Payload.guardedSoundnessSupported] using hNodeSupported
      intro M env hProblem hGuards
      exact (cert.residualCdclGuardedTopologicalStep valuation index hIndex
        hParents payload hPayload hPayloadSupported) (env := env) hProblem hGuards
theorem rootGuardedRefutationInvariant_of_guardedSoundnessSupported (hSupported : cert.dag.guardedSoundnessSupported = true) :
    Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt cert.dag.root cert.contract.root_exists) :=
  cert.rootByTopologicalInduction (P := fun _ _ node =>
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation node) (fun index hIndex hParents =>
      cert.guardedSoundnessSupportedTopologicalStep valuation (index := index) (hIndex := hIndex) hSupported hParents)
theorem rootEmptyContradiction_of_rootGuardedInvariant (hRootInvariant :
      Node.GuardedRefutationInvariant.{x} cert.dag.problem valuation (cert.dag.nodeAt cert.dag.root cert.contract.root_exists))
    {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M) (hProblem : cert.dag.problem.Valid env) : False := by
  have hRootGuards :
      Node.GuardsHold valuation (cert.dag.nodeAt cert.dag.root cert.contract.root_exists).guards :=
    Node.GuardsHold.of_isEmpty (by
      simpa [Node.unguarded] using cert.contract.root_unguarded)
  exact Clause.not_satisfies_of_isEmpty cert.contract.root_conclusion_empty (hRootInvariant env hProblem hRootGuards)
theorem rootEmptyContradiction_of_guardedSoundnessSupported (valuation : PropResolution.Valuation) (hSupported : cert.dag.guardedSoundnessSupported = true)
    {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M) (hProblem : cert.dag.problem.Valid env) : False :=
  cert.rootEmptyContradiction_of_rootGuardedInvariant valuation (cert.rootGuardedRefutationInvariant_of_guardedSoundnessSupported valuation
      hSupported)
    env hProblem
theorem semanticallyEntails_of_guardedSoundnessSupported (problem : DeepProblem σ) (hProblem : cert.dag.problem = ClauseProblem.ofDeepProblem problem)
    (hClosed : DeepProblem.FreeClosed problem) (hSupported : cert.dag.guardedSoundnessSupported = true) :
    SetLevel.SemanticallyEntailsAt.{x} problem.theory problem.target := by
  intro M env hModels
  classical
  let valuation : PropResolution.Valuation := fun _ => False
  by_cases hTarget : Logic.FirstOrder.Formula.satisfies env problem.target
  · exact hTarget
  · have hClauseProblem : cert.dag.problem.Valid env := by
      rw [hProblem]
      exact ClauseProblem.valid_ofDeepProblem_of_freeClosed
        problem env hClosed hModels hTarget
    exact False.elim (cert.rootEmptyContradiction_of_guardedSoundnessSupported
        valuation hSupported env hClauseProblem)
/--
当前 guarded 支持片段也可消费一个显式的 countermodel-to-clause-validity 桥。
这条接口不要求 DAG problem 由公式 problem 直接编译；预处理器可以先扩张模型，再把
canonical 初始字句有效性提供给整图 root contradiction。
-/
theorem semanticallyEntails_of_guardedSoundnessSupported_of_valid (problem : DeepProblem σ) (hSupported : cert.dag.guardedSoundnessSupported = true) (hValid :
      ∀ {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M),
        Logic.FirstOrder.Theory.Models problem.theory env →
          ¬ Logic.FirstOrder.Formula.satisfies env problem.target →
            ∃ (target : SetLevel.StructureAt.{x} σ),
              ∃ (targetEnv : SetLevel.EnvAt.{x} target),
                cert.dag.problem.Valid targetEnv) :
    SetLevel.SemanticallyEntailsAt.{x} problem.theory problem.target := by
  intro M env hModels
  classical
  let valuation : PropResolution.Valuation := fun _ => False
  by_cases hTarget : Logic.FirstOrder.Formula.satisfies env problem.target
  · exact hTarget
  · rcases hValid env hModels hTarget with ⟨target, targetEnv, hClauseProblem⟩
    exact False.elim (cert.rootEmptyContradiction_of_guardedSoundnessSupported
        valuation hSupported targetEnv hClauseProblem)
end CheckedDAGEnvironment
end CheckedDAG
end DAGCertificateSignature
end DAGCertificate
end Automation
end YesMetaZFC
