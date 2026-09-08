import YesMetaZFC.Automation.DAGCertificate.Core
import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.DenseDAG
import YesMetaZFC.Automation.Resolution
namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
open _root_.YesMetaZFC.Automation
section DAGCertificateSignature
variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]
inductive LocalRuleEvidence (σ : Signature) where
  | parentCopy (parent : ParentClause σ)
  | resolution (evidence : ResolutionEvidence σ)
  | factoring (evidence : FactoringEvidence σ)
  | equalityResolution (evidence : EqualityResolutionEvidence σ)
  | rewrite (kind : RewriteKind) (evidence : RewriteEvidence σ)
namespace LocalRuleEvidence
def family : LocalRuleEvidence σ → LocalRuleFamily
  | parentCopy _ => .parentCdcl
  | resolution _ => .parentCdcl
  | factoring _ => .parentCdcl
  | equalityResolution _ => .equality
  | rewrite _ _ => .equality
def parentClauses : LocalRuleEvidence σ → Array (ParentClause σ)
  | parentCopy parent => #[parent]
  | resolution evidence => #[evidence.left, evidence.right]
  | factoring evidence => #[evidence.parent]
  | equalityResolution evidence => #[evidence.parent]
  | rewrite _ evidence => #[evidence.equality, evidence.target]
def soundnessSupported : LocalRuleEvidence σ → Bool
  | _ => true
def parentIdsCheck (parents : Array NodeId) (evidence : LocalRuleEvidence σ) : Bool :=
  evidence.parentClauses.all fun parent => parent.idIn parents
def ruleCheck (conclusion : Clause σ) : LocalRuleEvidence σ → Bool
  | parentCopy parent => parent.clauseEq conclusion
  | resolution evidence => evidence.check conclusion
  | factoring evidence => evidence.check conclusion
  | equalityResolution evidence => evidence.check conclusion
  | rewrite kind evidence => evidence.check kind conclusion
def check (parents : Array NodeId) (conclusion : Clause σ) (evidence : LocalRuleEvidence σ) : Bool :=
  parentIdsCheck parents evidence && ruleCheck conclusion evidence
theorem check_parts
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : LocalRuleEvidence σ} (hCheck : check parents conclusion evidence = true) :
    parentIdsCheck parents evidence = true ∧
      ruleCheck conclusion evidence = true :=
  Bool.and_eq_true_iff.mp hCheck
theorem ruleCheck_of_check
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : LocalRuleEvidence σ} (hCheck : check parents conclusion evidence = true) :
    ruleCheck conclusion evidence = true := (check_parts hCheck).2
theorem parentIdCheck_of_check
    {parents : Array NodeId} {conclusion : Clause σ}
    {evidence : LocalRuleEvidence σ} {parent : ParentClause σ} (hCheck : check parents conclusion evidence = true)
    (hMem : parent ∈ evidence.parentClauses.toList) :
    parent.idIn parents = true := by
  have hIds := (check_parts hCheck).1
  change evidence.parentClauses.all (fun parent => parent.idIn parents) = true at hIds
  exact array_check_of_mem hIds hMem
theorem parentCopy_check_sound
    {conclusion : Clause σ} {parent : ParentClause σ} (hCheck : ruleCheck conclusion (.parentCopy parent) = true) :
    conclusion = parent.clause := by
  have hClause' : parent.clause.eq conclusion = true := by
    simpa [ruleCheck, ParentClause.clauseEq] using hCheck
  exact (Clause.eq_sound parent.clause conclusion hClause').symm
end LocalRuleEvidence
structure LocalRulePayload (σ : Signature) where
  family : LocalRuleFamily
  evidence : LocalRuleEvidence σ
  note : String := ""
namespace LocalRulePayload
def ruleTags  (payload : LocalRulePayload σ) : Array Certificate.RuleTag :=
  payload.family.ruleTags
def parentClauses  (payload : LocalRulePayload σ) : Array (ParentClause σ) :=
  payload.evidence.parentClauses
def soundnessSupported  (payload : LocalRulePayload σ) : Bool :=
  payload.evidence.soundnessSupported
/--
当前已经完成 guarded soundness 的本地规则 payload 片段。
所有 substitution 规则都通过环境搬运消费父节点的 guarded 不变量。
-/
def guardedSoundnessSupported  (payload : LocalRulePayload σ) : Bool :=
  payload.soundnessSupported
def check (parents : Array NodeId) (payload : LocalRulePayload σ) (conclusion : Clause σ) : Bool :=
  !parents.isEmpty &&
    payload.evidence.check parents conclusion &&
      decide (payload.evidence.family = payload.family)
def summary  (payload : LocalRulePayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"local({payload.family.label}){note}"
end LocalRulePayload
/-! ## Propositional closure evidence -/
structure PropLiteralLink (σ : Signature) where
  prop : PropResolution.Lit
  object : Literal σ
namespace PropLiteralLink
def outsideAtomMap  (atomMap : Array (Formula σ)) (lit : PropResolution.Lit) : Bool :=
  match atomMap[lit.var]? with
  | some _ => false
  | none => true
def check (atomMap : Array (Formula σ)) (link : PropLiteralLink σ) : Bool :=
  link.prop.positive == link.object.polarity &&
    match atomMap[link.prop.var]? with
    | some atom => StructuralEq.formula atom link.object.atom
    | none => false
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem outsideAtomMap_neg  {atomMap : Array (Formula σ)}
    {lit : PropResolution.Lit} (hOutside : outsideAtomMap atomMap lit = true) :
    outsideAtomMap atomMap lit.neg = true := by
  cases lit
  simpa [outsideAtomMap, PropResolution.Lit.neg] using hOutside
end PropLiteralLink
structure PropParentClauseLink (σ : Signature) where
  parent : ParentClause σ
  literalLinks : Array (PropLiteralLink σ)
namespace PropParentClauseLink
def encodedClause  (link : PropParentClauseLink σ) : PropResolution.Clause :=
  PropResolution.canonicalClause (link.literalLinks.map fun literal => literal.prop)
def objectClause  (link : PropParentClauseLink σ) : Clause σ :=
  { literals := link.literalLinks.map fun literal => literal.object }
def check (parents : Array NodeId) (atomMap : Array (Formula σ)) (initial : PropResolution.InitialClause) (link : PropParentClauseLink σ) : Bool :=
  link.parent.idIn parents &&
    link.parent.clause.eq link.objectClause &&
      PropResolution.clauseEq initial.clause link.encodedClause &&
        link.literalLinks.all fun literal => literal.check atomMap
end PropParentClauseLink
structure PropGuardActivationLink (σ : Signature) where
  parent : ParentClause σ
  guards : GuardSet
  literalLinks : Array (PropLiteralLink σ)
namespace PropGuardActivationLink
def encodedClause  (link : PropGuardActivationLink σ) :
    PropResolution.Clause :=
  PropResolution.canonicalClause (link.guards.map PropResolution.Lit.neg ++
      link.literalLinks.map fun literal => literal.prop)
def objectClause  (link : PropGuardActivationLink σ) : Clause σ :=
  { literals := link.literalLinks.map fun literal => literal.object }
def check (parents : Array NodeId) (atomMap : Array (Formula σ)) (initial : PropResolution.InitialClause) (link : PropGuardActivationLink σ) : Bool :=
  link.parent.idIn parents &&
    link.parent.clause.eq link.objectClause &&
      PropResolution.clauseEq initial.clause link.encodedClause &&
        link.guards.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
          link.literalLinks.all fun literal => literal.check atomMap
end PropGuardActivationLink
structure PropLearnedClauseLink where
  parent : NodeId
  clause : PropResolution.Clause
namespace PropLearnedClauseLink
def check  (parents : Array NodeId) (atomMap : Array (Formula σ)) (initial : PropResolution.InitialClause) (link : PropLearnedClauseLink) : Bool :=
  parents.contains link.parent &&
    link.clause.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
      PropResolution.clauseEq initial.clause link.clause
end PropLearnedClauseLink
structure PropAvatarSkeletonLink where
  parent : NodeId
  skeleton : PropResolution.Clause
namespace PropAvatarSkeletonLink
/--
AVATAR skeleton 链接的局部可计算检查。
split payload 与 skeleton 的对应关系由 DAG 级 checker 复核；这里检查父边、initial 槽位
以及 selector 变量不与对象 atom map 碰撞。
-/
def check  (parents : Array NodeId) (atomMap : Array (Formula σ)) (initial : PropResolution.InitialClause) (link : PropAvatarSkeletonLink) : Bool :=
  parents.contains link.parent &&
    link.skeleton.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
      PropResolution.clauseEq initial.clause link.skeleton
end PropAvatarSkeletonLink
inductive PropInitialJustification (σ : Signature) where
  | parentClause (link : PropParentClauseLink σ)
  | guardActivationClause (link : PropGuardActivationLink σ)
  | propLearnedClause (link : PropLearnedClauseLink)
  | avatarSkeleton (link : PropAvatarSkeletonLink)
structure PropositionalJustificationKeys where
  parents : List NodeId := []
  clauses : List PropResolution.Clause := []
  deriving Repr, Inhabited, Lean.ToExpr
namespace PropInitialJustification
def parentClause? : PropInitialJustification σ → Option (ParentClause σ)
  | parentClause link => some link.parent
  | guardActivationClause link => some link.parent
  | propLearnedClause _ => none
  | avatarSkeleton _ => none
def check (parents : Array NodeId) (atomMap : Array (Formula σ)) (initial : PropResolution.InitialClause) :
    PropInitialJustification σ → Bool
  | parentClause link =>
      link.check parents atomMap initial
  | guardActivationClause link =>
      link.check parents atomMap initial
  | propLearnedClause link =>
      link.check parents atomMap initial
  | avatarSkeleton link =>
      link.check parents atomMap initial
def keyData? : PropInitialJustification σ → Option (NodeId × PropResolution.Clause)
  | parentClause _ => none
  | guardActivationClause _ => none
  | propLearnedClause link => some (link.parent, link.clause)
  | avatarSkeleton link => some (link.parent, link.skeleton)
theorem check_eq_of_keyData
    {parents : Array NodeId} {atomMap : Array (Formula σ)}
    {initial : PropResolution.InitialClause}
    {justification : PropInitialJustification σ}
    {parent : NodeId} {clause : PropResolution.Clause} (hKey : keyData? justification = some (parent, clause)) :
    justification.check parents atomMap initial = (parents.contains parent &&
        clause.all (fun literal => PropLiteralLink.outsideAtomMap atomMap literal) &&
          PropResolution.clauseEq initial.clause clause) := by
  cases justification with
  | parentClause _ =>
      simp [keyData?] at hKey
  | guardActivationClause _ =>
      simp [keyData?] at hKey
  | propLearnedClause link =>
      rcases hKey with ⟨rfl, rfl⟩
      rfl
  | avatarSkeleton link =>
      rcases hKey with ⟨rfl, rfl⟩
      rfl
def guardedSoundnessSupported : PropInitialJustification σ → Bool
  | parentClause _ => true
  | guardActivationClause _ => true
  | propLearnedClause _ => true
  | avatarSkeleton _ => false
end PropInitialJustification
namespace PropositionalJustificationKeys
def ofJustifications? :
    List (PropInitialJustification σ) → Option PropositionalJustificationKeys
  | [] => some {}
  | justification :: rest => do
      let keys ← ofJustifications? rest
      match justification with
      | .propLearnedClause link =>
          some {
            parents := link.parent :: keys.parents
            clauses := link.clause :: keys.clauses
          }
      | .avatarSkeleton link =>
          some {
            parents := link.parent :: keys.parents
            clauses := link.skeleton :: keys.clauses
          }
      | _ =>
          none
def parentsCheck (parents : Array NodeId) (keys : PropositionalJustificationKeys) : Bool :=
  keys.parents.all parents.contains
def outsideAtomMapCheck  (atomMap : Array (Formula σ)) (keys : PropositionalJustificationKeys) : Bool :=
  keys.clauses.all fun clause =>
    clause.all fun literal => PropLiteralLink.outsideAtomMap atomMap literal
def check  (parents : Array NodeId) (atomMap : Array (Formula σ)) (initialClauses : Array PropResolution.InitialClause)
    (keys : PropositionalJustificationKeys) : Bool :=
  keys.parentsCheck parents &&
    keys.outsideAtomMapCheck atomMap &&
      decide ((PropResolution.initialClauseDatabase initialClauses).toList = keys.clauses)
theorem parentsCheck_eq_true_of_eq (parents : Array NodeId) (keys : PropositionalJustificationKeys) (hParents : keys.parents = parents.toList) :
    keys.parentsCheck parents = true := by
  apply List.all_eq_true.mpr
  intro parent hParent
  rw [hParents] at hParent
  exact Array.contains_eq_true_of_mem (Array.mem_def.mpr hParent)
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem cons_keyData_of_some
    {justification : PropInitialJustification σ}
    {rest : List (PropInitialJustification σ)}
    {keys tailKeys : PropositionalJustificationKeys} (hRest : ofJustifications? rest = some tailKeys)
    (hKeys : ofJustifications? (justification :: rest) = some keys) :
    ∃ parent clause,
      PropInitialJustification.keyData? justification = some (parent, clause) ∧
        keys.parents = parent :: tailKeys.parents ∧
          keys.clauses = clause :: tailKeys.clauses := by
  cases justification with
  | parentClause link =>
      simp [ofJustifications?, hRest] at hKeys
  | guardActivationClause link =>
      simp [ofJustifications?, hRest] at hKeys
  | propLearnedClause link =>
      simp [ofJustifications?, hRest] at hKeys
      subst keys
      exact ⟨link.parent, link.clause, rfl, rfl, rfl⟩
  | avatarSkeleton link =>
      simp [ofJustifications?, hRest] at hKeys
      subst keys
      exact ⟨link.parent, link.skeleton, rfl, rfl, rfl⟩
end PropositionalJustificationKeys
structure PropositionalClosurePayload (σ : Signature) where
  atomMap : Array (Formula σ) := #[]
  initialClauses : Array PropResolution.InitialClause
  initialJustifications : Array (PropInitialJustification σ) := #[]
  proof : PropResolution.CdclProof
  stats : Certificate.Stats := {}
  note : String := ""
namespace PropositionalClosurePayload
def computedStats  (payload : PropositionalClosurePayload σ) : Certificate.Stats :=
  {
    steps := payload.proof.journal.steps.size
    clauses := payload.initialClauses.size + payload.proof.journal.learns.size
    generated := payload.proof.journal.learns.size
    retained := payload.initialClauses.size + payload.proof.journal.learns.size
    verified := payload.proof.journal.learns.size
    residuals := 0
    fuel := payload.stats.fuel
  }
def parentClauses  (payload : PropositionalClosurePayload σ) :
    Array (ParentClause σ) :=
  payload.initialJustifications.filterMap PropInitialJustification.parentClause?
def justificationsListCheck (parents : Array NodeId) (atomMap : Array (Formula σ)) :
    List PropResolution.InitialClause → List (PropInitialJustification σ) → Bool
  | [], [] => true
  | initial :: initials, justification :: justifications =>
      justification.check parents atomMap initial &&
        justificationsListCheck parents atomMap initials justifications
  | _, _ => false
theorem justificationsListCheck_at (parents : Array NodeId) (atomMap : Array (Formula σ)) :
    ∀ {initials : List PropResolution.InitialClause}
      {justifications : List (PropInitialJustification σ)},
      justificationsListCheck parents atomMap initials justifications = true →
      ∀ slot (hInitial : slot < initials.length) (hJustification : slot < justifications.length),
        justifications[slot].check parents atomMap initials[slot] = true
  | [], _, hCheck, slot, hInitial, _ => by
      cases hInitial
  | _ :: _, [], hCheck, slot, _hInitial, _hJustification => by
      simp [justificationsListCheck] at hCheck
  | initial :: initials, justification :: justifications, hCheck,
      0, _hInitial, _hJustification => by
      exact (Bool.and_eq_true_iff.mp hCheck).1
  | initial :: initials, justification :: justifications, hCheck,
      slot + 1, hInitial, hJustification => by
      exact justificationsListCheck_at parents atomMap (Bool.and_eq_true_iff.mp hCheck).2 slot (Nat.lt_of_succ_lt_succ hInitial)
        (Nat.lt_of_succ_lt_succ hJustification)
theorem justificationsListCheck_eq_true_of_propositionalKeys (parents : Array NodeId) (atomMap : Array (Formula σ)) :
    ∀ {initials : List PropResolution.InitialClause}
      {justifications : List (PropInitialJustification σ)}
      {keys : PropositionalJustificationKeys},
      PropositionalJustificationKeys.ofJustifications? justifications = some keys →
      initials.map (fun initial => initial.clause) = keys.clauses →
      keys.parentsCheck parents = true →
      keys.outsideAtomMapCheck atomMap = true →
      justificationsListCheck parents atomMap initials justifications = true
  | [], [], keys, hKeys, _hClauses, _hParents, _hOutside => by
      simp [PropositionalJustificationKeys.ofJustifications?] at hKeys
      subst keys
      rfl
  | _ :: _, [], keys, hKeys, hClauses, _hParents, _hOutside => by
      simp [PropositionalJustificationKeys.ofJustifications?] at hKeys
      subst keys
      simp at hClauses
  | [], justification :: justifications, keys, hKeys, hClauses, _hParents, _hOutside => by
      cases hRest :
          PropositionalJustificationKeys.ofJustifications? justifications with
      | none =>
          simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
      | some tailKeys =>
          cases justification with
          | parentClause link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
          | guardActivationClause link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
          | propLearnedClause link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
              subst keys
              simp at hClauses
          | avatarSkeleton link =>
              simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
              subst keys
              simp at hClauses
  | initial :: initials, justification :: justifications, keys,
      hKeys, hClauses, hParents, hOutside => by
      cases hRest :
          PropositionalJustificationKeys.ofJustifications? justifications with
      | none =>
          simp [PropositionalJustificationKeys.ofJustifications?, hRest] at hKeys
      | some tailKeys =>
          rcases PropositionalJustificationKeys.cons_keyData_of_some hRest hKeys with
            ⟨parent, clause, hKey, hKeysParents, hKeysClauses⟩
          have hClauseParts :
              initial.clause = clause ∧
                initials.map (fun item => item.clause) = tailKeys.clauses := by
            simpa [hKeysClauses] using hClauses
          have hParentParts :
              parents.contains parent = true ∧
                tailKeys.parentsCheck parents = true := by
            simpa [PropositionalJustificationKeys.parentsCheck, hKeysParents] using hParents
          have hOutsideParts : (clause.all fun literal =>
                PropLiteralLink.outsideAtomMap atomMap literal) = true ∧
                tailKeys.outsideAtomMapCheck atomMap = true := by
            simpa [PropositionalJustificationKeys.outsideAtomMapCheck, hKeysClauses] using hOutside
          have hHeadCheck :
              justification.check parents atomMap initial = true := by
            rw [PropInitialJustification.check_eq_of_keyData hKey]
            exact Bool.and_eq_true_iff.mpr
              ⟨Bool.and_eq_true_iff.mpr
                  ⟨hParentParts.1, hOutsideParts.1⟩,
                PropResolution.clauseEq_eq.mpr hClauseParts.1⟩
          have hTail :=
            justificationsListCheck_eq_true_of_propositionalKeys
              parents atomMap hRest hClauseParts.2
                hParentParts.2 hOutsideParts.2
          simp [justificationsListCheck, hHeadCheck, hTail]
def justificationsCheck (parents : Array NodeId) (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialClauses.size == payload.initialJustifications.size &&
    match
      PropositionalJustificationKeys.ofJustifications?
        payload.initialJustifications.toList
    with
    | some keys =>
        keys.check parents payload.atomMap payload.initialClauses
    | none =>
        justificationsListCheck parents payload.atomMap
          payload.initialClauses.toList payload.initialJustifications.toList
theorem justificationsListCheck_eq_true_of_check
    {parents : Array NodeId} {payload : PropositionalClosurePayload σ} (hCheck : payload.justificationsCheck parents = true) :
    justificationsListCheck parents payload.atomMap
      payload.initialClauses.toList payload.initialJustifications.toList = true := by
  unfold justificationsCheck at hCheck
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨_hSize, hBody⟩
  cases hKeys :
      PropositionalJustificationKeys.ofJustifications?
        payload.initialJustifications.toList with
  | none =>
      simpa [hKeys] using hBody
  | some keys =>
      have hFields : (keys.parentsCheck parents = true ∧
            keys.outsideAtomMapCheck payload.atomMap = true) ∧ (PropResolution.initialClauseDatabase payload.initialClauses).toList =
                keys.clauses := by
        simpa [hKeys, PropositionalJustificationKeys.check] using hBody
      have hClauses :
          payload.initialClauses.toList.map (fun initial => initial.clause) =
            keys.clauses := by
        simpa [PropResolution.initialClauseDatabase, Array.toList_map] using hFields.2
      exact justificationsListCheck_eq_true_of_propositionalKeys
        parents payload.atomMap hKeys hClauses hFields.1.1 hFields.1.2
theorem justificationsCheck_eq_true_of_propositionalKeys (parents : Array NodeId) (payload : PropositionalClosurePayload σ)
    (keys : PropositionalJustificationKeys) (hSize : (payload.initialClauses.size == payload.initialJustifications.size) = true) (hKeys :
      PropositionalJustificationKeys.ofJustifications?
        payload.initialJustifications.toList = some keys) (hClauses : (PropResolution.initialClauseDatabase payload.initialClauses).toList =
        keys.clauses) (hParents : keys.parentsCheck parents = true) (hOutside : keys.outsideAtomMapCheck payload.atomMap = true) :
    payload.justificationsCheck parents = true := by
  simp [justificationsCheck, hSize, hKeys,
    PropositionalJustificationKeys.check, hClauses, hParents, hOutside]
def check (parents : Array NodeId) (payload : PropositionalClosurePayload σ) : Bool :=
  PropResolution.checkedUnsat payload.initialClauses payload.proof &&
    payload.justificationsCheck parents &&
    payload.stats.steps == payload.computedStats.steps &&
    payload.stats.clauses == payload.computedStats.clauses &&
    payload.stats.generated == payload.computedStats.generated &&
    payload.stats.retained == payload.computedStats.retained &&
    payload.stats.verified == payload.computedStats.verified
theorem check_eq_true_of_components (parents : Array NodeId) (payload : PropositionalClosurePayload σ) (hUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof = true) (hJustifications : payload.justificationsCheck parents = true)
    (hSteps : (payload.stats.steps == payload.computedStats.steps) = true) (hClauses : (payload.stats.clauses == payload.computedStats.clauses) = true)
    (hGenerated : (payload.stats.generated == payload.computedStats.generated) = true)
    (hRetained : (payload.stats.retained == payload.computedStats.retained) = true)
    (hVerified : (payload.stats.verified == payload.computedStats.verified) = true) :
    payload.check parents = true := by
  simp [check, hUnsat, hJustifications, hSteps, hClauses, hGenerated,
    hRetained, hVerified]
def guardedSoundnessSupported (payload : PropositionalClosurePayload σ) : Bool :=
  payload.initialJustifications.all PropInitialJustification.guardedSoundnessSupported
def ofRaw  (initialClauses : Array PropResolution.InitialClause) (proof : PropResolution.CdclProof) (atomMap : Array (Formula σ) := #[])
    (initialJustifications : Array (PropInitialJustification σ) := #[]) (fuel : Nat := 0) (note : String := "") : PropositionalClosurePayload σ :=
  let payload : PropositionalClosurePayload σ := {
    atomMap := atomMap
    initialClauses := initialClauses
    initialJustifications := initialJustifications
    proof := proof
    stats := { fuel := fuel }
    note := note
  }
  { payload with stats := payload.computedStats }
def ofCheckedUnsat  (cert : PropResolution.CheckedUnsatCertificate) (atomMap : Array (Formula σ) := #[])
    (initialJustifications : Array (PropInitialJustification σ) := #[]) (fuel : Nat := 0) (note : String := "") : PropositionalClosurePayload σ :=
  ofRaw cert.initialClauses cert.proof atomMap initialJustifications fuel note
def summary  (payload : PropositionalClosurePayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"prop-closure(initial={payload.initialClauses.size}; " ++
    s!"learns={payload.proof.journal.learns.size}; " ++
      s!"steps={payload.proof.journal.steps.size}){note}"
end PropositionalClosurePayload
/--
AVATAR source split descriptor。
该节点仍然复述原 source 字句，只把完整 literal partition 与 selector 表登记为后续
component 节点和命题 skeleton 的唯一可信来源。
-/
structure AvatarSplitPayload (σ : Signature) where
  source : ParentClause σ
  partitions : Array (Array Nat)
  selectors : PropResolution.Clause
  note : String := ""
namespace AvatarSplitPayload
def parentClauses  (payload : AvatarSplitPayload σ) :
    Array (ParentClause σ) :=
  #[payload.source]
/--
split 节点的局部可信合同只描述 DAG 拓扑与 source 复述。

partition 覆盖、component 支持不交、selector 正性及跨 split 一致性均由
`avatarRegistryCheckWith` 统一复算；索引精确分区与 selector 互异则是材料化层的
表示规范审计，不参与语义 soundness，故不在每个节点的核心回放中重复计算。
-/
def check (parents : Array NodeId) (payload : AvatarSplitPayload σ) (conclusion : Clause σ) : Bool :=
  parents.size == 1 &&
    payload.source.idIn parents &&
      payload.source.clause.eq conclusion
def summary  (payload : AvatarSplitPayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"avatarSplit(source={payload.source.id}; components={payload.partitions.size}){note}"
end AvatarSplitPayload
/--
AVATAR component 节点。
具体 component 字句与 singleton selector 都从父 split descriptor 复算，不在 payload
中重复保存。父 split 也只保存节点编号，避免每个 component 重复整份 split 字句。
-/
structure AvatarComponentPayload (σ : Signature) where
  split : NodeId
  componentIndex : Nat
  note : String := ""
namespace AvatarComponentPayload
def parentClauses  (_payload : AvatarComponentPayload σ) :
    Array (ParentClause σ) :=
  #[]
def check  (parents : Array NodeId) (payload : AvatarComponentPayload σ) : Bool :=
  parents.size == 1 && parents.contains payload.split
def summary  (payload : AvatarComponentPayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"avatarComponent(split={payload.split}; index={payload.componentIndex}){note}"
end AvatarComponentPayload
structure TheoryConflictPayload (σ : Signature) where
  conflict : ParentClause σ
  note : String := ""
namespace TheoryConflictPayload
def parentClauses  (payload : TheoryConflictPayload σ) :
    Array (ParentClause σ) :=
  #[payload.conflict]
def check  (parents : Array NodeId) (payload : TheoryConflictPayload σ) (conclusion : Clause σ) : Bool :=
  payload.conflict.idIn parents &&
    payload.conflict.clause.isEmpty &&
      conclusion.isEmpty
def summary  (payload : TheoryConflictPayload σ) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"theoryConflict(parent={payload.conflict.id}){note}"
end TheoryConflictPayload
structure PropositionalLearnedClausePayload where
  conflict : NodeId
  learned : PropResolution.Clause
  note : String := ""
namespace PropositionalLearnedClausePayload
def check  (parents : Array NodeId) (payload : PropositionalLearnedClausePayload) (conclusion : Clause σ) : Bool :=
  parents.contains payload.conflict &&
    conclusion.isEmpty
def summary (payload : PropositionalLearnedClausePayload) : String :=
  let note := if payload.note.isEmpty then "" else s!"; note={payload.note}"
  s!"propLearned(conflict={payload.conflict}; lits={payload.learned.size}){note}"
end PropositionalLearnedClausePayload
inductive Payload (σ : Signature) where
  | source (initialIndex : Nat)
  | avatarSplit (payload : AvatarSplitPayload σ)
  | avatarComponent (payload : AvatarComponentPayload σ)
  | localRule (payload : LocalRulePayload σ)
  | theoryConflict (payload : TheoryConflictPayload σ)
  | propositionalLearnedClause (payload : PropositionalLearnedClausePayload)
  | residualCdcl (payload : PropositionalClosurePayload σ)
namespace Payload
def ruleTags : Payload σ → Array Certificate.RuleTag
  | source _ => #[.sourceOrigin, .sourceFact]
  | avatarSplit _ => #[.sourceOrigin, .dagTopology]
  | avatarComponent _ => #[.sourceFact, .dagTopology]
  | localRule payload => payload.ruleTags
  | theoryConflict _ => #[.theoryConflict, .dagTopology]
  | propositionalLearnedClause _ => #[.propositionalLearnedClause, .parentCdclSkeleton]
  | residualCdcl _ => #[.residualCdcl, .parentCdclSkeleton]
def backend : Payload σ → Certificate.Backend
  | source _ => .sourceReplay
  | avatarSplit _ => .dagReflection
  | avatarComponent _ => .dagReflection
  | localRule _ => .superposition
  | theoryConflict _ => .dagReflection
  | propositionalLearnedClause _ => .propositionalCdcl
  | residualCdcl _ => .residualCdcl
def phase : Payload σ → Certificate.Phase
  | source _ => .sourceMaterialization
  | avatarSplit _ => .sourceMaterialization
  | avatarComponent _ => .sourceMaterialization
  | localRule _ => .saturation
  | theoryConflict _ => .dagCheck
  | propositionalLearnedClause _ => .residualSplit
  | residualCdcl _ => .residualSplit
def closureKind? : Payload σ → Option Certificate.ClosureKind
  | residualCdcl _ => some .residualCdcl
  | _ => none
def rootClosureEligible : Payload σ → Bool
  | propositionalLearnedClause _ => false
  | _ => true
def parentClauses : Payload σ → Array (ParentClause σ)
  | source _ => #[]
  | avatarSplit payload => payload.parentClauses
  | avatarComponent payload => payload.parentClauses
  | localRule payload => payload.parentClauses
  | theoryConflict payload => payload.parentClauses
  | propositionalLearnedClause _ => #[]
  | residualCdcl payload => payload.parentClauses
def check (problem : ClauseProblem σ) (parents : Array NodeId) (conclusion : Clause σ) : Payload σ → Bool
  | source initialIndex =>
      parents.isEmpty &&
        match problem.initialClauses[initialIndex]? with
        | some initial => conclusion.eq initial
        | none => false
  | avatarSplit payload =>
      payload.check parents conclusion
  | avatarComponent payload =>
      payload.check parents
  | localRule payload =>
      payload.check parents conclusion
  | theoryConflict payload =>
      payload.check parents conclusion
  | propositionalLearnedClause payload =>
      payload.check parents conclusion
  | residualCdcl payload =>
      !parents.isEmpty && conclusion.isEmpty && payload.check parents
theorem residualCdcl_check_eq_true_of_components (problem : ClauseProblem σ) (parents : Array NodeId) (conclusion : Clause σ)
    (payload : PropositionalClosurePayload σ) (hParents : (!parents.isEmpty) = true) (hConclusion : conclusion.isEmpty = true)
    (hPayload : payload.check parents = true) :
    check problem parents conclusion (.residualCdcl payload) = true := by
  simp [check, hParents, hConclusion, hPayload]
/--
当前已经完成 guarded soundness 的 payload 片段。
命题 learned-clause 节点只作为 guarded proof artifact 使用：它继承 theory-conflict
的 guard，并不允许作为无条件对象层空字句。residual CDCL 也只先进入 guarded 总定理。
-/
def guardedSoundnessSupported : Payload σ → Bool
  | source _ => true
  | avatarSplit _ => false
  | avatarComponent _ => false
  | localRule payload => payload.guardedSoundnessSupported
  | theoryConflict _ => true
  | propositionalLearnedClause _ => true
  | residualCdcl payload => payload.guardedSoundnessSupported
def summary : Payload σ → String
  | source initialIndex => s!"source(initial[{initialIndex}])"
  | avatarSplit payload => payload.summary
  | avatarComponent payload => payload.summary
  | localRule payload => payload.summary
  | theoryConflict payload => payload.summary
  | propositionalLearnedClause payload => payload.summary
  | residualCdcl payload => s!"residualCdcl; {payload.summary}"
end Payload
/-! ## DAG nodes -/
structure Node (σ : Signature) where
  id : NodeId
  parents : Array NodeId := #[]
  ruleTags : Array Certificate.RuleTag := #[]
  guards : GuardSet := #[]
  conclusion : Clause σ
  payload : Payload σ
namespace Node
def guardedConclusion (node : Node σ) : GuardedClause σ :=
  { guards := node.guards, clause := node.conclusion }
def unguarded (node : Node σ) : Bool :=
  node.guards.isEmpty
def globallyClosed (node : Node σ) : Bool :=
  node.guardedConclusion.globallyEmpty
def theoryConflict (node : Node σ) : Bool :=
  node.guardedConclusion.theoryConflict
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem theoryConflict_fields {node : Node σ} (hConflict : node.theoryConflict = true) :
    node.unguarded = false ∧ node.conclusion.isEmpty = true := by
  simpa [theoryConflict, GuardedClause.theoryConflict,
    Guards.GuardedClause.theoryConflict, guardedConclusion,
    GuardedClause.unguarded, Guards.GuardedClause.unguarded, unguarded]
    using hConflict
def ruleTagsOk (node : Node σ) : Bool :=
  node.ruleTags == node.payload.ruleTags
def guardedSoundnessSupported (node : Node σ) : Bool :=
  node.payload.guardedSoundnessSupported
def check (problem : ClauseProblem σ) (node : Node σ) : Bool :=
  node.ruleTagsOk && node.payload.check problem node.parents node.conclusion
theorem check_eq_true_of_components (problem : ClauseProblem σ) (node : Node σ) (hRuleTags : node.ruleTagsOk = true)
    (hPayload : node.payload.check problem node.parents node.conclusion = true) :
    node.check problem = true :=
  Bool.and_eq_true_iff.mpr ⟨hRuleTags, hPayload⟩
theorem fields_of_check_eq_true
    {problem : ClauseProblem σ} {node : Node σ} (hCheck : node.check problem = true) :
    node.ruleTagsOk = true ∧
      node.payload.check problem node.parents node.conclusion = true := by
  simpa [check] using hCheck
def summary (node : Node σ) : String :=
  s!"#{node.id}; parents={node.parents.size}; guards={node.guards.size}; " ++
    s!"lits={node.conclusion.literals.size}; " ++ node.payload.summary
def toPublicNode (node : Node σ) : Certificate.Node :=
  {
    id := node.id
    backend := node.payload.backend
    phase := node.payload.phase
    label := node.summary
    ruleTags := node.ruleTags
    closureKind? :=
      match node.payload.closureKind? with
      | some kind => some kind
      | none => if node.globallyClosed then some .dagReflection else none
    stats := {
      steps := 1
      clauses := 1
      literals := node.conclusion.literals.size
      verified := 0
      residuals :=
        match node.payload with
        | .residualCdcl _ => 1
        | _ => 0
    }
    dependencies := node.parents
  }
end Node
/-! ## Whole certificate -/
structure DAG (σ : Signature) where
  problem : ClauseProblem σ
  root : NodeId
  nodes : Array (Node σ)
namespace DAG
def graphView (dag : DAG σ) : DenseDAG.View (Node σ) where
  nodes := dag.nodes
  root := dag.root
  node_id := Node.id
  node_parents := Node.parents
def node? (dag : DAG σ) (id : NodeId) : Option (Node σ) :=
  dag.graphView.node? id
def nodeAt (dag : DAG σ) (index : Nat) (hIndex : index < dag.nodes.size) : Node σ :=
  dag.graphView.nodeAt index hIndex
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
@[simp]
theorem node?_eq_some_nodeAt (dag : DAG σ) {index : Nat} (hIndex : index < dag.nodes.size) :
    dag.node? index = some (dag.nodeAt index hIndex) := by
  simpa [node?, nodeAt, graphView] using
    DenseDAG.View.node?_eq_some_nodeAt dag.graphView hIndex
def parentSnapshotChecked (dag : DAG σ) (parent : ParentClause σ) : Bool :=
  match dag.node? parent.id with
  | some node => node.conclusion.eq parent.clause
  | none => false
theorem parentSnapshotChecked_sound
    {dag : DAG σ} {parent : ParentClause σ} (hChecked : dag.parentSnapshotChecked parent = true) :
    ∃ node, dag.node? parent.id = some node ∧ node.conclusion = parent.clause := by
  unfold parentSnapshotChecked at hChecked
  cases hNode : dag.node? parent.id with
  | none =>
      simp [hNode] at hChecked
  | some node =>
      have hClause : node.conclusion.eq parent.clause = true := by
        simpa [hNode] using hChecked
      exact ⟨node, rfl, Clause.eq_sound node.conclusion parent.clause hClause⟩
def nodeParentSnapshotsChecked (dag : DAG σ) (node : Node σ) : Bool :=
  node.payload.parentClauses.all fun parent => dag.parentSnapshotChecked parent
def parentSnapshotsChecked (dag : DAG σ) : Bool :=
  dag.nodes.all dag.nodeParentSnapshotsChecked
def parentSnapshotsListChecked (dag : DAG σ) : Bool :=
  dag.nodes.toList.all dag.nodeParentSnapshotsChecked
def parentGuards? (dag : DAG σ) (id : NodeId) : Option GuardSet := do
  let node ← dag.node? id
  some node.guards
def parentGuardUnionList? (dag : DAG σ) :
    List NodeId → Option GuardSet :=
  Guards.mergeList? dag.parentGuards?
/--
计算一组父节点 guard 的规范并集。
这是 guarded local step 的可信边界：搜索器可以随意调度 guard，但证书 checker 必须
重新计算结论 guard 是否恰好等于所有父节点 guard 的并集。
-/
def parentGuardUnion? (dag : DAG σ) (parents : Array NodeId) :
    Option GuardSet :=
  dag.parentGuardUnionList? parents.toList
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem mem_parentGuardUnionList_of_parent_mem {dag : DAG σ}
    {parents : List NodeId} {parent : NodeId} {parentNode : Node σ}
    {guards : GuardSet} {lit : GuardLit} (hUnion : dag.parentGuardUnionList? parents = some guards) (hParentMem : parent ∈ parents)
    (hParentNode : dag.node? parent = some parentNode) (hLit : lit ∈ (Guards.canonical parentNode.guards).toList) :
    lit ∈ (Guards.canonical guards).toList := by
  apply Guards.mem_canonical_mergeList_of_mem hUnion hParentMem ?_ hLit
  simp [parentGuards?, hParentNode]
def propLearnedInitialLinkOk (dag : DAG σ) (parents : Array NodeId) (link : PropLearnedClauseLink) : Bool :=
  parents.contains link.parent &&
    match dag.node? link.parent with
    | some parentNode =>
        match parentNode.payload with
        | .propositionalLearnedClause payload =>
            PropResolution.clauseEq link.clause payload.learned
        | _ => false
    | none => false
def propParentInitialLinkOk (dag : DAG σ) (parents : Array NodeId) (link : PropParentClauseLink σ) : Bool :=
  parents.contains link.parent.id &&
    dag.parentSnapshotChecked link.parent &&
    match dag.node? link.parent.id with
    | some parentNode => parentNode.unguarded
    | none => false
def propGuardActivationInitialLinkOk (dag : DAG σ) (parents : Array NodeId) (link : PropGuardActivationLink σ) : Bool :=
  parents.contains link.parent.id &&
    dag.parentSnapshotChecked link.parent &&
    match dag.node? link.parent.id with
    | some parentNode =>
        !parentNode.unguarded && Guards.eq link.guards parentNode.guards
    | none => false
def propAvatarSkeletonInitialLinkOk (dag : DAG σ) (parents : Array NodeId) (link : PropAvatarSkeletonLink) : Bool :=
  parents.contains link.parent &&
    match dag.node? link.parent with
    | some parentNode =>
        parentNode.unguarded &&
          match parentNode.payload with
          | .avatarSplit payload =>
              PropResolution.clauseEq link.skeleton (PropResolution.canonicalClause payload.selectors)
          | _ => false
    | none => false
def propInitialJustificationDagOk (dag : DAG σ) (parents : Array NodeId) : PropInitialJustification σ → Bool
  | .parentClause link => dag.propParentInitialLinkOk parents link
  | .propLearnedClause link => dag.propLearnedInitialLinkOk parents link
  | .guardActivationClause link => dag.propGuardActivationInitialLinkOk parents link
  | .avatarSkeleton link => dag.propAvatarSkeletonInitialLinkOk parents link
def propInitialLinksOk (dag : DAG σ) (node : Node σ) : Bool :=
  match node.payload with
  | .residualCdcl payload =>
      payload.initialJustifications.all fun justification =>
        dag.propInitialJustificationDagOk node.parents justification
  | _ => true
def avatarSplitNodeOk (dag : DAG σ) (node : Node σ) (payload : AvatarSplitPayload σ) : Bool :=
  node.unguarded &&
    dag.parentSnapshotChecked payload.source &&
      match dag.node? payload.source.id with
      | some sourceNode =>
          sourceNode.unguarded &&
            match sourceNode.payload with
            | .source _ => true
            | _ => false
      | none => false
def avatarComponentNodeOk (dag : DAG σ) (node : Node σ) (payload : AvatarComponentPayload σ) : Bool :=
  match dag.node? payload.split with
  | some splitNode =>
      splitNode.unguarded &&
        match splitNode.payload with
        | .avatarSplit splitPayload =>
            match splitPayload.partitions[payload.componentIndex]?,
                AvatarSplit.selectorAt? splitPayload.selectors payload.componentIndex with
            | some indices, some selector =>
                node.conclusion.eq (Clause.atIndices splitNode.conclusion indices) &&
                  Guards.eq node.guards #[selector]
            | _, _ => false
        | _ => false
  | none => false
def localNodeGuardsOk (dag : DAG σ) (node : Node σ) : Bool :=
  match node.payload with
  | .avatarSplit payload =>
      dag.avatarSplitNodeOk node payload
  | .avatarComponent payload =>
      dag.avatarComponentNodeOk node payload
  | .localRule _ =>
      match dag.parentGuardUnion? node.parents with
      | some guards => Guards.eq node.guards guards
      | none => false
  | .theoryConflict _ =>
      match dag.parentGuardUnion? node.parents with
      | some guards => Guards.eq node.guards guards
      | none => false
  | .propositionalLearnedClause payload =>
      node.conclusion.isEmpty &&
        match dag.node? payload.conflict with
        | some conflictNode =>
          conflictNode.theoryConflict &&
            Guards.eq node.guards conflictNode.guards && (match conflictNode.payload with
              | .theoryConflict _ =>
                  PropResolution.clauseEq payload.learned (Guards.learnedClause conflictNode.guards)
              | _ => false)
        | none => false
  | _ => true
def nodeGuardsChecked (dag : DAG σ) (node : Node σ) : Bool :=
  dag.localNodeGuardsOk node && dag.propInitialLinksOk node
def guardsChecked (dag : DAG σ) : Bool :=
  dag.nodes.all dag.nodeGuardsChecked
def guardsListChecked (dag : DAG σ) : Bool :=
  dag.nodes.toList.all dag.nodeGuardsChecked
theorem guard_fields_of_eq_true
      {dag : DAG σ} (hGuards : dag.guardsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true ∧
        dag.propInitialLinksOk (dag.nodeAt index hIndex) = true := by
  intro index hIndex
  simpa [guardsChecked, nodeGuardsChecked, nodeAt] using! (Array.all_eq_true.mp hGuards index hIndex)
theorem guardsChecked_of_eq_true
      {dag : DAG σ} (hGuards : dag.guardsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true := by
  exact fun index hIndex => (guard_fields_of_eq_true hGuards index hIndex).1
theorem propInitialLinksChecked_of_eq_true
      {dag : DAG σ} (hGuards : dag.guardsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size),
      dag.propInitialLinksOk (dag.nodeAt index hIndex) = true := by
  exact fun index hIndex => (guard_fields_of_eq_true hGuards index hIndex).2
def rootExists (dag : DAG σ) : Bool :=
  dag.graphView.rootExists
def rootClosed (dag : DAG σ) : Bool :=
  match dag.node? dag.root with
  | some node => node.globallyClosed && node.payload.rootClosureEligible
  | none => false
def denseIdChecked (index : Nat) (node : Node σ) : Bool :=
  node.id == index
def denseIds (dag : DAG σ) : Bool :=
  dag.graphView.denseIds

omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem denseIds_eq_true_of_listCheck {dag : DAG σ} {nodes : List (Node σ)}
    (hNodes : dag.nodes.toList = nodes)
    (hChecked : dag.graphView.denseIdsListCheck nodes = true) :
    dag.denseIds = true := by
  exact DenseDAG.View.denseIds_eq_true_of_listCheck hNodes hChecked

omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem denseIds_of_eq_true {dag : DAG σ} (hDense : dag.denseIds = true) :
    ∀ index (hIndex : index < dag.nodes.size), (dag.nodeAt index hIndex).id = index := by
  simpa [denseIds, graphView, nodeAt] using
    DenseDAG.View.denseIds_of_eq_true (view := dag.graphView) hDense
def nodeParentsBefore (index : Nat) (node : Node σ) : Bool :=
  node.parents.toList.all fun parent => decide (parent < index)
def parentsBefore (dag : DAG σ) : Bool :=
  dag.graphView.parentsBefore

omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem parentsBefore_eq_true_of_listCheck {dag : DAG σ} {nodes : List (Node σ)}
    (hNodes : dag.nodes.toList = nodes)
    (hChecked : dag.graphView.parentsBeforeListCheck nodes = true) :
    dag.parentsBefore = true := by
  exact DenseDAG.View.parentsBefore_eq_true_of_listCheck hNodes hChecked

def ParentsBefore (dag : DAG σ) : Prop :=
  dag.graphView.ParentsBefore
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem parentsBefore_of_eq_true {dag : DAG σ} (hParents : dag.parentsBefore = true) : dag.ParentsBefore := by
  simpa [parentsBefore, ParentsBefore, graphView, nodeAt] using
    DenseDAG.View.parentsBefore_of_eq_true (view := dag.graphView) hParents
def payloadsChecked (dag : DAG σ) : Bool :=
  dag.nodes.all fun node => node.check dag.problem
inductive CheckedList {α : Type} (check : α → Bool) : List α → Prop where
  | nil : CheckedList check []
  | cons {head tail} :
      check head = true →
        CheckedList check tail →
          CheckedList check (head :: tail)
namespace CheckedList
theorem all_eq_true {α : Type} {check : α → Bool} {values : List α} (checked : CheckedList check values) :
    values.all check = true := by
  induction checked with
  | nil => rfl
  | cons hHead _ ih =>
      exact Bool.and_eq_true_iff.mpr ⟨hHead, ih⟩
end CheckedList
/--
分块携带列表 checker 证明。
块内沿用 `CheckedList`，块间只按块数递归，供 replay 缓存有界深度的局部证明。
-/
inductive CheckedListChunks {α : Type} (check : α → Bool) : List α → Prop where
  | nil : CheckedListChunks check []
  | cons {chunk tail} :
      CheckedList check chunk →
        CheckedListChunks check tail →
          CheckedListChunks check (chunk ++ tail)
  | block {chunk tail} :
      chunk.all check = true →
        CheckedListChunks check tail →
          CheckedListChunks check (chunk ++ tail)
namespace CheckedListChunks
theorem all_eq_true {α : Type} {check : α → Bool} {values : List α} (checked : CheckedListChunks check values) :
    values.all check = true := by
  induction checked with
  | nil => rfl
  | cons hChunk _ ih =>
      simp [List.all_append, hChunk.all_eq_true, ih]
  | block hChunk _ ih =>
      simp [List.all_append, hChunk, ih]
end CheckedListChunks
inductive CheckedIndexedList {α : Type} (check : Nat → α → Bool) :
    Nat → List α → Prop where
  | nil {start} : CheckedIndexedList check start []
  | cons {start head tail} :
      check start head = true →
        CheckedIndexedList check (start + 1) tail →
          CheckedIndexedList check start (head :: tail)
namespace CheckedIndexedList
theorem mapIdx_all_eq_true {α : Type} {check : Nat → α → Bool}
    {start : Nat} {values : List α} (checked : CheckedIndexedList check start values) :
    (values.mapIdx fun offset value => check (start + offset) value).all id = true := by
  induction checked with
  | nil => rfl
  | cons hHead _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Bool.and_eq_true_iff.mpr ⟨hHead, ih⟩
end CheckedIndexedList
theorem payloadsChecked_eq_true_of_chunks (dag : DAG σ) (checked :
      CheckedListChunks (fun node => node.check dag.problem) dag.nodes.toList) :
    dag.payloadsChecked = true := by
  change dag.nodes.all (fun node => node.check dag.problem) = true
  rw [← Array.all_toList]
  exact checked.all_eq_true
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem denseIds_eq_true_of_nodes (dag : DAG σ) (checked : CheckedIndexedList denseIdChecked 0 dag.nodes.toList) :
    dag.denseIds = true := by
  unfold denseIds DenseDAG.View.denseIds
  rw [← Array.all_toList, Array.toList_mapIdx]
  simpa [graphView, DenseDAG.View.denseIdChecked, denseIdChecked] using
    checked.mapIdx_all_eq_true
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem parentsBefore_eq_true_of_nodes (dag : DAG σ) (checked : CheckedIndexedList nodeParentsBefore 0 dag.nodes.toList) :
    dag.parentsBefore = true := by
  unfold parentsBefore DenseDAG.View.parentsBefore
  rw [← Array.all_toList, Array.toList_mapIdx]
  simpa [graphView, DenseDAG.View.nodeParentsBefore, nodeParentsBefore] using
    checked.mapIdx_all_eq_true
theorem parentSnapshotsChecked_eq_true_of_listCheck (dag : DAG σ) (checked : dag.parentSnapshotsListChecked = true) :
    dag.parentSnapshotsChecked = true := by
  unfold parentSnapshotsListChecked at checked
  unfold parentSnapshotsChecked
  rw [← Array.all_toList]
  exact checked
theorem guardsChecked_eq_true_of_listCheck (dag : DAG σ) (checked : dag.guardsListChecked = true) :
    dag.guardsChecked = true := by
  unfold guardsListChecked at checked
  unfold guardsChecked
  rw [← Array.all_toList]
  exact checked
/--
canonical source 与 AVATAR split/component 来源必须唯一。
每个初始字句 slot 最多一个 source；每个 source 最多一个 split descriptor；每个 split
descriptor 的 component slot 最多一个节点。

三类键分别使用初始字句位图、节点位图和按 split partition 大小建立的二维位图；
初始化与扫描都只与 DAG 及 partition 总大小线性相关。
-/
def sourceIndicesUnique (dag : DAG σ) : Bool := Id.run do
  let mut sourceSeen :=
    Array.replicate dag.problem.initialClauses.size false
  let mut splitSeen := Array.replicate dag.nodes.size false
  let mut componentSeen :=
    dag.nodes.map fun node =>
      match node.payload with
      | .avatarSplit payload =>
          Array.replicate payload.partitions.size false
      | _ => #[]
  for node in dag.nodes do
    match node.payload with
    | .source initialIndex =>
        if h : initialIndex < sourceSeen.size then
          if sourceSeen[initialIndex] then
            return false
          sourceSeen := sourceSeen.setIfInBounds initialIndex true
        else
          return false
    | .avatarSplit payload =>
        if h : payload.source.id < splitSeen.size then
          if splitSeen[payload.source.id] then
            return false
          splitSeen := splitSeen.setIfInBounds payload.source.id true
        else
          return false
    | .avatarComponent payload =>
        if hSplit : payload.split < componentSeen.size then
          let row := componentSeen[payload.split]
          if hComponent : payload.componentIndex < row.size then
            if row[payload.componentIndex] then
              return false
            componentSeen :=
              componentSeen.setIfInBounds payload.split
                (row.setIfInBounds payload.componentIndex true)
          else
            return false
        else
          return false
    | _ => pure ()
  return true
def guardedSoundnessSupported (dag : DAG σ) : Bool :=
  dag.nodes.all fun node => node.guardedSoundnessSupported
theorem payloadsChecked_of_eq_true
      {dag : DAG σ} (hPayloads : dag.payloadsChecked = true) :
    ∀ index (hIndex : index < dag.nodes.size), (dag.nodeAt index hIndex).check dag.problem = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hPayloads
  simpa [payloadsChecked, nodeAt] using! hAll index hIndex
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem guardedSoundnessSupported_of_eq_true {dag : DAG σ} (hSupported : dag.guardedSoundnessSupported = true) :
    ∀ index (hIndex : index < dag.nodes.size), (dag.nodeAt index hIndex).payload.guardedSoundnessSupported = true := by
  intro index hIndex
  have hAll := Array.all_eq_true.mp hSupported
  have hNode : (dag.nodeAt index hIndex).guardedSoundnessSupported = true := by
    simpa [guardedSoundnessSupported, nodeAt] using! hAll index hIndex
  simpa [Node.guardedSoundnessSupported] using hNode
def guardedNodes (dag : DAG σ) : Array (Node σ) :=
  dag.nodes.filter fun node => !node.unguarded
def theoryConflicts (dag : DAG σ) : Array (Node σ) :=
  dag.nodes.filter Node.theoryConflict
def propositionalLearnedClauses (dag : DAG σ) : Array (Node σ) :=
  dag.nodes.filter fun node =>
    match node.payload with
    | .propositionalLearnedClause _ => true
    | _ => false
structure NodeContract (dag : DAG σ) (index : Nat) (hIndex : index < dag.nodes.size) : Prop where
  node_id : (dag.nodeAt index hIndex).id = index
  node_checked : (dag.nodeAt index hIndex).check dag.problem = true
  rule_tags_ok : (dag.nodeAt index hIndex).ruleTagsOk = true
  payload_checked : (dag.nodeAt index hIndex).payload.check dag.problem (dag.nodeAt index hIndex).parents (dag.nodeAt index hIndex).conclusion = true
  guards_checked : dag.localNodeGuardsOk (dag.nodeAt index hIndex) = true
  prop_initial_links_checked :
    dag.propInitialLinksOk (dag.nodeAt index hIndex) = true
  guarded_soundness_supported :
    dag.guardedSoundnessSupported = true → (dag.nodeAt index hIndex).payload.guardedSoundnessSupported = true
/--
整张 DAG 的结构契约。
根节点、拓扑顺序和逐节点局部检查在构造 checked DAG 时统一提取，后续证明只消费
这一个强接口，不再重复拆解同一条布尔等式。
-/
structure Contract (dag : DAG σ) : Prop where
  root_exists : dag.root < dag.nodes.size
  root_closed : dag.rootClosed = true
  root_unguarded : (dag.nodeAt dag.root root_exists).unguarded = true
  root_conclusion_empty : (dag.nodeAt dag.root root_exists).conclusion.isEmpty = true
  dense_ids : dag.denseIds = true
  parents_before : dag.ParentsBefore
  payloads_checked : dag.payloadsChecked = true
  parent_snapshots_checked : dag.parentSnapshotsChecked = true
  guards_checked : dag.guardsChecked = true
  node_contract :
    ∀ index (hIndex : index < dag.nodes.size), NodeContract dag index hIndex
def toComposite (dag : DAG σ) : Certificate.Composite :=
  {
    root := dag.root
    nodes := dag.nodes.map Node.toPublicNode
    residuals := dag.nodes.filterMap fun node =>
      match node.payload with
      | .residualCdcl _ => some node.id
      | _ => none
  }
def summary (dag : DAG σ) : String :=
  s!"root={dag.root}; nodes={dag.nodes.size}; " ++
    s!"rootClosed={dag.rootClosed}; dense={dag.denseIds}; parentsBefore={dag.parentsBefore}; " ++
      s!"parentSnapshots={dag.parentSnapshotsChecked}; guards={dag.guardsChecked}; " ++
        s!"sourceUnique={dag.sourceIndicesUnique}"
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
/--
拓扑归纳骨架。
若每个节点的性质只需要假设其父节点性质，并且 `ParentsBefore` 保证父节点都位于
当前节点之前，则性质可按数组顺序推广到整张 DAG。
-/
theorem topologicalInduction (dag : DAG σ) (hParents : dag.ParentsBefore)
    {P : ∀ index, index < dag.nodes.size → Node σ → Prop} (hStep :
      ∀ index (hIndex : index < dag.nodes.size), (∀ parent (hParent : parent ∈ (dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex)
              (dag.nodeAt parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (dag.nodeAt index hIndex)) :
    ∀ index (hIndex : index < dag.nodes.size),
      P index hIndex (dag.nodeAt index hIndex) := by
  simpa [ParentsBefore, graphView, nodeAt] using
    DenseDAG.View.topologicalInduction dag.graphView hParents hStep
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem rootByTopologicalInduction (dag : DAG σ) (hRoot : dag.root < dag.nodes.size) (hParents : dag.ParentsBefore)
    {P : ∀ index, index < dag.nodes.size → Node σ → Prop} (hStep :
      ∀ index (hIndex : index < dag.nodes.size), (∀ parent (hParent : parent ∈ (dag.nodeAt index hIndex).parents.toList),
            P parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex)
              (dag.nodeAt parent (Nat.lt_trans (hParents index hIndex parent hParent) hIndex))) →
          P index hIndex (dag.nodeAt index hIndex)) :
    P dag.root hRoot (dag.nodeAt dag.root hRoot) :=
  by
    simpa [ParentsBefore, graphView, nodeAt] using
      DenseDAG.View.rootByTopologicalInduction
        dag.graphView hRoot hParents hStep
end DAG
end DAGCertificateSignature
end DAGCertificate
end Automation
end YesMetaZFC

