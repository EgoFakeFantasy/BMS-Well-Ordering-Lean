import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.LocalRules

/-!
# DAG 内在语义回放

本模块把 checked DAG 的布尔合同直接接到 typed 一阶语义。守卫只在命题核中解释，
对象字句则始终使用 `Compile.CompiledClause.TrueIn`；因此回放层不再携带 raw 良构、
作用域或对象环境桥接。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace IntrinsicReplay

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]

/-- 在给定命题赋值下，规范化 guard 集中的每个文字都成立。 -/
def GuardsHold (valuation : PropResolution.Valuation) (guards : GuardSet) : Prop :=
  ∀ lit, lit ∈ (Guards.canonical guards).toList → lit.Holds valuation

namespace GuardsHold

theorem of_eq {valuation : PropResolution.Valuation}
    {left right : GuardSet} (hEq : Guards.eq left right = true)
    (hLeft : GuardsHold valuation left) :
    GuardsHold valuation right := by
  intro lit hLit
  have hCanonical : Guards.canonical left = Guards.canonical right :=
    PropResolution.clauseEq_eq.mp hEq
  apply hLeft lit
  rw [hCanonical]
  exact hLit

theorem neg_of_not_holds
    {valuation : PropResolution.Valuation} (lit : PropResolution.Lit)
    (hNot : ¬ lit.Holds valuation) :
    lit.neg.Holds valuation := by
  rcases lit with ⟨v, positive⟩
  cases positive with
  | false =>
      change ¬¬ valuation v at hNot
      change valuation v
      exact Classical.byContradiction fun hFalse => hNot hFalse
  | true =>
      change ¬ valuation v at hNot
      change ¬ valuation v
      exact hNot

end GuardsHold

omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem assignmentNonempty
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ) :
    ∀ context : SortContext σ, Nonempty (Assignment M context)
  | [] => ⟨Assignment.empty⟩
  | sort :: rest =>
      let ⟨value⟩ := M.nonempty sort
      let ⟨tail⟩ := assignmentNonempty M rest
      ⟨Assignment.push value tail⟩

omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem compiledClause_not_trueIn_of_raw_empty
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {registry : Compile.FreeRegistry σ}
    (compiled : Compile.CompiledClause registry)
    (hEmpty : compiled.raw.isEmpty = true) :
    ¬ compiled.TrueIn M := by
  rcases compiled.literal_view with
    ⟨formulas, hList, hFormula⟩
  have hRawList : compiled.raw.literals.toList = [] :=
    Clause.literals_toList_eq_nil_of_isEmpty hEmpty
  have hFormulas : formulas = [] := by
    rw [hRawList] at hList
    simpa [Compile.literalList?] using hList
  have hFalseFormula : compiled.formula = .falsum := by
    calc
      compiled.formula =
          Logic.FirstOrder.Formula.disjunctionList formulas := hFormula
      _ = Logic.FirstOrder.Formula.disjunctionList [] := by rw [hFormulas]
      _ = .falsum := rfl
  intro hTrue
  have hValid := (Compile.forallFree_trueIn_iff compiled.formula).mp hTrue
  rcases assignmentNonempty M registry.context with ⟨assignment⟩
  have hSat := hValid assignment
  simp [hFalseFormula, Logic.FirstOrder.Formula.satisfies] at hSat

theorem parentGuardsHold_of_union
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (parent : NodeId)
    (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentIndex : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation}
    {guards : GuardSet}
    (hUnion : cert.dag.parentGuardUnion?
      (cert.dag.nodeAt index hIndex).parents = some guards)
    (hCurrent : GuardsHold valuation
      (cert.dag.nodeAt index hIndex).guards)
    (hGuardEq : Guards.eq (cert.dag.nodeAt index hIndex).guards guards = true) :
    GuardsHold valuation (cert.dag.nodeAt parent hParentIndex).guards := by
  have hUnionHold : GuardsHold valuation guards :=
    GuardsHold.of_eq hGuardEq hCurrent
  intro lit hLit
  apply hUnionHold lit
  exact DAG.mem_parentGuardUnionList_of_parent_mem
    (dag := cert.dag)
    (parents := (cert.dag.nodeAt index hIndex).parents.toList)
    (parent := parent)
    (parentNode := cert.dag.nodeAt parent hParentIndex)
    (guards := guards)
    (lit := lit)
    (by simpa [DAG.parentGuardUnion?] using hUnion)
    hParentMem
    (cert.dag.node?_eq_some_nodeAt hParentIndex)
    hLit

theorem parentGuardsHold_of_localNodeGuardsOk
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload = .localRule payload)
    (parent : NodeId)
    (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentIndex : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation}
    (hCurrent : GuardsHold valuation
      (cert.dag.nodeAt index hIndex).guards) :
    GuardsHold valuation (cert.dag.nodeAt parent hParentIndex).guards := by
  have hGuardCheck :=
    (cert.contract.node_contract index hIndex).guards_checked
  unfold DAG.localNodeGuardsOk at hGuardCheck
  have hLocalCheck :
      (match cert.dag.parentGuardUnion?
        (cert.dag.nodeAt index hIndex).parents with
      | some guards =>
          Guards.eq (cert.dag.nodeAt index hIndex).guards guards
      | none => false) = true := by
    simpa [hPayload] using! hGuardCheck
  cases hUnion : cert.dag.parentGuardUnion?
      (cert.dag.nodeAt index hIndex).parents with
  | none =>
      simp [hUnion] at hLocalCheck
  | some guards =>
      have hEq : Guards.eq (cert.dag.nodeAt index hIndex).guards guards = true := by
        simpa [hUnion] using hLocalCheck
      exact parentGuardsHold_of_union cert index hIndex parent hParentMem
        hParentIndex hUnion hCurrent hEq

def GuardedNodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    {dag : DAG σ} (compiled : Compile.CheckedDAGClauses dag)
    (index : Nat) (hIndex : index < dag.nodes.size) : Prop :=
  GuardsHold valuation (dag.nodeAt index hIndex).guards →
    NodeTrueIn M compiled index hIndex

theorem payloadCheck_of_payload_eq
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    {payload : Payload σ}
    (hPayload : (cert.dag.nodeAt index hIndex).payload = payload) :
    payload.check cert.dag.problem
      (cert.dag.nodeAt index hIndex).parents
      (cert.dag.nodeAt index hIndex).conclusion = true := by
  have hChecked :=
    (cert.contract.node_contract index hIndex).payload_checked
  simpa [hPayload] using hChecked

theorem parentSnapshotChecked_of_payload_mem
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    {payload : Payload σ}
    (hPayload : (cert.dag.nodeAt index hIndex).payload = payload)
    {parent : ParentClause σ}
    (hParent : parent ∈ payload.parentClauses.toList) :
    cert.dag.parentSnapshotChecked parent = true := by
  have hAll := Array.all_eq_true.mp cert.contract.parent_snapshots_checked
  have hNode :
      (cert.dag.nodeAt index hIndex).payload.parentClauses.all
          (fun current => cert.dag.parentSnapshotChecked current) = true := by
    simpa [DAG.parentSnapshotsChecked, DAG.nodeParentSnapshotsChecked,
      DAG.nodeAt] using! hAll index hIndex
  rw [hPayload] at hNode
  exact array_check_of_mem hNode hParent

omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem empty_clause_eq
    {left right : Clause σ}
    (hLeft : left.isEmpty = true) (hRight : right.isEmpty = true) :
    left = right := by
  cases left with
  | mk leftLiterals =>
      cases right with
      | mk rightLiterals =>
          simp [Clause.isEmpty, Array.isEmpty_iff] at hLeft hRight ⊢
          simp [hLeft, hRight]

omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem compiledClause_exists_trueLiteral
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {registry : Compile.FreeRegistry σ}
    (compiled : Compile.CompiledClause registry)
    (assignment : Assignment M registry.context)
    (hTrue : compiled.TrueIn M) :
    ∃ literal ∈ compiled.raw.literals.toList, ∃ formula,
      Compile.formula? registry [] literal.toFormula = some formula ∧
        Logic.FirstOrder.Formula.satisfies
          (Compile.openEnv assignment) formula := by
  rcases compiled.literal_view with
    ⟨formulas, hCompile, hFormula⟩
  have hValid := (Compile.forallFree_trueIn_iff compiled.formula).mp hTrue
  have hSat := hValid assignment
  rw [hFormula,
    Logic.FirstOrder.Formula.satisfies_disjunctionList_iff] at hSat
  rcases hSat with ⟨formula, hFormulaMem, hFormulaSat⟩
  rcases Compile.literalList?_raw_of_mem registry hCompile hFormulaMem with
    ⟨literal, hLiteralMem, hLiteralCompile⟩
  exact ⟨literal, hLiteralMem, formula, hLiteralCompile, hFormulaSat⟩

def overlayValuation
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {registry : Compile.FreeRegistry σ}
    (assignment : Assignment M registry.context)
    (base : PropResolution.Valuation)
    (atomMap : Array (Formula σ)) : PropResolution.Valuation :=
  fun varId =>
    match atomMap[varId]? with
    | none => base varId
    | some atom =>
        ∃ formula,
          Compile.formula? registry [] atom = some formula ∧
            Logic.FirstOrder.Formula.satisfies
              (Compile.openEnv assignment) formula

omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem overlayValuation_eq_of_outside
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {registry : Compile.FreeRegistry σ}
    (assignment : Assignment M registry.context)
    (base : PropResolution.Valuation)
    (atomMap : Array (Formula σ))
    {literal : PropResolution.Lit}
    (hOutside : PropLiteralLink.outsideAtomMap atomMap literal = true) :
    overlayValuation M assignment base atomMap literal.var = base literal.var := by
  cases hLookup : atomMap[literal.var]? with
  | none => simp [overlayValuation, hLookup]
  | some atom =>
      simp [PropLiteralLink.outsideAtomMap, hLookup] at hOutside

omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem compiledLiteral_atomTruth
    {registry : Compile.FreeRegistry σ}
    (literal : Literal σ)
    {formula : Logic.FirstOrder.OpenFormula σ registry.context}
    (hCompile : Compile.formula? registry [] literal.toFormula = some formula)
    {M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ}
    {assignment : Assignment M registry.context}
    (hSat : Logic.FirstOrder.Formula.satisfies
      (Compile.openEnv assignment) formula) :
    ∃ atomFormula,
      Compile.formula? registry [] literal.atom = some atomFormula ∧
        ((literal.polarity = true ∧
            Logic.FirstOrder.Formula.satisfies
              (Compile.openEnv assignment) atomFormula) ∨
          (literal.polarity = false ∧
            ¬ Logic.FirstOrder.Formula.satisfies
              (Compile.openEnv assignment) atomFormula)) := by
  cases hPolarity : literal.polarity with
  | true =>
      have hAtomCompile :
          Compile.formula? registry [] literal.atom = some formula := by
        simpa [Literal.toFormula, hPolarity] using hCompile
      exact ⟨formula, hAtomCompile, Or.inl ⟨rfl, hSat⟩⟩
  | false =>
      cases hAtomCompile : Compile.formula? registry [] literal.atom with
      | none =>
          simp [Literal.toFormula, hPolarity, Compile.formula?, hAtomCompile]
            at hCompile
      | some atomFormula =>
          have hCompile' :
              Compile.formula? registry [] (.neg literal.atom) = some formula := by
            simpa [Literal.toFormula, hPolarity] using hCompile
          have hNegCompile :
              Logic.FirstOrder.Formula.neg atomFormula = formula := by
            change
              (Logic.FirstOrder.Formula.neg <$>
                Compile.formula? registry [] literal.atom) = some formula at hCompile'
            simp [hAtomCompile] at hCompile'
            exact hCompile'
          have hAtomFalse :
              ¬ Logic.FirstOrder.Formula.satisfies
                (Compile.openEnv assignment) atomFormula := by
            have hSatNeg :
                Logic.FirstOrder.Formula.satisfies
                  (Compile.openEnv assignment)
                  (Logic.FirstOrder.Formula.neg atomFormula) := by
              simpa [hNegCompile] using hSat
            simpa [Logic.FirstOrder.Formula.satisfies] using hSatNeg
          exact ⟨atomFormula, rfl,
            Or.inr ⟨rfl, hAtomFalse⟩⟩

omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem overlayValuation_atomTruth
    {registry : Compile.FreeRegistry σ}
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (assignment : Assignment M registry.context)
    (base : PropResolution.Valuation)
    (atomMap : Array (Formula σ))
    {varId : Nat} {atom : Formula σ} {atomFormula}
    (hLookup : atomMap[varId]? = some atom)
    (hCompile : Compile.formula? registry [] atom = some atomFormula) :
    overlayValuation M assignment base atomMap varId ↔
      Logic.FirstOrder.Formula.satisfies
        (Compile.openEnv assignment) atomFormula := by
  simp only [overlayValuation, hLookup]
  constructor
  · rintro ⟨formula, hFormula, hSat⟩
    have hEq : formula = atomFormula :=
      Option.some.inj (hFormula.symm.trans hCompile)
    exact hEq ▸ hSat
  · intro hSat
    exact ⟨atomFormula, hCompile, hSat⟩

theorem overlayLit_holds_of_link
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {registry : Compile.FreeRegistry σ}
    (assignment : Assignment M registry.context)
    (base : PropResolution.Valuation)
    (atomMap : Array (Formula σ))
    (link : PropLiteralLink σ)
    {formula : Logic.FirstOrder.OpenFormula σ registry.context}
    (hLink : link.check atomMap = true)
    (hCompile : Compile.formula? registry [] link.object.toFormula = some formula)
    (hSat : Logic.FirstOrder.Formula.satisfies
      (Compile.openEnv assignment) formula) :
    link.prop.Holds (overlayValuation M assignment base atomMap) := by
  have hParts := Bool.and_eq_true_iff.mp hLink
  have hPolarity : link.prop.positive = link.object.polarity :=
    beq_iff_eq.mp hParts.1
  rcases compiledLiteral_atomTruth link.object hCompile hSat with
    ⟨atomFormula, hAtomCompile, hAtomTruth⟩
  cases hLookup : atomMap[link.prop.var]? with
  | none =>
      simp [ hLookup] at hParts
  | some atom =>
      have hAtomCheck : StructuralEq.formula atom link.object.atom = true := by
        simpa [PropLiteralLink.check, hLookup] using hParts.2
      have hAtomEq : atom = link.object.atom :=
        StructuralEq.formula_sound atom link.object.atom hAtomCheck
      have hAtomCompile' :
          Compile.formula? registry [] atom = some atomFormula := by
        simpa [hAtomEq] using hAtomCompile
      have hOverlay :
          overlayValuation M assignment base atomMap link.prop.var ↔
            Logic.FirstOrder.Formula.satisfies
              (Compile.openEnv assignment) atomFormula :=
        overlayValuation_atomTruth M assignment base atomMap
          hLookup hAtomCompile'
      rcases hAtomTruth with hPositive | hNegative
      · have hPropPositive : link.prop.positive = true :=
          hPolarity.trans hPositive.1
        simpa [PropResolution.Lit.Holds, hPropPositive] using
          hOverlay.mpr hPositive.2
      · have hPropNegative : link.prop.positive = false :=
          hPolarity.trans hNegative.1
        have hNotOverlay :
            ¬ overlayValuation M assignment base atomMap link.prop.var := by
          intro hValue
          exact hNegative.2 (hOverlay.mp hValue)
        simpa [PropResolution.Lit.Holds, hPropNegative] using hNotOverlay

omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem holds_of_outside_overlay
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    {registry : Compile.FreeRegistry σ}
    (assignment : Assignment M registry.context)
    (base : PropResolution.Valuation)
    (atomMap : Array (Formula σ))
    (lit : PropResolution.Lit)
    (hOutside : PropLiteralLink.outsideAtomMap atomMap lit = true) :
    lit.Holds (overlayValuation M assignment base atomMap) ↔
      lit.Holds base := by
  have hValue := overlayValuation_eq_of_outside M assignment base atomMap hOutside
  cases lit with
  | mk var positive =>
      cases positive <;>
        simp [PropResolution.Lit.Holds, hValue]

theorem guardsHold_of_unguarded
    {valuation : PropResolution.Valuation} {guards : GuardSet}
    (hUnguarded : guards.isEmpty = true) :
    GuardsHold valuation guards := by
  have hGuards : guards = #[] := by
    apply Array.toList_inj.mp
    simpa [Clause.isEmpty, Array.isEmpty_iff] using hUnguarded
  subst guards
  intro lit hLit
  exact False.elim <| by
    simp [Guards.canonical, PropResolution.canonicalClause,
      PropResolution.canonicalClauseList,
      PropResolution.mergeCanonicalRuns] at hLit

theorem parentNode_trueIn_of_unguarded
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex))
    (parent : NodeId)
    (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentIndex : parent < cert.dag.nodes.size)
    {guards : GuardSet} (hUnguarded : guards.isEmpty = true)
    (hParentGuards : (cert.dag.nodeAt parent hParentIndex).guards = guards) :
    NodeTrueIn M compiled parent hParentIndex := by
  have hGuarded := hParents parent hParentMem
  apply hGuarded
  rw [hParentGuards]
  exact guardsHold_of_unguarded hUnguarded

theorem parentClause_initial_satisfies
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (atomMap : Array (Formula σ))
    (link : PropParentClauseLink σ)
    (initial : PropResolution.InitialClause)
    (hCheck : link.check (cert.dag.nodeAt index hIndex).parents
      atomMap initial = true)
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex))
    (hParentIndex : link.parent.id < cert.dag.nodes.size)
    (hParentUnguarded :
      (cert.dag.nodeAt link.parent.id hParentIndex).unguarded = true)
    (hSnapshot : cert.dag.parentSnapshotChecked link.parent = true) :
    PropResolution.Clause.Satisfies
      (overlayValuation M assignment valuation atomMap) initial.clause := by
  have hCheckParts := Bool.and_eq_true_iff.mp hCheck
  have hClauseParts := Bool.and_eq_true_iff.mp hCheckParts.1
  have hIdAndObject := Bool.and_eq_true_iff.mp hClauseParts.1
  have hObjectEq : link.parent.clause = link.objectClause :=
    Clause.eq_sound link.parent.clause link.objectClause hIdAndObject.2
  have hInitialEq : initial.clause = link.encodedClause :=
    PropResolution.clauseEq_eq.mp hClauseParts.2
  have hLinkChecks := hCheckParts.2
  have hParentMem : link.parent.id ∈
      (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hIdAndObject.1
  have hParentTrue : NodeTrueIn M compiled link.parent.id hParentIndex :=
    parentNode_trueIn_of_unguarded M valuation cert compiled index hIndex
      hParents link.parent.id hParentMem hParentIndex
      (guards := (cert.dag.nodeAt link.parent.id hParentIndex).guards)
      (by simpa [Node.unguarded] using hParentUnguarded) rfl
  rcases DAG.parentSnapshotChecked_sound hSnapshot with
    ⟨snapshotNode, hSnapshotNode, hSnapshotClause⟩
  have hSnapshotNodeEq :
      snapshotNode = cert.dag.nodeAt link.parent.id hParentIndex := by
    exact Option.some.inj <| hSnapshotNode.symm.trans
      (cert.dag.node?_eq_some_nodeAt hParentIndex)
  subst snapshotNode
  have hParentRaw :
      (compiled.nodeAt link.parent.id hParentIndex).raw = link.parent.clause :=
    (compiled.nodeAt_raw link.parent.id hParentIndex).trans hSnapshotClause
  rcases compiledClause_exists_trueLiteral M
      (compiled.nodeAt link.parent.id hParentIndex) assignment hParentTrue with
    ⟨literal, hLiteralMem, formula, hLiteralCompile, hLiteralSat⟩
  rw [hParentRaw] at hLiteralMem
  have hObjectMem : literal ∈ link.objectClause.literals.toList := by
    simpa [hObjectEq] using hLiteralMem
  have hMappedMem : literal ∈
      (link.literalLinks.map (fun item => item.object)).toList := by
    simpa [PropParentClauseLink.objectClause] using hObjectMem
  have hMappedMem' : literal ∈
      List.map (fun item => item.object) link.literalLinks.toList := by
    simpa [Array.toList_map] using hMappedMem
  rcases List.mem_map.mp hMappedMem' with
    ⟨item, hItemMem, hItemObject⟩
  have hItemCheck : item.check atomMap = true :=
    array_check_of_mem hLinkChecks hItemMem
  have hItemCompile :
      Compile.formula? compiled.compilation.registry [] item.object.toFormula =
        some formula := by
    simpa [hItemObject] using hLiteralCompile
  have hItemHolds := overlayLit_holds_of_link M assignment valuation atomMap
    item hItemCheck hItemCompile hLiteralSat
  have hPropMem' : item.prop ∈
      List.map (fun current => current.prop) link.literalLinks.toList :=
    List.mem_map.mpr ⟨item, hItemMem, rfl⟩
  have hPropMem : item.prop ∈
      (link.literalLinks.map (fun current => current.prop)).toList := by
    simpa [Array.toList_map] using hPropMem'
  have hPropCanonical : item.prop ∈ link.encodedClause.toList := by
    simpa [PropParentClauseLink.encodedClause] using
      PropResolution.mem_canonicalClause_of_mem hPropMem
  have hPropInitial : item.prop ∈ initial.clause.toList := by
    rw [hInitialEq]
    exact hPropCanonical
  exact ⟨item.prop, hPropInitial, hItemHolds⟩

theorem guardActivationClause_initial_satisfies
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (atomMap : Array (Formula σ))
    (link : PropGuardActivationLink σ)
    (initial : PropResolution.InitialClause)
    (hCheck : link.check (cert.dag.nodeAt index hIndex).parents
      atomMap initial = true)
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex))
    (hParentIndex : link.parent.id < cert.dag.nodes.size)
    (hParentGuardsEq : Guards.eq link.guards
      (cert.dag.nodeAt link.parent.id hParentIndex).guards = true)
    (hSnapshot : cert.dag.parentSnapshotChecked link.parent = true) :
    PropResolution.Clause.Satisfies
      (overlayValuation M assignment valuation atomMap) initial.clause := by
  have hCheckParts := Bool.and_eq_true_iff.mp hCheck
  have hClauseParts := Bool.and_eq_true_iff.mp hCheckParts.1
  have hIdAndObject := Bool.and_eq_true_iff.mp hClauseParts.1
  have hParentIdAndObject := Bool.and_eq_true_iff.mp hIdAndObject.1
  have hObjectEq : link.parent.clause = link.objectClause :=
    Clause.eq_sound link.parent.clause link.objectClause hParentIdAndObject.2
  have hInitialEq : initial.clause = link.encodedClause :=
    PropResolution.clauseEq_eq.mp hIdAndObject.2
  have hParentMem : link.parent.id ∈
      (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hParentIdAndObject.1
  have hOutsideGuards := hClauseParts.2
  have hLinkChecks := hCheckParts.2
  by_cases hAllGuards : GuardsHold valuation link.guards
  · have hParentGuards : GuardsHold valuation
        (cert.dag.nodeAt link.parent.id hParentIndex).guards :=
      GuardsHold.of_eq hParentGuardsEq hAllGuards
    have hParentTrue : NodeTrueIn M compiled link.parent.id hParentIndex :=
      hParents link.parent.id hParentMem hParentGuards
    rcases DAG.parentSnapshotChecked_sound hSnapshot with
      ⟨snapshotNode, hSnapshotNode, hSnapshotClause⟩
    have hSnapshotNodeEq :
        snapshotNode = cert.dag.nodeAt link.parent.id hParentIndex := by
      exact Option.some.inj <| hSnapshotNode.symm.trans
        (cert.dag.node?_eq_some_nodeAt hParentIndex)
    subst snapshotNode
    have hParentRaw :
        (compiled.nodeAt link.parent.id hParentIndex).raw = link.parent.clause :=
      (compiled.nodeAt_raw link.parent.id hParentIndex).trans hSnapshotClause
    rcases compiledClause_exists_trueLiteral M
        (compiled.nodeAt link.parent.id hParentIndex) assignment hParentTrue with
      ⟨literal, hLiteralMem, formula, hLiteralCompile, hLiteralSat⟩
    rw [hParentRaw] at hLiteralMem
    have hObjectMem : literal ∈ link.objectClause.literals.toList := by
      simpa [hObjectEq] using hLiteralMem
    have hMappedMem : literal ∈
        (link.literalLinks.map (fun item => item.object)).toList := by
      simpa [PropGuardActivationLink.objectClause] using hObjectMem
    have hMappedMem' : literal ∈
        List.map (fun item => item.object) link.literalLinks.toList := by
      simpa [Array.toList_map] using hMappedMem
    rcases List.mem_map.mp hMappedMem' with
      ⟨item, hItemMem, hItemObject⟩
    have hItemCheck : item.check atomMap = true :=
      array_check_of_mem hLinkChecks hItemMem
    have hItemCompile :
        Compile.formula? compiled.compilation.registry [] item.object.toFormula =
          some formula := by
      simpa [hItemObject] using hLiteralCompile
    have hItemHolds := overlayLit_holds_of_link M assignment valuation atomMap
      item hItemCheck hItemCompile hLiteralSat
    have hPropMem' : item.prop ∈
        List.map (fun current => current.prop) link.literalLinks.toList :=
      List.mem_map.mpr ⟨item, hItemMem, rfl⟩
    have hPropMem : item.prop ∈
        (link.literalLinks.map (fun current => current.prop)).toList := by
      simpa [Array.toList_map] using hPropMem'
    have hPropCanonical : item.prop ∈ link.encodedClause.toList := by
      simpa [PropGuardActivationLink.encodedClause] using
        PropResolution.mem_canonicalClause_of_mem
          (show item.prop ∈
              (link.guards.map PropResolution.Lit.neg ++
                link.literalLinks.map (fun current => current.prop)).toList by
            simp only [Array.toList_append, List.mem_append]
            exact Or.inr hPropMem)
    have hPropInitial : item.prop ∈ initial.clause.toList := by
      rw [hInitialEq]
      exact hPropCanonical
    exact ⟨item.prop, hPropInitial, hItemHolds⟩
  · have hGuardExists : ∃ guard,
        guard ∈ (Guards.canonical link.guards).toList ∧
          ¬ guard.Holds valuation := by
      apply Classical.byContradiction
      intro hNone
      apply hAllGuards
      intro guard hGuard
      exact Classical.byContradiction (fun hNot =>
        hNone ⟨guard, hGuard, hNot⟩)
    rcases hGuardExists with ⟨guard, hGuardMem, hGuardFalse⟩
    have hGuardRaw : guard ∈ link.guards.toList :=
      Guards.mem_of_mem_canonical hGuardMem
    have hGuardArrayMem : guard ∈ link.guards.toList := hGuardRaw
    have hGuardOutside :
        PropLiteralLink.outsideAtomMap atomMap guard = true :=
      array_check_of_mem hOutsideGuards hGuardArrayMem
    have hNegOutside :
        PropLiteralLink.outsideAtomMap atomMap guard.neg = true :=
      PropLiteralLink.outsideAtomMap_neg hGuardOutside
    have hNegHoldsBase : guard.neg.Holds valuation :=
      GuardsHold.neg_of_not_holds guard hGuardFalse
    have hNegHoldsOverlay :
        guard.neg.Holds (overlayValuation M assignment valuation atomMap) :=
      (holds_of_outside_overlay M assignment valuation atomMap guard.neg
        hNegOutside).mpr hNegHoldsBase
    have hNegRaw : guard.neg ∈
        (link.guards.map PropResolution.Lit.neg).toList := by
      simpa [Array.toList_map] using
        (List.mem_map.mpr ⟨guard, hGuardRaw, rfl⟩ :
          guard.neg ∈ List.map PropResolution.Lit.neg link.guards.toList)
    have hNegEncoded : guard.neg ∈ link.encodedClause.toList := by
      simpa [PropGuardActivationLink.encodedClause] using
        PropResolution.mem_canonicalClause_of_mem
          (show guard.neg ∈
              (link.guards.map PropResolution.Lit.neg ++
                link.literalLinks.map (fun current => current.prop)).toList by
            simp only [Array.toList_append, List.mem_append]
            exact Or.inl hNegRaw)
    have hNegInitial : guard.neg ∈ initial.clause.toList := by
      rw [hInitialEq]
      exact hNegEncoded
    exact ⟨guard.neg, hNegInitial, hNegHoldsOverlay⟩

theorem propLearnedClause_initial_satisfies
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (atomMap : Array (Formula σ))
    (link : PropLearnedClauseLink)
    (initial : PropResolution.InitialClause)
    (payload : PropositionalLearnedClausePayload)
    (hCheck : link.check (cert.dag.nodeAt index hIndex).parents
      atomMap initial = true)
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex))
    (hParentIndex : link.parent < cert.dag.nodes.size)
    (hPayload : (cert.dag.nodeAt link.parent hParentIndex).payload =
      .propositionalLearnedClause payload)
    (hDagLink : cert.dag.propLearnedInitialLinkOk
      (cert.dag.nodeAt index hIndex).parents link = true) :
    PropResolution.Clause.Satisfies
      (overlayValuation M assignment valuation atomMap) initial.clause := by
  have hCheckParts := Bool.and_eq_true_iff.mp hCheck
  have hParentOutside := Bool.and_eq_true_iff.mp hCheckParts.1
  have hParentMem : link.parent ∈
      (cert.dag.nodeAt index hIndex).parents.toList :=
    Array.mem_def.mp (by simpa using hParentOutside.1)
  have hOutside := hParentOutside.2
  have hInitialEq : initial.clause = link.clause :=
    PropResolution.clauseEq_eq.mp hCheckParts.2
  have hDagParts := Bool.and_eq_true_iff.mp hDagLink
  have hPayloadClauseCheck :
      PropResolution.clauseEq link.clause payload.learned = true := by
    simpa [cert.dag.node?_eq_some_nodeAt hParentIndex, hPayload] using
      hDagParts.2
  have hClauseLearned : link.clause = payload.learned :=
    PropResolution.clauseEq_eq.mp hPayloadClauseCheck
  have hGuardCheck :=
    (cert.contract.node_contract link.parent hParentIndex).guards_checked
  have hGuardFields :
      (cert.dag.nodeAt link.parent hParentIndex).conclusion.isEmpty = true ∧
        (match cert.dag.node? payload.conflict with
        | some conflictNode =>
            conflictNode.theoryConflict &&
              Guards.eq (cert.dag.nodeAt link.parent hParentIndex).guards
                conflictNode.guards &&
                (match conflictNode.payload with
                | .theoryConflict _ =>
                    PropResolution.clauseEq payload.learned
                      (Guards.learnedClause conflictNode.guards)
                | _ => false)
        | none => false) = true := by
    simpa [DAG.localNodeGuardsOk, hPayload] using! hGuardCheck
  have hConclusionEmpty := hGuardFields.1
  cases hConflictNode : cert.dag.node? payload.conflict with
  | none =>
      simp [hConflictNode] at hGuardFields
  | some conflictNode =>
      have hConflictFields :
          conflictNode.theoryConflict &&
            Guards.eq (cert.dag.nodeAt link.parent hParentIndex).guards
              conflictNode.guards &&
            (match conflictNode.payload with
            | .theoryConflict _ =>
                PropResolution.clauseEq payload.learned
                  (Guards.learnedClause conflictNode.guards)
            | _ => false) = true := by
        simpa [hConflictNode] using hGuardFields.2
      have hConflictParts := Bool.and_eq_true_iff.mp hConflictFields
      have hTheoryAndGuard := Bool.and_eq_true_iff.mp hConflictParts.1
      have hGuardEq : Guards.eq
          (cert.dag.nodeAt link.parent hParentIndex).guards
            conflictNode.guards = true :=
        hTheoryAndGuard.2
      cases hConflictPayload : conflictNode.payload with
      | theoryConflict conflictPayload =>
          have hLearnedCheck :
              PropResolution.clauseEq payload.learned
                (Guards.learnedClause conflictNode.guards) = true := by
            simpa [hConflictPayload] using hConflictParts.2
          have hLearnedEq : payload.learned =
              Guards.learnedClause conflictNode.guards :=
            PropResolution.clauseEq_eq.mp hLearnedCheck
          by_cases hParentGuards : GuardsHold valuation
              (cert.dag.nodeAt link.parent hParentIndex).guards
          · have hParentTrue : NodeTrueIn M compiled link.parent hParentIndex :=
              hParents link.parent hParentMem hParentGuards
            exact False.elim <|
              compiledClause_not_trueIn_of_raw_empty M
                (compiled.nodeAt link.parent hParentIndex)
                (by
                  rw [compiled.nodeAt_raw]
                  exact hConclusionEmpty) hParentTrue
          · have hGuardExists : ∃ guard,
                guard ∈
                    (Guards.canonical
                      (cert.dag.nodeAt link.parent hParentIndex).guards).toList ∧
                  ¬ guard.Holds valuation := by
              apply Classical.byContradiction
              intro hNone
              apply hParentGuards
              intro guard hGuard
              exact Classical.byContradiction (fun hNot =>
                hNone ⟨guard, hGuard, hNot⟩)
            rcases hGuardExists with ⟨guard, hGuardMem, hGuardFalse⟩
            have hGuardCanonicalEq :
                Guards.canonical
                    (cert.dag.nodeAt link.parent hParentIndex).guards =
                  Guards.canonical conflictNode.guards :=
              PropResolution.clauseEq_eq.mp hGuardEq
            have hConflictGuardMem : guard ∈
                (Guards.canonical conflictNode.guards).toList := by
              rw [← hGuardCanonicalEq]
              exact hGuardMem
            have hConflictGuardRaw : guard ∈ conflictNode.guards.toList :=
              Guards.mem_of_mem_canonical hConflictGuardMem
            have hNegLearned : guard.neg ∈
                (Guards.learnedClause conflictNode.guards).toList := by
              have hNegRaw : guard.neg ∈
                  (conflictNode.guards.map PropResolution.Lit.neg).toList := by
                simpa [Array.toList_map] using
                  (List.mem_map.mpr ⟨guard, hConflictGuardRaw, rfl⟩ :
                    guard.neg ∈
                      List.map PropResolution.Lit.neg conflictNode.guards.toList)
              simpa [Guards.learnedClause] using!
                PropResolution.mem_canonicalClause_of_mem hNegRaw
            have hNegPayload : guard.neg ∈ payload.learned.toList := by
              rw [hLearnedEq]
              exact hNegLearned
            have hNegLink : guard.neg ∈ link.clause.toList := by
              rw [hClauseLearned]
              exact hNegPayload
            have hNegOutside :
                PropLiteralLink.outsideAtomMap atomMap guard.neg = true :=
              array_check_of_mem hOutside hNegLink
            have hNegBase : guard.neg.Holds valuation :=
              GuardsHold.neg_of_not_holds guard hGuardFalse
            have hNegOverlay :
                guard.neg.Holds
                  (overlayValuation M assignment valuation atomMap) :=
              (holds_of_outside_overlay M assignment valuation atomMap guard.neg
                hNegOutside).mpr hNegBase
            have hNegInitial : guard.neg ∈ initial.clause.toList := by
              rw [hInitialEq]
              exact hNegLink
            exact ⟨guard.neg, hNegInitial, hNegOverlay⟩
      | _ =>
          simp [hConflictPayload] at hConflictParts

theorem initialJustification_satisfies
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (atomMap : Array (Formula σ))
    (justification : PropInitialJustification σ)
    (initial : PropResolution.InitialClause)
    (hCheck : justification.check (cert.dag.nodeAt index hIndex).parents
      atomMap initial = true)
    (hDag : cert.dag.propInitialJustificationDagOk
      (cert.dag.nodeAt index hIndex).parents justification = true)
    (hSupported : justification.guardedSoundnessSupported = true)
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex)) :
    PropResolution.Clause.Satisfies
      (overlayValuation M assignment valuation atomMap) initial.clause := by
  cases justification with
  | parentClause link =>
      have hDagParts := Bool.and_eq_true_iff.mp hDag
      have hDagPrefix := Bool.and_eq_true_iff.mp hDagParts.1
      have hParentMem : link.parent.id ∈
          (cert.dag.nodeAt index hIndex).parents.toList :=
        ParentClause.mem_toList_of_idIn hDagPrefix.1
      let hParentIndex :=
        Nat.lt_trans
          (cert.contract.parents_before index hIndex link.parent.id hParentMem)
          hIndex
      have hUnguarded :
          (cert.dag.nodeAt link.parent.id hParentIndex).unguarded = true := by
        simpa [cert.dag.node?_eq_some_nodeAt hParentIndex] using hDagParts.2
      exact parentClause_initial_satisfies M valuation cert compiled index hIndex
        assignment atomMap link initial hCheck hParents hParentIndex hUnguarded
        hDagPrefix.2
  | guardActivationClause link =>
      have hDagParts := Bool.and_eq_true_iff.mp hDag
      have hDagPrefix := Bool.and_eq_true_iff.mp hDagParts.1
      have hParentMem : link.parent.id ∈
          (cert.dag.nodeAt index hIndex).parents.toList :=
        ParentClause.mem_toList_of_idIn hDagPrefix.1
      let hParentIndex :=
        Nat.lt_trans
          (cert.contract.parents_before index hIndex link.parent.id hParentMem)
          hIndex
      have hGuardData :
          (!((cert.dag.nodeAt link.parent.id hParentIndex).unguarded) &&
            Guards.eq link.guards
              (cert.dag.nodeAt link.parent.id hParentIndex).guards) = true := by
        simpa [cert.dag.node?_eq_some_nodeAt hParentIndex] using hDagParts.2
      have hGuardParts := Bool.and_eq_true_iff.mp hGuardData
      exact guardActivationClause_initial_satisfies M valuation cert compiled
        index hIndex assignment atomMap link initial hCheck hParents hParentIndex
        hGuardParts.2 hDagPrefix.2
  | propLearnedClause link =>
      change cert.dag.propLearnedInitialLinkOk
        (cert.dag.nodeAt index hIndex).parents link = true at hDag
      have hCheckParts := Bool.and_eq_true_iff.mp hCheck
      have hParentPart := Bool.and_eq_true_iff.mp hCheckParts.1
      have hParentMem : link.parent ∈
          (cert.dag.nodeAt index hIndex).parents.toList :=
        Array.mem_def.mp (by simpa using hParentPart.1)
      let hParentIndex :=
        Nat.lt_trans
          (cert.contract.parents_before index hIndex link.parent hParentMem)
          hIndex
      cases hNode : cert.dag.node? link.parent with
      | none =>
          have hDag' := hDag
          unfold DAG.propLearnedInitialLinkOk at hDag'
          rw [hNode] at hDag'
          simp at hDag'
      | some parentNode =>
          cases hPayload : parentNode.payload with
          | propositionalLearnedClause payload =>
              have hNodeEq : parentNode =
                  cert.dag.nodeAt link.parent hParentIndex := by
                rw [cert.dag.node?_eq_some_nodeAt hParentIndex] at hNode
                exact (Option.some.inj hNode).symm
              have hPayloadAt :
                  (cert.dag.nodeAt link.parent hParentIndex).payload =
                    .propositionalLearnedClause payload := by
                rw [← hNodeEq]
                exact hPayload
              exact propLearnedClause_initial_satisfies M valuation cert compiled
                index hIndex assignment atomMap link initial payload hCheck
                hParents hParentIndex hPayloadAt hDag
          | _ =>
              have hDag' := hDag
              unfold DAG.propLearnedInitialLinkOk at hDag'
              rw [hNode] at hDag'
              simp [hPayload] at hDag'
  | avatarSkeleton link =>
      simp [PropInitialJustification.guardedSoundnessSupported] at hSupported

theorem initialSatisfies_of_justificationsListCheck
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (atomMap : Array (Formula σ))
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex)) :
    ∀ {initials : List PropResolution.InitialClause}
      {justifications : List (PropInitialJustification σ)},
      PropositionalClosurePayload.justificationsListCheck
        (cert.dag.nodeAt index hIndex).parents atomMap
        initials justifications = true →
      (∀ justification, justification ∈ justifications →
        cert.dag.propInitialJustificationDagOk
          (cert.dag.nodeAt index hIndex).parents justification = true) →
      (∀ justification, justification ∈ justifications →
        justification.guardedSoundnessSupported = true) →
      ∀ initial, initial ∈ initials →
        PropResolution.Clause.Satisfies
          (overlayValuation M assignment valuation atomMap) initial.clause := by
  intro initials
  induction initials with
  | nil =>
      intro justifications hCheck hDag hSupported target hTarget
      simp at hTarget
  | cons initial initials ih =>
      intro justifications
      cases justifications with
      | nil =>
          intro hCheck hDag hSupported target hTarget
          simp [PropositionalClosurePayload.justificationsListCheck] at hCheck
      | cons justification justifications =>
          intro hCheck hDag hSupported target hTarget
          have hCheckParts := Bool.and_eq_true_iff.mp hCheck
          have hHeadCheck := hCheckParts.1
          have hTailCheck := hCheckParts.2
          have hHeadDag := hDag justification (by simp)
          have hHeadSupported := hSupported justification (by simp)
          have hHeadSat := initialJustification_satisfies M valuation cert compiled
            index hIndex assignment atomMap justification initial hHeadCheck
            hHeadDag hHeadSupported hParents
          have hTailDag : ∀ item, item ∈ justifications →
              cert.dag.propInitialJustificationDagOk
                  (cert.dag.nodeAt index hIndex).parents item = true := by
            intro item hItem
            exact hDag item (by simp [hItem])
          have hTailSupported : ∀ item, item ∈ justifications →
              item.guardedSoundnessSupported = true := by
            intro item hItem
            exact hSupported item (by simp [hItem])
          rcases List.mem_cons.mp hTarget with rfl | hTarget
          · exact hHeadSat
          · exact ih hTailCheck hTailDag hTailSupported target hTarget

theorem residualCdcl_guardedNodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (assignment : Assignment M compiled.compilation.registry.context)
    (payload : PropositionalClosurePayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
      .residualCdcl payload)
    (hPayloadSupported : payload.guardedSoundnessSupported = true)
    (hParents : ∀ parent (hParent : parent ∈
        (cert.dag.nodeAt index hIndex).parents.toList),
      GuardedNodeTrueIn M valuation compiled parent
        (Nat.lt_trans
          (cert.contract.parents_before index hIndex parent hParent)
          hIndex)) :
    GuardedNodeTrueIn M valuation compiled index hIndex := by
  intro _hCurrent
  have hCheck := payloadCheck_of_payload_eq cert index hIndex hPayload
  have hResidualCheck :
      (!((cert.dag.nodeAt index hIndex).parents.isEmpty) &&
        (cert.dag.nodeAt index hIndex).conclusion.isEmpty &&
          payload.check (cert.dag.nodeAt index hIndex).parents) = true := by
    simpa [Payload.check, hPayload] using hCheck
  have hPayloadCheck : payload.check
      (cert.dag.nodeAt index hIndex).parents = true :=
    (Bool.and_eq_true_iff.mp hResidualCheck).2
  have hCheck₁ := Bool.and_eq_true_iff.mp hPayloadCheck
  have hCheck₂ := Bool.and_eq_true_iff.mp hCheck₁.1
  have hCheck₃ := Bool.and_eq_true_iff.mp hCheck₂.1
  have hCheck₄ := Bool.and_eq_true_iff.mp hCheck₃.1
  have hCheck₅ := Bool.and_eq_true_iff.mp hCheck₄.1
  have hCheck₆ := Bool.and_eq_true_iff.mp hCheck₅.1
  have hUnsat :
      PropResolution.checkedUnsat payload.initialClauses payload.proof = true :=
    hCheck₆.1
  have hJustifications :
      payload.justificationsCheck (cert.dag.nodeAt index hIndex).parents = true :=
    hCheck₆.2
  have hJustificationsList :=
    PropositionalClosurePayload.justificationsListCheck_eq_true_of_check
      hJustifications
  have hDagLinksAll :
      payload.initialJustifications.all (fun justification =>
        cert.dag.propInitialJustificationDagOk
          (cert.dag.nodeAt index hIndex).parents justification) = true := by
    have hLinks :=
      (cert.contract.node_contract index hIndex).prop_initial_links_checked
    simpa [DAG.propInitialLinksOk, hPayload] using hLinks
  have hDagLinks : ∀ justification,
      justification ∈ payload.initialJustifications.toList →
        cert.dag.propInitialJustificationDagOk
          (cert.dag.nodeAt index hIndex).parents justification = true := by
    intro justification hMem
    exact array_check_of_mem hDagLinksAll hMem
  have hSupportedAll :
      payload.initialJustifications.all
        PropInitialJustification.guardedSoundnessSupported = true := by
    simpa [PropositionalClosurePayload.guardedSoundnessSupported] using
      hPayloadSupported
  have hSupported : ∀ justification,
      justification ∈ payload.initialJustifications.toList →
        justification.guardedSoundnessSupported = true := by
    intro justification hMem
    exact array_check_of_mem hSupportedAll hMem
  have hInitial : ∀ initial,
      initial ∈ payload.initialClauses.toList →
        PropResolution.Clause.Satisfies
          (overlayValuation M assignment valuation payload.atomMap) initial.clause := by
    exact initialSatisfies_of_justificationsListCheck M valuation cert compiled
      index hIndex assignment payload.atomMap hParents hJustificationsList
      hDagLinks hSupported
  exact False.elim <|
    PropResolution.checkedUnsat_sound
      (valuation := overlayValuation M assignment valuation payload.atomMap)
      hInitial hUnsat

theorem parentGuardsHold_of_theoryConflictNodeGuardsOk
    (cert : CheckedDAG (σ := σ))
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : TheoryConflictPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
      .theoryConflict payload)
    (parent : NodeId)
    (hParentMem : parent ∈ (cert.dag.nodeAt index hIndex).parents.toList)
    (hParentIndex : parent < cert.dag.nodes.size)
    {valuation : PropResolution.Valuation}
    (hCurrent : GuardsHold valuation
      (cert.dag.nodeAt index hIndex).guards) :
    GuardsHold valuation (cert.dag.nodeAt parent hParentIndex).guards := by
  have hGuardCheck :=
    (cert.contract.node_contract index hIndex).guards_checked
  unfold DAG.localNodeGuardsOk at hGuardCheck
  have hLocalCheck :
      (match cert.dag.parentGuardUnion?
        (cert.dag.nodeAt index hIndex).parents with
      | some guards =>
          Guards.eq (cert.dag.nodeAt index hIndex).guards guards
      | none => false) = true := by
    simpa [hPayload] using! hGuardCheck
  cases hUnion : cert.dag.parentGuardUnion?
      (cert.dag.nodeAt index hIndex).parents with
  | none =>
      simp [hUnion] at hLocalCheck
  | some guards =>
      have hEq : Guards.eq (cert.dag.nodeAt index hIndex).guards guards = true := by
        simpa [hUnion] using hLocalCheck
      exact parentGuardsHold_of_union cert index hIndex parent hParentMem
        hParentIndex hUnion hCurrent hEq

theorem source_guardedNodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (initialIndex : Nat)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
      .source initialIndex)
    (hInitial : ∀ target ∈ compiled.compilation.initialClauses.toList,
      target.TrueIn M) :
    GuardedNodeTrueIn M valuation compiled index hIndex := by
  intro _hGuards
  exact source_trueIn M cert compiled hInitial index hIndex initialIndex
    (payloadCheck_of_payload_eq cert index hIndex hPayload)

theorem localRule_guardedNodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : LocalRulePayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
      .localRule payload)
    (hParents :
      ∀ parent (hParent : parent ∈
          (cert.dag.nodeAt index hIndex).parents.toList),
        GuardedNodeTrueIn M valuation compiled parent
          (Nat.lt_trans
            (cert.contract.parents_before index hIndex parent hParent)
            hIndex)) :
    GuardedNodeTrueIn M valuation compiled index hIndex := by
  intro hCurrent
  apply localRule_trueIn M cert compiled index hIndex payload hPayload
  intro parent hParentMem hParentIndex
  have hParentGuards :=
    parentGuardsHold_of_localNodeGuardsOk cert index hIndex payload
      hPayload parent hParentMem hParentIndex hCurrent
  exact hParents parent hParentMem hParentGuards

theorem theoryConflict_guardedNodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : TheoryConflictPayload σ)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
      .theoryConflict payload)
    (hParents :
      ∀ parent (hParent : parent ∈
          (cert.dag.nodeAt index hIndex).parents.toList),
        GuardedNodeTrueIn M valuation compiled parent
          (Nat.lt_trans
            (cert.contract.parents_before index hIndex parent hParent)
            hIndex)) :
    GuardedNodeTrueIn M valuation compiled index hIndex := by
  intro hCurrent
  have hCheck := payloadCheck_of_payload_eq cert index hIndex hPayload
  have hFields :
      payload.conflict.idIn (cert.dag.nodeAt index hIndex).parents = true ∧
        payload.conflict.clause.isEmpty = true ∧
          (cert.dag.nodeAt index hIndex).conclusion.isEmpty = true := by
    have hParts :=
      Bool.and_eq_true_iff.mp
        (show
          payload.conflict.idIn (cert.dag.nodeAt index hIndex).parents &&
              payload.conflict.clause.isEmpty &&
                (cert.dag.nodeAt index hIndex).conclusion.isEmpty = true by
          simpa [Payload.check, TheoryConflictPayload.check] using hCheck)
    have hPrefix := Bool.and_eq_true_iff.mp hParts.1
    have hConclusion :
        (cert.dag.nodeAt index hIndex).conclusion.isEmpty = true := by
      exact of_decide_eq_true hParts.2
    exact ⟨hPrefix.1, hPrefix.2, hConclusion⟩
  have hParentMem :
      payload.conflict.id ∈
        (cert.dag.nodeAt index hIndex).parents.toList :=
    ParentClause.mem_toList_of_idIn hFields.1
  let hParentIndex :=
    Nat.lt_trans
      (cert.contract.parents_before index hIndex payload.conflict.id
        hParentMem) hIndex
  have hSnapshot :=
    parentSnapshotChecked_of_payload_mem cert index hIndex hPayload
      (parent := payload.conflict)
      (by simp [Payload.parentClauses, TheoryConflictPayload.parentClauses])
  rcases DAG.parentSnapshotChecked_sound hSnapshot with
    ⟨snapshotNode, hSnapshotNode, hSnapshotClause⟩
  have hSnapshotNodeEq :
      snapshotNode = cert.dag.nodeAt payload.conflict.id hParentIndex := by
    rw [cert.dag.node?_eq_some_nodeAt hParentIndex] at hSnapshotNode
    exact (Option.some.inj hSnapshotNode).symm
  have hParentConclusion :
      (cert.dag.nodeAt payload.conflict.id hParentIndex).conclusion =
        payload.conflict.clause := by
    simpa [hSnapshotNodeEq] using hSnapshotClause
  have hParentRaw :
      (compiled.nodeAt payload.conflict.id hParentIndex).raw =
        payload.conflict.clause :=
    (compiled.nodeAt_raw payload.conflict.id hParentIndex).trans
      hParentConclusion
  have hParentGuards :=
    parentGuardsHold_of_theoryConflictNodeGuardsOk cert index hIndex
      payload hPayload payload.conflict.id hParentMem
      (show payload.conflict.id < cert.dag.nodes.size from
        Nat.lt_trans
          (cert.contract.parents_before index hIndex payload.conflict.id
            hParentMem) hIndex)
      hCurrent
  have hParentTrue :=
    hParents payload.conflict.id hParentMem hParentGuards
  exact False.elim <|
    compiledClause_not_trueIn_of_raw_empty M
      (compiled.nodeAt payload.conflict.id hParentIndex)
      (by rw [hParentRaw]; exact hFields.2.1) hParentTrue

theorem propositionalLearned_guardedNodeTrueIn
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (index : Nat) (hIndex : index < cert.dag.nodes.size)
    (payload : PropositionalLearnedClausePayload)
    (hPayload : (cert.dag.nodeAt index hIndex).payload =
      .propositionalLearnedClause payload)
    (hParents :
      ∀ parent (hParent : parent ∈
          (cert.dag.nodeAt index hIndex).parents.toList),
        GuardedNodeTrueIn M valuation compiled parent
          (Nat.lt_trans
            (cert.contract.parents_before index hIndex parent hParent)
            hIndex)) :
    GuardedNodeTrueIn M valuation compiled index hIndex := by
  intro hCurrent
  have hCheck := payloadCheck_of_payload_eq cert index hIndex hPayload
  have hPayloadCheck :
      PropositionalLearnedClausePayload.check
        (cert.dag.nodeAt index hIndex).parents payload
        (cert.dag.nodeAt index hIndex).conclusion = true := by
    simpa [Payload.check] using hCheck
  have hParentMem :
      payload.conflict ∈ (cert.dag.nodeAt index hIndex).parents.toList := by
    have hPrefix :
        (cert.dag.nodeAt index hIndex).parents.contains
          payload.conflict = true :=
      (Bool.and_eq_true_iff.mp
        (show
          (cert.dag.nodeAt index hIndex).parents.contains
              payload.conflict &&
            (cert.dag.nodeAt index hIndex).conclusion.isEmpty = true by
          simpa [PropositionalLearnedClausePayload.check] using hPayloadCheck)).1
    exact Array.mem_def.mp (by simpa using hPrefix)
  let hConflictIndex :=
    Nat.lt_trans
      (cert.contract.parents_before index hIndex payload.conflict hParentMem)
      hIndex
  have hGuardCheck :=
    (cert.contract.node_contract index hIndex).guards_checked
  unfold DAG.localNodeGuardsOk at hGuardCheck
  simp [hPayload] at hGuardCheck
  have hGuardData := hGuardCheck.2
  cases hConflictNode :
      cert.dag.node? payload.conflict with
  | none =>
      simp [hConflictNode] at hGuardCheck
  | some conflictNode =>
      have hConflictFields :
          conflictNode.theoryConflict &&
            Guards.eq (cert.dag.nodeAt index hIndex).guards
              conflictNode.guards &&
            (match conflictNode.payload with
            | .theoryConflict _ =>
                PropResolution.clauseEq payload.learned
                  (Guards.learnedClause conflictNode.guards)
            | _ => false) = true := by
        simpa [hConflictNode] using! hGuardData
      have hConflictParts := Bool.and_eq_true_iff.mp hConflictFields
      have hTheoryAndGuard := Bool.and_eq_true_iff.mp hConflictParts.1
      have hTheory : conflictNode.theoryConflict = true :=
        hTheoryAndGuard.1
      have hGuardEq : Guards.eq
          (cert.dag.nodeAt index hIndex).guards conflictNode.guards = true :=
        hTheoryAndGuard.2
      have hConflictCanonical :
          conflictNode = cert.dag.nodeAt payload.conflict hConflictIndex := by
        apply Option.some.inj
        rw [cert.dag.node?_eq_some_nodeAt hConflictIndex] at hConflictNode
        exact hConflictNode.symm
      subst conflictNode
      have hConflictGuards :=
        GuardsHold.of_eq hGuardEq hCurrent
      have hConflictTrue :=
        hParents payload.conflict hParentMem hConflictGuards
      have hConflictEmpty :
          (cert.dag.nodeAt payload.conflict hConflictIndex).conclusion.isEmpty =
            true :=
        (Node.theoryConflict_fields hTheory).2
      exact False.elim <|
        compiledClause_not_trueIn_of_raw_empty M
          (compiled.nodeAt payload.conflict hConflictIndex)
          (by
            rw [compiled.nodeAt_raw]
            exact hConflictEmpty) hConflictTrue

theorem guardedNodeTrueIn_of_supported
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (hInitial : ∀ target ∈ compiled.compilation.initialClauses.toList,
      target.TrueIn M)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    ∀ index (hIndex : index < cert.dag.nodes.size),
      GuardedNodeTrueIn M valuation compiled index hIndex := by
  refine cert.dag.topologicalInduction cert.contract.parents_before
    (P := fun index hIndex _ => GuardedNodeTrueIn M valuation compiled index hIndex) ?_
  intro index hIndex hParents
  have hNodeSupported :=
    DAG.guardedSoundnessSupported_of_eq_true hSupported index hIndex
  cases hPayload : (cert.dag.nodeAt index hIndex).payload with
  | source initialIndex =>
      exact source_guardedNodeTrueIn M valuation cert compiled index hIndex
        initialIndex hPayload hInitial
  | avatarSplit payload =>
      simp [hPayload, Payload.guardedSoundnessSupported] at hNodeSupported
  | avatarComponent payload =>
      simp [hPayload, Payload.guardedSoundnessSupported] at hNodeSupported
  | localRule payload =>
      exact localRule_guardedNodeTrueIn M valuation cert compiled index hIndex
        payload hPayload hParents
  | theoryConflict payload =>
      exact theoryConflict_guardedNodeTrueIn M valuation cert compiled index hIndex
        payload hPayload hParents
  | propositionalLearnedClause payload =>
      exact propositionalLearned_guardedNodeTrueIn M valuation cert compiled
        index hIndex payload hPayload hParents
  | residualCdcl payload =>
      have hPayloadSupported : payload.guardedSoundnessSupported = true := by
        simpa [hPayload, Payload.guardedSoundnessSupported] using hNodeSupported
      rcases assignmentNonempty M compiled.compilation.registry.context with
        ⟨assignment⟩
      exact residualCdcl_guardedNodeTrueIn M valuation cert compiled index hIndex
        assignment
        payload hPayload hPayloadSupported hParents

theorem rootNodeTrueIn_of_supported
    (M : Logic.FirstOrder.Structure.{0, 0, 0, x} σ)
    (valuation : PropResolution.Valuation)
    (cert : CheckedDAG (σ := σ))
    (compiled : Compile.CheckedDAGClauses cert.dag)
    (hInitial : ∀ target ∈ compiled.compilation.initialClauses.toList,
      target.TrueIn M)
    (hSupported : cert.dag.guardedSoundnessSupported = true) :
    NodeTrueIn M compiled cert.dag.root cert.contract.root_exists := by
  have hAll := guardedNodeTrueIn_of_supported M valuation cert compiled
    hInitial hSupported cert.dag.root cert.contract.root_exists
  have hRootUnguarded :
      (cert.dag.nodeAt cert.dag.root cert.contract.root_exists).guards.isEmpty = true := by
    simpa [Node.unguarded] using cert.contract.root_unguarded
  exact hAll (guardsHold_of_unguarded hRootUnguarded)

end IntrinsicReplay
end DAGCertificate
end Automation
end YesMetaZFC
