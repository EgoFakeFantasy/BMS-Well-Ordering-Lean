import Lean
import YesMetaZFC.Automation.FirstOrderDerives.TypedView
import YesMetaZFC.Logic.FirstOrder.Derivation.Equality
import YesMetaZFC.Logic.FirstOrder.Derivation.Quantifier
/-!
# 一阶 `Derives` 的命题模式重放
本模块处理外层已经是 `Derives T Γ φ` 的目标。它主要观察 `φ` 的命题连接词；
此外直接闭合自反等式，并可为存在目标选择 canonical free-variable witness。无法
继续展开的公式参数、关系原子和全称式仍保持为原子。纯命题骨架先只消费局部资源，
避免无关非空理论污染搜索；需要理论时，再按目标变量直接实例化全称事实，最后才运行
带事实预算的兼容饱和。搜索成功后直接组合 `Derives` 构造子及其结构规则，不经过
语义完备性，也不要求原子公式额外携带良构性证明。
这条路线适合元数理中的公式模式定理：公式参数可以像 FOOL 布尔原子一样参与搜索，
但最终证书仍留在原签名和原上下文中。
-/
namespace YesMetaZFC
namespace Automation
namespace FirstOrderDerives
open Lean Elab Tactic Meta
open TypedView
register_option prove_auto.derives.maxFuel : Nat := {
  defValue := 64
  descr := "maximum replay fuel for first-order Derives propositional patterns"
}
register_option prove_auto.derives.maxFacts : Nat := {
  defValue := 128
  descr := "fallback universal saturation fact limit; 0 disables the limit"
}
inductive SearchMode where
  | localOnly
  | withTheory
deriving Repr, BEq
private structure GoalView where
  signature : Expr
  decidableEq : Expr
  theory : Expr
  context : Expr
  formula : Expr
private def goal_view_from_arguments (arguments : Array Expr) :
    MetaM (Option GoalView) := do
  if arguments.size < 5 then
    return none
  return some {
    signature := arguments[0]!
    decidableEq := arguments[1]!
    theory := arguments[2]!
    context := arguments[3]!
    formula := arguments[4]!
  }
private def goal_view? (target : Expr) : MetaM (Option GoalView) := do
  let target ← instantiateMVars target
  if target.isAppOfArity ``Logic.FirstOrder.Derives 5 then
    return ← goal_view_from_arguments target.getAppArgs
  let target ← whnf target
  unless target.isAppOfArity ``Nonempty 1 do
    return none
  let payloadType ← whnf target.getAppArgs[0]!
  unless payloadType.isAppOfArity ``Logic.FirstOrder.ND_Checked 5 do
    return none
  goal_view_from_arguments payloadType.getAppArgs
private def same_expression (left right : Expr) : MetaM Bool := do
  if Expr.equal left right then
    return true
  withoutModifyingState do
    withTransparency .reducible <| isDefEq left right
private structure Fact where
  node : FormulaNode
  proof : Expr
private structure RawFact where
  formula : Expr
  proof : Expr
private structure TheoryMember where
  formula : Expr
  membership : Expr
private structure ReplayState where
  config : TypedView.Config
  theory : Expr
  context : Expr
  objectVariables : Array ObjectVariable := #[]
  facts : Array Fact := #[]
/-!
搜索帧只记录目标和可用公式事实，不记录不断增长但没有新增信息的重复上下文前缀。
这样可以剪掉重复引入同一假设造成的经典搜索回路。
-/
private inductive SearchTarget where
  | formula (raw : Expr) (allowClassical : Bool)
  | falsum (deriveNegativeBody : Bool)
private structure SearchFrame where
  facts : Array Fact
  target : SearchTarget
private def same_fact_surface (left right : Array Fact) : Bool :=
  left.size == right.size && (left.toList.zip right.toList).all fun (leftFact, rightFact) =>
      Expr.equal leftFact.node.raw rightFact.node.raw
private def same_search_target (left right : SearchTarget) : Bool :=
  match left, right with
  | .formula leftRaw leftClassical,
      .formula rightRaw rightClassical =>
      leftClassical == rightClassical &&
        Expr.equal leftRaw rightRaw
  | .falsum leftNegative, .falsum rightNegative =>
      leftNegative == rightNegative
  | _, _ =>
      false
private def SearchFrame.matches (left right : SearchFrame) : Bool :=
  same_search_target left.target right.target &&
    same_fact_surface left.facts right.facts
private def formula_shell_label : FormulaShell → String
  | .falsum => "falsum"
  | .truth => "truth"
  | .neg .. => "neg"
  | .conj .. => "conj"
  | .disj .. => "disj"
  | .imp .. => "imp"
  | .iff .. => "iff"
  | .forallE .. => "forall"
  | .existsE .. => "exists"
  | .equal .. => "equal"
  | .atom => "atom"
private inductive FormulaHead where
  | falsum
  | truth
  | neg
  | conj
  | disj
  | imp
  | iff
  | forallE
  | existsE
  | equal
  | atom
  deriving BEq, Inhabited
private def formula_head : FormulaShell → FormulaHead
  | .falsum => .falsum
  | .truth => .truth
  | .neg .. => .neg
  | .conj .. => .conj
  | .disj .. => .disj
  | .imp .. => .imp
  | .iff .. => .iff
  | .forallE .. => .forallE
  | .existsE .. => .existsE
  | .equal .. => .equal
  | .atom => .atom
private partial def forall_conclusion_head (node : FormulaNode) : FormulaHead :=
  match node.shell with
  | .forallE _ body =>
      forall_conclusion_head body
  | shell =>
      formula_head shell
private def delta_head? (expression : Expr) : MetaM (Option Expr) := do
  match expression.getAppFn with
  | .const declaration levels =>
      let info ← getConstInfo declaration
      let some value := info.value?
        | return none
      let value := value.instantiateLevelParams info.levelParams levels
      return some (value.beta expression.getAppArgs)
  | _ =>
      return none
private partial def expose_theory_head (theory : Expr) (fuel : Nat := 32) : MetaM Expr := do
  let theory ← zetaReduce (← instantiateMVars theory)
  if theory.isAppOfArity ``Logic.FirstOrder.Theory.empty 1 ||
      theory.isAppOfArity ``Logic.FirstOrder.Theory.singleton 2 ||
      theory.isAppOfArity ``Logic.FirstOrder.Theory.insert 3 ||
      fuel == 0 then
    return theory
  let some unfolded ← delta_head? theory
    | return theory
  expose_theory_head unfolded (fuel - 1)
private partial def collect_theory_members (theory : Expr) (fuel : Nat := 32) :
    MetaM (Array TheoryMember) := do
  if fuel == 0 then
    return #[]
  let exposed ← expose_theory_head theory fuel
  if exposed.isAppOfArity ``Logic.FirstOrder.Theory.empty 1 then
    return #[]
  if exposed.isAppOfArity ``Logic.FirstOrder.Theory.singleton 2 then
    let formula := exposed.getAppArgs[1]!
    let membership ← mkAppM ``Eq.refl #[formula]
    return #[{ formula, membership }]
  if exposed.isAppOfArity ``Logic.FirstOrder.Theory.insert 3 then
    let arguments := exposed.getAppArgs
    let formula := arguments[1]!
    let tail := arguments[2]!
    let equalityType ← mkAppM ``Eq #[formula, formula]
    let tailMembershipType := mkApp tail formula
    let equalityProof ← mkAppM ``Eq.refl #[formula]
    let headMembership :=
      mkApp3 (mkConst ``Or.inl)
        equalityType tailMembershipType equalityProof
    let mut members : Array TheoryMember :=
      #[{ formula, membership := headMembership }]
    for member in ← collect_theory_members tail (fuel - 1) do
      let equalityType ← mkAppM ``Eq #[member.formula, formula]
      let tailMembershipType := mkApp tail member.formula
      members := members.push {
        formula := member.formula
        membership :=
          mkApp3 (mkConst ``Or.inr)
            equalityType tailMembershipType member.membership
      }
    return members
  return #[]
private def ReplayState.find? (state : ReplayState) (node : FormulaNode) :
    MetaM (Option Expr) := do
  for fact in state.facts do
    if let some alignment ←
        fact.node.alignment_with? state.config node then
      return some (← cast_derives alignment fact.proof)
  return none
private def ReplayState.add_fact (state : ReplayState) (fact : Fact) :
    MetaM (ReplayState × Bool) := do
  if (← state.find? fact.node).isSome then
    return (state, false)
  else
    return ({ state with facts := state.facts.push fact }, true)
private def formula_admissible_type (config : TypedView.Config) (formula : Expr) : Expr :=
  mkAppN (mkConst ``Logic.FirstOrder.Formula.Admissible
      config.universeLevels)
    #[config.signature, config.decidableEq, formula]
private def local_proof_of_type? (target : Expr) :
    MetaM (Option Expr) := do
  for declaration in (← getLCtx) do
    if declaration.isImplementationDetail ||
        declaration.isAuxDecl ||
        declaration.binderInfo.isInstImplicit then
      continue
    let type ← instantiateMVars declaration.type
    if ← same_expression type target then
      return some (mkFVar declaration.fvarId)
  return none
/-- 把逻辑层 admissibility 转为内核消费的纯函数检查等式。 -/
private def check_certificate_of_admissible
    (hAdmissible : Expr) : MetaM Expr :=
  mkAppM ``Logic.FirstOrder.Formula.check_admissible_complete
    #[hAdmissible]
/-- 把项的排序与闭性证明封装为内核消费的纯函数检查证书。 -/
private def term_check_certificate_of_admissible
    (hAdmissible : Expr) : MetaM Expr :=
  mkAppM ``Logic.FirstOrder.Term.check_admissible_complete
    #[hAdmissible]
/--
为证书重放恢复公式 admissibility。
优先消费显式局部证书和已有 `Derives` 事实；随后从复合事实反演分量，最后才按
当前目标的命题结构逐层装配。量词体不被误当作空 scope 公式，原子与量词公式若无
外部证书会安全失败。
-/
private partial def ReplayState.admissibility? (state : ReplayState) (node : FormulaNode) (fuel : Nat := 64) :
    MetaM (Option Expr) := do
  if fuel == 0 then
    return none
  let targetType := formula_admissible_type state.config node.raw
  if let some proof ← local_proof_of_type? targetType then
    return some proof
  if let some proof ← state.find? node then
    return some <|
      ← mkAppM ``Logic.FirstOrder.Derives.admissible #[proof]
  for fact in state.facts do
    let hFact ←
      mkAppM ``Logic.FirstOrder.Derives.admissible #[fact.proof]
    let tryChild (child : FormulaNode) (projection : Name) :
        MetaM (Option Expr) := do
      let some alignment ←
          child.alignment_with? state.config node
        | return none
      let projected ← mkAppM projection #[hFact]
      return some (← cast_admissible alignment projected)
    match fact.node.shell with
    | .neg body =>
        if let some proof ←
            tryChild body ``Logic.FirstOrder.Formula.Admissible.neg_body then
          return some proof
    | .conj left right =>
        if let some proof ←
            tryChild left ``Logic.FirstOrder.Formula.Admissible.conj_left then
          return some proof
        if let some proof ←
            tryChild right ``Logic.FirstOrder.Formula.Admissible.conj_right then
          return some proof
    | .disj left right =>
        if let some proof ←
            tryChild left ``Logic.FirstOrder.Formula.Admissible.disj_left then
          return some proof
        if let some proof ←
            tryChild right ``Logic.FirstOrder.Formula.Admissible.disj_right then
          return some proof
    | .imp left right =>
        if let some proof ←
            tryChild left ``Logic.FirstOrder.Formula.Admissible.imp_left then
          return some proof
        if let some proof ←
            tryChild right ``Logic.FirstOrder.Formula.Admissible.imp_right then
          return some proof
    | .iff left right =>
        if let some proof ←
            tryChild left ``Logic.FirstOrder.Formula.Admissible.iff_left then
          return some proof
        if let some proof ←
            tryChild right ``Logic.FirstOrder.Formula.Admissible.iff_right then
          return some proof
    | _ =>
        pure ()
  match node.shell with
  | .falsum =>
      return some <|
        mkAppN (mkConst ``Logic.FirstOrder.Formula.Admissible.falsum
            state.config.universeLevels)
          #[state.config.signature, state.config.decidableEq]
  | .truth =>
      return some <|
        mkAppN (mkConst ``Logic.FirstOrder.Formula.Admissible.truth
            state.config.universeLevels)
          #[state.config.signature, state.config.decidableEq]
  | .neg body =>
      let some hBody ← state.admissibility? body (fuel - 1)
        | return none
      return some <|
        ← mkAppM ``Logic.FirstOrder.Formula.Admissible.neg #[hBody]
  | .conj left right =>
      let some hLeft ← state.admissibility? left (fuel - 1)
        | return none
      let some hRight ← state.admissibility? right (fuel - 1)
        | return none
      return some <|
        ← mkAppM ``Logic.FirstOrder.Formula.Admissible.conj
          #[hLeft, hRight]
  | .disj left right =>
      let some hLeft ← state.admissibility? left (fuel - 1)
        | return none
      let some hRight ← state.admissibility? right (fuel - 1)
        | return none
      return some <|
        ← mkAppM ``Logic.FirstOrder.Formula.Admissible.disj
          #[hLeft, hRight]
  | .imp left right =>
      let some hLeft ← state.admissibility? left (fuel - 1)
        | return none
      let some hRight ← state.admissibility? right (fuel - 1)
        | return none
      return some <|
        ← mkAppM ``Logic.FirstOrder.Formula.Admissible.imp
          #[hLeft, hRight]
  | .iff left right =>
      let some hLeft ← state.admissibility? left (fuel - 1)
        | return none
      let some hRight ← state.admissibility? right (fuel - 1)
        | return none
      return some <|
        ← mkAppM ``Logic.FirstOrder.Formula.Admissible.iff
          #[hLeft, hRight]
  | .forallE .. | .existsE .. | .equal .. | .atom =>
      return none
private def ReplayState.extend (state : ReplayState) (node : FormulaNode) :
    MetaM ReplayState := do
  let some hNode ← state.admissibility? node
    | throwError
        "cannot recover admissibility for introduced formula {node.raw}"
  let nextContext ← mkAppM ``List.cons #[node.raw, state.context]
  let mut nextFacts := #[]
  for fact in state.facts do
    let proof ←
      mkAppOptM ``Logic.FirstOrder.Derives.context_weaken_cons
        #[none, none, some state.theory, some state.context,
          some node.raw, some fact.node.raw, some fact.proof]
    nextFacts := nextFacts.push {
      node := fact.node
      proof
    }
  let membership ←
    mkAppOptM ``List.Mem.head
      #[none, some node.raw, some state.context]
  let hCheck ← check_certificate_of_admissible hNode
  let assumption ←
    mkAppOptM ``Logic.FirstOrder.Derives.assumption
      #[none, none, some state.theory, some nextContext,
        some node.raw, some membership, some hCheck]
  let next : ReplayState := {
    state with
    context := nextContext
    facts := nextFacts
  }
  return (← next.add_fact { node, proof := assumption }).1
private partial def saturate_conj_facts (state : ReplayState) (fuel : Nat) : MetaM ReplayState := do
  if fuel == 0 then
    return state
  let mut next := state
  let mut added := false
  for fact in state.facts do
    trace[YesMetaZFC.proveAuto.firstOrderDerives]
      "conj.saturate shell={formula_shell_label fact.node.shell}; \
      formula={fact.node.raw}"
    match fact.node.shell with
    | .conj left right =>
        let hLeft ←
          mkAppM ``Logic.FirstOrder.Derives.conjElimLeft #[fact.proof]
        let hRight ←
          mkAppM ``Logic.FirstOrder.Derives.conjElimRight #[fact.proof]
        let (afterLeft, leftAdded) ←
          next.add_fact { node := left, proof := hLeft }
        next := afterLeft
        let (afterRight, rightAdded) ←
          next.add_fact { node := right, proof := hRight }
        next := afterRight
        added := added || leftAdded || rightAdded
    | _ =>
        pure ()
  if added then
    saturate_conj_facts next (fuel - 1)
  else
    return next
private partial def discharge_context_prefix? (config : TypedView.Config) (theory : Expr) (targetContext resourceContext formula proof : Expr)
    (fuel : Nat := 64) :
    MetaM (Option RawFact) := do
  let resourceContext ← whnf (← instantiateMVars resourceContext)
  if ← same_expression resourceContext targetContext then
    return some { formula, proof }
  if fuel == 0 then
    return none
  unless resourceContext.isAppOfArity ``List.cons 3 do
    return none
  let arguments := resourceContext.getAppArgs
  let antecedent := arguments[1]!
  let tail := arguments[2]!
  let some fact ←
      discharge_context_prefix?
        config theory targetContext tail formula proof (fuel - 1)
    | return none
  let compiled ← compile_formula config antecedent
  let admissibilityState : ReplayState := {
    config
    theory
    context := tail
  }
  let some hAntecedentNormalized ←
      admissibilityState.admissibility? compiled.node
    | return none
  let hAntecedent ←
    cast_admissible (← mkEqSymm compiled.alignment) hAntecedentNormalized
  let hAntecedentCheck ←
    check_certificate_of_admissible hAntecedent
  let nextFormula ←
    mkAppM ``Logic.FirstOrder.Formula.imp #[antecedent, fact.formula]
  let nextProof ←
    mkAppM ``Logic.FirstOrder.Derives.impIntro
      #[fact.proof, hAntecedentCheck]
  return some { formula := nextFormula, proof := nextProof }
private def resource_fact? (config : TypedView.Config) (theory context : Expr) (resource : FVarId) :
    MetaM (Option RawFact) := do
  let proposition ← instantiateMVars (← resource.getType)
  let some view ← goal_view? proposition
    | return none
  unless ← same_expression view.theory theory do
    return none
  discharge_context_prefix?
    config theory context view.context view.formula (mkFVar resource)
private def collect_facts (config : TypedView.Config) (theory context : Expr) (resources : Array FVarId) :
    MetaM (Array RawFact) := do
  let mut facts := #[]
  for resource in resources do
    if let some fact ←
        resource_fact? config theory context resource then
      unless facts.any fun existing => Expr.equal existing.formula fact.formula do
        facts := facts.push fact
  return facts
private def collect_theory_facts (signature decidableEq : Expr) (universeLevels : List Level) (theory context : Expr) :
    MetaM (Array RawFact) := do
  let mut facts := #[]
  for member in ← collect_theory_members theory do
    let admissibilityType :=
      mkAppN (mkConst ``Logic.FirstOrder.Formula.Admissible
          universeLevels)
        #[signature, decidableEq, member.formula]
    if let some hAdmissible ←
        local_proof_of_type? admissibilityType then
      let hCheck ←
        check_certificate_of_admissible hAdmissible
      let proof ←
        mkAppOptM ``Logic.FirstOrder.Derives.theoryAxiom
          #[some signature, some decidableEq, some theory,
            some context, some member.formula,
            some member.membership, some hCheck]
      facts := facts.push {
        formula := member.formula
        proof
      }
  return facts
private def compile_facts (config : TypedView.Config) (rawFacts : Array RawFact) :
    MetaM (Array Fact) := do
  let mut facts := #[]
  for rawFact in rawFacts do
    let compiled ← compile_formula config rawFact.formula
    let node := compiled.node
    let proof ← cast_derives compiled.alignment rawFact.proof
    let mut found := false
    for existing in facts do
      if (← existing.node.alignment_with? config node).isSome then
        found := true
    unless found do
      facts := facts.push { node, proof }
  return facts
private def completed_proof? (proof : Expr) : MetaM (Option Expr) := do
  let proof ← instantiateMVars proof
  unless (← getMVarsNoDelayed proof).isEmpty do
    return none
  return some proof
private def attempt_proof (action : MetaM (Option Expr)) : MetaM (Option Expr) := do
  let savedState ← saveState
  try
    let result ← action
    let result ← result.mapM completed_proof?
    savedState.restore
    return result.bind id
  catch error =>
    savedState.restore
    trace[YesMetaZFC.proveAuto.firstOrderDerives]
      "candidate failed: {error.toMessageData}"
    return none
private partial def saturate_forall_facts (state : ReplayState) (fuel maxFacts : Nat) :
    MetaM ReplayState := do
  if fuel == 0 || state.objectVariables.isEmpty || (maxFacts != 0 && state.facts.size >= maxFacts) then
    return state
  let mut next := state
  let mut added := false
  for fact in state.facts do
    match fact.node.shell with
    | .forallE sort body =>
      for candidate in state.objectVariables do
        if ← atomic_eq candidate.sort sort then
          if let some proof ← attempt_proof do
              return some <|
                mkAppN (mkConst
                    ``Logic.FirstOrder.Derives.forall_elim_fvar
                    state.config.universeLevels)
                  #[state.config.signature, state.config.decidableEq,
                    state.theory, state.context, sort,
                    candidate.id, body.raw, fact.proof] then
            let opened ←
              body.open_at
                state.config sort 0 candidate.term candidate.key
            let proof ← cast_derives opened.alignment proof
            trace[YesMetaZFC.proveAuto.firstOrderDerives]
              "forall.saturate candidate={candidate.id}; \
              opened={opened.node.raw}"
            let (after, wasAdded) ←
              next.add_fact { node := opened.node, proof }
            next := after
            added := added || wasAdded
            if maxFacts != 0 && next.facts.size >= maxFacts then
              trace[YesMetaZFC.proveAuto.firstOrderDerives]
                "forall saturation fact limit reached; facts={next.facts.size}"
              return next
    | _ =>
        pure ()
  if added then
    saturate_forall_facts next (fuel - 1) maxFacts
  else
    return next
/-!
只沿目标中已经出现的对象变量实例化一个全称事实。中间实例不加入全局事实面；
只有最终公式与目标对齐时才返回完整 `Derives` 证书。
-/
private partial def specialize_forall_fact_to_target? (state : ReplayState) (fact : Fact) (target : FormulaNode) (fuel : Nat) : MetaM (Option Expr) := do
  if let some alignment ←
      fact.node.alignment_with? state.config target then
    return some (← cast_derives alignment fact.proof)
  if fuel == 0 then
    return none
  unless forall_conclusion_head fact.node ==
      forall_conclusion_head target do
    return none
  let .forallE sort body := fact.node.shell
    | return none
  for candidate in state.objectVariables do
    if ← atomic_eq candidate.sort sort then
      if let some proof ← attempt_proof do
          let specialized :=
            mkAppN (mkConst
                ``Logic.FirstOrder.Derives.forall_elim_fvar
                state.config.universeLevels)
              #[state.config.signature, state.config.decidableEq,
                state.theory, state.context, sort,
                candidate.id, body.raw, fact.proof]
          let opened ←
            body.open_at
              state.config sort 0 candidate.term candidate.key
          let specialized ←
            cast_derives opened.alignment specialized
          specialize_forall_fact_to_target?
            state { node := opened.node, proof := specialized }
            target (fuel - 1) then
        trace[YesMetaZFC.proveAuto.firstOrderDerives]
          "forall.target candidate={candidate.id}; target={target.raw}"
        return some proof
  return none
private def specialize_forall_facts_to_target? (state : ReplayState) (target : FormulaNode) (fuel : Nat) :
    MetaM (Option Expr) := do
  for fact in state.facts do
    if let some proof ←
        specialize_forall_fact_to_target? state fact target fuel then
      return some proof
  return none
mutual
  private partial def derive_formula? (state : ReplayState) (formula : FormulaNode) (fuel : Nat) (allowClassical : Bool := true)
      (active : Array SearchFrame := #[]) :
      MetaM (Option Expr) := do
    if fuel == 0 then
      return none
    let frame : SearchFrame := {
      facts := state.facts
      target := .formula formula.raw allowClassical
    }
    if active.any fun candidate => candidate.matches frame then
      trace[YesMetaZFC.proveAuto.firstOrderDerives]
        "derive cycle cut; formula={formula.raw}"
      return none
    let active := active.push frame
    trace[YesMetaZFC.proveAuto.firstOrderDerives]
      "derive shell={formula_shell_label formula.shell}; formula={formula.raw}"
    if let some proof ← state.find? formula then
      trace[YesMetaZFC.proveAuto.firstOrderDerives]
        "derive fact hit"
      return some proof
    if let some (_, hFormula) ←
        formula.equality_reflexive_alignment? state.config then
      trace[YesMetaZFC.proveAuto.firstOrderDerives]
        "derive equality sameTerms=true"
      let .equal leftNode _ := formula.shell
        | return none
      if let some checked ←
          leftNode.checked_admissibility? state.config then
        if let some proof ← attempt_proof do
            let hAdmissible ←
              mkAppM ``And.intro
                #[checked.wellSorted, checked.boundClosed]
            let hCheck ←
              term_check_certificate_of_admissible hAdmissible
            let reflexive :=
              mkAppN (mkConst
                  ``Logic.FirstOrder.Derives.eq_refl_m
                  state.config.universeLevels)
                #[state.config.signature, state.config.decidableEq,
                  state.theory, state.context, checked.sort, checked.term,
                  hCheck]
            let equalConstructor :=
              mkApp (mkConst ``Logic.FirstOrder.Formula.equal
                  state.config.universeLevels)
                state.config.signature
            let hLeftFunction ←
              mkCongrArg equalConstructor checked.alignment
            let hBoth ← mkCongr hLeftFunction checked.alignment
            let hNormalized ← mkEqSymm hBoth
            let hTarget ← mkEqTrans hNormalized hFormula
            let casted ← cast_derives hTarget reflexive
            return some casted then
          trace[YesMetaZFC.proveAuto.firstOrderDerives]
            "derive equality proof accepted"
          return some proof
    if let some proof ←
        specialize_forall_facts_to_target? state formula fuel then
      trace[YesMetaZFC.proveAuto.firstOrderDerives]
        "derive forall target hit"
      return some proof
    if let .existsE sort body := formula.shell then
      if let some proof ← attempt_proof do
          let some hExistential ← state.admissibility? formula
            | return none
          let witnessId := mkNatLit 0
          let witness :=
            state.config.mk_fvar_term sort witnessId
          let opened ←
            body.open_at state.config sort 0 witness (.fvar sort witnessId)
          trace[YesMetaZFC.proveAuto.firstOrderDerives]
            "derive exists opened={opened.node.raw}; \
            shell={formula_shell_label opened.node.shell}"
          let some hOpened ←
              derive_formula? state opened.node (fuel - 1)
                allowClassical active
            | trace[YesMetaZFC.proveAuto.firstOrderDerives]
                "derive exists body failed"
              return none
          let hOpened ←
            cast_derives (← mkEqSymm opened.alignment) hOpened
          return some <|
            mkAppN (mkConst
                ``Logic.FirstOrder.Derives.exists_intro_fvar
                state.config.universeLevels)
              #[state.config.signature, state.config.decidableEq,
                state.theory, state.context, sort, witnessId,
                body.raw, hExistential, hOpened] then
        trace[YesMetaZFC.proveAuto.firstOrderDerives]
          "derive exists proof accepted"
        return some proof
    match formula.shell with
    | .truth =>
        attempt_proof do
          return some <|
            ← mkAppOptM ``Logic.FirstOrder.Derives.truthIntro
              #[none, none, some state.theory, some state.context]
    | .falsum =>
        derive_false? state (fuel - 1) true active
    | .conj left right =>
        if let some proof ← attempt_proof do
            let some hLeft ←
                derive_formula? state left (fuel - 1)
                  allowClassical active
              | return none
            let some hRight ←
                derive_formula? state right (fuel - 1)
                  allowClassical active
              | return none
            return some <|
              ← mkAppM ``Logic.FirstOrder.Derives.conjIntro #[hLeft, hRight] then
          return some proof
        derive_from_facts? state formula fuel allowClassical active
    | .imp antecedent consequent =>
        if let some proof ← attempt_proof do
            let some hAntecedent ← state.admissibility? antecedent
              | return none
            let hAntecedentCheck ←
              check_certificate_of_admissible hAntecedent
            let next ← state.extend antecedent
            let some body ←
                derive_formula? next consequent (fuel - 1)
                  allowClassical active
              | return none
            return some <|
              ← mkAppM ``Logic.FirstOrder.Derives.impIntro
                #[body, hAntecedentCheck] then
          return some proof
        derive_from_facts? state formula fuel allowClassical active
    | .iff left right =>
        if let some proof ← attempt_proof do
            let forwardState ← state.extend left
            let some forward ←
                derive_formula? forwardState right (fuel - 1)
                  allowClassical active
              | return none
            let backwardState ← state.extend right
            let some backward ←
                derive_formula? backwardState left (fuel - 1)
                  allowClassical active
              | return none
            return some <|
              ← mkAppM ``Logic.FirstOrder.Derives.iffIntro
                #[forward, backward] then
          return some proof
        derive_from_facts? state formula fuel allowClassical active
    | .neg body =>
        if let some proof ← attempt_proof do
            let some hBody ← state.admissibility? body
              | return none
            let hBodyCheck ←
              check_certificate_of_admissible hBody
            let next ← state.extend body
            let some contradiction ←
                derive_false? next (fuel - 1) true active
              | return none
            return some <|
              ← mkAppM ``Logic.FirstOrder.Derives.negIntro
                #[contradiction, hBodyCheck] then
          return some proof
        derive_from_facts? state formula fuel allowClassical active
    | .disj left right =>
        if let some proof ← attempt_proof do
            let some hRightAdmissible ← state.admissibility? right
              | return none
            let hRightCheck ←
              check_certificate_of_admissible hRightAdmissible
            let some hLeft ←
                derive_formula? state left (fuel - 1) false active
              | return none
            return some <|
                ← mkAppOptM ``Logic.FirstOrder.Derives.disjIntroLeft
                  #[none, none, some state.theory, some state.context,
                    some left.raw, some right.raw,
                    some hLeft, some hRightCheck] then
          return some proof
        if let some proof ← attempt_proof do
            let some hLeftAdmissible ← state.admissibility? left
              | return none
            let hLeftCheck ←
              check_certificate_of_admissible hLeftAdmissible
            let some hRight ←
                derive_formula? state right (fuel - 1) false active
              | return none
            return some <|
                ← mkAppOptM ``Logic.FirstOrder.Derives.disjIntroRight
                  #[none, none, some state.theory, some state.context,
                    some left.raw, some right.raw,
                    some hRight, some hLeftCheck] then
          return some proof
        if allowClassical then
          if let some proof ← attempt_proof do
              let some hLeftAdmissible ← state.admissibility? left
                | return none
              let some hRightAdmissible ← state.admissibility? right
                | return none
              let hRightCheck ←
                check_certificate_of_admissible hRightAdmissible
              let hLeftCheck ←
                check_certificate_of_admissible hLeftAdmissible
              let negatedLeft := left.neg state.config
              let hCases :=
                mkAppN (mkConst
                    ``Logic.FirstOrder.Derives.excluded_middle_m
                    state.config.universeLevels)
                  #[state.config.signature, state.config.decidableEq,
                    state.theory, state.context, left.raw,
                    hLeftCheck]
              let positiveState ← state.extend left
              let some hPositiveLeft ← positiveState.find? left
                | return none
              let hPositive ←
                mkAppOptM ``Logic.FirstOrder.Derives.disjIntroLeft
                  #[none, none, some state.theory,
                    some positiveState.context, some left.raw,
                    some right.raw, some hPositiveLeft,
                    some hRightCheck]
              let negativeState ← state.extend negatedLeft
              let some hNegativeRight ←
                  derive_formula? negativeState right (fuel - 1)
                    true active
                | return none
              let hNegative ←
                mkAppOptM ``Logic.FirstOrder.Derives.disjIntroRight
                  #[none, none, some state.theory,
                    some negativeState.context, some left.raw,
                    some right.raw, some hNegativeRight,
                    some hLeftCheck]
              return some <|
                ← mkAppM ``Logic.FirstOrder.Derives.disjElim
                  #[hCases, hPositive, hNegative] then
            return some proof
        derive_from_facts? state formula fuel allowClassical active
    | .forallE .. | .existsE .. | .equal .. | .atom =>
        let state ← saturate_conj_facts state (fuel - 1)
        if let some proof ← state.find? formula then
          return some proof
        if allowClassical then
          if let some proof ← attempt_proof do
              let some hFormula ← state.admissibility? formula
                | return none
              let hFormulaCheck ←
                check_certificate_of_admissible hFormula
              let negated := formula.neg state.config
              let next ← state.extend negated
              let some contradiction ←
                  derive_false? next (fuel - 1) true active
                | return none
              return some <|
                ← mkAppOptM ``Logic.FirstOrder.Derives.byContradiction
                  #[none, none, some state.theory, some state.context,
                    some formula.raw, some contradiction,
                    some hFormulaCheck] then
            return some proof
        derive_from_facts? state formula fuel false active
  private partial def derive_from_facts? (state : ReplayState) (formula : FormulaNode) (fuel : Nat) (allowClassical : Bool) (active : Array SearchFrame) :
      MetaM (Option Expr) := do
    if fuel == 0 then
      return none
    for fact in state.facts do
      match fact.node.shell with
      | .conj left right =>
          if let some proof ← attempt_proof do
              let hLeft ←
                mkAppM ``Logic.FirstOrder.Derives.conjElimLeft #[fact.proof]
              let hRight ←
                mkAppM ``Logic.FirstOrder.Derives.conjElimRight #[fact.proof]
              let (next, addedLeft) ←
                state.add_fact { node := left, proof := hLeft }
              let (next, addedRight) ←
                next.add_fact { node := right, proof := hRight }
              if !addedLeft && !addedRight then
                return none
              derive_formula? next formula (fuel - 1)
                allowClassical active then
            return some proof
      | .imp antecedent consequent =>
          if let some proof ← attempt_proof do
              let some hAntecedent ←
                  derive_formula? state antecedent (fuel - 1)
                    false active
                | return none
              let hConsequent ←
                mkAppM ``Logic.FirstOrder.Derives.impElim
                  #[fact.proof, hAntecedent]
              let (next, added) ←
                state.add_fact {
                  node := consequent
                  proof := hConsequent
                }
              unless added do
                return none
              derive_formula? next formula (fuel - 1)
                allowClassical active then
            return some proof
      | .iff left right =>
          if let some proof ← attempt_proof do
              let some hLeft ←
                  derive_formula? state left (fuel - 1)
                    false active
                | return none
              let hRight ←
                mkAppM ``Logic.FirstOrder.Derives.iffElimRight
                  #[fact.proof, hLeft]
              let (next, added) ←
                state.add_fact { node := right, proof := hRight }
              unless added do
                return none
              derive_formula? next formula (fuel - 1)
                allowClassical active then
            return some proof
          if let some proof ← attempt_proof do
              let some hRight ←
                  derive_formula? state right (fuel - 1)
                    false active
                | return none
              let hLeft ←
                mkAppM ``Logic.FirstOrder.Derives.iffElimLeft
                  #[fact.proof, hRight]
              let (next, added) ←
                state.add_fact { node := left, proof := hLeft }
              unless added do
                return none
              derive_formula? next formula (fuel - 1)
                allowClassical active then
            return some proof
      | .disj left right =>
          if let some proof ← attempt_proof do
              let leftState ← state.extend left
              let some hLeft ←
                  derive_formula? leftState formula (fuel - 1)
                    allowClassical active
                | return none
              let rightState ← state.extend right
              let some hRight ←
                  derive_formula? rightState formula (fuel - 1)
                    allowClassical active
                | return none
              return some <|
                ← mkAppM ``Logic.FirstOrder.Derives.disjElim
                  #[fact.proof, hLeft, hRight] then
            return some proof
      | .neg inner =>
          match inner.shell with
          | .neg body =>
              if let some proof ← attempt_proof do
                  let hBody ←
                    mkAppM ``Logic.FirstOrder.Derives.neg_neg_elim_m
                      #[fact.proof]
                  let (next, added) ←
                    state.add_fact { node := body, proof := hBody }
                  unless added do
                    return none
                  derive_formula? next formula (fuel - 1)
                    allowClassical active then
                return some proof
          | _ =>
              pure ()
      | .falsum | .truth | .forallE .. | .existsE .. | .equal .. | .atom =>
          pure ()
    if let some contradiction ←
        derive_false? state (fuel - 1) allowClassical active then
      if let some proof ← attempt_proof do
          let some hFormula ← state.admissibility? formula
            | return none
          let hFormulaCheck ←
            check_certificate_of_admissible hFormula
          return some <|
            ← mkAppOptM ``Logic.FirstOrder.Derives.falsumElim
              #[none, none, some state.theory, some state.context,
                some formula.raw, some contradiction,
                some hFormulaCheck] then
        return some proof
    unless allowClassical do
      return none
    attempt_proof do
      let some hFormula ← state.admissibility? formula
        | return none
      let hFormulaCheck ←
        check_certificate_of_admissible hFormula
      let negated := formula.neg state.config
      let next ← state.extend negated
      let some contradiction ←
          derive_false? next (fuel - 1) true active
        | return none
      return some <|
        ← mkAppOptM ``Logic.FirstOrder.Derives.byContradiction
          #[none, none, some state.theory, some state.context,
            some formula.raw, some contradiction,
            some hFormulaCheck]
  private partial def derive_false? (state : ReplayState) (fuel : Nat) (deriveNegativeBody : Bool := true) (active : Array SearchFrame := #[]) :
      MetaM (Option Expr) := do
    if fuel == 0 then
      return none
    let frame : SearchFrame := {
      facts := state.facts
      target := .falsum deriveNegativeBody
    }
    if active.any fun candidate => candidate.matches frame then
      trace[YesMetaZFC.proveAuto.firstOrderDerives]
        "derive falsum cycle cut"
      return none
    let active := active.push frame
    for fact in state.facts do
      match fact.node.shell with
      | .falsum =>
          return some fact.proof
      | .neg body =>
          if let some hBody ← state.find? body then
            return ← attempt_proof do
              return some <|
                ← mkAppM ``Logic.FirstOrder.Derives.negElim
                  #[hBody, fact.proof]
      | _ =>
          pure ()
    for fact in state.facts do
      match fact.node.shell with
      | .neg body =>
          if deriveNegativeBody then
            if let some proof ← attempt_proof do
                let some hBody ←
                    derive_formula? state body (fuel - 1)
                      true active
                  | return none
                return some <|
                  ← mkAppM ``Logic.FirstOrder.Derives.negElim
                    #[hBody, fact.proof] then
              return some proof
      | .conj left right =>
          if let some proof ← attempt_proof do
              let hLeft ←
                mkAppM ``Logic.FirstOrder.Derives.conjElimLeft #[fact.proof]
              let hRight ←
                mkAppM ``Logic.FirstOrder.Derives.conjElimRight #[fact.proof]
              let (next, addedLeft) ←
                state.add_fact { node := left, proof := hLeft }
              let (next, addedRight) ←
                next.add_fact { node := right, proof := hRight }
              if !addedLeft && !addedRight then
                return none
              derive_false? next (fuel - 1)
                deriveNegativeBody active then
            return some proof
      | .imp antecedent consequent =>
          if let some proof ← attempt_proof do
              let some hAntecedent ←
                  derive_formula? state antecedent (fuel - 1)
                    false active
                | return none
              let hConsequent ←
                mkAppM ``Logic.FirstOrder.Derives.impElim
                  #[fact.proof, hAntecedent]
              let (next, added) ←
                state.add_fact {
                  node := consequent
                  proof := hConsequent
                }
              unless added do
                return none
              derive_false? next (fuel - 1)
                deriveNegativeBody active then
            return some proof
      | .iff left right =>
          if let some proof ← attempt_proof do
              let some hLeft ←
                  derive_formula? state left (fuel - 1)
                    false active
                | return none
              let hRight ←
                mkAppM ``Logic.FirstOrder.Derives.iffElimRight
                  #[fact.proof, hLeft]
              let (next, added) ←
                state.add_fact { node := right, proof := hRight }
              unless added do
                return none
              derive_false? next (fuel - 1)
                deriveNegativeBody active then
            return some proof
          if let some proof ← attempt_proof do
              let some hRight ←
                  derive_formula? state right (fuel - 1)
                    false active
                | return none
              let hLeft ←
                mkAppM ``Logic.FirstOrder.Derives.iffElimLeft
                  #[fact.proof, hRight]
              let (next, added) ←
                state.add_fact { node := left, proof := hLeft }
              unless added do
                return none
              derive_false? next (fuel - 1)
                deriveNegativeBody active then
            return some proof
      | .disj left right =>
          if let some proof ← attempt_proof do
              let leftState ← state.extend left
              let some hLeft ←
                  derive_false? leftState (fuel - 1)
                    deriveNegativeBody active
                | return none
              let rightState ← state.extend right
              let some hRight ←
                  derive_false? rightState (fuel - 1)
                    deriveNegativeBody active
                | return none
              return some <|
                ← mkAppM ``Logic.FirstOrder.Derives.disjElim
                  #[fact.proof, hLeft, hRight] then
            return some proof
      | .falsum | .truth | .forallE .. | .existsE .. | .equal .. | .atom =>
          pure ()
    return none
end
/--
尝试闭合一个 `Derives T Γ φ` 命题模式目标。
返回 `false` 表示目标不是 `Derives`，或当前有界命题重放未找到证明；调用方可以继续
尝试其他 focused sequent 规则和 checked provider。
-/
unsafe def try_close (goal : MVarId) (resources : Array FVarId) (mode : SearchMode := .withTheory) :
    MetaM Bool := goal.withContext do
  let options ← getOptions
  let fuel := prove_auto.derives.maxFuel.get options
  let maxFacts := prove_auto.derives.maxFacts.get options
  let target ← instantiateMVars (← goal.getType)
  let some view ← goal_view? target
    | return false
  let signatureType ← whnf (← inferType view.signature)
  let universeLevels ←
    match signatureType.getAppFn with
    | .const _ levels =>
        pure levels
    | _ =>
      throwError
          "first-order Derives signature has unexpected type {signatureType}"
  let config : TypedView.Config := {
    signature := view.signature
    decidableEq := view.decidableEq
    universeLevels
  }
  let targetCompiled ← compile_formula config view.formula
  let targetNode := targetCompiled.node
  let resourceRawFacts ←
    collect_facts config view.theory view.context resources
  let resourceFacts ← compile_facts config resourceRawFacts
  let objectVariables ←
    targetNode.collect_variables config
  let resourceState : ReplayState := {
    config
    theory := view.theory
    context := view.context
    objectVariables
    facts := resourceFacts
  }
  let mut proof? : Option Expr := none
  let mut usedFactCount := resourceFacts.size
  trace[YesMetaZFC.proveAuto.firstOrderDerives]
    "start phase=local; target={view.formula}; \
    resources={resources.size}; facts={resourceFacts.size}; \
    variables={objectVariables.size}; fuel={fuel}; maxFacts={maxFacts}"
  proof? ← derive_formula? resourceState targetNode fuel
  if proof?.isNone && mode == .withTheory then
    let mut rawFacts := resourceRawFacts
    for fact in ←
        collect_theory_facts
          view.signature view.decidableEq universeLevels
          view.theory view.context do
      unless rawFacts.any fun existing =>
          Expr.equal existing.formula fact.formula do
        rawFacts := rawFacts.push fact
    let facts ← compile_facts config rawFacts
    usedFactCount := facts.size
    trace[YesMetaZFC.proveAuto.firstOrderDerives]
      "start phase=theory; target={view.formula}; \
      resources={resources.size}; facts={facts.size}; \
      variables={objectVariables.size}; fuel={fuel}; maxFacts={maxFacts}"
    let state : ReplayState := {
      config
      theory := view.theory
      context := view.context
      objectVariables
      facts
    }
    let directProof? ← derive_formula? state targetNode fuel
    proof? ←
      match directProof? with
      | some proof =>
          pure (some proof)
      | none =>
          let saturatedState ←
            saturate_forall_facts state fuel maxFacts
          usedFactCount := saturatedState.facts.size
          if same_fact_surface saturatedState.facts state.facts then
            pure none
          else
            trace[YesMetaZFC.proveAuto.firstOrderDerives]
              "retry after forall saturation; facts={saturatedState.facts.size}"
            derive_formula? saturatedState targetNode fuel
  let some proof := proof?
    | trace[YesMetaZFC.proveAuto.firstOrderDerives]
        "no proof found for {view.formula}"
      return false
  let proof ←
    instantiateMVars <|
      ← cast_derives (← mkEqSymm targetCompiled.alignment) proof
  unless (← getMVarsNoDelayed proof).isEmpty do
    trace[YesMetaZFC.proveAuto.firstOrderDerives]
      "proof contains unresolved metavariables"
    return false
  let proofType ← inferType proof
  unless ← withTransparency .all <| isDefEq proofType target do
    trace[YesMetaZFC.proveAuto.firstOrderDerives]
      "final proof type mismatch; proofType={proofType}; target={target}"
    return false
  goal.assign proof
  trace[YesMetaZFC.proveAuto.firstOrderDerives]
    "closed target={view.formula}; facts={usedFactCount}"
  return true
private def local_proof_resources : MetaM (Array FVarId) := do
  let mut resources := #[]
  for declaration in (← getLCtx) do
    if declaration.isLet || declaration.isImplementationDetail ||
        declaration.isAuxDecl || declaration.binderInfo.isInstImplicit then
      continue
    let proposition ← instantiateMVars declaration.type
    if proposition.hasMVar || !(← isProp proposition) then
      continue
    resources := resources.push declaration.fvarId
  return resources
private unsafe def run_user_tactic (label : String) (mode : SearchMode) : TacticM Unit := do
  let savedState ← saveState
  let goal ← getMainGoal
  let target ← withMainContext <| instantiateMVars (← getMainTarget)
  let resources ← withMainContext local_proof_resources
  try
    if ← try_close goal resources mode then
      replaceMainGoal []
    else
      throwError
        "{label} failed to close the Derives goal{indentExpr target}"
  catch error =>
    savedState.restore
    throw error
/--
只消费局部 `Derives` 证明，重放当前目标的经典命题骨架。
该入口不会读取背景理论，也不会回退到完整 `prove_auto`。
-/
syntax (name := deriveProp) "derive_prop" : tactic
/--
在局部命题重放失败后，允许实例化背景理论中的全称事实。
该入口仍只运行 `FirstOrderDerives` 小证明器，不调用宿主相继式或外部 provider。
-/
syntax (name := derivePropTheory) "derive_prop_theory" : tactic
@[tactic deriveProp] unsafe def eval_derive_prop : Tactic :=
  fun _ => run_user_tactic "derive_prop" .localOnly
@[tactic derivePropTheory] unsafe def eval_derive_prop_theory : Tactic :=
  fun _ => run_user_tactic "derive_prop_theory" .withTheory
end FirstOrderDerives
end Automation
end YesMetaZFC
