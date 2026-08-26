import Lean
import YesMetaZFC.Logic.FirstOrder.Derivation.Core
import YesMetaZFC.Logic.FirstOrder.Admissibility
/-!
# 一阶自动化的类型化公式视图
本模块把任意一阶签名上的原始 `Term` / `Formula` 投影为轻量类型化视图。sort、
函数符号和关系符号保留其原签名中的 Lean 表达式身份，不编码到固定的自动化签名。
`openAt`、`closeFreeAt` 与 `substituteFree` 不在公式层递归归约；编译器只记录惰性
变换环境，穿过量词时调整对应 sort 的深度，并在抵达 `Term.var` / `Term.app`
边界后才执行。这样公式等价比较只需要检查类型化原子，而不会强迫 Lean 展开整棵
原始公式 AST。
-/
namespace YesMetaZFC
namespace Automation
namespace FirstOrderDerives
namespace TypedView
open Lean Meta
initialize registerTraceClass `YesMetaZFC.proveAuto.firstOrderDerives
universe u v w
theorem derives_cast_formula
    {σ : Logic.Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {T : Logic.FirstOrder.Theory σ} {Γ : Logic.FirstOrder.Context σ}
    {φ ψ : Logic.FirstOrder.Formula σ} (hFormula : φ = ψ) (proof : Logic.FirstOrder.Derives T Γ φ) :
    Logic.FirstOrder.Derives T Γ ψ := by
  cases hFormula
  exact proof
/-- 沿公式等式运输 admissibility 证书。 -/
theorem admissible_cast_formula
    {σ : Logic.Signature.{u, v, w}} [DecidableEq σ.SortSymbol]
    {φ ψ : Logic.FirstOrder.Formula σ} (hFormula : φ = ψ) (proof : Logic.FirstOrder.Formula.Admissible φ) :
    Logic.FirstOrder.Formula.Admissible ψ := by
  cases hFormula
  exact proof
structure Config where
  signature : Expr
  decidableEq : Expr
  universeLevels : List Level
inductive PendingTransform where
  | openAt (sort : Expr) (depth : Nat) (replacement : Expr)
  | closeFreeAt (sort id : Expr) (depth : Nat)
  | substituteFree (sort id replacement : Expr)
mutual
  inductive TermKey where
    | bvar (sort : Expr) (index : Nat)
    | fvar (sort id : Expr)
    | app (function : Expr) (arguments : TermListKey)
    | opaque (raw : Expr)
  inductive TermListKey where
    | nil
    | cons (head : TermKey) (tail : TermListKey)
    | opaque (raw : Expr)
end
inductive FormulaKey where
  | falsum
  | truth
  | rel (relation : Expr) (arguments : TermListKey)
  | equal (left right : TermKey)
  | neg (body : FormulaKey)
  | conj (left right : FormulaKey)
  | disj (left right : FormulaKey)
  | imp (left right : FormulaKey)
  | iff (left right : FormulaKey)
  | forallE (sort : Expr) (body : FormulaKey)
  | existsE (sort : Expr) (body : FormulaKey)
  | opaque (source : Expr) (transforms : List PendingTransform)
structure FormulaNode where
  raw : Expr
  key : FormulaKey
structure TermNode where
  raw : Expr
  key : TermKey
structure CompiledFormula where
  source : Expr
  node : FormulaNode
  alignment : Expr
structure ObjectVariable where
  sort : Expr
  id : Expr
  term : Expr
  key : TermKey
inductive FormulaShell where
  | falsum
  | truth
  | neg (body : FormulaNode)
  | conj (left right : FormulaNode)
  | disj (left right : FormulaNode)
  | imp (left right : FormulaNode)
  | iff (left right : FormulaNode)
  | forallE (sort : Expr) (body : FormulaNode)
  | existsE (sort : Expr) (body : FormulaNode)
  | equal (left right : TermNode)
  | atom
/--
原子字段的定义等价比较。
这里的输入只会是 sort、符号、变量编号、项或项列表，不会是完整公式 shell。
-/
def atomic_eq (left right : Expr) : MetaM Bool := do
  if Expr.equal left right then
    return true
  withoutModifyingState do
    withTransparency .reducible <| isDefEq left right
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
private def nat_value? (expression : Expr) : MetaM (Option Nat) := do
  match ← whnf (← instantiateMVars expression) with
  | .lit (.natVal value) =>
      return some value
  | _ =>
      return none
private def Config.term_type (config : Config) : Expr :=
  mkApp (mkConst ``Logic.FirstOrder.Term config.universeLevels)
    config.signature
private def Config.mk_bvar_term (config : Config) (sort : Expr) (index : Nat) : Expr :=
  let objectVar :=
    mkApp3 (mkConst ``Logic.FirstOrder.Var.bvar config.universeLevels)
      config.signature sort (mkNatLit index)
  mkApp2 (mkConst ``Logic.FirstOrder.Term.var config.universeLevels)
    config.signature objectVar
def Config.mk_fvar_term (config : Config) (sort id : Expr) : Expr :=
  let objectVar :=
    mkApp3 (mkConst ``Logic.FirstOrder.Var.fvar config.universeLevels)
      config.signature sort id
  mkApp2 (mkConst ``Logic.FirstOrder.Term.var config.universeLevels)
    config.signature objectVar
private def Config.mk_term_app (config : Config) (function arguments : Expr) : Expr :=
  mkApp3 (mkConst ``Logic.FirstOrder.Term.app config.universeLevels)
    config.signature function arguments
private def Config.mk_formula_falsum (config : Config) : Expr :=
  mkApp (mkConst ``Logic.FirstOrder.Formula.falsum config.universeLevels)
    config.signature
private def Config.mk_formula_truth (config : Config) : Expr :=
  mkApp (mkConst ``Logic.FirstOrder.Formula.truth config.universeLevels)
    config.signature
private def Config.mk_formula_rel (config : Config) (relation arguments : Expr) : Expr :=
  mkApp3 (mkConst ``Logic.FirstOrder.Formula.rel config.universeLevels)
    config.signature relation arguments
private def Config.mk_formula_equal (config : Config) (left right : Expr) : Expr :=
  mkApp3 (mkConst ``Logic.FirstOrder.Formula.equal config.universeLevels)
    config.signature left right
private def Config.mk_formula_unary (config : Config) (constructor : Name) (body : Expr) : Expr :=
  mkApp2 (mkConst constructor config.universeLevels)
    config.signature body
private def Config.mk_formula_binary (config : Config) (constructor : Name) (left right : Expr) : Expr :=
  mkApp3 (mkConst constructor config.universeLevels)
    config.signature left right
private def Config.mk_formula_quantifier (config : Config) (constructor : Name) (sort body : Expr) : Expr :=
  mkApp3 (mkConst constructor config.universeLevels)
    config.signature sort body
private def Config.apply_term_transform_raw (config : Config) (transform : PendingTransform) (term : Expr) : Expr :=
  match transform with
  | .openAt sort depth replacement =>
      mkAppN (mkConst ``Logic.FirstOrder.Term.openAt config.universeLevels)
        #[config.signature, config.decidableEq, sort, mkNatLit depth,
          replacement, term]
  | .closeFreeAt sort id depth =>
      mkAppN (mkConst ``Logic.FirstOrder.Term.closeFreeAt config.universeLevels)
        #[config.signature, config.decidableEq, sort, id, mkNatLit depth, term]
  | .substituteFree sort id replacement =>
      mkAppN (mkConst ``Logic.FirstOrder.Term.substituteFree config.universeLevels)
        #[config.signature, config.decidableEq, sort, id, replacement, term]
private def Config.apply_formula_transform_raw (config : Config) (transform : PendingTransform) (formula : Expr) : Expr :=
  match transform with
  | .openAt sort depth replacement =>
      mkAppN (mkConst ``Logic.FirstOrder.Formula.openAt config.universeLevels)
        #[config.signature, config.decidableEq, sort, mkNatLit depth,
          replacement, formula]
  | .closeFreeAt sort id depth =>
      mkAppN (mkConst ``Logic.FirstOrder.Formula.closeFreeAt config.universeLevels)
        #[config.signature, config.decidableEq, sort, id, mkNatLit depth,
          formula]
  | .substituteFree sort id replacement =>
      mkAppN (mkConst ``Logic.FirstOrder.Formula.substituteFree config.universeLevels)
        #[config.signature, config.decidableEq, sort, id, replacement, formula]
private def Config.apply_term_transforms_raw (config : Config) (transforms : List PendingTransform) (term : Expr) : Expr :=
  transforms.foldl (fun current transform =>
      config.apply_term_transform_raw transform current)
    term
private def Config.apply_formula_transforms_raw (config : Config) (transforms : List PendingTransform) (formula : Expr) : Expr :=
  transforms.foldl (fun current transform =>
      config.apply_formula_transform_raw transform current)
    formula
private def Config.apply_term_list_transform_raw (config : Config) (transform : PendingTransform) (terms : Expr) : MetaM Expr := do
  withLocalDeclD `term config.term_type fun term => do
    let body := config.apply_term_transform_raw transform term
    let function ← mkLambdaFVars #[term] body
    mkAppM ``List.map #[function, terms]
private def Config.apply_term_list_transforms_raw (config : Config) (transforms : List PendingTransform) (terms : Expr) : MetaM Expr := do
  let mut current := terms
  for transform in transforms do
    current ← config.apply_term_list_transform_raw transform current
  return current
private def PendingTransform.enter_binder (transform : PendingTransform) (binderSort : Expr) :
    MetaM PendingTransform := do
  match transform with
  | .openAt sort depth replacement =>
      if ← atomic_eq sort binderSort then
        return .openAt sort (depth + 1) replacement
      return transform
  | .closeFreeAt sort id depth =>
      if ← atomic_eq sort binderSort then
        return .closeFreeAt sort id (depth + 1)
      return transform
  | .substituteFree .. =>
      return transform
private def enter_binder (transforms : List PendingTransform) (binderSort : Expr) :
    MetaM (List PendingTransform) :=
  transforms.mapM (·.enter_binder binderSort)
mutual
  private partial def compile_term (config : Config) (expression : Expr) (transforms : List PendingTransform := [])
      (fuel : Nat := 128) : MetaM (Expr × TermKey) := do
    let expression ← instantiateMVars expression
    if expression.isAppOfArity ``Logic.FirstOrder.Term.openAt 6 then
      let arguments := expression.getAppArgs
      let some depth ← nat_value? arguments[3]!
        | let raw := config.apply_term_transforms_raw transforms expression
          return (raw, .opaque raw)
      return ←
        compile_term config arguments[5]! (.openAt arguments[2]! depth arguments[4]! :: transforms)
          fuel
    if expression.isAppOfArity ``Logic.FirstOrder.Term.closeFreeAt 6 then
      let arguments := expression.getAppArgs
      let some depth ← nat_value? arguments[4]!
        | let raw := config.apply_term_transforms_raw transforms expression
          return (raw, .opaque raw)
      return ←
        compile_term config arguments[5]! (.closeFreeAt arguments[2]! arguments[3]! depth :: transforms)
          fuel
    if expression.isAppOfArity ``Logic.FirstOrder.Term.substituteFree 6 then
      let arguments := expression.getAppArgs
      return ←
        compile_term config arguments[5]! (.substituteFree arguments[2]! arguments[3]! arguments[4]! ::
            transforms)
          fuel
    if expression.isAppOfArity ``Logic.FirstOrder.Term.var 2 then
      return ←
        compile_variable config expression.getAppArgs[1]! transforms fuel
    if expression.isAppOfArity ``Logic.FirstOrder.Term.app 3 then
      let arguments := expression.getAppArgs
      let (rawArguments, keyArguments) ←
        compile_term_list config arguments[2]! transforms fuel
      return ( (config.mk_term_app arguments[1]! rawArguments,
          .app arguments[1]! keyArguments))
    if fuel > 0 then
      if let some unfolded ← delta_head? expression then
        unless Expr.equal unfolded expression do
          return ← compile_term config unfolded transforms (fuel - 1)
      let reduced ← withTransparency .reducible <| whnf expression
      unless Expr.equal reduced expression do
        return ← compile_term config reduced transforms (fuel - 1)
    let raw := config.apply_term_transforms_raw transforms expression
    return (raw, .opaque raw)
  private partial def compile_variable (config : Config) (expression : Expr) (transforms : List PendingTransform) (fuel : Nat) : MetaM (Expr × TermKey) := do
    let expression ← instantiateMVars expression
    if expression.isAppOfArity ``Logic.FirstOrder.Var.bvar 3 then
      let arguments := expression.getAppArgs
      let some index ← nat_value? arguments[2]!
        | let term :=
            mkApp2 (mkConst ``Logic.FirstOrder.Term.var config.universeLevels)
              config.signature expression
          let raw := config.apply_term_transforms_raw transforms term
          return (raw, .opaque raw)
      return ←
        compile_bvar config arguments[1]! index transforms
    if expression.isAppOfArity ``Logic.FirstOrder.Var.fvar 3 then
      let arguments := expression.getAppArgs
      return ←
        compile_fvar config arguments[1]! arguments[2]! transforms
    if fuel > 0 then
      if let some unfolded ← delta_head? expression then
        unless Expr.equal unfolded expression do
          return ← compile_variable config unfolded transforms (fuel - 1)
      let reduced ← withTransparency .reducible <| whnf expression
      unless Expr.equal reduced expression do
        return ← compile_variable config reduced transforms (fuel - 1)
    let term :=
      mkApp2 (mkConst ``Logic.FirstOrder.Term.var config.universeLevels)
        config.signature expression
    let raw := config.apply_term_transforms_raw transforms term
    return (raw, .opaque raw)
  private partial def compile_bvar (config : Config) (sort : Expr) (index : Nat) (transforms : List PendingTransform) :
      MetaM (Expr × TermKey) := do
    match transforms with
    | [] =>
        return (config.mk_bvar_term sort index, .bvar sort index)
    | transform :: rest =>
        match transform with
        | .openAt target depth replacement =>
            if ← atomic_eq sort target then
              if index == depth then
                return ← compile_term config replacement rest
              if depth < index then
                return ← compile_bvar config sort (index - 1) rest
            return ← compile_bvar config sort index rest
        | .closeFreeAt target _ depth =>
            if (← atomic_eq sort target) && depth ≤ index then
              return ← compile_bvar config sort (index + 1) rest
            return ← compile_bvar config sort index rest
        | .substituteFree .. =>
            return ← compile_bvar config sort index rest
  private partial def compile_fvar (config : Config) (sort id : Expr) (transforms : List PendingTransform) :
      MetaM (Expr × TermKey) := do
    match transforms with
    | [] =>
        return (config.mk_fvar_term sort id, .fvar sort id)
    | transform :: rest =>
        match transform with
        | .openAt .. =>
            return ← compile_fvar config sort id rest
        | .closeFreeAt target targetId depth =>
            if (← atomic_eq sort target) && (← atomic_eq id targetId) then
              return ← compile_bvar config sort depth rest
            return ← compile_fvar config sort id rest
        | .substituteFree target targetId replacement =>
            if (← atomic_eq sort target) && (← atomic_eq id targetId) then
              return ← compile_term config replacement rest
            return ← compile_fvar config sort id rest
  private partial def compile_term_list (config : Config) (expression : Expr) (transforms : List PendingTransform)
      (fuel : Nat) : MetaM (Expr × TermListKey) := do
    let expression ← instantiateMVars expression
    if expression.isAppOfArity ``List.nil 1 then
      return (expression, .nil)
    if expression.isAppOfArity ``List.cons 3 then
      let arguments := expression.getAppArgs
      let (rawHead, keyHead) ←
        compile_term config arguments[1]! transforms fuel
      let (rawTail, keyTail) ←
        compile_term_list config arguments[2]! transforms fuel
      let raw ← mkAppM ``List.cons #[rawHead, rawTail]
      return (raw, .cons keyHead keyTail)
    if fuel > 0 then
      if let some unfolded ← delta_head? expression then
        unless Expr.equal unfolded expression do
          return ←
            compile_term_list config unfolded transforms (fuel - 1)
      let reduced ← withTransparency .reducible <| whnf expression
      unless Expr.equal reduced expression do
        return ←
          compile_term_list config reduced transforms (fuel - 1)
    let raw ← config.apply_term_list_transforms_raw transforms expression
    return (raw, .opaque raw)
end
private partial def compile_formula_with
    (config : Config) (expression : Expr) (transforms : List PendingTransform) (fuel : Nat) : MetaM FormulaNode := do
  let expression ← instantiateMVars expression
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.openAt 6 then
    let arguments := expression.getAppArgs
    let some depth ← nat_value? arguments[3]!
      | return {
          raw := config.apply_formula_transforms_raw transforms expression
          key := .opaque expression transforms
        }
    return ←
      compile_formula_with config arguments[5]! (.openAt arguments[2]! depth arguments[4]! :: transforms)
        fuel
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.closeFreeAt 6 then
    let arguments := expression.getAppArgs
    let some depth ← nat_value? arguments[4]!
      | return {
          raw := config.apply_formula_transforms_raw transforms expression
          key := .opaque expression transforms
        }
    return ←
      compile_formula_with config arguments[5]! (.closeFreeAt arguments[2]! arguments[3]! depth :: transforms)
        fuel
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.substituteFree 6 then
    let arguments := expression.getAppArgs
    return ←
      compile_formula_with config arguments[5]! (.substituteFree arguments[2]! arguments[3]! arguments[4]! ::
          transforms)
        fuel
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.falsum 1 then
    return { raw := config.mk_formula_falsum, key := .falsum }
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.truth 1 then
    return { raw := config.mk_formula_truth, key := .truth }
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.rel 3 then
    let arguments := expression.getAppArgs
    let (rawArguments, keyArguments) ←
      compile_term_list config arguments[2]! transforms fuel
    return {
      raw := config.mk_formula_rel arguments[1]! rawArguments
      key := .rel arguments[1]! keyArguments
    }
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.equal 3 then
    let arguments := expression.getAppArgs
    let (rawLeft, keyLeft) ←
      compile_term config arguments[1]! transforms fuel
    let (rawRight, keyRight) ←
      compile_term config arguments[2]! transforms fuel
    return {
      raw := config.mk_formula_equal rawLeft rawRight
      key := .equal keyLeft keyRight
    }
  if expression.isAppOfArity ``Logic.FirstOrder.Formula.neg 2 then
    let body ←
      compile_formula_with config expression.getAppArgs[1]!
        transforms fuel
    return {
      raw := config.mk_formula_unary ``Logic.FirstOrder.Formula.neg body.raw
      key := .neg body.key
    }
  for constructor in
      [``Logic.FirstOrder.Formula.conj,
        ``Logic.FirstOrder.Formula.disj,
        ``Logic.FirstOrder.Formula.imp,
        ``Logic.FirstOrder.Formula.iff] do
    if expression.isAppOfArity constructor 3 then
      let arguments := expression.getAppArgs
      let left ←
        compile_formula_with config arguments[1]! transforms fuel
      let right ←
        compile_formula_with config arguments[2]! transforms fuel
      let key :=
        if constructor == ``Logic.FirstOrder.Formula.conj then
          FormulaKey.conj left.key right.key
        else if constructor == ``Logic.FirstOrder.Formula.disj then
          FormulaKey.disj left.key right.key
        else if constructor == ``Logic.FirstOrder.Formula.imp then
          FormulaKey.imp left.key right.key
        else
          FormulaKey.iff left.key right.key
      return {
        raw := config.mk_formula_binary constructor left.raw right.raw
        key
      }
  for constructor in
      [``Logic.FirstOrder.Formula.forallE,
        ``Logic.FirstOrder.Formula.existsE] do
    if expression.isAppOfArity constructor 3 then
      let arguments := expression.getAppArgs
      let nestedTransforms ← enter_binder transforms arguments[1]!
      let body ←
        compile_formula_with config arguments[2]!
          nestedTransforms fuel
      let key :=
        if constructor == ``Logic.FirstOrder.Formula.forallE then
          FormulaKey.forallE arguments[1]! body.key
        else
          FormulaKey.existsE arguments[1]! body.key
      return {
        raw :=
          config.mk_formula_quantifier
            constructor arguments[1]! body.raw
        key
      }
  if fuel > 0 then
    if let some unfolded ← delta_head? expression then
      unless Expr.equal unfolded expression do
        return ←
          compile_formula_with config unfolded transforms (fuel - 1)
    let reduced ← withTransparency .reducible <| whnf expression
    unless Expr.equal reduced expression do
      return ←
        compile_formula_with config reduced transforms (fuel - 1)
  return {
    raw := config.apply_formula_transforms_raw transforms expression
    key := .opaque expression transforms
  }
private def compile_formula_node (config : Config) (formula : Expr) : MetaM FormulaNode :=
  compile_formula_with config formula [] 128
/--
构造原子字段的普通 Lean 等式。
这里允许完整定义等价检查，因为调用点只会传入 sort、符号、项、项列表或显式
`opaque` 原子，不会传入带逻辑外壳的完整公式。
-/
private def atomic_alignment? (left right : Expr) :
    MetaM (Option Expr) := do
  if Expr.equal left right then
    return some (← mkEqRefl left)
  let savedState ← saveState
  let aligned ←
    try
      withTransparency .all <| isDefEq left right
    catch _ =>
      pure false
  savedState.restore
  if aligned then
    return some (← mkEqRefl left)
  return none
private def term_atom_simp_context : MetaM Simp.Context := do
  let mut theorems ← getSimpTheorems
  for equation in
      [``Logic.FirstOrder.Term.openAt.eq_1,
        ``Logic.FirstOrder.Term.openAt.eq_2,
        ``Logic.FirstOrder.Term.openAt.eq_3,
        ``Logic.FirstOrder.Term.closeFreeAt.eq_1,
        ``Logic.FirstOrder.Term.closeFreeAt.eq_2,
        ``Logic.FirstOrder.Term.closeFreeAt.eq_3,
        ``Logic.FirstOrder.Term.substituteFree.eq_1,
        ``Logic.FirstOrder.Term.substituteFree.eq_2,
        ``Logic.FirstOrder.Term.substituteFree.eq_3] do
    theorems ← theorems.addConst equation
  theorems ←
    theorems.addDeclToUnfold ``Logic.FirstOrder.Formula.next_depth
  Simp.mkContext (config := {
      maxSteps := 2048
      maxDischargeDepth := 2
      contextual := false
      memoize := true
      failIfUnchanged := false
      autoUnfold := true
      beta := true
      iota := true
      zeta := true
      zetaDelta := false
      proj := true
      index := true
    }) (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
private def normalize_term_atom (source : Expr) : MetaM (Expr × Expr) := do
  let source ← instantiateMVars source
  let context ← term_atom_simp_context
  let simprocs : Simp.SimprocsArray :=
    #[(← Simp.getSimprocs)]
  let mut current := source
  let mut proof ← mkEqRefl source
  -- 连续变换可能在一轮后才暴露下一个可规约的原子头；只在原子内部迭代到稳定。
  for _ in [0:4] do
    let (result, _) ← simp current context simprocs
    let normal ← instantiateMVars result.expr
    let stepProof ←
      match result.proof? with
      | some stepProof =>
          instantiateMVars stepProof
      | none =>
          mkEqRefl current
    let unchanged := Expr.equal normal current
    proof ← mkEqTrans proof stepProof
    current := normal
    if unchanged then
      break
  let expected ← mkEq source current
  let proofType ← inferType proof
  unless ← withTransparency .all <| isDefEq proofType expected do
    throwError "typed atom normalization produced a misaligned equality"
  return (current, proof)
private def mk_binary_congr (function hLeft hRight : Expr) : MetaM Expr := do
  let hFunction ← mkCongrArg function hLeft
  mkCongr hFunction hRight
mutual
  private partial def align_term_normal? (config : Config) (source target : Expr) (key : TermKey) (fuel : Nat := 128) : MetaM (Option Expr) := do
    if let some proof ← atomic_alignment? source target then
      return some proof
    if fuel == 0 then
      return none
    let source ← withTransparency .all <| whnf source
    let target ← withTransparency .all <| whnf target
    match key with
    | .bvar .. | .fvar .. | .opaque .. =>
        atomic_alignment? source target
    | .app _ arguments =>
        unless source.isAppOfArity ``Logic.FirstOrder.Term.app 3 &&
            target.isAppOfArity ``Logic.FirstOrder.Term.app 3 do
          return none
        let sourceArguments := source.getAppArgs
        let targetArguments := target.getAppArgs
        let some hFunction ←
            atomic_alignment? sourceArguments[1]! targetArguments[1]!
          | return none
        let some hArguments ←
            align_term_list_normal? config sourceArguments[2]!
              targetArguments[2]! arguments (fuel - 1)
          | return none
        let constructor :=
          mkApp (mkConst ``Logic.FirstOrder.Term.app config.universeLevels)
            config.signature
        return some (← mk_binary_congr constructor hFunction hArguments)
  private partial def align_term_list_normal? (config : Config) (source target : Expr) (key : TermListKey) (fuel : Nat := 128) : MetaM (Option Expr) := do
    if let some proof ← atomic_alignment? source target then
      return some proof
    if fuel == 0 then
      return none
    let source ← withTransparency .all <| whnf source
    let target ← withTransparency .all <| whnf target
    match key with
    | .nil | .opaque .. =>
        atomic_alignment? source target
    | .cons head tail =>
        unless source.isAppOfArity ``List.cons 3 &&
            target.isAppOfArity ``List.cons 3 do
          return none
        let sourceArguments := source.getAppArgs
        let targetArguments := target.getAppArgs
        let some hHead ←
            align_term_normal? config sourceArguments[1]!
              targetArguments[1]! head (fuel - 1)
          | return none
        let some hTail ←
            align_term_list_normal? config sourceArguments[2]!
              targetArguments[2]! tail (fuel - 1)
          | return none
        let termType ← inferType sourceArguments[1]!
        let termLevel ← getLevel termType
        let constructor :=
          mkApp (mkConst ``List.cons [termLevel]) termType
        return some (← mk_binary_congr constructor hHead hTail)
end
private def align_term_atom? (config : Config) (source target : Expr) (key : TermKey) :
    MetaM (Option Expr) := do
  let (sourceNormal, hSource) ← normalize_term_atom source
  let (targetNormal, hTarget) ← normalize_term_atom target
  let some hNormal ←
      align_term_normal? config sourceNormal targetNormal key
    | return none
  let hTarget ← mkEqSymm hTarget
  return some (← mkEqTrans (← mkEqTrans hSource hNormal) hTarget)
private def align_term_list_atom? (config : Config) (source target : Expr) (key : TermListKey) :
    MetaM (Option Expr) := do
  let (sourceNormal, hSource) ← normalize_term_atom source
  let (targetNormal, hTarget) ← normalize_term_atom target
  let some hNormal ←
      align_term_list_normal? config sourceNormal targetNormal key
    | return none
  let hTarget ← mkEqSymm hTarget
  return some (← mkEqTrans (← mkEqTrans hSource hNormal) hTarget)
private partial def align_formula? (config : Config) (source : Expr) (targetNode : FormulaNode) (fuel : Nat := 256) : MetaM (Option Expr) := do
  if Expr.equal source targetNode.raw then
    return some (← mkEqRefl source)
  if fuel == 0 then
    return none
  let source ← withTransparency .all <| whnf (← instantiateMVars source)
  let target ←
    withTransparency .all <| whnf (← instantiateMVars targetNode.raw)
  match targetNode.key with
  | .falsum | .truth =>
      atomic_alignment? source target
  | .rel _ arguments =>
      unless source.isAppOfArity ``Logic.FirstOrder.Formula.rel 3 &&
          target.isAppOfArity ``Logic.FirstOrder.Formula.rel 3 do
        return none
      let sourceArguments := source.getAppArgs
      let targetArguments := target.getAppArgs
      let some hRelation ←
          atomic_alignment? sourceArguments[1]! targetArguments[1]!
        | return none
      let some hArguments ←
          align_term_list_atom? config sourceArguments[2]!
            targetArguments[2]! arguments
        | return none
      let constructor :=
        mkApp (mkConst ``Logic.FirstOrder.Formula.rel config.universeLevels)
          config.signature
      return some (← mk_binary_congr constructor hRelation hArguments)
  | .equal left right =>
      unless source.isAppOfArity ``Logic.FirstOrder.Formula.equal 3 &&
          target.isAppOfArity ``Logic.FirstOrder.Formula.equal 3 do
        return none
      let sourceArguments := source.getAppArgs
      let targetArguments := target.getAppArgs
      let some hLeft ←
          align_term_atom? config sourceArguments[1]!
            targetArguments[1]! left
        | return none
      let some hRight ←
          align_term_atom? config sourceArguments[2]!
            targetArguments[2]! right
        | return none
      let constructor :=
        mkApp (mkConst ``Logic.FirstOrder.Formula.equal config.universeLevels)
          config.signature
      return some (← mk_binary_congr constructor hLeft hRight)
  | .neg body =>
      unless source.isAppOfArity ``Logic.FirstOrder.Formula.neg 2 &&
          target.isAppOfArity ``Logic.FirstOrder.Formula.neg 2 do
        return none
      let some hBody ←
          align_formula? config source.getAppArgs[1]!
            { raw := target.getAppArgs[1]!, key := body } (fuel - 1)
        | return none
      let constructor :=
        mkApp (mkConst ``Logic.FirstOrder.Formula.neg config.universeLevels)
          config.signature
      return some (← mkCongrArg constructor hBody)
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      let constructorName :=
        match targetNode.key with
        | .conj .. => ``Logic.FirstOrder.Formula.conj
        | .disj .. => ``Logic.FirstOrder.Formula.disj
        | .imp .. => ``Logic.FirstOrder.Formula.imp
        | .iff .. => ``Logic.FirstOrder.Formula.iff
        | _ => unreachable!
      unless source.isAppOfArity constructorName 3 &&
          target.isAppOfArity constructorName 3 do
        return none
      let sourceArguments := source.getAppArgs
      let targetArguments := target.getAppArgs
      let some hLeft ←
          align_formula? config sourceArguments[1]!
            { raw := targetArguments[1]!, key := left } (fuel - 1)
        | return none
      let some hRight ←
          align_formula? config sourceArguments[2]!
            { raw := targetArguments[2]!, key := right } (fuel - 1)
        | return none
      let constructor :=
        mkApp (mkConst constructorName config.universeLevels)
          config.signature
      return some (← mk_binary_congr constructor hLeft hRight)
  | .forallE _ body
  | .existsE _ body =>
      let constructorName :=
        match targetNode.key with
        | .forallE .. => ``Logic.FirstOrder.Formula.forallE
        | .existsE .. => ``Logic.FirstOrder.Formula.existsE
        | _ => unreachable!
      unless source.isAppOfArity constructorName 3 &&
          target.isAppOfArity constructorName 3 do
        return none
      let sourceArguments := source.getAppArgs
      let targetArguments := target.getAppArgs
      let some hSort ←
          atomic_alignment? sourceArguments[1]! targetArguments[1]!
        | return none
      let some hBody ←
          align_formula? config sourceArguments[2]!
            { raw := targetArguments[2]!, key := body } (fuel - 1)
        | return none
      let constructor :=
        mkApp (mkConst constructorName config.universeLevels)
          config.signature
      return some (← mk_binary_congr constructor hSort hBody)
  | .opaque .. =>
      atomic_alignment? source target
def compile_formula (config : Config) (formula : Expr) : MetaM CompiledFormula := do
  let formula ← instantiateMVars formula
  let node ← compile_formula_node config formula
  let some alignment ← align_formula? config formula node
    | throwError
        "typed formula view could not replay the atom-local alignment for \
        {formula}; normal={node.raw}"
  let alignment ← instantiateMVars alignment
  let expected ← mkEq formula node.raw
  let proofType ← inferType alignment
  unless ← withTransparency .all <| isDefEq proofType expected do
    throwError "typed formula view produced an invalid alignment proof"
  return { source := formula, node, alignment }
def cast_derives (alignment proof : Expr) : MetaM Expr :=
  mkAppM ``derives_cast_formula #[alignment, proof]
def cast_admissible (alignment proof : Expr) : MetaM Expr :=
  mkAppM ``admissible_cast_formula #[alignment, proof]
def FormulaNode.alignment_with? (config : Config) (left right : FormulaNode) :
    MetaM (Option Expr) :=
  align_formula? config left.raw right
def TermNode.alignment_with? (config : Config) (left right : TermNode) :
    MetaM (Option Expr) :=
  align_term_atom? config left.raw right.raw right.key
mutual
  private partial def TermKey.reify (config : Config) : TermKey → MetaM Expr
    | .bvar sort index =>
        return config.mk_bvar_term sort index
    | .fvar sort id =>
        return config.mk_fvar_term sort id
    | .app function arguments =>
        return config.mk_term_app function (← arguments.reify config)
    | .opaque raw =>
        return raw
  private partial def TermListKey.reify (config : Config) : TermListKey → MetaM Expr
    | .nil =>
        mkAppOptM ``List.nil #[some config.term_type]
    | .cons head tail => do
        let rawHead ← head.reify config
        let rawTail ← tail.reify config
        mkAppM ``List.cons #[rawHead, rawTail]
    | .opaque raw =>
        return raw
end
structure CheckedTermAdmissibility where
  term : Expr
  sort : Expr
  wellSorted : Expr
  boundClosed : Expr
  alignment : Expr
/--
对具体 raw 项运行公共可计算检查器，并返回推断 sort、sort 正确性与
bound-closed 证书。对不透明参数无法归约时安全失败，不会伪造自反等式。
-/
def TermNode.checked_admissibility? (config : Config) (node : TermNode) :
    MetaM (Option CheckedTermAdmissibility) := do
  let term ← node.key.reify config
  let sort ←
    mkAppM ``Logic.FirstOrder.Term.inferredSort #[term]
  let hWellCheck ←
    mkAppM ``Logic.FirstOrder.Term.check_wellSorted #[sort, term]
  let truth := mkConst ``Bool.true
  unless ← withTransparency .all <| isDefEq hWellCheck truth do
    trace[YesMetaZFC.proveAuto.firstOrderDerives]
      "checked admissibility well-sorted failed; term={term}; check={hWellCheck}"
    return none
  let hWellCheckProof ← mkEqRefl hWellCheck
  let hWell ←
    mkAppM ``Logic.FirstOrder.Term.check_wellSorted_sound
      #[hWellCheckProof]
  let emptyScope :=
    mkApp (mkConst ``Logic.FirstOrder.Scope.empty config.universeLevels)
      config.signature
  let hScopedCheck ←
    mkAppM ``Logic.FirstOrder.Term.check_scoped
      #[emptyScope, term]
  unless ← withTransparency .all <| isDefEq hScopedCheck truth do
    trace[YesMetaZFC.proveAuto.firstOrderDerives]
      "checked admissibility scoped failed; term={term}; check={hScopedCheck}"
    return none
  let hScopedCheckProof ← mkEqRefl hScopedCheck
  let hClosed ←
    mkAppM ``Logic.FirstOrder.Term.check_scoped_sound
      #[hScopedCheckProof]
  let normalized : TermNode := { raw := term, key := node.key }
  let some alignment ← node.alignment_with? config normalized
    | return none
  return some {
    term
    sort
    wellSorted := hWell
    boundClosed := hClosed
    alignment
  }
def FormulaNode.shell (node : FormulaNode) : FormulaShell :=
  match node.key with
  | .falsum =>
      .falsum
  | .truth =>
      .truth
  | .neg body =>
      .neg { raw := node.raw.getAppArgs[1]!, key := body }
  | .conj left right =>
      .conj
        { raw := node.raw.getAppArgs[1]!, key := left }
        { raw := node.raw.getAppArgs[2]!, key := right }
  | .disj left right =>
      .disj
        { raw := node.raw.getAppArgs[1]!, key := left }
        { raw := node.raw.getAppArgs[2]!, key := right }
  | .imp left right =>
      .imp
        { raw := node.raw.getAppArgs[1]!, key := left }
        { raw := node.raw.getAppArgs[2]!, key := right }
  | .iff left right =>
      .iff
        { raw := node.raw.getAppArgs[1]!, key := left }
        { raw := node.raw.getAppArgs[2]!, key := right }
  | .forallE sort body =>
      .forallE sort { raw := node.raw.getAppArgs[2]!, key := body }
  | .existsE sort body =>
      .existsE sort { raw := node.raw.getAppArgs[2]!, key := body }
  | .equal left right =>
      .equal
        { raw := node.raw.getAppArgs[1]!, key := left }
        { raw := node.raw.getAppArgs[2]!, key := right }
  | .rel .. | .opaque .. =>
      .atom
/--
若等式公式的两端具有同一个类型化项键，返回左端项以及
`left ≐ left = left ≐ right` 的公式等式。
-/
def FormulaNode.equality_reflexive_alignment? (config : Config) (node : FormulaNode) :
    MetaM (Option (Expr × Expr)) := do
  let .equal left right := node.shell
    | return none
  let some hTerm ← left.alignment_with? config right
    | return none
  let constructor :=
    mkApp2 (mkConst ``Logic.FirstOrder.Formula.equal config.universeLevels)
      config.signature left.raw
  let hFormula ← mkCongrArg constructor hTerm
  return some (left.raw, hFormula)
def FormulaNode.neg (config : Config) (body : FormulaNode) : FormulaNode :=
  {
    raw := config.mk_formula_unary ``Logic.FirstOrder.Formula.neg body.raw
    key := .neg body.key
  }
def FormulaNode.conj (config : Config) (left right : FormulaNode) : FormulaNode :=
  {
    raw :=
      config.mk_formula_binary
        ``Logic.FirstOrder.Formula.conj left.raw right.raw
    key := .conj left.key right.key
  }
def FormulaNode.disj (config : Config) (left right : FormulaNode) : FormulaNode :=
  {
    raw :=
      config.mk_formula_binary
        ``Logic.FirstOrder.Formula.disj left.raw right.raw
    key := .disj left.key right.key
  }
def FormulaNode.imp (config : Config) (left right : FormulaNode) : FormulaNode :=
  {
    raw :=
      config.mk_formula_binary
        ``Logic.FirstOrder.Formula.imp left.raw right.raw
    key := .imp left.key right.key
  }
def FormulaNode.iff (config : Config) (left right : FormulaNode) : FormulaNode :=
  {
    raw :=
      config.mk_formula_binary
        ``Logic.FirstOrder.Formula.iff left.raw right.raw
    key := .iff left.key right.key
  }
mutual
  private partial def TermKey.open_at (config : Config) (target : Expr) (depth : Nat) (replacement : Expr × TermKey) : TermKey → MetaM TermKey
    | .bvar sort index => do
        if ← atomic_eq sort target then
          if index == depth then
            return replacement.2
          if depth < index then
            return .bvar sort (index - 1)
        return .bvar sort index
    | .fvar sort id =>
        return .fvar sort id
    | .app function arguments =>
        return .app function (← arguments.open_at config target depth replacement)
    | .opaque raw =>
        return .opaque <|
          config.apply_term_transform_raw (.openAt target depth replacement.1) raw
  private partial def TermListKey.open_at (config : Config) (target : Expr) (depth : Nat) (replacement : Expr × TermKey) : TermListKey → MetaM TermListKey
    | .nil =>
        return .nil
    | .cons head tail =>
        return .cons (← head.open_at config target depth replacement) (← tail.open_at config target depth replacement)
    | .opaque raw =>
        return .opaque <|
          ← config.apply_term_list_transform_raw (.openAt target depth replacement.1) raw
end
private partial def FormulaKey.open_at (config : Config) (target : Expr) (depth : Nat) (replacement : Expr × TermKey) : FormulaKey → MetaM FormulaKey
  | .falsum =>
      return .falsum
  | .truth =>
      return .truth
  | .rel relation arguments =>
      return .rel relation (← arguments.open_at config target depth replacement)
  | .equal left right =>
      return .equal (← left.open_at config target depth replacement) (← right.open_at config target depth replacement)
  | .neg body =>
      return .neg (← body.open_at config target depth replacement)
  | .conj left right =>
      return .conj (← left.open_at config target depth replacement) (← right.open_at config target depth replacement)
  | .disj left right =>
      return .disj (← left.open_at config target depth replacement) (← right.open_at config target depth replacement)
  | .imp left right =>
      return .imp (← left.open_at config target depth replacement) (← right.open_at config target depth replacement)
  | .iff left right =>
      return .iff (← left.open_at config target depth replacement) (← right.open_at config target depth replacement)
  | .forallE sort body => do
      let next_depth :=
        if ← atomic_eq sort target then depth + 1 else depth
      return .forallE sort (← body.open_at config target next_depth replacement)
  | .existsE sort body => do
      let next_depth :=
        if ← atomic_eq sort target then depth + 1 else depth
      return .existsE sort (← body.open_at config target next_depth replacement)
  | .opaque source transforms =>
      return .opaque source (transforms ++ [.openAt target depth replacement.1])
/--
直接在类型化键上打开一个 binder；原始公式只归约到结果的最外层 shell。
-/
def FormulaNode.open_at (config : Config) (target : Expr) (depth : Nat) (replacementRaw : Expr) (replacementKey : TermKey)
    (body : FormulaNode) : MetaM CompiledFormula := do
  let source :=
    config.apply_formula_transform_raw (.openAt target depth replacementRaw) body.raw
  let key ←
    body.key.open_at config target depth (replacementRaw, replacementKey)
  let raw ←
    match key with
    | .opaque .. =>
        pure source
    | _ =>
        -- 这里只归约一个公式 shell；深层替换仍由类型化键直接计算。
        withTransparency .all <| whnf source
  let node : FormulaNode := { raw, key }
  let some alignment ← align_formula? config source node
    | throwError
        "typed formula view could not replay an opened formula alignment"
  return { source, node, alignment }
mutual
  private partial def TermKey.collect_variables (config : Config) (variables : Array ObjectVariable) :
      TermKey → MetaM (Array ObjectVariable)
    | .bvar .. | .opaque .. =>
        return variables
    | .fvar sort id => do
        for candidate in variables do
          if (← atomic_eq candidate.sort sort) && (← atomic_eq candidate.id id) then
            return variables
        return variables.push {
          sort
          id
          term := config.mk_fvar_term sort id
          key := .fvar sort id
        }
    | .app _ arguments =>
        arguments.collect_variables config variables
  private partial def TermListKey.collect_variables (config : Config) (variables : Array ObjectVariable) :
      TermListKey → MetaM (Array ObjectVariable)
    | .nil | .opaque .. =>
        return variables
    | .cons head tail => do
        let variables ← head.collect_variables config variables
        tail.collect_variables config variables
end
private partial def FormulaKey.collect_variables (config : Config) (variables : Array ObjectVariable) :
    FormulaKey → MetaM (Array ObjectVariable)
  | .falsum | .truth | .opaque .. =>
      return variables
  | .rel _ arguments =>
      arguments.collect_variables config variables
  | .equal left right => do
      let variables ← left.collect_variables config variables
      right.collect_variables config variables
  | .neg body
  | .forallE _ body
  | .existsE _ body =>
      body.collect_variables config variables
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right => do
      let variables ← left.collect_variables config variables
      right.collect_variables config variables
def FormulaNode.collect_variables (config : Config) (node : FormulaNode) :
    MetaM (Array ObjectVariable) :=
  node.key.collect_variables config #[]
end TypedView
end FirstOrderDerives
end Automation
end YesMetaZFC
