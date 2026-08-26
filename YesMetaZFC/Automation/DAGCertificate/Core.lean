import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.DenseDAG
import YesMetaZFC.Automation.Guards
import YesMetaZFC.Automation.LogicSoundness
import YesMetaZFC.Automation.Resolution
import YesMetaZFC.Logic.FreeVariableSupport
import YesMetaZFC.Logic.FirstOrder.Admissibility
/-!
# 零层级大型 DAG 证书
本文件是新 `Logic` 语义核上的 DAG 证书数据层。它不导入旧 LCF replay，也不携带
Lean `Expr`；搜索层后续只需要把自己的轨迹落成这里的节点、父边和可检查 payload。
当前模块同时定义结构 checker 与整图 soundness：
* 节点编号采用 dense array id：`node.id = index`；
* 每条父边必须指向更早节点；
* source 节点只能引用 `ClauseProblem.initialClauses` 的显式索引；
* residual CDCL 携带 checked propositional UNSAT payload；
* 根节点必须是空字句。
soundness 在这些结构条件上做统一拓扑归纳；公式级问题只在最终出口编译为初始字句。
-/
namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
universe x
open _root_.YesMetaZFC.Automation
open _root_.YesMetaZFC.Automation.LogicSoundness
abbrev Signature := LogicSoundness.SetLevel.Signature
section DAGCertificateSignature
variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]
abbrev Term (σ : Signature) := LogicSoundness.SetLevel.Term σ
abbrev Formula (σ : Signature) := LogicSoundness.SetLevel.Formula σ
abbrev DeepProblem (σ : Signature) := LogicSoundness.SetLevel.DeepProblem σ
abbrev NodeId := Certificate.NodeId
theorem array_check_of_mem {α : Type} {check : α → Bool}
    {values : Array α} (hCheck : values.all check = true)
    {value : α} (hMem : value ∈ values.toList) : check value = true := by
  exact Array.all_eq_true_iff_forall_mem.mp hCheck value (Array.mem_def.mpr hMem)
/-! ## Clause view -/
namespace StructuralEq
open _root_.YesMetaZFC.Logic.FirstOrder
mutual
  def term    :
      Term σ → Term σ → Bool
    | .var value => fun right =>
        match value, right with
        | .bvar sort index, .var (.bvar otherSort otherIndex) =>
            decide (sort = otherSort) && index == otherIndex
        | .fvar sort index, .var (.fvar otherSort otherIndex) =>
            decide (sort = otherSort) && index == otherIndex
        | _, _ => false
    | .app function arguments => fun right =>
        match right with
        | .app otherFunction otherArguments =>
            decide (function = otherFunction) &&
              termList arguments otherArguments
        | _ => false
  def termList
       : List (Term σ) → List (Term σ) → Bool
    | [] => fun right =>
        match right with
        | [] => true
        | _ => false
    | head :: tail => fun right =>
        match right with
        | otherHead :: otherTail =>
            term head otherHead && termList tail otherTail
        | _ => false
end
def formula
     : Formula σ → Formula σ → Bool
  | .falsum => fun right =>
      match right with
      | .falsum => true
      | _ => false
  | .truth => fun right =>
      match right with
      | .truth => true
      | _ => false
  | .rel relation arguments => fun right =>
      match right with
      | .rel otherRelation otherArguments =>
          decide (relation = otherRelation) &&
            termList arguments otherArguments
      | _ => false
  | .equal left right => fun other =>
      match other with
      | .equal otherLeft otherRight =>
          term left otherLeft && term right otherRight
      | _ => false
  | .neg body => fun right =>
      match right with
      | .neg otherBody => formula body otherBody
      | _ => false
  | .conj left right => fun other =>
      match other with
      | .conj otherLeft otherRight =>
          formula left otherLeft && formula right otherRight
      | _ => false
  | .disj left right => fun other =>
      match other with
      | .disj otherLeft otherRight =>
          formula left otherLeft && formula right otherRight
      | _ => false
  | .imp left right => fun other =>
      match other with
      | .imp otherLeft otherRight =>
          formula left otherLeft && formula right otherRight
      | _ => false
  | .iff left right => fun other =>
      match other with
      | .iff otherLeft otherRight =>
          formula left otherLeft && formula right otherRight
      | _ => false
  | .forallE sort body => fun right =>
      match right with
      | .forallE otherSort otherBody =>
          decide (sort = otherSort) && formula body otherBody
      | _ => false
  | .existsE sort body => fun right =>
      match right with
      | .existsE otherSort otherBody =>
          decide (sort = otherSort) && formula body otherBody
      | _ => false
section
omit [DecidableEq σ.RelSymbol]
mutual
  theorem term_refl (input : Term σ) :
      term input input = true := by
    cases input with
    | var value =>
        cases value <;> simp [term]
    | app function arguments =>
        simp [term, termList_refl arguments]
  theorem termList_refl (input : List (Term σ)) :
      termList input input = true := by
    cases input with
    | nil => simp [termList]
    | cons head tail =>
        simp [termList, term_refl head, termList_refl tail]
end
end
theorem formula_refl (input : Formula σ) : formula input input = true := by
  induction input with
  | falsum => simp [formula]
  | truth => simp [formula]
  | rel relation arguments => simp [formula, termList_refl arguments]
  | equal left right => simp [formula, term_refl left, term_refl right]
  | neg body ih => simpa [formula] using ih
  | conj left right ihLeft ihRight => simp [formula, ihLeft, ihRight]
  | disj left right ihLeft ihRight => simp [formula, ihLeft, ihRight]
  | imp left right ihLeft ihRight => simp [formula, ihLeft, ihRight]
  | iff left right ihLeft ihRight => simp [formula, ihLeft, ihRight]
  | forallE sort body ih => simp [formula, ih]
  | existsE sort body ih => simp [formula, ih]
omit [DecidableEq σ.RelSymbol] in
theorem term_eq_true_of_eq
     {left right : Term σ} (equality : left = right) :
    term left right = true := by
  cases equality
  exact term_refl left
omit [DecidableEq σ.RelSymbol] in
theorem termList_eq_true_of_eq
     {left right : List (Term σ)} (equality : left = right) :
    termList left right = true := by
  cases equality
  exact termList_refl left
theorem formula_eq_true_of_eq
    {left right : Formula σ} (equality : left = right) :
    formula left right = true := by
  cases equality
  exact formula_refl left
omit [DecidableEq σ.RelSymbol] in
theorem term_sound (left : Term σ) : ∀ right : Term σ, term left right = true → left = right := by
  refine Term.rec (motive_1 := fun left => ∀ right, term left right = true → left = right)
    (motive_2 := fun lefts => ∀ right, termList lefts right = true → lefts = right)
    ?_ ?_ ?_ ?_ left
  · intro v right h
    cases right <;> simp [term] at h
    case var other =>
      cases v <;> cases other <;> simp at h
      all_goals
        rcases h with ⟨hSort, hIndex⟩
        cases hSort
        cases hIndex
        rfl
  · intro f args ihArgs right h
    cases right <;> simp [term] at h
    case app otherFunction otherArgs =>
      rcases h with ⟨hFunction, hArgs⟩
      cases hFunction
      exact congrArg (Term.app f) (ihArgs _ hArgs)
  · intro right h
    cases right with
    | nil => rfl
    | cons _ _ => simp [termList] at h
  · intro head tail ihHead ihTail right h
    cases right <;> simp [termList] at h
    case cons otherHead otherTail =>
      rcases h with ⟨hHead, hTail⟩
      have hHeadEq := ihHead _ hHead
      have hTailEq := ihTail _ hTail
      cases hHeadEq
      cases hTailEq
      rfl
omit [DecidableEq σ.RelSymbol] in
theorem termList_sound (left : List (Term σ)) :
    ∀ right : List (Term σ), termList left right = true → left = right := by
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | cons _ _ => simp [termList] at h
  | cons head tail ih =>
      intro right h
      cases right <;> simp [termList] at h
      case cons otherHead otherTail =>
        rcases h with ⟨hHead, hTail⟩
        cases term_sound head _ hHead
        cases ih _ hTail
        rfl
theorem formula_sound (left : Formula σ) :
    ∀ right : Formula σ, formula left right = true → left = right := by
  refine Formula.rec (motive := fun left => ∀ right, formula left right = true → left = right)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro right h
    cases right <;> simp [formula] at h
    · rfl
  · intro right h
    cases right <;> simp [formula] at h
    · rfl
  · intro relation args right h
    cases right <;> simp [formula] at h
    case rel otherRelation otherArgs =>
      rcases h with ⟨hRelation, hArgs⟩
      cases hRelation
      exact congrArg (Formula.rel relation) (termList_sound args _ hArgs)
  · intro leftTerm rightTerm right h
    cases right <;> simp [formula] at h
    case equal otherLeft otherRight =>
      rcases h with ⟨hLeft, hRight⟩
      have hLeftEq := term_sound leftTerm _ hLeft
      have hRightEq := term_sound rightTerm _ hRight
      cases hLeftEq
      cases hRightEq
      rfl
  · intro φ ih right h
    cases right <;> simp [formula] at h
    case neg ψ =>
      exact congrArg Formula.neg (ih _ h)
  · intro φ ψ ihφ ihψ right h
    cases right <;> simp [formula] at h
    case conj φ' ψ' =>
      rcases h with ⟨hφ, hψ⟩
      have hφEq := ihφ _ hφ
      have hψEq := ihψ _ hψ
      cases hφEq
      cases hψEq
      rfl
  · intro φ ψ ihφ ihψ right h
    cases right <;> simp [formula] at h
    case disj φ' ψ' =>
      rcases h with ⟨hφ, hψ⟩
      have hφEq := ihφ _ hφ
      have hψEq := ihψ _ hψ
      cases hφEq
      cases hψEq
      rfl
  · intro φ ψ ihφ ihψ right h
    cases right <;> simp [formula] at h
    case imp φ' ψ' =>
      rcases h with ⟨hφ, hψ⟩
      have hφEq := ihφ _ hφ
      have hψEq := ihψ _ hψ
      cases hφEq
      cases hψEq
      rfl
  · intro φ ψ ihφ ihψ right h
    cases right <;> simp [formula] at h
    case iff φ' ψ' =>
      rcases h with ⟨hφ, hψ⟩
      have hφEq := ihφ _ hφ
      have hψEq := ihψ _ hψ
      cases hφEq
      cases hψEq
      rfl
  · intro sort body ih right h
    cases right <;> simp [formula] at h
    case forallE otherSort otherBody =>
      rcases h with ⟨hSort, hBody⟩
      cases hSort
      exact congrArg (Formula.forallE sort) (ih _ hBody)
  · intro sort body ih right h
    cases right <;> simp [formula] at h
    case existsE otherSort otherBody =>
      rcases h with ⟨hSort, hBody⟩
      cases hSort
      exact congrArg (Formula.existsE sort) (ih _ hBody)
end StructuralEq
abbrev TermSubstitution (σ : Signature) := List (σ.SortSymbol × Nat × Term σ)
namespace TermSubstitution
def empty : TermSubstitution σ := []
def lookup (subst : TermSubstitution σ) (sort : σ.SortSymbol) (id : Nat) :
    Option (Term σ) :=
  match subst with
  | [] => none
  | (entrySort, entryId, term) :: rest =>
      if entrySort = sort && entryId == id then
        some term
      else
        lookup rest sort id
end TermSubstitution
namespace Term
mutual
  def applySubstitution (subst : TermSubstitution σ) : Term σ → Term σ
    | .var (.fvar sort id) =>
        match TermSubstitution.lookup subst sort id with
        | some term => term
        | none => .var (.fvar sort id)
    | .var (.bvar sort index) => .var (.bvar sort index)
    | .app function arguments =>
        .app function (applySubstitutionList subst arguments)
  def applySubstitutionList (subst : TermSubstitution σ) : List (Term σ) → List (Term σ)
    | [] => []
    | head :: tail =>
        applySubstitution subst head :: applySubstitutionList subst tail
end
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem applySubstitutionList_eq_map (subst : TermSubstitution σ) :
    ∀ input : List (Term σ),
      applySubstitutionList subst input = input.map (applySubstitution subst)
  | [] => rfl
  | head :: tail => by
      rw [applySubstitutionList, List.map, applySubstitutionList_eq_map]
section
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
mutual
  theorem applySubstitution_empty (input : Term σ) : applySubstitution [] input = input := by
    cases input with
    | var value =>
        cases value <;> simp [applySubstitution, TermSubstitution.lookup]
    | app function arguments =>
        simp [applySubstitution, applySubstitutionList_empty arguments]
  theorem applySubstitutionList_empty (input : List (Term σ)) :
      applySubstitutionList [] input = input := by
    cases input with
    | nil => rfl
    | cons head tail =>
        simp [applySubstitutionList, applySubstitution_empty head,
          applySubstitutionList_empty tail]
end
end
mutual
  def renameFreeVars (offset : Nat) : Term σ → Term σ
    | .var (.fvar sort id) => .var (.fvar sort (id + offset))
    | .var (.bvar sort index) => .var (.bvar sort index)
    | .app function arguments =>
        .app function (renameFreeVarsList offset arguments)
  def renameFreeVarsList (offset : Nat) : List (Term σ) → List (Term σ)
    | [] => []
    | head :: tail =>
        renameFreeVars offset head :: renameFreeVarsList offset tail
end
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem renameFreeVarsList_eq_map (offset : Nat) :
    ∀ input : List (Term σ),
      renameFreeVarsList offset input = input.map (renameFreeVars offset)
  | [] => rfl
  | head :: tail => by
      rw [renameFreeVarsList, List.map, renameFreeVarsList_eq_map]
section
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
mutual
  theorem renameFreeVars_zero (input : Term σ) :
      renameFreeVars 0 input = input := by
    cases input with
    | var value =>
        cases value <;> simp [renameFreeVars]
    | app function arguments =>
        simp [renameFreeVars, renameFreeVarsList_zero arguments]
  theorem renameFreeVarsList_zero (input : List (Term σ)) :
      renameFreeVarsList 0 input = input := by
    cases input with
    | nil => rfl
    | cons head tail =>
        simp [renameFreeVarsList, renameFreeVars_zero head,
          renameFreeVarsList_zero tail]
end
end
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem eq_renameFreeVars_of_offset_eq_zero (input : Term σ) (offset : Nat) (hOffset : offset = 0) :
    input = renameFreeVars offset input := by
  cases hOffset
  exact (renameFreeVars_zero input).symm
inductive ClosureMode
  | boundOnly
  | freeOnly
@[simp] def Closed (mode : ClosureMode) : Term σ → Prop
  | .var (.bvar ..) => mode = .boundOnly
  | .var (.fvar ..) => mode = .freeOnly
  | .app _ args => ∀ term ∈ args, Closed mode term
mutual
  def checkClosed (mode : ClosureMode) : Term σ → Bool
    | .var (.bvar ..) =>
        match mode with
        | .boundOnly => true
        | .freeOnly => false
    | .var (.fvar ..) =>
        match mode with
        | .boundOnly => false
        | .freeOnly => true
    | .app _ args => checkClosedList mode args
  def checkClosedList (mode : ClosureMode) : List (Term σ) → Bool
    | [] => true
    | term :: rest => checkClosed mode term && checkClosedList mode rest
end
section
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
mutual
  theorem checkClosed_sound (mode : ClosureMode) :
      ∀ {term : Term σ}, checkClosed mode term = true → Closed mode term
    | .var v, hCheck => by
        cases mode <;> cases v <;>
          simp [checkClosed, Closed] at hCheck ⊢
    | .app _ args, hCheck => by
        have hList : checkClosedList mode args = true := by
          simpa [checkClosed] using hCheck
        simpa [Closed] using checkClosedList_sound mode hList
  theorem checkClosedList_sound (mode : ClosureMode) :
      ∀ {terms : List (Term σ)}, checkClosedList mode terms = true →
        ∀ term, term ∈ terms → Closed mode term
    | [], _hCheck, term, hMem => by
        cases hMem
    | head :: tail, hCheck, term, hMem => by
        rcases Bool.and_eq_true_iff.mp hCheck with ⟨hHead, hTail⟩
        rcases List.mem_cons.mp hMem with hEq | hTailMem
        · cases hEq
          exact checkClosed_sound mode hHead
        · exact checkClosedList_sound mode hTail term hTailMem
end
end
abbrev BoundClosed : Term σ → Prop := Closed .freeOnly
abbrev FreeClosed : Term σ → Prop := Closed .boundOnly
abbrev checkBoundClosed : Term σ → Bool := checkClosed .freeOnly
abbrev checkFreeClosed : Term σ → Bool := checkClosed .boundOnly
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkBoundClosed_sound {term : Term σ} :
    checkBoundClosed term = true → BoundClosed term :=
  checkClosed_sound .freeOnly
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkFreeClosed_sound {term : Term σ} :
    checkFreeClosed term = true → FreeClosed term :=
  checkClosed_sound .boundOnly
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem eval_pushBound_of_boundClosed
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {term : Term σ} (hClosed : BoundClosed term) (sort : σ.SortSymbol) (value : M.Domain) (hValue : M.sortInterp sort value) :
    Logic.FirstOrder.Term.eval (env.pushBound sort value hValue) term =
      Logic.FirstOrder.Term.eval env term := by
  exact Logic.FirstOrder.Term.rec (motive_1 := fun term =>
      BoundClosed term →
        Logic.FirstOrder.Term.eval (env.pushBound sort value hValue) term =
          Logic.FirstOrder.Term.eval env term) (motive_2 := fun terms =>
      (∀ term, term ∈ terms → BoundClosed term) →
        terms.map (Logic.FirstOrder.Term.eval (env.pushBound sort value hValue)) =
          terms.map (Logic.FirstOrder.Term.eval env)) (fun v hClosed => by
      cases v <;>
        simp [BoundClosed, Logic.FirstOrder.Term.eval,
          Logic.FirstOrder.Env.pushBound] at hClosed ⊢) (fun f args ihArgs hClosed => by
      simpa [Logic.FirstOrder.Term.eval] using
        congrArg (M.funcInterp f) (ihArgs (by simpa [BoundClosed] using hClosed))) (fun _hClosed => rfl) (fun head tail ihHead ihTail hClosed => by
      simp [ihHead (hClosed head (by simp)),
        ihTail (fun term hMem => hClosed term (by simp [hMem]))])
    term hClosed
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem eval_eq_of_freeClosed_of_boundVal_eq
    {M : SetLevel.StructureAt.{x} σ} {env targetEnv : SetLevel.EnvAt.{x} M} (hBound : ∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index) :
    ∀ term : Term σ, FreeClosed term →
      Logic.FirstOrder.Term.eval targetEnv term =
        Logic.FirstOrder.Term.eval env term
  | .var (.bvar sort index), _hClosed => by
      simpa [Logic.FirstOrder.Term.eval] using hBound sort index
  | .var (.fvar ..), hClosed => by
      simp [FreeClosed] at hClosed
  | .app f args, hClosed => by
      have hArgsClosed : ∀ term, term ∈ args → FreeClosed term := by
        simpa [FreeClosed] using hClosed
      simp [Logic.FirstOrder.Term.eval]
      apply congrArg (M.funcInterp f)
      exact List.map_congr_left fun term hMem =>
        eval_eq_of_freeClosed_of_boundVal_eq hBound term (hArgsClosed term hMem)
end Term
namespace TermSubstitution
def BoundClosed (subst : TermSubstitution σ) : Prop :=
  ∀ sort id replacement,
    lookup subst sort id = some replacement → Term.BoundClosed replacement
def WellSorted (subst : TermSubstitution σ) : Prop :=
  ∀ sort id replacement,
    lookup subst sort id = some replacement →
      Logic.FirstOrder.TermWellSorted replacement sort
def checkTerms (checkTerm : σ.SortSymbol → Term σ → Bool) :
    TermSubstitution σ → Bool
  | [] => true
  | (sort, _, term) :: rest =>
      checkTerm sort term && checkTerms checkTerm rest
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkTerms_sound
    {checkTerm : σ.SortSymbol → Term σ → Bool}
    {Property : σ.SortSymbol → Term σ → Prop} (hTerm :
      ∀ {sort term}, checkTerm sort term = true → Property sort term)
    {subst : TermSubstitution σ} :
    checkTerms checkTerm subst = true →
      ∀ sort id replacement,
        lookup subst sort id = some replacement →
          Property sort replacement := by
  induction subst with
  | nil =>
      intro _hCheck sort id replacement hLookup
      simp [lookup] at hLookup
  | cons entry rest ih =>
      rcases entry with ⟨entrySort, entryId, term⟩
      intro hCheck sort id replacement hLookup
      rcases Bool.and_eq_true_iff.mp (by simpa [checkTerms] using hCheck) with
        ⟨hHead, hRest⟩
      by_cases hSort : entrySort = sort
      · by_cases hId : entryId = id
        · have hLookupHead : term = replacement := by
            simpa [lookup, hSort, hId] using hLookup
          cases hLookupHead
          cases hSort
          exact hTerm hHead
        · have hLookupRest : lookup rest sort id = some replacement := by
            simpa [lookup, hSort, hId] using hLookup
          exact ih hRest sort id replacement hLookupRest
      · have hLookupRest : lookup rest sort id = some replacement := by
          simpa [lookup, hSort] using hLookup
        exact ih hRest sort id replacement hLookupRest
def checkBoundClosed (subst : TermSubstitution σ) : Bool :=
  checkTerms (fun _ term => Term.checkBoundClosed term) subst
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkBoundClosed_sound
    {subst : TermSubstitution σ} :
    checkBoundClosed subst = true → BoundClosed subst := by
  simpa [checkBoundClosed, BoundClosed] using (checkTerms_sound (checkTerm := fun _ term => Term.checkBoundClosed term)
      (Property := fun _ term => Term.BoundClosed term) (fun {_ term} h => Term.checkBoundClosed_sound h) (subst := subst))
def checkWellSorted (subst : TermSubstitution σ) : Bool :=
  checkTerms (fun sort term => Logic.FirstOrder.Term.check_wellSorted sort term)
    subst
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkWellSorted_sound
    {subst : TermSubstitution σ} :
    checkWellSorted subst = true → WellSorted subst := by
  simpa [checkWellSorted, WellSorted] using (checkTerms_sound (checkTerm := fun sort term => Logic.FirstOrder.Term.check_wellSorted sort term)
      (Property := fun sort term => Logic.FirstOrder.TermWellSorted term sort) (fun {_ term} h => Logic.FirstOrder.Term.check_wellSorted_sound h)
      (subst := subst))
def checkAdmissible (subst : TermSubstitution σ) : Bool :=
  checkBoundClosed subst && checkWellSorted subst
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkAdmissible_sound
    {subst : TermSubstitution σ} (hCheck : checkAdmissible subst = true) :
    BoundClosed subst ∧ WellSorted subst := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hClosed, hWell⟩
  exact ⟨checkBoundClosed_sound hClosed, checkWellSorted_sound hWell⟩
/--
`targetEnv` 是把 `subst` 作用到 `env` 的语义环境：
bound 栈保持一致，free 变量按 substitution 更新；没有命中的 free 变量保持原值。
-/
def EnvMatches
    {M : SetLevel.StructureAt.{x} σ} (subst : TermSubstitution σ) (env targetEnv : SetLevel.EnvAt.{x} M) : Prop :=
  (∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index) ∧
    ∀ sort id,
      targetEnv.freeVal sort id =
        match lookup subst sort id with
        | some replacement => Logic.FirstOrder.Term.eval env replacement
        | none => env.freeVal sort id
def semanticEnv
    {M : SetLevel.StructureAt.{x} σ} (subst : TermSubstitution σ) (env : SetLevel.EnvAt.{x} M) (hAdmissible : WellSorted subst) : SetLevel.EnvAt.{x} M where
  boundVal := env.boundVal
  freeVal := fun sort id =>
    match lookup subst sort id with
    | some replacement => Logic.FirstOrder.Term.eval env replacement
    | none => env.freeVal sort id
  boundSort := env.boundSort
  freeSort := by
    intro sort id
    cases hLookup : lookup subst sort id with
    | none =>
        simpa [hLookup] using env.freeSort sort id
    | some replacement =>
        simpa [hLookup] using
          Logic.FirstOrder.Term.eval_sort_of_wellSorted (env := env) (term := replacement) (hAdmissible sort id replacement hLookup)
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem semanticEnv_matches
    {M : SetLevel.StructureAt.{x} σ} {subst : TermSubstitution σ}
    {env : SetLevel.EnvAt.{x} M} (hAdmissible : WellSorted subst) :
    EnvMatches subst env (semanticEnv subst env hAdmissible) := by
  constructor
  · intro sort index
    rfl
  · intro sort id
    rfl
namespace EnvMatches
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem pushBound
    {M : SetLevel.StructureAt.{x} σ} {subst : TermSubstitution σ}
    {env targetEnv : SetLevel.EnvAt.{x} M} (hClosed : BoundClosed subst) (hEnv : EnvMatches subst env targetEnv) (sort : σ.SortSymbol) (value : M.Domain)
    (hValue : M.sortInterp sort value) :
    EnvMatches subst (env.pushBound sort value hValue) (targetEnv.pushBound sort value hValue) := by
  constructor
  · exact Logic.FirstOrder.Env.SameBoundStack.pushBound
      hEnv.1 sort value hValue
  · intro target id
    have hFree := hEnv.2 target id
    cases hLookup : lookup subst target id with
    | none =>
        simpa [Logic.FirstOrder.Env.pushBound, hLookup] using hFree
    | some replacement =>
        have hStable :
            Logic.FirstOrder.Term.eval (env.pushBound sort value hValue) replacement =
              Logic.FirstOrder.Term.eval env replacement :=
          Term.eval_pushBound_of_boundClosed (env := env) (term := replacement) (hClosed target id replacement hLookup) sort value hValue
        simpa [Logic.FirstOrder.Env.pushBound, hLookup, hStable.symm] using hFree
end EnvMatches
end TermSubstitution
namespace FreeVarRenaming
/--
`targetEnv` 是从 `sourceEnv` 按 `offset` 投影得到的自由变量环境。
bound 栈保持一致，目标环境中的 `id` 对应源环境中的 `id + offset`。
-/
def EnvMatches  {M : SetLevel.StructureAt.{x} σ} (offset : Nat) (sourceEnv targetEnv : SetLevel.EnvAt.{x} M) : Prop :=
  (∀ sort index, targetEnv.boundVal sort index = sourceEnv.boundVal sort index) ∧
    ∀ sort id, targetEnv.freeVal sort id = sourceEnv.freeVal sort (id + offset)
def semanticEnv  {M : SetLevel.StructureAt.{x} σ} (offset : Nat) (sourceEnv : SetLevel.EnvAt.{x} M) : SetLevel.EnvAt.{x} M where
  boundVal := sourceEnv.boundVal
  freeVal := fun sort id => sourceEnv.freeVal sort (id + offset)
  boundSort := sourceEnv.boundSort
  freeSort := fun sort id => sourceEnv.freeSort sort (id + offset)
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem semanticEnv_matches  {M : SetLevel.StructureAt.{x} σ}
    {offset : Nat} {sourceEnv : SetLevel.EnvAt.{x} M} :
    EnvMatches offset sourceEnv (semanticEnv offset sourceEnv) := by
  constructor <;> intro sort index <;> rfl
namespace EnvMatches
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem pushBound
    {M : SetLevel.StructureAt.{x} σ} {offset : Nat}
    {sourceEnv targetEnv : SetLevel.EnvAt.{x} M} (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) (sort : σ.SortSymbol) (value : M.Domain)
    (hValue : M.sortInterp sort value) :
    FreeVarRenaming.EnvMatches offset (sourceEnv.pushBound sort value hValue) (targetEnv.pushBound sort value hValue) := by
  constructor
  · exact Logic.FirstOrder.Env.SameBoundStack.pushBound
      hEnv.1 sort value hValue
  · intro target id
    simpa [Logic.FirstOrder.Env.pushBound] using hEnv.2 target id
end EnvMatches
end FreeVarRenaming
namespace Term
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem eval_applySubstitution_eq_of_envMatches
     {M : SetLevel.StructureAt.{x} σ}
    {subst : TermSubstitution σ} {env targetEnv : SetLevel.EnvAt.{x} M} (hEnv : TermSubstitution.EnvMatches subst env targetEnv) :
    ∀ term : Term σ,
      Logic.FirstOrder.Term.eval env (applySubstitution subst term) =
        Logic.FirstOrder.Term.eval targetEnv term
  | .var (.bvar sort index) => by
      simpa [applySubstitution, Logic.FirstOrder.Term.eval] using (hEnv.1 sort index).symm
  | .var (.fvar sort id) => by
      cases hLookup : TermSubstitution.lookup subst sort id with
      | none =>
          simpa [applySubstitution, Logic.FirstOrder.Term.eval, hLookup] using (hEnv.2 sort id).symm
      | some replacement =>
          simpa [applySubstitution, Logic.FirstOrder.Term.eval, hLookup] using (hEnv.2 sort id).symm
  | .app f args => by
      simp only [applySubstitution, Logic.FirstOrder.Term.eval]
      apply congrArg (M.funcInterp f)
      rw [applySubstitutionList_eq_map, List.map_map]
      exact List.map_congr_left fun term _ =>
        eval_applySubstitution_eq_of_envMatches (subst := subst) (env := env) (targetEnv := targetEnv) hEnv term
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem eval_renameFreeVars_eq_of_envMatches
    {M : SetLevel.StructureAt.{x} σ} {offset : Nat}
    {sourceEnv targetEnv : SetLevel.EnvAt.{x} M} (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) :
    ∀ term : Term σ,
      Logic.FirstOrder.Term.eval sourceEnv (renameFreeVars offset term) =
        Logic.FirstOrder.Term.eval targetEnv term
  | .var (.bvar sort index) => by
      simpa [renameFreeVars, Logic.FirstOrder.Term.eval] using (hEnv.1 sort index).symm
  | .var (.fvar sort id) => by
      simpa [renameFreeVars, Logic.FirstOrder.Term.eval] using (hEnv.2 sort id).symm
  | .app f args => by
      simp only [renameFreeVars, Logic.FirstOrder.Term.eval]
      apply congrArg (M.funcInterp f)
      rw [renameFreeVarsList_eq_map, List.map_map]
      exact List.map_congr_left fun term _ =>
        eval_renameFreeVars_eq_of_envMatches (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv term
end Term
namespace Formula
def mapTerms (transform : Term σ → Term σ) : Formula σ → Formula σ
  | .falsum => .falsum
  | .truth => .truth
  | .rel r args => .rel r (args.map transform)
  | .equal left right =>
      .equal (transform left) (transform right)
  | .neg φ => .neg (mapTerms transform φ)
  | .conj φ ψ => .conj (mapTerms transform φ) (mapTerms transform ψ)
  | .disj φ ψ => .disj (mapTerms transform φ) (mapTerms transform ψ)
  | .imp φ ψ => .imp (mapTerms transform φ) (mapTerms transform ψ)
  | .iff φ ψ => .iff (mapTerms transform φ) (mapTerms transform ψ)
  | .forallE sort body => .forallE sort (mapTerms transform body)
  | .existsE sort body => .existsE sort (mapTerms transform body)
def applySubstitution (subst : TermSubstitution σ) : Formula σ → Formula σ :=
  mapTerms (Term.applySubstitution subst)
def renameFreeVars (offset : Nat) : Formula σ → Formula σ :=
  mapTerms (Term.renameFreeVars offset)
def FreeClosed : Formula σ → Prop
  | .falsum => True
  | .truth => True
  | .rel _ args => ∀ term, term ∈ args → Term.FreeClosed term
  | .equal left right => Term.FreeClosed left ∧ Term.FreeClosed right
  | .neg φ => FreeClosed φ
  | .conj φ ψ => FreeClosed φ ∧ FreeClosed ψ
  | .disj φ ψ => FreeClosed φ ∧ FreeClosed ψ
  | .imp φ ψ => FreeClosed φ ∧ FreeClosed ψ
  | .iff φ ψ => FreeClosed φ ∧ FreeClosed ψ
  | .forallE _ body => FreeClosed body
  | .existsE _ body => FreeClosed body
def checkFreeClosed :
    Formula σ → Bool
  | .falsum => true
  | .truth => true
  | .rel _ args => args.all Term.checkFreeClosed
  | .equal left right => Term.checkFreeClosed left && Term.checkFreeClosed right
  | .neg φ => checkFreeClosed φ
  | .conj φ ψ => checkFreeClosed φ && checkFreeClosed ψ
  | .disj φ ψ => checkFreeClosed φ && checkFreeClosed ψ
  | .imp φ ψ => checkFreeClosed φ && checkFreeClosed ψ
  | .iff φ ψ => checkFreeClosed φ && checkFreeClosed ψ
  | .forallE _ body => checkFreeClosed body
  | .existsE _ body => checkFreeClosed body
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkFreeClosed_sound :
    ∀ {φ : Formula σ}, checkFreeClosed φ = true → FreeClosed φ := by
  intro φ
  induction φ <;>
    simp_all [checkFreeClosed, FreeClosed, Term.checkFreeClosed_sound,
      List.all_eq_true]
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_iff_of_freeClosed_of_boundVal_eq
     {M : SetLevel.StructureAt.{x} σ}
    {env targetEnv : SetLevel.EnvAt.{x} M} (hBound : ∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index)
    (φ : Formula σ) (hClosed : FreeClosed φ) :
      Logic.FirstOrder.Formula.satisfies targetEnv φ ↔
        Logic.FirstOrder.Formula.satisfies env φ := by
  induction φ generalizing env targetEnv with
  | falsum | truth =>
      simp [Logic.FirstOrder.Formula.satisfies]
  | rel r args =>
      have hArgsClosed : ∀ term, term ∈ args → Term.FreeClosed term := by
        simpa [FreeClosed] using hClosed
      have hArgs :
          args.map (Logic.FirstOrder.Term.eval targetEnv) =
            args.map (Logic.FirstOrder.Term.eval env) := by
        exact List.map_congr_left fun term hMem =>
          Term.eval_eq_of_freeClosed_of_boundVal_eq hBound term (hArgsClosed term hMem)
      simp [Logic.FirstOrder.Formula.satisfies, hArgs]
  | equal left right =>
      have hClosed' : Term.FreeClosed left ∧ Term.FreeClosed right := by
        simpa [FreeClosed] using hClosed
      rcases hClosed' with ⟨hLeft, hRight⟩
      simp [Logic.FirstOrder.Formula.satisfies,
        Term.eval_eq_of_freeClosed_of_boundVal_eq hBound left hLeft,
        Term.eval_eq_of_freeClosed_of_boundVal_eq hBound right hRight]
  | neg φ ih =>
      simpa [Logic.FirstOrder.Formula.satisfies] using
        not_congr (ih hBound hClosed)
  | conj φ ψ ihφ ihψ
  | disj φ ψ ihφ ihψ
  | imp φ ψ ihφ ihψ
  | iff φ ψ ihφ ihψ =>
      have ⟨hφ, hψ⟩ : FreeClosed φ ∧ FreeClosed ψ := by
        simpa [FreeClosed] using hClosed
      simp [Logic.FirstOrder.Formula.satisfies,
        ihφ hBound hφ, ihψ hBound hψ]
  | forallE qsort body ih =>
      constructor
      · intro h value hValue
        exact (ih (Logic.FirstOrder.Env.SameBoundStack.pushBound
          hBound qsort value hValue) hClosed).mp (h value hValue)
      · intro h value hValue
        exact (ih (Logic.FirstOrder.Env.SameBoundStack.pushBound
          hBound qsort value hValue) hClosed).mpr (h value hValue)
  | existsE qsort body ih =>
      constructor
      · rintro ⟨value, hValue, hBody⟩
        exact ⟨value, hValue, (ih (Logic.FirstOrder.Env.SameBoundStack.pushBound
            hBound qsort value hValue) hClosed).mp hBody⟩
      · rintro ⟨value, hValue, hBody⟩
        exact ⟨value, hValue, (ih (Logic.FirstOrder.Env.SameBoundStack.pushBound
            hBound qsort value hValue) hClosed).mpr hBody⟩
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_map_terms_iff_of_env_rel
    {M : SetLevel.StructureAt.{x} σ}
    {transform : Term σ → Term σ}
    {EnvRel : SetLevel.EnvAt.{x} M → SetLevel.EnvAt.{x} M → Prop} (hEval :
      ∀ {sourceEnv targetEnv}, EnvRel sourceEnv targetEnv →
        ∀ term,
          Logic.FirstOrder.Term.eval sourceEnv (transform term) =
            Logic.FirstOrder.Term.eval targetEnv term) (hPush :
      ∀ {sourceEnv targetEnv}, EnvRel sourceEnv targetEnv →
        ∀ sort value (hValue : M.sortInterp sort value),
          EnvRel (sourceEnv.pushBound sort value hValue) (targetEnv.pushBound sort value hValue))
    {sourceEnv targetEnv} (hEnv : EnvRel sourceEnv targetEnv) :
    ∀ φ : Formula σ,
      Logic.FirstOrder.Formula.satisfies sourceEnv (mapTerms transform φ) ↔
        Logic.FirstOrder.Formula.satisfies targetEnv φ := by
  intro φ
  induction φ generalizing sourceEnv targetEnv with
  | falsum | truth =>
      simp [mapTerms, Logic.FirstOrder.Formula.satisfies]
  | rel r args =>
      have hArgs : (args.map transform).map (Logic.FirstOrder.Term.eval sourceEnv) =
            args.map (Logic.FirstOrder.Term.eval targetEnv) := by
        rw [List.map_map]
        exact List.map_congr_left fun term _ => hEval hEnv term
      simp [mapTerms, Logic.FirstOrder.Formula.satisfies, hArgs]
  | equal left right =>
      simp [mapTerms, Logic.FirstOrder.Formula.satisfies, hEval hEnv]
  | neg φ ih =>
      simpa [mapTerms, Logic.FirstOrder.Formula.satisfies] using
        not_congr (ih hEnv)
  | conj φ ψ ihφ ihψ
  | disj φ ψ ihφ ihψ
  | imp φ ψ ihφ ihψ
  | iff φ ψ ihφ ihψ =>
      simp [mapTerms, Logic.FirstOrder.Formula.satisfies,
        ihφ hEnv, ihψ hEnv]
  | forallE sort body ih =>
      constructor
      · intro h value hValue
        exact (ih (hPush hEnv sort value hValue)).mp (h value hValue)
      · intro h value hValue
        exact (ih (hPush hEnv sort value hValue)).mpr (h value hValue)
  | existsE sort body ih =>
      constructor
      · rintro ⟨value, hValue, hBody⟩
        exact ⟨value, hValue, (ih (hPush hEnv sort value hValue)).mp hBody⟩
      · rintro ⟨value, hValue, hBody⟩
        exact ⟨value, hValue, (ih (hPush hEnv sort value hValue)).mpr hBody⟩
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_applySubstitution_iff_of_envMatches
     {M : SetLevel.StructureAt.{x} σ}
    {subst : TermSubstitution σ} {env targetEnv : SetLevel.EnvAt.{x} M} (hClosed : TermSubstitution.BoundClosed subst)
    (hEnv : TermSubstitution.EnvMatches subst env targetEnv) :
    ∀ φ : Formula σ,
      Logic.FirstOrder.Formula.satisfies env (applySubstitution subst φ) ↔
        Logic.FirstOrder.Formula.satisfies targetEnv φ := by
  intro φ
  simpa only [applySubstitution] using
    satisfies_map_terms_iff_of_env_rel (transform := Term.applySubstitution subst) (EnvRel := TermSubstitution.EnvMatches subst)
      (Term.eval_applySubstitution_eq_of_envMatches (subst := subst)) (TermSubstitution.EnvMatches.pushBound (subst := subst) hClosed)
      hEnv φ
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_renameFreeVars_iff_of_envMatches
     {M : SetLevel.StructureAt.{x} σ}
    {offset : Nat} {sourceEnv targetEnv : SetLevel.EnvAt.{x} M} (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) :
    ∀ φ : Formula σ,
      Logic.FirstOrder.Formula.satisfies sourceEnv (renameFreeVars offset φ) ↔
        Logic.FirstOrder.Formula.satisfies targetEnv φ := by
  intro φ
  simpa only [renameFreeVars] using
    satisfies_map_terms_iff_of_env_rel (transform := Term.renameFreeVars offset) (EnvRel := FreeVarRenaming.EnvMatches offset)
      (Term.eval_renameFreeVars_eq_of_envMatches (offset := offset))
      FreeVarRenaming.EnvMatches.pushBound
      hEnv φ
end Formula
namespace DeepProblem
def FreeClosed (problem : DeepProblem σ) : Prop :=
  Formula.FreeClosed problem.target ∧
    ∀ premise, premise ∈ problem.premises → Formula.FreeClosed premise
def freeClosed (problem : DeepProblem σ) : Bool :=
  Formula.checkFreeClosed problem.target &&
    problem.premises.all Formula.checkFreeClosed
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem freeClosed_sound
    {problem : DeepProblem σ} (hCheck : problem.freeClosed = true) :
    FreeClosed problem := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hTarget, hPremises⟩
  exact ⟨Formula.checkFreeClosed_sound hTarget, fun premise hMem =>
    Formula.checkFreeClosed_sound ((List.all_eq_true.mp hPremises) premise hMem)⟩
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem models_of_freeClosed_of_boundVal_eq
     {M : SetLevel.StructureAt.{x} σ}
    {problem : DeepProblem σ} {env targetEnv : SetLevel.EnvAt.{x} M} (hClosed : FreeClosed problem)
    (hBound : ∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index) (hModels : Logic.FirstOrder.Theory.Models problem.theory env) :
    Logic.FirstOrder.Theory.Models problem.theory targetEnv := by
  intro premise hMem
  exact (Formula.satisfies_iff_of_freeClosed_of_boundVal_eq hBound
      premise (hClosed.2 premise hMem)).mpr (hModels premise hMem)
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem targetFalse_of_freeClosed_of_boundVal_eq
     {M : SetLevel.StructureAt.{x} σ}
    {problem : DeepProblem σ} {env targetEnv : SetLevel.EnvAt.{x} M} (hClosed : FreeClosed problem)
    (hBound : ∀ sort index, targetEnv.boundVal sort index = env.boundVal sort index) (hTargetFalse : ¬ Logic.FirstOrder.Formula.satisfies env problem.target) :
    ¬ Logic.FirstOrder.Formula.satisfies targetEnv problem.target := by
  intro hTarget
  exact hTargetFalse ((Formula.satisfies_iff_of_freeClosed_of_boundVal_eq hBound
      problem.target hClosed.1).mp hTarget)
end DeepProblem
structure Literal (σ : Signature) where
  polarity : Bool
  atom : Formula σ
namespace Literal
def pos  (φ : Formula σ) : Literal σ :=
  { polarity := true, atom := φ }
def neg  (φ : Formula σ) : Literal σ :=
  { polarity := false, atom := φ }
def toFormula  (literal : Literal σ) : Formula σ :=
  if literal.polarity then literal.atom else .neg literal.atom
def freeSupport  (literal : Literal σ) :
    Logic.FirstOrder.FreeVariable.Support σ :=
  Logic.FirstOrder.Formula.freeSupport literal.atom
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem freeSupport_toFormula  (literal : Literal σ) :
    Logic.FirstOrder.Formula.freeSupport literal.toFormula = literal.freeSupport := by
  cases literal with
  | mk polarity atom =>
      cases polarity <;> rfl
def applySubstitution (subst : TermSubstitution σ) (literal : Literal σ) : Literal σ :=
  { literal with atom := Formula.applySubstitution subst literal.atom }
def renameFreeVars  (offset : Nat) (literal : Literal σ) :
    Literal σ :=
  { literal with atom := Formula.renameFreeVars offset literal.atom }
def eq (left right : Literal σ) : Bool :=
  left.polarity == right.polarity && StructuralEq.formula left.atom right.atom
theorem eq_sound (left right : Literal σ) :
    left.eq right = true → left = right := by
  cases left
  cases right
  intro h
  simp [eq] at h
  rcases h with ⟨hPolarity, hAtom⟩
  cases hPolarity
  have hAtomEq := StructuralEq.formula_sound _ _ hAtom
  cases hAtomEq
  rfl
def Satisfies   {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M) (literal : Literal σ) : Prop :=
  Logic.FirstOrder.Formula.satisfies env literal.toFormula
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_iff_of_agreesOn
    {M : SetLevel.StructureAt.{x} σ} {left right : SetLevel.EnvAt.{x} M} (literal : Literal σ)
    (hEnv : Logic.FirstOrder.Env.AgreesOn literal.freeSupport left right) :
    Satisfies left literal ↔ Satisfies right literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · change (¬ Logic.FirstOrder.Formula.satisfies left atom) ↔
            ¬ Logic.FirstOrder.Formula.satisfies right atom
        exact not_congr (Logic.FirstOrder.Formula.satisfies_iff_of_agreesOn atom hEnv)
      · exact Logic.FirstOrder.Formula.satisfies_iff_of_agreesOn atom hEnv
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_applySubstitution_iff_of_envMatches
     {M : SetLevel.StructureAt.{x} σ}
    {subst : TermSubstitution σ} {env targetEnv : SetLevel.EnvAt.{x} M} (hClosed : TermSubstitution.BoundClosed subst)
    (hEnv : TermSubstitution.EnvMatches subst env targetEnv) (literal : Literal σ) :
    Satisfies env (applySubstitution subst literal) ↔
      Satisfies targetEnv literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · change (¬ Logic.FirstOrder.Formula.satisfies env (Formula.applySubstitution subst atom)) ↔
            ¬ Logic.FirstOrder.Formula.satisfies targetEnv atom
        exact not_congr (Formula.satisfies_applySubstitution_iff_of_envMatches (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv atom)
      · exact
          Formula.satisfies_applySubstitution_iff_of_envMatches (subst := subst) (env := env) (targetEnv := targetEnv) hClosed hEnv atom
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_renameFreeVars_iff_of_envMatches
     {M : SetLevel.StructureAt.{x} σ}
    {offset : Nat} {sourceEnv targetEnv : SetLevel.EnvAt.{x} M} (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) (literal : Literal σ) :
    Satisfies sourceEnv (renameFreeVars offset literal) ↔
      Satisfies targetEnv literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · change (¬ Logic.FirstOrder.Formula.satisfies sourceEnv (Formula.renameFreeVars offset atom)) ↔
            ¬ Logic.FirstOrder.Formula.satisfies targetEnv atom
        exact not_congr (Formula.satisfies_renameFreeVars_iff_of_envMatches (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv atom)
      · exact
          Formula.satisfies_renameFreeVars_iff_of_envMatches (offset := offset) (sourceEnv := sourceEnv) (targetEnv := targetEnv) hEnv atom
def matchesAtom (polarity : Bool) (atom : Formula σ) (literal : Literal σ) : Bool :=
  literal.polarity == polarity && StructuralEq.formula literal.atom atom
theorem matchesAtom_sound
    {polarity : Bool} {atom : Formula σ} {literal : Literal σ} (hMatches : literal.matchesAtom polarity atom = true) :
    literal.polarity = polarity ∧ literal.atom = atom := by
  unfold matchesAtom at hMatches
  rcases Bool.and_eq_true_iff.mp hMatches with ⟨hPolarity, hAtom⟩
  exact ⟨beq_iff_eq.mp hPolarity,
    StructuralEq.formula_sound literal.atom atom hAtom⟩
theorem not_satisfies_matchesAtom_complement
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {pivotPolarity : Bool} {atom : Formula σ} {left right : Literal σ} (hLeftMatch : left.matchesAtom pivotPolarity atom = true)
    (hRightMatch : right.matchesAtom (!pivotPolarity) atom = true) (hLeft : Satisfies env left) (hRight : Satisfies env right) : False := by
  cases left with
  | mk leftPolarity leftAtom =>
  cases right with
  | mk rightPolarity rightAtom =>
  rcases matchesAtom_sound hLeftMatch with ⟨hLeftPolarity, hLeftAtom⟩
  rcases matchesAtom_sound hRightMatch with ⟨hRightPolarity, hRightAtom⟩
  cases hLeftPolarity
  cases hLeftAtom
  cases hRightPolarity
  cases hRightAtom
  cases leftPolarity
  · simp [Satisfies, toFormula, Logic.FirstOrder.Formula.satisfies] at hLeft hRight
    exact hLeft hRight
  · simp [Satisfies, toFormula, Logic.FirstOrder.Formula.satisfies] at hLeft hRight
    exact hRight hLeft
theorem not_satisfies_reflexive_negative_equality
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {left right : Term σ} {literal : Literal σ} (hTerm : StructuralEq.term left right = true) (hMatch : literal.matchesAtom false (.equal left right) = true)
    (hLiteral : Satisfies env literal) : False := by
  rcases matchesAtom_sound hMatch with ⟨hPolarity, hAtom⟩
  have hTermEq : left = right := StructuralEq.term_sound left right hTerm
  cases literal
  cases hPolarity
  cases hAtom
  cases hTermEq
  simp [Satisfies, toFormula, Logic.FirstOrder.Formula.satisfies] at hLiteral
end Literal
structure Clause (σ : Signature) where
  literals : Array (Literal σ) := #[]
namespace Clause
def empty : Clause σ :=
  { literals := #[] }
def singleton  (literal : Literal σ) : Clause σ :=
  { literals := #[literal] }
def applySubstitution (subst : TermSubstitution σ) (clause : Clause σ) : Clause σ :=
  { literals := clause.literals.map (Literal.applySubstitution subst) }
def renameFreeVars  (offset : Nat) (clause : Clause σ) : Clause σ :=
  { literals := clause.literals.map (Literal.renameFreeVars offset) }
def ofFormula  (φ : Formula σ) : Clause σ :=
  singleton (Literal.pos φ)
def ofNegatedFormula  (φ : Formula σ) : Clause σ :=
  singleton (Literal.neg φ)
def atIndices  (clause : Clause σ) (indices : Array Nat) : Clause σ :=
  { literals := indices.filterMap fun index => clause.literals[index]? }
def isEmpty  (clause : Clause σ) : Bool :=
  clause.literals.size == 0
def nonempty  (clause : Clause σ) : Bool :=
  !clause.isEmpty
def freeSupportList : List (Literal σ) →
    Logic.FirstOrder.FreeVariable.Support σ
  | [] => []
  | literal :: rest => literal.freeSupport ++ freeSupportList rest
def freeSupport  (clause : Clause σ) :
    Logic.FirstOrder.FreeVariable.Support σ :=
  freeSupportList clause.literals.toList
private def toFormulaList : List (Literal σ) → Formula σ
  | [] => .falsum
  | literal :: rest => .disj literal.toFormula (toFormulaList rest)
def toFormula  (clause : Clause σ) : Formula σ :=
  toFormulaList clause.literals.toList
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem freeSupport_toFormula  (clause : Clause σ) :
    Logic.FirstOrder.Formula.freeSupport clause.toFormula = clause.freeSupport := by
  cases clause with
  | mk literals =>
      simp only [toFormula, freeSupport]
      induction literals.toList with
      | nil =>
          rfl
      | cons literal rest ih =>
          simp only [toFormulaList, Logic.FirstOrder.Formula.freeSupport, freeSupportList]
          rw [Literal.freeSupport_toFormula, ih]
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
private theorem literal_freeSupport_subset_of_mem_list
    {literal : Literal σ} :
    ∀ {literals : List (Literal σ)}, literal ∈ literals →
      ∀ fv, fv ∈ literal.freeSupport → fv ∈ freeSupportList literals
  | [], hMem, _fv, _hSupport => by
      cases hMem
  | head :: tail, hMem, fv, hSupport => by
      rcases List.mem_cons.mp hMem with hEq | hTail
      · cases hEq
        simp [freeSupportList, hSupport]
      · simp [freeSupportList,
          literal_freeSupport_subset_of_mem_list hTail fv hSupport]
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem literal_freeSupport_subset_of_mem
    {literal : Literal σ} {clause : Clause σ} (hMem : literal ∈ clause.literals.toList) :
    ∀ fv, fv ∈ literal.freeSupport → fv ∈ clause.freeSupport := by
  intro fv hSupport
  exact literal_freeSupport_subset_of_mem_list hMem fv hSupport
private def literalListEq
      :
    List (Literal σ) → List (Literal σ) → Bool
  | [], [] => true
  | literal :: rest, literal' :: rest' => literal.eq literal' && literalListEq rest rest'
  | _, _ => false
private theorem literalListEq_sound (left : List (Literal σ)) :
    ∀ right : List (Literal σ), literalListEq left right = true → left = right := by
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | cons _ _ => simp [literalListEq] at h
  | cons literal rest ih =>
      intro right h
      cases right <;> simp [literalListEq] at h
      case cons literal' rest' =>
        rcases h with ⟨hLiteral, hRest⟩
        have hLiteralEq := Literal.eq_sound literal literal' hLiteral
        have hRestEq := ih _ hRest
        cases hLiteralEq
        cases hRestEq
        rfl
def eq (left right : Clause σ) : Bool :=
  literalListEq left.literals.toList right.literals.toList
theorem eq_sound (left right : Clause σ) :
    left.eq right = true → left = right := by
  cases left
  case mk leftLiterals =>
  cases right
  case mk rightLiterals =>
  intro h
  simp [eq] at h
  have hList := literalListEq_sound _ _ h
  cases leftLiterals
  cases rightLiterals
  simp at hList
  simp [hList]
def filterOutList (polarity : Bool) (atom : Formula σ) :
    List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if literal.matchesAtom polarity atom then
        filterOutList polarity atom rest
      else
        literal :: filterOutList polarity atom rest
def filterOut (polarity : Bool) (atom : Formula σ) (clause : Clause σ) : Clause σ :=
  { literals := (filterOutList polarity atom clause.literals.toList).toArray }
def containsLiteralList (needle : Literal σ) : List (Literal σ) → Bool
  | [] => false
  | literal :: rest => needle.eq literal || containsLiteralList needle rest
def containsLiteral (clause : Clause σ) (needle : Literal σ) : Bool :=
  containsLiteralList needle clause.literals.toList
def allLiteralsCovered (source target : Clause σ) : Bool :=
  source.literals.toList.all fun literal => target.containsLiteral literal
def containsMatching (clause : Clause σ) (polarity : Bool) (atom : Formula σ) : Bool :=
  clause.literals.toList.any fun literal => literal.matchesAtom polarity atom
def resolutionResult (leftPolarity : Bool) (pivot : Formula σ) (left right : Clause σ) : Clause σ :=
  {
    literals := (filterOutList leftPolarity pivot left.literals.toList ++
        filterOutList (!leftPolarity) pivot right.literals.toList).toArray
  }
def equalityResolutionResult (left right : Term σ) (parent : Clause σ) : Clause σ :=
  parent.filterOut false (.equal left right)
theorem mem_filterOutList_of_mem_of_not_matches
    {polarity : Bool} {atom : Formula σ} {literal : Literal σ} :
    ∀ {literals : List (Literal σ)}, literal ∈ literals →
      literal.matchesAtom polarity atom = false →
        literal ∈ filterOutList polarity atom literals
  | [], hMem, _ => by cases hMem
  | head :: rest, hMem, hNoMatch => by
      by_cases hHead : head.matchesAtom polarity atom = true
      · rw [filterOutList]
        simp [hHead]
        rcases List.mem_cons.mp hMem with hEq | hTail
        · subst hEq
          simp [hHead] at hNoMatch
        · exact mem_filterOutList_of_mem_of_not_matches hTail hNoMatch
      · have hHeadFalse : head.matchesAtom polarity atom = false := by
          cases hValue : head.matchesAtom polarity atom <;> simp [hValue] at hHead ⊢
        rw [filterOutList]
        simp [hHeadFalse]
        rcases List.mem_cons.mp hMem with hEq | hTail
        · exact Or.inl hEq
        · exact Or.inr (mem_filterOutList_of_mem_of_not_matches hTail hNoMatch)
theorem mem_resolutionResult_left
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Formula σ}
    {literal : Literal σ} (hMem : literal ∈ left.literals.toList) (hNoMatch : literal.matchesAtom leftPolarity pivot = false) :
    literal ∈ (resolutionResult leftPolarity pivot left right).literals.toList := by
  simp [resolutionResult]
  exact Or.inl (mem_filterOutList_of_mem_of_not_matches hMem hNoMatch)
theorem mem_resolutionResult_right
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Formula σ}
    {literal : Literal σ} (hMem : literal ∈ right.literals.toList) (hNoMatch : literal.matchesAtom (!leftPolarity) pivot = false) :
    literal ∈ (resolutionResult leftPolarity pivot left right).literals.toList := by
  simp [resolutionResult]
  exact Or.inr (mem_filterOutList_of_mem_of_not_matches hMem hNoMatch)
theorem mem_equalityResolutionResult
    {left right : Term σ} {parent : Clause σ} {literal : Literal σ} (hMem : literal ∈ parent.literals.toList)
    (hNoMatch : literal.matchesAtom false (.equal left right) = false) :
    literal ∈ (equalityResolutionResult left right parent).literals.toList := by
  simpa [equalityResolutionResult, filterOut] using
    mem_filterOutList_of_mem_of_not_matches hMem hNoMatch
theorem containsLiteralList_sound
    {needle : Literal σ} :
    ∀ {literals : List (Literal σ)}, containsLiteralList needle literals = true →
      ∃ literal, literal ∈ literals ∧ literal = needle
  | [], h => by simp [containsLiteralList] at h
  | head :: rest, h => by
      simp [containsLiteralList] at h
      rcases h with hHead | hRest
      · exact ⟨head, List.mem_cons_self, (Literal.eq_sound needle head hHead).symm⟩
      · rcases containsLiteralList_sound hRest with ⟨literal, hMem, hEq⟩
        exact ⟨literal, List.mem_cons_of_mem head hMem, hEq⟩
theorem allLiteralsCovered_sound
    {source target : Clause σ} (hCovered : allLiteralsCovered source target = true) :
    ∀ {literal : Literal σ}, literal ∈ source.literals.toList →
      ∃ literal', literal' ∈ target.literals.toList ∧ literal' = literal := by
  intro literal hMem
  unfold allLiteralsCovered at hCovered
  exact containsLiteralList_sound ((List.all_eq_true.mp hCovered) literal hMem)
end Clause
/-! ## Refutation semantics -/
namespace Clause
def Satisfies   {M : SetLevel.StructureAt.{x} σ} (env : SetLevel.EnvAt.{x} M) (clause : Clause σ) : Prop :=
  Logic.FirstOrder.Formula.satisfies env clause.toFormula
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
private theorem satisfies_toFormulaList_iff_exists_literal
     {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} :
    ∀ literals : List (Literal σ),
      Logic.FirstOrder.Formula.satisfies env (toFormulaList literals) ↔
        ∃ literal, literal ∈ literals ∧ Literal.Satisfies env literal
  | [] => by
      simp [toFormulaList, Logic.FirstOrder.Formula.satisfies]
  | literal :: rest => by
      simp [toFormulaList, Logic.FirstOrder.Formula.satisfies, Literal.Satisfies,
        satisfies_toFormulaList_iff_exists_literal (env := env) rest]
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_iff_exists_literal
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {clause : Clause σ} :
    Satisfies env clause ↔
      ∃ literal, literal ∈ clause.literals.toList ∧ Literal.Satisfies env literal := by
  cases clause
  simp [Satisfies, toFormula, satisfies_toFormulaList_iff_exists_literal]
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_iff_of_agreesOn
    {M : SetLevel.StructureAt.{x} σ} {left right : SetLevel.EnvAt.{x} M} (clause : Clause σ)
    (hEnv : Logic.FirstOrder.Env.AgreesOn clause.freeSupport left right) :
    Satisfies left clause ↔ Satisfies right clause := by
  constructor
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    have hLiteralEnv :
        Logic.FirstOrder.Env.AgreesOn literal.freeSupport left right :=
      hEnv.mono (literal_freeSupport_subset_of_mem hMem)
    exact satisfies_iff_exists_literal.mpr
      ⟨literal, hMem, (Literal.satisfies_iff_of_agreesOn literal hLiteralEnv).mp hLiteral⟩
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    have hLiteralEnv :
        Logic.FirstOrder.Env.AgreesOn literal.freeSupport left right :=
      hEnv.mono (literal_freeSupport_subset_of_mem hMem)
    exact satisfies_iff_exists_literal.mpr
      ⟨literal, hMem, (Literal.satisfies_iff_of_agreesOn literal hLiteralEnv).mpr hLiteral⟩
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_applySubstitution_iff_of_envMatches
     {M : SetLevel.StructureAt.{x} σ}
    {subst : TermSubstitution σ} {env targetEnv : SetLevel.EnvAt.{x} M} (hClosed : TermSubstitution.BoundClosed subst)
    (hEnv : TermSubstitution.EnvMatches subst env targetEnv) (clause : Clause σ) :
    Satisfies env (applySubstitution subst clause) ↔
      Satisfies targetEnv clause := by
  constructor
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    have hMemList :
        literal ∈ clause.literals.toList.map (Literal.applySubstitution subst) := by
      simpa [applySubstitution, Array.toList_map] using hMem
    rcases List.mem_map.mp hMemList with ⟨sourceLiteral, hSourceMem, hEq⟩
    cases hEq
    exact satisfies_iff_exists_literal.mpr
      ⟨sourceLiteral, hSourceMem, (Literal.satisfies_applySubstitution_iff_of_envMatches
          hClosed hEnv sourceLiteral).mp hLiteral⟩
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    exact satisfies_iff_exists_literal.mpr
      ⟨Literal.applySubstitution subst literal,
        by
          have hMappedList :
              Literal.applySubstitution subst literal ∈
                clause.literals.toList.map (Literal.applySubstitution subst) :=
            List.mem_map.mpr ⟨literal, hMem, rfl⟩
          simpa [applySubstitution, Array.toList_map] using hMappedList, (Literal.satisfies_applySubstitution_iff_of_envMatches
          hClosed hEnv literal).mpr hLiteral⟩
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_renameFreeVars_iff_of_envMatches
     {M : SetLevel.StructureAt.{x} σ}
    {offset : Nat} {sourceEnv targetEnv : SetLevel.EnvAt.{x} M} (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) (clause : Clause σ) :
    Satisfies sourceEnv (renameFreeVars offset clause) ↔
      Satisfies targetEnv clause := by
  constructor
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    have hMemList :
        literal ∈ clause.literals.toList.map (Literal.renameFreeVars offset) := by
      simpa [renameFreeVars, Array.toList_map] using hMem
    rcases List.mem_map.mp hMemList with ⟨sourceLiteral, hSourceMem, hEq⟩
    cases hEq
    exact satisfies_iff_exists_literal.mpr
      ⟨sourceLiteral, hSourceMem, (Literal.satisfies_renameFreeVars_iff_of_envMatches
          hEnv sourceLiteral).mp hLiteral⟩
  · intro hSat
    rcases satisfies_iff_exists_literal.mp hSat with
      ⟨literal, hMem, hLiteral⟩
    exact satisfies_iff_exists_literal.mpr
      ⟨Literal.renameFreeVars offset literal,
        by
          have hMappedList :
              Literal.renameFreeVars offset literal ∈
                clause.literals.toList.map (Literal.renameFreeVars offset) :=
            List.mem_map.mpr ⟨literal, hMem, rfl⟩
          simpa [renameFreeVars, Array.toList_map] using hMappedList, (Literal.satisfies_renameFreeVars_iff_of_envMatches
          hEnv literal).mpr hLiteral⟩
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem literals_toList_eq_nil_of_isEmpty  {clause : Clause σ} (hEmpty : clause.isEmpty = true) :
    clause.literals.toList = [] := by
  cases clause with
  | mk literals =>
      have hSize : literals.size = 0 := by
        have hBool : (literals.size == 0) = true := by
          simpa [isEmpty] using hEmpty
        cases h : literals.size with
        | zero => rfl
        | succ n =>
            have hFalse : (literals.size == 0) = false := by
              simp [h]
            rw [hFalse] at hBool
            cases hBool
      have hArray : literals = #[] :=
        Array.eq_empty_of_size_eq_zero hSize
      simp [hArray]
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem not_satisfies_of_isEmpty
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {clause : Clause σ}
    (hEmpty : clause.isEmpty = true) (hSat : Satisfies env clause) : False := by
  have hList := literals_toList_eq_nil_of_isEmpty hEmpty
  rcases satisfies_iff_exists_literal.mp hSat with ⟨literal, hMem, _hLiteral⟩
  rw [hList] at hMem
  cases hMem
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_of_literal_mem
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {clause : Clause σ}
    {literal : Literal σ} (hMem : literal ∈ clause.literals.toList) (hLiteral : Literal.Satisfies env literal) :
    Satisfies env clause :=
  satisfies_iff_exists_literal.mpr ⟨literal, hMem, hLiteral⟩
theorem satisfies_resolutionResult
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Formula σ} (hLeft : Satisfies env left) (hRight : Satisfies env right) :
    Satisfies env (resolutionResult leftPolarity pivot left right) := by
  rcases satisfies_iff_exists_literal.mp hLeft with
    ⟨leftLiteral, hLeftMem, hLeftLiteral⟩
  cases hLeftMatch : leftLiteral.matchesAtom leftPolarity pivot with
  | false =>
      exact satisfies_of_literal_mem (mem_resolutionResult_left hLeftMem hLeftMatch) hLeftLiteral
  | true =>
      rcases satisfies_iff_exists_literal.mp hRight with
        ⟨rightLiteral, hRightMem, hRightLiteral⟩
      cases hRightMatch : rightLiteral.matchesAtom (!leftPolarity) pivot with
      | false =>
          exact satisfies_of_literal_mem (mem_resolutionResult_right hRightMem hRightMatch) hRightLiteral
      | true =>
          exact False.elim (Literal.not_satisfies_matchesAtom_complement
              hLeftMatch hRightMatch hLeftLiteral hRightLiteral)
theorem satisfies_of_allLiteralsCovered
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {source target : Clause σ} (hCovered : source.allLiteralsCovered target = true) (hSource : Satisfies env source) :
    Satisfies env target := by
  rcases satisfies_iff_exists_literal.mp hSource with
    ⟨literal, hMem, hLiteral⟩
  rcases allLiteralsCovered_sound hCovered hMem with
    ⟨literal', hTargetMem, hEq⟩
  cases hEq
  exact satisfies_of_literal_mem hTargetMem hLiteral
theorem satisfies_equalityResolutionResult
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {left right : Term σ} {parent : Clause σ} (hTerm : StructuralEq.term left right = true) (hParent : Satisfies env parent) :
    Satisfies env (equalityResolutionResult left right parent) := by
  rcases satisfies_iff_exists_literal.mp hParent with
    ⟨literal, hMem, hLiteral⟩
  cases hMatch : literal.matchesAtom false (.equal left right) with
  | false =>
      exact satisfies_of_literal_mem (mem_equalityResolutionResult hMem hMatch) hLiteral
  | true =>
      exact False.elim (Literal.not_satisfies_reflexive_negative_equality hTerm hMatch hLiteral)
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_ofFormula
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {φ : Formula σ} (hφ : Logic.FirstOrder.Formula.satisfies env φ) :
    Satisfies env (ofFormula φ) := by
  simp [Satisfies, toFormula, toFormulaList, ofFormula, singleton, Literal.toFormula,
    Literal.pos, Logic.FirstOrder.Formula.satisfies, hφ]
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_ofNegatedFormula
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M} {φ : Formula σ} (hφ : ¬ Logic.FirstOrder.Formula.satisfies env φ) :
    Satisfies env (ofNegatedFormula φ) := by
  simp [Satisfies, toFormula, toFormulaList, ofNegatedFormula, singleton, Literal.toFormula,
    Literal.neg, Logic.FirstOrder.Formula.satisfies, hφ]
end Clause
/-! ## 原生一阶初始字句问题 -/
/--
一阶 DAG 直接消费的初始字句问题。
搜索与证书层只依赖这个结构，不再把公式级前提、目标和局部推理规则混在同一个接口里。
-/
structure ClauseProblem (σ : Signature) where
  initialClauses : Array (Clause σ)
namespace ClauseProblem
def Satisfies   {M : SetLevel.StructureAt.{x} σ} (problem : ClauseProblem σ) (env : SetLevel.EnvAt.{x} M) : Prop :=
  ∀ (index : Nat) (clause : Clause σ),
    problem.initialClauses[index]? = some clause → Clause.Satisfies env clause
def SameBoundStack  {M : SetLevel.StructureAt.{x} σ} (targetEnv sourceEnv : SetLevel.EnvAt.{x} M) : Prop :=
  ∀ sort index, targetEnv.boundVal sort index = sourceEnv.boundVal sort index
/--
初始字句问题在一个 bound stack 上有效。
自由变量环境可以任意变化；bound stack 保持不变，正好对应 substitution 与
standardize-apart 语义环境的稳定边界。
-/
def Valid   {M : SetLevel.StructureAt.{x} σ} (problem : ClauseProblem σ) (sourceEnv : SetLevel.EnvAt.{x} M) : Prop :=
  ∀ targetEnv, SameBoundStack targetEnv sourceEnv → problem.Satisfies targetEnv
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem Valid.of_sameBoundStack
    {M : SetLevel.StructureAt.{x} σ} {problem : ClauseProblem σ}
    {sourceEnv targetEnv : SetLevel.EnvAt.{x} M} (hValid : problem.Valid sourceEnv) (hBound : SameBoundStack targetEnv sourceEnv) :
    problem.Valid targetEnv := by
  intro nextEnv hNext
  exact hValid nextEnv fun sort index =>
    (hNext sort index).trans (hBound sort index)
/--
把公式级问题直接编译成最小原生字句问题。
前提按原顺序占据前缀索引，最后一个索引固定保存目标的否定。
-/
def ofDeepProblem  (problem : DeepProblem σ) : ClauseProblem σ where
  initialClauses := (problem.premises.map Clause.ofFormula).toArray.push (Clause.ofNegatedFormula problem.target)
def negatedTargetIndex  (problem : DeepProblem σ) : Nat :=
  problem.premises.length
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
@[simp]
theorem getElem?_ofDeepProblem_negatedTarget (problem : DeepProblem σ) : (ofDeepProblem problem).initialClauses[negatedTargetIndex problem]? =
      some (Clause.ofNegatedFormula problem.target) := by
  simp [ofDeepProblem, negatedTargetIndex]
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_ofDeepProblem
    {M : SetLevel.StructureAt.{x} σ} (problem : DeepProblem σ) (env : SetLevel.EnvAt.{x} M) (hModels : Logic.FirstOrder.Theory.Models problem.theory env)
    (hTargetFalse : ¬ Logic.FirstOrder.Formula.satisfies env problem.target) : (ofDeepProblem problem).Satisfies env := by
  intro index clause hLookup
  unfold ofDeepProblem at hLookup
  rw [Array.getElem?_push] at hLookup
  by_cases hTargetIndex :
      index = (problem.premises.map Clause.ofFormula).toArray.size
  · rw [if_pos hTargetIndex] at hLookup
    cases Option.some.inj hLookup
    exact Clause.satisfies_ofNegatedFormula hTargetFalse
  · rw [if_neg hTargetIndex] at hLookup
    rw [List.getElem?_toArray, List.getElem?_map] at hLookup
    cases hPremise : problem.premises[index]? with
    | none => simp [hPremise] at hLookup
    | some premise =>
        simp [hPremise] at hLookup
        cases hLookup
        apply Clause.satisfies_ofFormula
        apply hModels
        rcases List.getElem?_eq_some_iff.mp hPremise with ⟨hIndex, hGet⟩
        rw [← hGet]
        exact List.getElem_mem hIndex
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
/--
free-closed 公式级反例可提升为直接编译字句问题的全环境有效性。
闭合合同只留在公式问题到字句问题的边界；DAG 内部规则不再依赖它。
-/
theorem valid_ofDeepProblem_of_freeClosed
     {M : SetLevel.StructureAt.{x} σ} (problem : DeepProblem σ) (env : SetLevel.EnvAt.{x} M) (hClosed : DeepProblem.FreeClosed problem)
    (hModels : Logic.FirstOrder.Theory.Models problem.theory env) (hTargetFalse : ¬ Logic.FirstOrder.Formula.satisfies env problem.target) :
    (ofDeepProblem problem).Valid env := by
  intro targetEnv hBound
  apply satisfies_ofDeepProblem
  · exact DeepProblem.models_of_freeClosed_of_boundVal_eq hClosed
      hBound hModels
  · exact DeepProblem.targetFalse_of_freeClosed_of_boundVal_eq hClosed
      hBound hTargetFalse
end ClauseProblem
/-! ## Guarded clause view -/
abbrev GuardLit := Guards.Lit
abbrev GuardSet := Guards.Set
abbrev GuardedClause (σ : Signature) := Guards.GuardedClause (Clause σ)
namespace GuardedClause
def plain  (clause : Clause σ) : GuardedClause σ :=
  Guards.GuardedClause.plain clause
def unguarded  (gclause : GuardedClause σ) : Bool :=
  Guards.GuardedClause.unguarded gclause
def globallyEmpty  (gclause : GuardedClause σ) : Bool :=
  Guards.GuardedClause.globallyEmpty Clause.isEmpty gclause
def theoryConflict  (gclause : GuardedClause σ) : Bool :=
  Guards.GuardedClause.theoryConflict Clause.isEmpty gclause
def eq (left right : GuardedClause σ) : Bool :=
  Guards.GuardedClause.eq Clause.eq left right
end GuardedClause
/-! ## Node payloads -/
/-! ## Parent snapshots and local evidence -/
structure ParentClause (σ : Signature) where
  id : NodeId
  clause : Clause σ
namespace ParentClause
def idIn (parents : Array NodeId) (parent : ParentClause σ) : Bool :=
  parents.contains parent.id
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem mem_toList_of_idIn  {parents : Array NodeId}
    {parent : ParentClause σ} (hIn : parent.idIn parents = true) :
    parent.id ∈ parents.toList := by
  have hArray : parent.id ∈ parents := by
    simpa [idIn] using hIn
  exact Array.mem_def.mp hArray
def clauseEq (parent : ParentClause σ) (clause : Clause σ) : Bool :=
  parent.clause.eq clause
end ParentClause
structure StandardizeApartSideEvidence (σ : Signature) where
  original : Clause σ
  offset : Nat := 0
  renamed : Clause σ
namespace StandardizeApartSideEvidence
def expected  (evidence : StandardizeApartSideEvidence σ) :
    Clause σ :=
  Clause.renameFreeVars evidence.offset evidence.original
def check (evidence : StandardizeApartSideEvidence σ) :
    Bool :=
  evidence.renamed.eq evidence.expected
theorem check_sound
    {evidence : StandardizeApartSideEvidence σ} (hCheck : evidence.check = true) :
    evidence.renamed = evidence.expected :=
  Clause.eq_sound evidence.renamed evidence.expected hCheck
end StandardizeApartSideEvidence
/--
二元规则的 standardize-apart 证据。
`left/right` 对应 resolution 的左右父字句；在 rewrite/superposition 中对应
`equality/target`。证据显式保存“原始父快照 -> 改名后父快照”这一步。
-/
structure StandardizeApartEvidence (σ : Signature) where
  left : StandardizeApartSideEvidence σ
  right : StandardizeApartSideEvidence σ
namespace StandardizeApartEvidence
def check (evidence : StandardizeApartEvidence σ) :
    Bool :=
  evidence.left.check && evidence.right.check
theorem check_sound
    {evidence : StandardizeApartEvidence σ} (hCheck : evidence.check = true) :
    evidence.left.renamed = evidence.left.expected ∧
      evidence.right.renamed = evidence.right.expected := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
  exact ⟨StandardizeApartSideEvidence.check_sound hLeft,
    StandardizeApartSideEvidence.check_sound hRight⟩
end StandardizeApartEvidence
def standardizeApartCheck (left right : ParentClause σ) (evidence? : Option (StandardizeApartEvidence σ)) : Bool :=
  match evidence? with
  | none => true
  | some evidence =>
      evidence.check && (left.clause.eq evidence.left.original &&
          right.clause.eq evidence.right.original)
namespace StandardizeApartEvidence
theorem check_sound_for_parents
    {left right : ParentClause σ}
    {evidence : StandardizeApartEvidence σ} (hCheck :
      standardizeApartCheck left right (some evidence) = true) :
    evidence.left.renamed =
        Clause.renameFreeVars evidence.left.offset left.clause ∧
      evidence.right.renamed =
        Clause.renameFreeVars evidence.right.offset right.clause := by
  simp only [standardizeApartCheck, StandardizeApartEvidence.check,
    StandardizeApartSideEvidence.check, Bool.and_eq_true] at hCheck
  have hLeftOriginal :
      evidence.left.original = left.clause := (Clause.eq_sound left.clause evidence.left.original hCheck.2.1).symm
  have hRightOriginal :
      evidence.right.original = right.clause := (Clause.eq_sound right.clause evidence.right.original hCheck.2.2).symm
  exact ⟨by
      simpa [StandardizeApartSideEvidence.expected, hLeftOriginal] using
        StandardizeApartSideEvidence.check_sound hCheck.1.1,
    by
      simpa [StandardizeApartSideEvidence.expected, hRightOriginal] using
        StandardizeApartSideEvidence.check_sound hCheck.1.2⟩
def sideEvidence (evidence : StandardizeApartEvidence σ) : Bool → StandardizeApartSideEvidence σ
  | false => evidence.left
  | true => evidence.right
def sideParent (left right : ParentClause σ) : Bool → ParentClause σ
  | false => left
  | true => right
theorem check_sound_for_side
    {left right : ParentClause σ}
    {evidence : StandardizeApartEvidence σ} (side : Bool) (hCheck : standardizeApartCheck left right (some evidence) = true) :
    (sideEvidence evidence side).renamed =
      Clause.renameFreeVars (sideEvidence evidence side).offset (sideParent left right side).clause := by
  cases side
  · simpa [sideEvidence, sideParent] using (check_sound_for_parents hCheck).1
  · simpa [sideEvidence, sideParent] using (check_sound_for_parents hCheck).2
end StandardizeApartEvidence
inductive LocalRuleFamily where
  | parentCdcl
  | equality
  | congruence
  | quantifier
  | theory
  | composite
  deriving Repr, Inhabited, DecidableEq
namespace LocalRuleFamily
def label : LocalRuleFamily → String
  | parentCdcl => "parent-CDCL"
  | equality => "equality"
  | congruence => "congruence"
  | quantifier => "quantifier"
  | theory => "theory"
  | composite => "composite"
def ruleTags : LocalRuleFamily → Array Certificate.RuleTag
  | parentCdcl => #[.localRuleWitness, .parentCdclSkeleton, .firstOrderResolution]
  | equality => #[.localRuleWitness, .termEquality, .demodulation, .firstOrderSuperposition]
  | congruence => #[.localRuleWitness, .formulaCongruence, .argumentCongruence]
  | quantifier => #[.localRuleWitness, .quantifierCongruence]
  | theory => #[.localRuleWitness, .theoryFact]
  | composite => #[.localRuleWitness, .composite]
end LocalRuleFamily
/--
本地规则的可检查 evidence。
无替换规则已经接入当前对象层 soundness-supported 片段；带 substitution 的规则先作为
checked evidence 进入 DAG，等待替换语义引理补齐后再提升到 soundness-supported。
-/
structure ResolutionEvidence (σ : Signature) where
  left : ParentClause σ
  right : ParentClause σ
  pivot : Formula σ
  leftPolarity : Bool := true
  substitution : TermSubstitution σ := []
  standardizeApart? : Option (StandardizeApartEvidence σ) := none
structure FactoringEvidence (σ : Signature) where
  parent : ParentClause σ
  substitution : TermSubstitution σ := []
structure EqualityResolutionEvidence (σ : Signature) where
  parent : ParentClause σ
  left : Term σ
  right : Term σ
  substitution : TermSubstitution σ := []
inductive RewriteKind where
  | demodulation
  | positiveSuperposition
  | negativeSuperposition
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr
namespace RewriteKind
def label : RewriteKind → String
  | demodulation => "demodulation"
  | positiveSuperposition => "positive superposition"
  | negativeSuperposition => "negative superposition"
end RewriteKind
inductive TermContext (σ : Signature) where
  | hole
  | app (f : σ.FuncSymbol) (before : List (Term σ)) (ctx : TermContext σ) (suffix : List (Term σ))
namespace TermContext
def fill : TermContext σ → Term σ → Term σ
  | hole, term => term
  | app f before ctx suffix, term =>
      .app f (before ++ [fill ctx term] ++ suffix)
omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem eval_fill_eq_of_eq
     {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {ctx : TermContext σ} {lhs rhs : Term σ} (hEq : Logic.FirstOrder.Term.eval env lhs = Logic.FirstOrder.Term.eval env rhs) :
    Logic.FirstOrder.Term.eval env (ctx.fill lhs) =
      Logic.FirstOrder.Term.eval env (ctx.fill rhs) := by
  induction ctx generalizing lhs rhs with
  | hole =>
      simpa [fill] using hEq
  | app f before ctx suffix ih =>
      have hArgs : (before ++ [fill ctx lhs] ++ suffix).map (Logic.FirstOrder.Term.eval env) = (before ++ [fill ctx rhs] ++ suffix).map
              (Logic.FirstOrder.Term.eval env) := by
        simp [List.map_append, ih hEq]
      simpa [fill, Logic.FirstOrder.Term.eval, List.map_append] using
        congrArg (M.funcInterp f) hArgs
end TermContext
inductive AtomContext (σ : Signature) where
  | rel (r : σ.RelSymbol) (before : List (Term σ)) (ctx : TermContext σ) (suffix : List (Term σ))
  | equalLeft (ctx : TermContext σ) (right : Term σ)
  | equalRight (left : Term σ) (ctx : TermContext σ)
namespace AtomContext
def isEquality : AtomContext σ → Bool
  | rel _ _ _ _ => false
  | equalLeft _ _ => true
  | equalRight _ _ => true
def fill : AtomContext σ → Term σ → Formula σ
  | rel r before ctx suffix, term =>
      .rel r (before ++ [ctx.fill term] ++ suffix)
  | equalLeft ctx right, term =>
      .equal (ctx.fill term) right
  | equalRight left ctx, term =>
      .equal left (ctx.fill term)
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_iff_of_eval_eq
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {ctx : AtomContext σ} {lhs rhs : Term σ} (hEq : Logic.FirstOrder.Term.eval env lhs = Logic.FirstOrder.Term.eval env rhs) :
    Logic.FirstOrder.Formula.satisfies env (ctx.fill lhs) ↔
      Logic.FirstOrder.Formula.satisfies env (ctx.fill rhs) := by
  cases ctx with
  | rel r before ctx suffix =>
      have hArgs : (before ++ [ctx.fill lhs] ++ suffix).map (Logic.FirstOrder.Term.eval env) = (before ++ [ctx.fill rhs] ++ suffix).map
              (Logic.FirstOrder.Term.eval env) := by
        simp [List.map_append, TermContext.eval_fill_eq_of_eq hEq]
      change M.relInterp r ((before ++ [ctx.fill lhs] ++ suffix).map (Logic.FirstOrder.Term.eval env)) ↔
        M.relInterp r ((before ++ [ctx.fill rhs] ++ suffix).map (Logic.FirstOrder.Term.eval env))
      rw [hArgs]
  | equalLeft ctx right =>
      have hTerm := TermContext.eval_fill_eq_of_eq (ctx := ctx) hEq
      simp [fill, Logic.FirstOrder.Formula.satisfies, hTerm]
  | equalRight left ctx =>
      have hTerm := TermContext.eval_fill_eq_of_eq (ctx := ctx) hEq
      simp [fill, Logic.FirstOrder.Formula.satisfies, hTerm]
end AtomContext
def literalOfContext  (polarity : Bool) (ctx : AtomContext σ) (term : Term σ) :
    Literal σ :=
  { polarity := polarity, atom := ctx.fill term }
def rewriteLiteralList (needle replacement : Literal σ) :
    List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if literal.eq needle then
        replacement :: rewriteLiteralList needle replacement rest
      else
        literal :: rewriteLiteralList needle replacement rest
structure RewriteEvidence (σ : Signature) where
  equality : ParentClause σ
  target : ParentClause σ
  substitution : TermSubstitution σ := []
  standardizeApart? : Option (StandardizeApartEvidence σ) := none
  context : AtomContext σ
  lhs : Term σ
  rhs : Term σ
  equalityReversed : Bool := false
  targetPolarity : Bool := true
namespace RewriteEvidence
def equalityBaseClause (evidence : RewriteEvidence σ) : Clause σ :=
  match evidence.standardizeApart? with
  | none => evidence.equality.clause
  | some standardizeApart => standardizeApart.left.renamed
def targetBaseClause (evidence : RewriteEvidence σ) : Clause σ :=
  match evidence.standardizeApart? with
  | none => evidence.target.clause
  | some standardizeApart => standardizeApart.right.renamed
def equalityClause (evidence : RewriteEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.equalityBaseClause
def targetClause (evidence : RewriteEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.targetBaseClause
def equalityAtom  (evidence : RewriteEvidence σ) : Formula σ :=
  if evidence.equalityReversed then
    .equal evidence.rhs evidence.lhs
  else
    .equal evidence.lhs evidence.rhs
def needle  (evidence : RewriteEvidence σ) : Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.lhs
def replacement  (evidence : RewriteEvidence σ) : Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.rhs
def result (evidence : RewriteEvidence σ) : Clause σ :=
  { literals := (Clause.filterOutList true evidence.equalityAtom
          evidence.equalityClause.literals.toList ++
        rewriteLiteralList evidence.needle evidence.replacement
          evidence.targetClause.literals.toList).toArray }
def kindCheck  (kind : RewriteKind) (evidence : RewriteEvidence σ) : Bool :=
  match kind with
  | .demodulation => decide (evidence.equalityClause.literals.size = 1)
  | .positiveSuperposition => evidence.targetPolarity
  | .negativeSuperposition =>
      !evidence.targetPolarity && evidence.context.isEquality
def check (kind : RewriteKind) (conclusion : Clause σ) (evidence : RewriteEvidence σ) : Bool :=
  standardizeApartCheck evidence.equality evidence.target evidence.standardizeApart? && (TermSubstitution.checkAdmissible evidence.substitution &&
      (evidence.equalityClause.containsMatching true evidence.equalityAtom && (evidence.targetClause.containsLiteral evidence.needle &&
          (kindCheck kind evidence &&
            conclusion.eq (result evidence)))))
theorem check_admissible
    {kind : RewriteKind} {conclusion : Clause σ}
    {evidence : RewriteEvidence σ} (hCheck : check kind conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  simp only [RewriteEvidence.check, Bool.and_eq_true] at hCheck
  exact TermSubstitution.checkAdmissible_sound hCheck.2.1
theorem check_conclusion
  {kind : RewriteKind} {conclusion : Clause σ}
  {evidence : RewriteEvidence σ} (hCheck : check kind conclusion evidence = true) :
  conclusion = result evidence := by
  simp only [RewriteEvidence.check, Bool.and_eq_true] at hCheck
  exact Clause.eq_sound conclusion (result evidence) hCheck.2.2.2.2.2
theorem eval_eq_of_parent
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {evidence : RewriteEvidence σ}
    {literal : Literal σ} (hMatch : literal.matchesAtom true evidence.equalityAtom = true) (hLiteral : Literal.Satisfies env literal) :
    Logic.FirstOrder.Term.eval env evidence.lhs =
      Logic.FirstOrder.Term.eval env evidence.rhs := by
  cases literal with
  | mk polarity atom =>
      rcases Literal.matchesAtom_sound hMatch with ⟨hPolarity, hAtom⟩
      cases polarity
      · simp at hPolarity
      · cases hReversed : evidence.equalityReversed with
        | false =>
            have hAtom' :
                atom = (.equal evidence.lhs evidence.rhs : Formula σ) := by
              simpa [equalityAtom, hReversed] using hAtom
            cases hAtom'
            simpa [Literal.Satisfies, Literal.toFormula,
              Logic.FirstOrder.Formula.satisfies] using hLiteral
        | true =>
            have hAtom' :
                atom = (.equal evidence.rhs evidence.lhs : Formula σ) := by
              simpa [equalityAtom, hReversed] using hAtom
            cases hAtom'
            have hReverse :
                Logic.FirstOrder.Term.eval env evidence.rhs =
                  Logic.FirstOrder.Term.eval env evidence.lhs := by
              simpa [Literal.Satisfies, Literal.toFormula,
                Logic.FirstOrder.Formula.satisfies] using hLiteral
            exact hReverse.symm
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_iff_replacement
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {evidence : RewriteEvidence σ} (hEq : Logic.FirstOrder.Term.eval env evidence.lhs =
      Logic.FirstOrder.Term.eval env evidence.rhs) :
    Literal.Satisfies env evidence.needle ↔ Literal.Satisfies env evidence.replacement := by
  cases evidence with
  | mk equality target _substitution _standardizeApart context lhs rhs
      equalityReversed targetPolarity =>
      have hAtom := AtomContext.satisfies_iff_of_eval_eq (ctx := context) hEq
      cases targetPolarity <;>
        simp [needle, replacement, literalOfContext, Literal.Satisfies,
          Literal.toFormula, Logic.FirstOrder.Formula.satisfies, hAtom]
private theorem satisfies_rewriteLiteralList
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {needle replacement : Literal σ} (hRewrite : Literal.Satisfies env needle → Literal.Satisfies env replacement) :
    ∀ {literals : List (Literal σ)}, (∃ literal, literal ∈ literals ∧ Literal.Satisfies env literal) →
        ∃ literal, literal ∈ rewriteLiteralList needle replacement literals ∧
          Literal.Satisfies env literal
  | [], h => by
      rcases h with ⟨literal, hMem, _hSat⟩
      cases hMem
  | literal :: rest, h => by
      rcases h with ⟨witness, hMem, hSat⟩
      by_cases hMatch : literal.eq needle = true
      · have hLiteralEq : literal = needle := Literal.eq_sound literal needle hMatch
        rw [rewriteLiteralList, hMatch]
        rcases List.mem_cons.mp hMem with hHead | hTail
        · have hSatLiteral : Literal.Satisfies env literal := by
            simpa [hHead] using hSat
          exact ⟨replacement, by simp, hRewrite (by simpa [hLiteralEq] using hSatLiteral)⟩
        · rcases satisfies_rewriteLiteralList (literals := rest) hRewrite
              ⟨witness, hTail, hSat⟩ with
            ⟨witness', hMem', hSat'⟩
          exact ⟨witness', by simp [hMem'], hSat'⟩
      · have hNoMatch : literal.eq needle = false := by
          cases hValue : literal.eq needle <;> simp [hValue] at hMatch ⊢
        rw [rewriteLiteralList, hNoMatch]
        rcases List.mem_cons.mp hMem with hHead | hTail
        · have hSatLiteral : Literal.Satisfies env literal := by
            simpa [hHead] using hSat
          exact ⟨literal, by simp, hSatLiteral⟩
        · rcases satisfies_rewriteLiteralList (literals := rest) hRewrite
              ⟨witness, hTail, hSat⟩ with
            ⟨witness', hMem', hSat'⟩
          exact ⟨witness', by simp [hMem'], hSat'⟩
theorem satisfies_result
    {M : SetLevel.StructureAt.{x} σ} {env : SetLevel.EnvAt.{x} M}
    {evidence : RewriteEvidence σ} (hEquality : Clause.Satisfies env evidence.equalityClause) (hTarget : Clause.Satisfies env evidence.targetClause) :
    Clause.Satisfies env (result evidence) := by
  rcases Clause.satisfies_iff_exists_literal.mp hEquality with
    ⟨equalityLiteral, hEqualityMem, hEqualitySat⟩
  cases hMatch : equalityLiteral.matchesAtom true evidence.equalityAtom with
  | false =>
      exact Clause.satisfies_of_literal_mem (by
          simp [result]
          exact Or.inl (Clause.mem_filterOutList_of_mem_of_not_matches (polarity := true) (atom := evidence.equalityAtom)
            (literal := equalityLiteral) hEqualityMem hMatch))
        hEqualitySat
  | true =>
      have hEq :
          Logic.FirstOrder.Term.eval env evidence.lhs =
            Logic.FirstOrder.Term.eval env evidence.rhs :=
        eval_eq_of_parent (evidence := evidence) hMatch hEqualitySat
      have hRewrite :
          Literal.Satisfies env evidence.needle →
            Literal.Satisfies env evidence.replacement := (satisfies_iff_replacement (evidence := evidence) hEq).mp
      have hTarget' :=
        satisfies_rewriteLiteralList (needle := evidence.needle) (replacement := evidence.replacement) hRewrite (by
            rcases Clause.satisfies_iff_exists_literal.mp hTarget with
              ⟨targetLiteral, hTargetMem, hTargetSat⟩
            exact ⟨targetLiteral, hTargetMem, hTargetSat⟩)
      rcases hTarget' with ⟨literal, hMem, hSat⟩
      exact Clause.satisfies_of_literal_mem (by
          simp [result]
          exact Or.inr hMem)
        hSat
end RewriteEvidence
namespace ResolutionEvidence
def leftBaseClause (evidence : ResolutionEvidence σ) : Clause σ :=
  match evidence.standardizeApart? with
  | none => evidence.left.clause
  | some standardizeApart => standardizeApart.left.renamed
def rightBaseClause (evidence : ResolutionEvidence σ) : Clause σ :=
  match evidence.standardizeApart? with
  | none => evidence.right.clause
  | some standardizeApart => standardizeApart.right.renamed
def leftClause (evidence : ResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.leftBaseClause
def rightClause (evidence : ResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.rightBaseClause
def check (conclusion : Clause σ) (evidence : ResolutionEvidence σ) : Bool :=
  standardizeApartCheck evidence.left evidence.right evidence.standardizeApart? && (TermSubstitution.checkAdmissible evidence.substitution &&
      (evidence.leftClause.containsMatching evidence.leftPolarity evidence.pivot &&
        (evidence.rightClause.containsMatching (!evidence.leftPolarity) evidence.pivot &&
          conclusion.eq (Clause.resolutionResult evidence.leftPolarity evidence.pivot
              evidence.leftClause evidence.rightClause))))
theorem check_admissible
    {conclusion : Clause σ}
    {evidence : ResolutionEvidence σ} (hCheck : check conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  simp only [ResolutionEvidence.check, Bool.and_eq_true] at hCheck
  exact TermSubstitution.checkAdmissible_sound hCheck.2.1
theorem check_conclusion
    {conclusion : Clause σ}
    {evidence : ResolutionEvidence σ} (hCheck : check conclusion evidence = true) :
    conclusion =
      Clause.resolutionResult evidence.leftPolarity evidence.pivot
        evidence.leftClause evidence.rightClause := by
  simp only [ResolutionEvidence.check, Bool.and_eq_true] at hCheck
  exact Clause.eq_sound conclusion (Clause.resolutionResult evidence.leftPolarity evidence.pivot
      evidence.leftClause evidence.rightClause) hCheck.2.2.2.2
end ResolutionEvidence
namespace FactoringEvidence
def parentClause (evidence : FactoringEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.parent.clause
def check (conclusion : Clause σ) (evidence : FactoringEvidence σ) : Bool :=
  TermSubstitution.checkAdmissible evidence.substitution && (evidence.parentClause.allLiteralsCovered conclusion &&
      (conclusion.allLiteralsCovered evidence.parentClause &&
        decide (conclusion.literals.size <= evidence.parentClause.literals.size)))
theorem check_admissible
    {conclusion : Clause σ}
    {evidence : FactoringEvidence σ} (hCheck : check conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  simp only [FactoringEvidence.check, Bool.and_eq_true] at hCheck
  exact TermSubstitution.checkAdmissible_sound hCheck.1
theorem check_sound
    {conclusion : Clause σ}
    {evidence : FactoringEvidence σ} (hCheck : check conclusion evidence = true) :
    evidence.parentClause.allLiteralsCovered conclusion = true ∧
      conclusion.allLiteralsCovered evidence.parentClause = true ∧
        conclusion.literals.size <= evidence.parentClause.literals.size := by
  simp only [FactoringEvidence.check, Bool.and_eq_true] at hCheck
  exact ⟨hCheck.2.1, hCheck.2.2.1, by simpa using hCheck.2.2.2⟩
end FactoringEvidence
namespace EqualityResolutionEvidence
def parentClause (evidence : EqualityResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.parent.clause
def check (conclusion : Clause σ) (evidence : EqualityResolutionEvidence σ) : Bool :=
  TermSubstitution.checkAdmissible evidence.substitution && (StructuralEq.term evidence.left evidence.right &&
      (evidence.parentClause.containsMatching false (.equal evidence.left evidence.right) &&
        conclusion.eq (Clause.equalityResolutionResult evidence.left evidence.right
            evidence.parentClause)))
theorem check_admissible
    {conclusion : Clause σ}
    {evidence : EqualityResolutionEvidence σ} (hCheck : check conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  simp only [EqualityResolutionEvidence.check, Bool.and_eq_true] at hCheck
  exact TermSubstitution.checkAdmissible_sound hCheck.1
theorem check_sound
    {conclusion : Clause σ}
    {evidence : EqualityResolutionEvidence σ} (hCheck : check conclusion evidence = true) :
    StructuralEq.term evidence.left evidence.right = true ∧
      evidence.parentClause.containsMatching false (.equal evidence.left evidence.right) = true ∧
        conclusion =
          Clause.equalityResolutionResult evidence.left evidence.right evidence.parentClause := by
  simp only [EqualityResolutionEvidence.check, Bool.and_eq_true] at hCheck
  exact ⟨hCheck.2.1, hCheck.2.2.1,
    Clause.eq_sound conclusion (Clause.equalityResolutionResult evidence.left evidence.right evidence.parentClause)
      hCheck.2.2.2⟩
end EqualityResolutionEvidence
end DAGCertificateSignature
end DAGCertificate
end Automation
end YesMetaZFC
