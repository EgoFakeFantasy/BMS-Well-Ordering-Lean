import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Logic.Signature

/-!
# DAG 证书的可计算语法

本模块只定义搜索器和证书检查器使用的有限原始语法。它与可信逻辑语法严格分离：
原始语法允许自然数变量编号，可信语法仍由类型索引保证排序与作用域。两者之间只能
通过后续的检查编译器连接。

所有闭合性和良构性命题都直接定义为对应布尔检查等于真，不再复制一套递归 Prop，
因此 checker 结果可直接作为证书事实消费。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate

abbrev Signature := Logic.Signature.{0, 0, 0}
abbrev NodeId := Certificate.NodeId

variable {σ : Signature}

/-- 证书语法中的显式变量编号。 -/
inductive Variable (σ : Signature) where
  | bvar (sort : σ.SortSymbol) (index : Nat)
  | fvar (sort : σ.SortSymbol) (id : Nat)

/-- 证书语法中的一阶项。 -/
inductive Term (σ : Signature) where
  | var (entry : Variable σ)
  | app (function : σ.FuncSymbol) (arguments : List (Term σ))

/-- 证书语法中的一阶公式。 -/
inductive Formula (σ : Signature) where
  | falsum
  | truth
  | rel (relation : σ.RelSymbol) (arguments : List (Term σ))
  | equal (left right : Term σ)
  | neg (body : Formula σ)
  | conj (left right : Formula σ)
  | disj (left right : Formula σ)
  | imp (left right : Formula σ)
  | iff (left right : Formula σ)
  | forallE (sort : σ.SortSymbol) (body : Formula σ)
  | existsE (sort : σ.SortSymbol) (body : Formula σ)

/-- 公式级证书输入；进入可信边界前必须被编译为闭句问题。 -/
structure Problem (σ : Signature) where
  premises : List (Formula σ) := []
  target : Formula σ

mutual

/-- 项的线性节点权重，供递归证明和后续资源界限共用。 -/
def Term.weight : Term σ → Nat
  | .var _ => 1
  | .app _ arguments => weightList arguments + 1

def Term.weightList : List (Term σ) → Nat
  | [] => 0
  | term :: rest => term.weight + weightList rest + 1

end

theorem array_check_of_mem {α : Type} {check : α → Bool}
    {values : Array α} (hCheck : values.all check = true)
    {value : α} (hMem : value ∈ values.toList) : check value = true := by
  exact Array.all_eq_true_iff_forall_mem.mp hCheck value
    (Array.mem_def.mpr hMem)

/-! ## 结构相等 -/

namespace StructuralEq

mutual

def term [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] :
    Term σ → Term σ → Bool
  | .var (.bvar sort index), .var (.bvar otherSort otherIndex)
  | .var (.fvar sort index), .var (.fvar otherSort otherIndex) =>
      decide (sort = otherSort) && index == otherIndex
  | .app function arguments, .app otherFunction otherArguments =>
      decide (function = otherFunction) &&
        termList arguments otherArguments
  | _, _ => false

def termList [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] :
    List (Term σ) → List (Term σ) → Bool
  | [], [] => true
  | head :: tail, otherHead :: otherTail =>
      term head otherHead && termList tail otherTail
  | _, _ => false

end

def formula [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] :
    Formula σ → Formula σ → Bool
  | .falsum, .falsum
  | .truth, .truth => true
  | .rel relation arguments, .rel otherRelation otherArguments =>
      decide (relation = otherRelation) &&
        termList arguments otherArguments
  | .equal left right, .equal otherLeft otherRight =>
      term left otherLeft && term right otherRight
  | .neg body, .neg otherBody =>
      formula body otherBody
  | .conj left right, .conj otherLeft otherRight
  | .disj left right, .disj otherLeft otherRight
  | .imp left right, .imp otherLeft otherRight
  | .iff left right, .iff otherLeft otherRight =>
      formula left otherLeft && formula right otherRight
  | .forallE sort body, .forallE otherSort otherBody
  | .existsE sort body, .existsE otherSort otherBody =>
      decide (sort = otherSort) && formula body otherBody
  | _, _ => false

mutual

@[simp] theorem term_refl [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] (input : Term σ) :
    term input input = true := by
  cases input with
  | var entry =>
      cases entry <;> simp [term]
  | app function arguments =>
      simp [term, termList_refl arguments]

@[simp] theorem termList_refl [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] (input : List (Term σ)) :
    termList input input = true := by
  cases input with
  | nil => rfl
  | cons head tail =>
      simp [termList, term_refl head, termList_refl tail]

end

@[simp] theorem formula_refl [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (input : Formula σ) :
    formula input input = true := by
  induction input <;> simp_all [formula]

theorem term_eq_true_of_eq [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] {left right : Term σ}
    (equality : left = right) :
    term left right = true := by
  subst right
  exact term_refl left

theorem termList_eq_true_of_eq [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] {left right : List (Term σ)}
    (equality : left = right) :
    termList left right = true := by
  subst right
  exact termList_refl left

theorem formula_eq_true_of_eq [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {left right : Formula σ} (equality : left = right) :
    formula left right = true := by
  subst right
  exact formula_refl left

mutual

private theorem term_sound_aux [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] :
    ∀ {left right : Term σ}, term left right = true → left = right
  | .var (.bvar sort index), .var (.bvar otherSort otherIndex), h => by
      simp [term] at h
      rcases h with ⟨hSort, hIndex⟩
      cases hSort
      cases hIndex
      rfl
  | .var (.fvar sort id), .var (.fvar otherSort otherId), h => by
      simp [term] at h
      rcases h with ⟨hSort, hId⟩
      cases hSort
      cases hId
      rfl
  | .app function arguments, .app otherFunction otherArguments, h => by
      simp [term] at h
      rcases h with ⟨hFunction, hArguments⟩
      cases hFunction
      exact congrArg (Term.app function)
        (termList_sound_aux hArguments)
  | .var (.bvar ..), .var (.fvar ..), h => by
      simp [term] at h
  | .var (.fvar ..), .var (.bvar ..), h => by
      simp [term] at h
  | .var (.bvar ..), .app .., h => by
      simp [term] at h
  | .var (.fvar ..), .app .., h => by
      simp [term] at h
  | .app .., .var (.bvar ..), h => by
      simp [term] at h
  | .app .., .var (.fvar ..), h => by
      simp [term] at h
  termination_by left right _ => left.weight + right.weight
  decreasing_by
    all_goals
      simp [Term.weight]
      omega

private theorem termList_sound_aux [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] :
    ∀ {left right : List (Term σ)},
      termList left right = true → left = right
  | [], [], _ => rfl
  | [], _ :: _, h
  | _ :: _, [], h => by
      simp [termList] at h
  | head :: tail, otherHead :: otherTail, h => by
      simp [termList] at h
      rcases h with ⟨hHead, hTail⟩
      rw [term_sound_aux hHead, termList_sound_aux hTail]
  termination_by left right _ =>
    Term.weightList left + Term.weightList right
  decreasing_by
    all_goals
      simp [Term.weightList]
      omega

end

theorem term_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] (left right : Term σ) :
    term left right = true → left = right :=
  term_sound_aux

theorem termList_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] (left right : List (Term σ)) :
    termList left right = true → left = right :=
  termList_sound_aux

theorem formula_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left : Formula σ) :
    ∀ right : Formula σ, formula left right = true → left = right := by
  induction left with
  | falsum =>
      intro right h
      cases right <;> simp [formula] at h ⊢
  | truth =>
      intro right h
      cases right <;> simp [formula] at h ⊢
  | rel relation arguments =>
      intro right h
      cases right with
      | rel otherRelation otherArguments =>
          simp [formula] at h
          rcases h with ⟨hRelation, hArguments⟩
          cases hRelation
          exact congrArg (Formula.rel relation)
            (termList_sound arguments otherArguments hArguments)
      | _ => simp [formula] at h
  | equal leftTerm rightTerm =>
      intro right h
      cases right with
      | equal otherLeft otherRight =>
          simp [formula] at h
          rcases h with ⟨hLeft, hRight⟩
          have hLeftEq := term_sound leftTerm otherLeft hLeft
          have hRightEq := term_sound rightTerm otherRight hRight
          cases hLeftEq
          cases hRightEq
          rfl
      | _ => simp [formula] at h
  | neg body ih =>
      intro right h
      cases right with
      | neg otherBody =>
          exact congrArg Formula.neg (ih otherBody h)
      | _ => simp [formula] at h
  | conj left right ihLeft ihRight
  | disj left right ihLeft ihRight
  | imp left right ihLeft ihRight
  | iff left right ihLeft ihRight =>
      intro other h
      cases other <;> simp [formula] at h
      all_goals
        rcases h with ⟨hLeft, hRight⟩
        have hLeftEq := ihLeft _ hLeft
        have hRightEq := ihRight _ hRight
        cases hLeftEq
        cases hRightEq
        rfl
  | forallE sort body ih
  | existsE sort body ih =>
      intro right h
      cases right <;> simp [formula] at h
      all_goals
        rcases h with ⟨hSort, hBody⟩
        cases hSort
        have hBodyEq := ih _ hBody
        cases hBodyEq
        rfl

end StructuralEq

/-! ## 排序与作用域检查 -/

namespace Term

def lookupBound? : List σ.SortSymbol → Nat → Option σ.SortSymbol
  | [], _ => none
  | sort :: _, 0 => some sort
  | _ :: rest, index + 1 => lookupBound? rest index

mutual

def inferSortWith [DecidableEq σ.SortSymbol]
    (bound : List σ.SortSymbol) : Term σ → Option σ.SortSymbol
  | .var (.bvar sort index) =>
      if lookupBound? bound index = some sort then some sort else none
  | .var (.fvar sort _) => some sort
  | .app function arguments => do
      let sorts ← inferSortListWith bound arguments
      if sorts = σ.funcDomain function then
        some (σ.funcCodomain function)
      else
        none

def inferSortListWith [DecidableEq σ.SortSymbol]
    (bound : List σ.SortSymbol) :
    List (Term σ) → Option (List σ.SortSymbol)
  | [] => some []
  | term :: rest => do
      let sort ← inferSortWith bound term
      let sorts ← inferSortListWith bound rest
      pure (sort :: sorts)

end

def inferSort? [DecidableEq σ.SortSymbol]
    (term : Term σ) : Option σ.SortSymbol :=
  inferSortWith [] term

def checkAt [DecidableEq σ.SortSymbol]
    (bound : List σ.SortSymbol) (sort : σ.SortSymbol)
    (term : Term σ) : Bool :=
  decide (inferSortWith bound term = some sort)

def check [DecidableEq σ.SortSymbol]
    (sort : σ.SortSymbol) (term : Term σ) : Bool :=
  checkAt [] sort term

mutual

def checkBoundClosed : Term σ → Bool
  | .var (.bvar ..) => false
  | .var (.fvar ..) => true
  | .app _ arguments => checkBoundClosedList arguments

def checkBoundClosedList : List (Term σ) → Bool
  | [] => true
  | term :: rest =>
      checkBoundClosed term && checkBoundClosedList rest

end

mutual

def checkFreeClosed : Term σ → Bool
  | .var (.bvar ..) => true
  | .var (.fvar ..) => false
  | .app _ arguments => checkFreeClosedList arguments

def checkFreeClosedList : List (Term σ) → Bool
  | [] => true
  | term :: rest =>
      checkFreeClosed term && checkFreeClosedList rest

end

abbrev BoundClosed (term : Term σ) : Prop :=
  checkBoundClosed term = true

abbrev FreeClosed (term : Term σ) : Prop :=
  checkFreeClosed term = true

abbrev WellSorted [DecidableEq σ.SortSymbol]
    (term : Term σ) (sort : σ.SortSymbol) : Prop :=
  check sort term = true

theorem checkBoundClosed_sound {term : Term σ} :
    checkBoundClosed term = true → BoundClosed term :=
  id

theorem checkFreeClosed_sound {term : Term σ} :
    checkFreeClosed term = true → FreeClosed term :=
  id

mutual

def applySubstitution [DecidableEq σ.SortSymbol]
    (subst : List (σ.SortSymbol × Nat × Term σ)) :
    Term σ → Term σ
  | .var (.fvar sort id) =>
      match subst.find? (fun entry =>
          decide (entry.1 = sort) && entry.2.1 == id) with
      | some entry => entry.2.2
      | none => .var (.fvar sort id)
  | .var (.bvar sort index) => .var (.bvar sort index)
  | .app function arguments =>
      .app function (applySubstitutionList subst arguments)

def applySubstitutionList [DecidableEq σ.SortSymbol]
    (subst : List (σ.SortSymbol × Nat × Term σ)) :
    List (Term σ) → List (Term σ)
  | [] => []
  | head :: tail =>
      applySubstitution subst head ::
        applySubstitutionList subst tail

end

theorem applySubstitutionList_eq_map [DecidableEq σ.SortSymbol]
    (subst : List (σ.SortSymbol × Nat × Term σ)) :
    ∀ input : List (Term σ),
      applySubstitutionList subst input =
        input.map (applySubstitution subst)
  | [] => rfl
  | _ :: tail => by
      simp [applySubstitutionList,
        applySubstitutionList_eq_map subst tail]

mutual

def renameFreeVars (offset : Nat) : Term σ → Term σ
  | .var (.fvar sort id) => .var (.fvar sort (id + offset))
  | .var (.bvar sort index) => .var (.bvar sort index)
  | .app function arguments =>
      .app function (renameFreeVarsList offset arguments)

def renameFreeVarsList (offset : Nat) :
    List (Term σ) → List (Term σ)
  | [] => []
  | head :: tail =>
      renameFreeVars offset head :: renameFreeVarsList offset tail

end

theorem renameFreeVarsList_eq_map (offset : Nat) :
    ∀ input : List (Term σ),
      renameFreeVarsList offset input =
        input.map (renameFreeVars offset)
  | [] => rfl
  | _ :: tail => by
      simp [renameFreeVarsList, renameFreeVarsList_eq_map offset tail]

mutual

theorem renameFreeVars_zero (input : Term σ) :
    renameFreeVars 0 input = input := by
  cases input with
  | var entry =>
      cases entry <;> simp [renameFreeVars]
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

theorem eq_renameFreeVars_of_offset_eq_zero
    (input : Term σ) (offset : Nat) (hOffset : offset = 0) :
    input = renameFreeVars offset input := by
  subst offset
  exact (renameFreeVars_zero input).symm

def freeSupport : Term σ → List (σ.SortSymbol × Nat)
  | .var (.bvar ..) => []
  | .var (.fvar sort id) => [(sort, id)]
  | .app _ arguments =>
      arguments.flatMap freeSupport

end Term

abbrev TermSubstitution (σ : Signature) :=
  List (σ.SortSymbol × Nat × Term σ)

namespace TermSubstitution

def empty : TermSubstitution σ := []

def lookup [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) (sort : σ.SortSymbol) (id : Nat) :
    Option (Term σ) :=
  match subst.find? (fun entry =>
      decide (entry.1 = sort) && entry.2.1 == id) with
  | some entry => some entry.2.2
  | none => none

def checkBoundClosed (subst : TermSubstitution σ) : Bool :=
  subst.all fun entry => Term.checkBoundClosed entry.2.2

def checkWellSorted [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) : Bool :=
  subst.all fun entry => Term.check entry.1 entry.2.2

def checkAdmissible [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) : Bool :=
  checkBoundClosed subst && checkWellSorted subst

abbrev BoundClosed (subst : TermSubstitution σ) : Prop :=
  checkBoundClosed subst = true

abbrev WellSorted [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) : Prop :=
  checkWellSorted subst = true

abbrev Admissible [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) : Prop :=
  checkAdmissible subst = true

theorem checkBoundClosed_sound {subst : TermSubstitution σ} :
    checkBoundClosed subst = true → BoundClosed subst :=
  id

theorem checkWellSorted_sound [DecidableEq σ.SortSymbol]
    {subst : TermSubstitution σ} :
    checkWellSorted subst = true → WellSorted subst :=
  id

theorem checkAdmissible_sound [DecidableEq σ.SortSymbol]
    {subst : TermSubstitution σ}
    (hCheck : checkAdmissible subst = true) :
    BoundClosed subst ∧ WellSorted subst :=
  Bool.and_eq_true_iff.mp hCheck

end TermSubstitution

namespace Formula

def mapTerms (transform : Term σ → Term σ) : Formula σ → Formula σ
  | .falsum => .falsum
  | .truth => .truth
  | .rel relation arguments => .rel relation (arguments.map transform)
  | .equal left right => .equal (transform left) (transform right)
  | .neg body => .neg (mapTerms transform body)
  | .conj left right =>
      .conj (mapTerms transform left) (mapTerms transform right)
  | .disj left right =>
      .disj (mapTerms transform left) (mapTerms transform right)
  | .imp left right =>
      .imp (mapTerms transform left) (mapTerms transform right)
  | .iff left right =>
      .iff (mapTerms transform left) (mapTerms transform right)
  | .forallE sort body => .forallE sort (mapTerms transform body)
  | .existsE sort body => .existsE sort (mapTerms transform body)

def applySubstitution [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) : Formula σ → Formula σ :=
  mapTerms (Term.applySubstitution subst)

def renameFreeVars (offset : Nat) : Formula σ → Formula σ :=
  mapTerms (Term.renameFreeVars offset)

mutual

def checkWith [DecidableEq σ.SortSymbol]
    (bound : List σ.SortSymbol) : Formula σ → Bool
  | .falsum => true
  | .truth => true
  | .rel relation arguments =>
      decide
        (Term.inferSortListWith bound arguments =
          some (σ.relDomain relation))
  | .equal left right =>
      match Term.inferSortWith bound left,
          Term.inferSortWith bound right with
      | some leftSort, some rightSort => decide (leftSort = rightSort)
      | _, _ => false
  | .neg body => checkWith bound body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      checkWith bound left && checkWith bound right
  | .forallE sort body
  | .existsE sort body =>
      checkWith (sort :: bound) body

end

def check [DecidableEq σ.SortSymbol] (formula : Formula σ) : Bool :=
  checkWith [] formula

def checkFreeClosed : Formula σ → Bool
  | .falsum => true
  | .truth => true
  | .rel _ arguments => arguments.all Term.checkFreeClosed
  | .equal left right =>
      Term.checkFreeClosed left && Term.checkFreeClosed right
  | .neg body => checkFreeClosed body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      checkFreeClosed left && checkFreeClosed right
  | .forallE _ body
  | .existsE _ body =>
      checkFreeClosed body

abbrev FreeClosed (formula : Formula σ) : Prop :=
  checkFreeClosed formula = true

abbrev WellFormed [DecidableEq σ.SortSymbol]
    (formula : Formula σ) : Prop :=
  check formula = true

theorem checkFreeClosed_sound {formula : Formula σ} :
    checkFreeClosed formula = true → FreeClosed formula :=
  id

def freeSupport : Formula σ → List (σ.SortSymbol × Nat)
  | .falsum => []
  | .truth => []
  | .rel _ arguments => arguments.flatMap Term.freeSupport
  | .equal left right => left.freeSupport ++ right.freeSupport
  | .neg body => freeSupport body
  | .conj left right
  | .disj left right
  | .imp left right
  | .iff left right =>
      freeSupport left ++ freeSupport right
  | .forallE _ body
  | .existsE _ body =>
      freeSupport body

def disjunctionList : List (Formula σ) → Formula σ
  | [] => .falsum
  | [formula] => formula
  | formula :: rest => .disj formula (disjunctionList rest)

def conjunctionList : List (Formula σ) → Formula σ
  | [] => .truth
  | [formula] => formula
  | formula :: rest => .conj formula (conjunctionList rest)

end Formula

namespace Problem

def freeClosed (problem : Problem σ) : Bool :=
  Formula.checkFreeClosed problem.target &&
    problem.premises.all Formula.checkFreeClosed

abbrev FreeClosed (problem : Problem σ) : Prop :=
  freeClosed problem = true

theorem freeClosed_sound {problem : Problem σ}
    (hClosed : freeClosed problem = true) :
    FreeClosed problem :=
  hClosed

def wellFormed [DecidableEq σ.SortSymbol]
    (problem : Problem σ) : Bool :=
  Formula.check problem.target &&
    problem.premises.all Formula.check

def check [DecidableEq σ.SortSymbol]
    (problem : Problem σ) : Bool :=
  problem.freeClosed && problem.wellFormed

end Problem

/-! ## 字面与字句 -/

structure Literal (σ : Signature) where
  polarity : Bool
  atom : Formula σ

namespace Literal

def pos (formula : Formula σ) : Literal σ :=
  { polarity := true, atom := formula }

def neg (formula : Formula σ) : Literal σ :=
  { polarity := false, atom := formula }

def toFormula (literal : Literal σ) : Formula σ :=
  if literal.polarity then literal.atom else .neg literal.atom

def freeSupport (literal : Literal σ) :
    List (σ.SortSymbol × Nat) :=
  literal.atom.freeSupport

def applySubstitution [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) (literal : Literal σ) : Literal σ :=
  { literal with atom := Formula.applySubstitution subst literal.atom }

def renameFreeVars (offset : Nat) (literal : Literal σ) : Literal σ :=
  { literal with atom := Formula.renameFreeVars offset literal.atom }

def eq [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (left right : Literal σ) : Bool :=
  left.polarity == right.polarity &&
    StructuralEq.formula left.atom right.atom

theorem eq_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left right : Literal σ) :
    left.eq right = true → left = right := by
  intro h
  rcases Bool.and_eq_true_iff.mp h with ⟨hPolarity, hAtom⟩
  have hPolarityEq := beq_iff_eq.mp hPolarity
  have hAtomEq :=
    StructuralEq.formula_sound left.atom right.atom hAtom
  cases left
  cases right
  cases hPolarityEq
  cases hAtomEq
  rfl

def matchesAtom [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (polarity : Bool) (atom : Formula σ) (literal : Literal σ) : Bool :=
  literal.polarity == polarity &&
    StructuralEq.formula literal.atom atom

theorem matchesAtom_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {polarity : Bool} {atom : Formula σ} {literal : Literal σ}
    (hMatches : literal.matchesAtom polarity atom = true) :
    literal.polarity = polarity ∧ literal.atom = atom := by
  rcases Bool.and_eq_true_iff.mp hMatches with ⟨hPolarity, hAtom⟩
  exact ⟨beq_iff_eq.mp hPolarity,
    StructuralEq.formula_sound literal.atom atom hAtom⟩

def check [DecidableEq σ.SortSymbol] (literal : Literal σ) : Bool :=
  Formula.check literal.atom

end Literal

structure Clause (σ : Signature) where
  literals : Array (Literal σ) := #[]

namespace Clause

def empty : Clause σ :=
  { literals := #[] }

def singleton (literal : Literal σ) : Clause σ :=
  { literals := #[literal] }

def applySubstitution [DecidableEq σ.SortSymbol]
    (subst : TermSubstitution σ) (clause : Clause σ) : Clause σ :=
  { literals := clause.literals.map (Literal.applySubstitution subst) }

def renameFreeVars (offset : Nat) (clause : Clause σ) : Clause σ :=
  { literals := clause.literals.map (Literal.renameFreeVars offset) }

def ofFormula (formula : Formula σ) : Clause σ :=
  singleton (Literal.pos formula)

def ofNegatedFormula (formula : Formula σ) : Clause σ :=
  singleton (Literal.neg formula)

def atIndices (clause : Clause σ) (indices : Array Nat) : Clause σ :=
  { literals := indices.filterMap fun index => clause.literals[index]? }

def isEmpty (clause : Clause σ) : Bool :=
  clause.literals.isEmpty

def nonempty (clause : Clause σ) : Bool :=
  !clause.isEmpty

def freeSupport (clause : Clause σ) :
    List (σ.SortSymbol × Nat) :=
  clause.literals.toList.flatMap Literal.freeSupport

def toFormula (clause : Clause σ) : Formula σ :=
  Formula.disjunctionList
    (clause.literals.toList.map Literal.toFormula)

private def literalListEq [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] :
    List (Literal σ) → List (Literal σ) → Bool
  | [], [] => true
  | literal :: rest, otherLiteral :: otherRest =>
      literal.eq otherLiteral && literalListEq rest otherRest
  | _, _ => false

def eq [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol] (left right : Clause σ) : Bool :=
  literalListEq left.literals.toList right.literals.toList

private theorem literalListEq_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left : List (Literal σ)) :
    ∀ right : List (Literal σ),
      literalListEq left right = true → left = right := by
  induction left with
  | nil =>
      intro right h
      cases right with
      | nil => rfl
      | cons _ _ => simp [literalListEq] at h
  | cons literal rest ih =>
      intro right h
      cases right with
      | nil => simp [literalListEq] at h
      | cons otherLiteral otherRest =>
          simp [literalListEq] at h
          rcases h with ⟨hLiteral, hRest⟩
          have hLiteralEq := Literal.eq_sound literal otherLiteral hLiteral
          have hRestEq := ih otherRest hRest
          cases hLiteralEq
          cases hRestEq
          rfl

theorem eq_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left right : Clause σ) :
    left.eq right = true → left = right := by
  intro h
  unfold eq at h
  cases left with
  | mk leftLiterals =>
  cases right with
  | mk rightLiterals =>
  have hList := literalListEq_sound _ _ h
  exact congrArg Clause.mk (Array.toList_inj.mp hList)

def filterOutList [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (polarity : Bool) (atom : Formula σ) :
    List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if literal.matchesAtom polarity atom then
        filterOutList polarity atom rest
      else
        literal :: filterOutList polarity atom rest

def filterOut [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (polarity : Bool) (atom : Formula σ) (clause : Clause σ) :
    Clause σ :=
  { literals :=
      (filterOutList polarity atom clause.literals.toList).toArray }

/-- 不匹配目标原子的字面在过滤后仍保留。 -/
theorem mem_filterOutList_of_mem_of_not_matches
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    (polarity : Bool) (atom : Formula σ) {literal : Literal σ} :
    ∀ {literals : List (Literal σ)},
      literal ∈ literals →
      literal.matchesAtom polarity atom = false →
        literal ∈ filterOutList polarity atom literals
  | [], hMem, _hNot => by simp at hMem
  | head :: tail, hMem, hNot => by
      simp only [List.mem_cons] at hMem
      by_cases hHead : head.matchesAtom polarity atom = true
      · simp [filterOutList, hHead]
        rcases hMem with hLiteral | hTail
        · subst head
          simp [hHead] at hNot
        · exact mem_filterOutList_of_mem_of_not_matches
            polarity atom hTail hNot
      · have hHeadFalse : head.matchesAtom polarity atom = false :=
          by cases hValue : head.matchesAtom polarity atom <;> simp_all
        simp [filterOutList, hHeadFalse]
        rcases hMem with hLiteral | hTail
        · exact Or.inl hLiteral
        · exact Or.inr <|
            mem_filterOutList_of_mem_of_not_matches
              polarity atom hTail hNot

def containsLiteralList [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (needle : Literal σ) : List (Literal σ) → Bool
  | [] => false
  | literal :: rest =>
      needle.eq literal || containsLiteralList needle rest

def containsLiteral [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (clause : Clause σ) (needle : Literal σ) : Bool :=
  containsLiteralList needle clause.literals.toList

theorem containsLiteralList_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {needle : Literal σ} :
    ∀ {literals : List (Literal σ)},
      containsLiteralList needle literals = true →
        needle ∈ literals
  | [], hContains => by
      cases hContains
  | literal :: rest, hContains => by
      rw [containsLiteralList] at hContains
      simp only [Bool.or_eq_true] at hContains
      rcases hContains with hHead | hTail
      · have hEq := Literal.eq_sound needle literal hHead
        simp [hEq]
      · exact List.mem_cons_of_mem literal
          (containsLiteralList_sound hTail)

def allLiteralsCovered [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (source target : Clause σ) : Bool :=
  source.literals.toList.all (fun literal => target.containsLiteral literal)

def containsMatching [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (clause : Clause σ) (polarity : Bool) (atom : Formula σ) : Bool :=
  clause.literals.toList.any
    (fun literal => literal.matchesAtom polarity atom)

def resolutionResult [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (leftPolarity : Bool) (pivot : Formula σ)
    (left right : Clause σ) : Clause σ where
  literals :=
    (filterOutList leftPolarity pivot left.literals.toList ++
      filterOutList (!leftPolarity) pivot right.literals.toList).toArray

def equalityResolutionResult [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    (left right : Term σ) (parent : Clause σ) : Clause σ :=
  parent.filterOut false (.equal left right)

theorem containsLiteral_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {clause : Clause σ} {needle : Literal σ}
    (hContains : clause.containsLiteral needle = true) :
    needle ∈ clause.literals.toList := by
  unfold containsLiteral at hContains
  exact containsLiteralList_sound hContains

theorem allLiteralsCovered_sound [DecidableEq σ.SortSymbol]
    [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol]
    {source target : Clause σ}
    (hCovered : source.allLiteralsCovered target = true) :
    ∀ {literal : Literal σ}, literal ∈ source.literals.toList →
      literal ∈ target.literals.toList := by
  intro literal hMem
  exact containsLiteral_sound
    (List.all_eq_true.mp hCovered literal hMem)

theorem literals_toList_eq_nil_of_isEmpty
    {clause : Clause σ} (hEmpty : clause.isEmpty = true) :
    clause.literals.toList = [] := by
  simpa [isEmpty, Array.isEmpty_iff] using hEmpty

def check [DecidableEq σ.SortSymbol] (clause : Clause σ) : Bool :=
  clause.literals.all Literal.check

end Clause

/-- 一阶 DAG 直接消费的初始字句集合。 -/
structure ClauseProblem (σ : Signature) where
  initialClauses : Array (Clause σ)

namespace ClauseProblem

def check [DecidableEq σ.SortSymbol]
    (problem : ClauseProblem σ) : Bool :=
  problem.initialClauses.all Clause.check

/-- 公式问题的直接初始字句视图。 -/
def ofProblem (problem : Problem σ) : ClauseProblem σ where
  initialClauses :=
    (problem.premises.map Clause.ofFormula).toArray.push
      (Clause.ofNegatedFormula problem.target)

def negatedTargetIndex (problem : Problem σ) : Nat :=
  problem.premises.length

@[simp] theorem getElem?_ofProblem_negatedTarget
    (problem : Problem σ) :
    (ofProblem problem).initialClauses[negatedTargetIndex problem]? =
      some (Clause.ofNegatedFormula problem.target) := by
  simp [ofProblem, negatedTargetIndex]

end ClauseProblem

end DAGCertificate
end Automation
end YesMetaZFC
