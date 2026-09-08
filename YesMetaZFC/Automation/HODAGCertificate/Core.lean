import YesMetaZFC.Automation.AvatarSplit
import YesMetaZFC.Automation.Certificate
import YesMetaZFC.Automation.DenseDAG
import YesMetaZFC.Automation.Guards
import YesMetaZFC.Automation.Resolution
import YesMetaZFC.Logic.HigherOrder
/-!
# 原生高阶 DAG 的子句边界
本模块先固定 HO 证书直接消费的 atom、literal 与 clause 形状。项语法来自新的
`Logic.HigherOrder`，因此 `apply/lam` 是 checker 可见的一等数据，而不是搜索器附带的
不透明 payload。
-/
namespace YesMetaZFC
namespace Automation
namespace HODAGCertificate
open Logic.HigherOrder
universe u v w x
-- 各字段（或其签名别名）保留独立宇宙；结构类型的 max 不是冗余参数。
set_option linter.checkUnivs false in
abbrev Signature := Logic.HigherOrder.Signature
abbrev SimpleType (σ : Signature) := Logic.HigherOrder.SimpleType σ.BaseSort
abbrev Term (σ : Signature) := Logic.HigherOrder.Term σ
abbrev Context (σ : Signature) := Logic.HigherOrder.Context σ
abbrev Structure (σ : Signature) := Logic.HigherOrder.Structure σ
section HODAGCertificateSignature
variable {σ : Signature.{u, v, w}}
variable [DecidableEq σ.BaseSort]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]
/-! ## 可计算结构相等 -/
namespace StructuralEq
mutual
  def term
       : Term σ → Term σ → Bool
    | .var (.bvar sort index), .var (.bvar sort' index') =>
        decide (sort = sort') && index == index'
    | .var (.fvar sort id), .var (.fvar sort' id') =>
        decide (sort = sort') && id == id'
    | .app symbol arguments, .app symbol' arguments' =>
        decide (symbol = symbol') && termList arguments arguments'
    | .apply function argument, .apply function' argument' =>
        term function function' && term argument argument'
    | .lam domain codomain body, .lam domain' codomain' body' =>
        decide (domain = domain') && decide (codomain = codomain') && term body body'
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right
  def termList
       : List (Term σ) → List (Term σ) → Bool
    | [], [] => true
    | left :: rest, right :: rest' => term left right && termList rest rest'
    | _, _ => false
  termination_by left right => sizeOf left + sizeOf right
end
omit [DecidableEq σ.RelSymbol] in
theorem term_sound (left : Term σ) :
    ∀ right : Term σ, term left right = true → left = right := by
  refine Logic.HigherOrder.Term.rec (motive_1 := fun left => ∀ right, term left right = true → left = right)
    (motive_2 := fun lefts => ∀ right, termList lefts right = true → lefts = right)
    ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro value right h
    cases right <;> try simp [term] at h
    case var other =>
      cases value <;> cases other <;> simp [term] at h
      all_goals
        rcases h with ⟨hSort, hIndex⟩
        cases hSort
        cases hIndex
        rfl
  · intro symbol arguments ihArguments right h
    cases right <;> try simp [term] at h
    case app otherSymbol otherArguments =>
      rcases h with ⟨hSymbol, hArguments⟩
      cases hSymbol
      exact congrArg (Term.app symbol) (ihArguments _ hArguments)
  · intro function argument ihFunction ihArgument right h
    cases right <;> try simp [term] at h
    case apply otherFunction otherArgument =>
      rcases h with ⟨hFunction, hArgument⟩
      cases ihFunction _ hFunction
      cases ihArgument _ hArgument
      rfl
  · intro domain codomain body ihBody right h
    cases right <;> try simp [term] at h
    case lam otherDomain otherCodomain otherBody =>
      have hFields : (domain = otherDomain ∧ codomain = otherCodomain) ∧
            term body otherBody = true := by
        simpa [term] using h
      rcases hFields with ⟨⟨hDomain, hCodomain⟩, hBody⟩
      have hBodyEq := ihBody _ hBody
      cases hDomain
      cases hCodomain
      cases hBodyEq
      rfl
  · intro right h
    cases right with
    | nil => rfl
    | cons _ _ => simp [termList] at h
  · intro head tail ihHead ihTail right h
    cases right <;> simp [termList] at h
    case cons otherHead otherTail =>
      rcases h with ⟨hHead, hTail⟩
      cases ihHead _ hHead
      cases ihTail _ hTail
      rfl
omit [DecidableEq σ.RelSymbol] in
theorem termList_sound (left : List (Term σ)) :
    ∀ right : List (Term σ), termList left right = true → left = right := by
  refine Logic.HigherOrder.Term.rec_1 (motive_1 := fun left => ∀ right, term left right = true → left = right)
    (motive_2 := fun lefts => ∀ right, termList lefts right = true → lefts = right)
    ?_ ?_ ?_ ?_ ?_ ?_ left
  · intro value right h
    cases right <;> try simp [term] at h
    case var other =>
      cases value <;> cases other <;> simp [term] at h
      all_goals
        rcases h with ⟨hSort, hIndex⟩
        cases hSort
        cases hIndex
        rfl
  · intro symbol arguments ihArguments right h
    cases right <;> try simp [term] at h
    case app otherSymbol otherArguments =>
      rcases h with ⟨hSymbol, hArguments⟩
      cases hSymbol
      exact congrArg (Term.app symbol) (ihArguments _ hArguments)
  · intro function argument ihFunction ihArgument right h
    cases right <;> try simp [term] at h
    case apply otherFunction otherArgument =>
      rcases h with ⟨hFunction, hArgument⟩
      cases ihFunction _ hFunction
      cases ihArgument _ hArgument
      rfl
  · intro domain codomain body ihBody right h
    cases right <;> try simp [term] at h
    case lam otherDomain otherCodomain otherBody =>
      have hFields : (domain = otherDomain ∧ codomain = otherCodomain) ∧
            term body otherBody = true := by
        simpa [term] using h
      rcases hFields with ⟨⟨hDomain, hCodomain⟩, hBody⟩
      have hBodyEq := ihBody _ hBody
      cases hDomain
      cases hCodomain
      cases hBodyEq
      rfl
  · intro right h
    cases right with
    | nil => rfl
    | cons _ _ => simp [termList] at h
  · intro head tail ihHead ihTail right h
    cases right <;> simp [termList] at h
    case cons otherHead otherTail =>
      rcases h with ⟨hHead, hTail⟩
      cases ihHead _ hHead
      cases ihTail _ hTail
      rfl
end StructuralEq
inductive Atom (σ : Signature.{u, v, w}) where
  | rel (symbol : σ.RelSymbol) (arguments : List (Term σ))
  | equal (sort : SimpleType σ) (left right : Term σ)
namespace Atom
def applySubstitution (substitution : TermSubstitution σ) : Atom σ → Atom σ
  | .rel symbol arguments =>
      .rel symbol (Term.applySubstitutionList substitution arguments)
  | .equal sort left right =>
      .equal sort (left.applySubstitution substitution) (right.applySubstitution substitution)
def renameFreeVars  (offset : Nat) : Atom σ → Atom σ
  | .rel symbol arguments =>
      .rel symbol (Term.renameFreeVarsList offset arguments)
  | .equal sort left right =>
      .equal sort (left.renameFreeVars offset) (right.renameFreeVars offset)
def eq
      :
    Atom σ → Atom σ → Bool
  | .rel symbol arguments, .rel symbol' arguments' =>
      decide (symbol = symbol') && StructuralEq.termList arguments arguments'
  | .equal sort left right, .equal sort' left' right' =>
      decide (sort = sort') &&
        StructuralEq.term left left' && StructuralEq.term right right'
  | _, _ => false
theorem eq_sound (left right : Atom σ) (hEq : eq left right = true) :
    left = right := by
  cases left with
  | rel symbol arguments =>
      cases right with
      | rel symbol' arguments' =>
          have hFields :
              symbol = symbol' ∧
                StructuralEq.termList arguments arguments' = true := by
            simpa [eq] using hEq
          rcases hFields with ⟨hSymbol, hArguments⟩
          cases hSymbol
          cases StructuralEq.termList_sound _ _ hArguments
          rfl
      | equal otherSort otherLeft otherRight =>
          simp [eq] at hEq
  | equal sort leftTerm rightTerm =>
      cases right with
      | rel otherSymbol otherArguments =>
          simp [eq] at hEq
      | equal sort' left' right' =>
          have hFields : (sort = sort' ∧ StructuralEq.term leftTerm left' = true) ∧
                StructuralEq.term rightTerm right' = true := by
            simpa [eq] using hEq
          rcases hFields with ⟨⟨hSort, hLeft⟩, hRight⟩
          have hLeftEq := StructuralEq.term_sound _ _ hLeft
          have hRightEq := StructuralEq.term_sound _ _ hRight
          cases hSort
          cases hLeftEq
          cases hRightEq
          rfl
def toFormula : Atom σ → Logic.HigherOrder.Formula σ
  | .rel symbol arguments => .rel symbol arguments
  | .equal sort left right => .equal sort left right
def checkWith (context : Context σ) (atom : Atom σ) : Bool :=
  atom.toFormula.checkWith context
def WellFormed (context : Context σ) (atom : Atom σ) : Prop :=
  FormulaWellFormed context atom.toFormula
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkWith_sound
    {context : Context σ} {atom : Atom σ} (hCheck : atom.checkWith context = true) :
    atom.WellFormed context :=
  Logic.HigherOrder.Formula.checkWith_sound hCheck
def Satisfies  {M : Structure.{u, v, w, x} σ} (env : Logic.HigherOrder.Env M) : Atom σ → Prop
  | .rel symbol arguments => M.relInterp symbol (arguments.map (Term.eval env))
  | .equal _ left right => Term.eval env left = Term.eval env right
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_applySubstitution_iff_of_envMatches
    {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
    {sourceEnv targetEnv : Logic.HigherOrder.Env M} (hAdmissible : substitution.Admissible)
    (hEnv : TermSubstitution.EnvMatches substitution sourceEnv targetEnv) :
    ∀ atom : Atom σ,
      Satisfies sourceEnv (applySubstitution substitution atom) ↔
        Satisfies targetEnv atom
  | .rel symbol arguments => by
      change
        M.relInterp symbol ((Term.applySubstitutionList substitution arguments).map (Term.eval sourceEnv)) ↔
          M.relInterp symbol (arguments.map (Term.eval targetEnv))
      rw [Term.evalList_applySubstitution_eq_of_envMatches
        hAdmissible hEnv arguments]
  | .equal sort left right => by
      simp only [applySubstitution, Satisfies]
      rw [Term.eval_applySubstitution_eq_of_envMatches hAdmissible hEnv left,
        Term.eval_applySubstitution_eq_of_envMatches hAdmissible hEnv right]
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_renameFreeVars_iff_of_envMatches
     {M : Structure.{u, v, w, x} σ}
    {offset : Nat} {sourceEnv targetEnv : Logic.HigherOrder.Env M} (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) :
    ∀ atom : Atom σ,
      Satisfies sourceEnv (renameFreeVars offset atom) ↔ Satisfies targetEnv atom
  | .rel symbol arguments => by
      change
        M.relInterp symbol ((Term.renameFreeVarsList offset arguments).map (Term.eval sourceEnv)) ↔
          M.relInterp symbol (arguments.map (Term.eval targetEnv))
      rw [Term.evalList_renameFreeVars_eq_of_envMatches hEnv arguments]
  | .equal sort left right => by
      simp only [renameFreeVars, Satisfies]
      rw [Term.eval_renameFreeVars_eq_of_envMatches hEnv left,
        Term.eval_renameFreeVars_eq_of_envMatches hEnv right]
end Atom
structure Literal (σ : Signature.{u, v, w}) where
  polarity : Bool
  atom : Atom σ
namespace Literal
def applySubstitution (substitution : TermSubstitution σ) (literal : Literal σ) : Literal σ :=
  { literal with atom := literal.atom.applySubstitution substitution }
def renameFreeVars  (offset : Nat) (literal : Literal σ) : Literal σ :=
  { literal with atom := literal.atom.renameFreeVars offset }
def eq (left right : Literal σ) : Bool :=
  decide (left.polarity = right.polarity) && left.atom.eq right.atom
theorem eq_sound (left right : Literal σ) (hEq : left.eq right = true) :
    left = right := by
  cases left with
  | mk polarity atom =>
      cases right with
      | mk polarity' atom' =>
          simp [eq] at hEq
          rcases hEq with ⟨hPolarity, hAtom⟩
          cases hPolarity
          cases Atom.eq_sound atom atom' hAtom
          rfl
def checkWith (context : Context σ) (literal : Literal σ) : Bool :=
  literal.atom.checkWith context
def WellFormed (context : Context σ) (literal : Literal σ) : Prop :=
  literal.atom.WellFormed context
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkWith_sound
    {context : Context σ} {literal : Literal σ} (hCheck : literal.checkWith context = true) :
    literal.WellFormed context :=
  Atom.checkWith_sound hCheck
def Satisfies  {M : Structure.{u, v, w, x} σ} (env : Logic.HigherOrder.Env M) (literal : Literal σ) : Prop :=
  if literal.polarity then literal.atom.Satisfies env else ¬ literal.atom.Satisfies env
def matchesAtom (polarity : Bool) (atom : Atom σ) (literal : Literal σ) : Bool :=
  decide (literal.polarity = polarity) && literal.atom.eq atom
theorem matchesAtom_sound
    {polarity : Bool} {atom : Atom σ} {literal : Literal σ} (hMatches : literal.matchesAtom polarity atom = true) :
    literal.polarity = polarity ∧ literal.atom = atom := by
  rcases Bool.and_eq_true_iff.mp hMatches with ⟨hPolarity, hAtom⟩
  exact ⟨of_decide_eq_true hPolarity, Atom.eq_sound literal.atom atom hAtom⟩
theorem not_satisfies_matchesAtom_complement
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {pivotPolarity : Bool} {atom : Atom σ} {left right : Literal σ} (hLeftMatch : left.matchesAtom pivotPolarity atom = true)
    (hRightMatch : right.matchesAtom (!pivotPolarity) atom = true) (hLeft : Satisfies env left) (hRight : Satisfies env right) : False := by
  rcases matchesAtom_sound hLeftMatch with ⟨hLeftPolarity, hLeftAtom⟩
  rcases matchesAtom_sound hRightMatch with ⟨hRightPolarity, hRightAtom⟩
  cases left with
  | mk leftPolarity leftAtom =>
      cases right with
      | mk rightPolarity rightAtom =>
          cases hLeftPolarity
          cases hLeftAtom
          cases hRightPolarity
          cases hRightAtom
          cases leftPolarity
          · exact hLeft hRight
          · exact hRight hLeft
theorem not_satisfies_reflexive_negative_equality
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {sort : SimpleType σ} {left right : Term σ} {literal : Literal σ} (hTerm : StructuralEq.term left right = true)
    (hMatch : literal.matchesAtom false (.equal sort left right) = true) (hLiteral : Satisfies env literal) : False := by
  rcases matchesAtom_sound hMatch with ⟨hPolarity, hAtom⟩
  have hTermEq : left = right := StructuralEq.term_sound left right hTerm
  cases literal
  cases hPolarity
  cases hAtom
  cases hTermEq
  exact hLiteral rfl
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_applySubstitution_iff_of_envMatches
    {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
    {sourceEnv targetEnv : Logic.HigherOrder.Env M} (hAdmissible : substitution.Admissible)
    (hEnv : TermSubstitution.EnvMatches substitution sourceEnv targetEnv) (literal : Literal σ) :
    Satisfies sourceEnv (applySubstitution substitution literal) ↔
      Satisfies targetEnv literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · exact not_congr (Atom.satisfies_applySubstitution_iff_of_envMatches hAdmissible hEnv atom)
      · exact Atom.satisfies_applySubstitution_iff_of_envMatches hAdmissible hEnv atom
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_renameFreeVars_iff_of_envMatches
     {M : Structure.{u, v, w, x} σ}
    {offset : Nat} {sourceEnv targetEnv : Logic.HigherOrder.Env M} (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) (literal : Literal σ) :
    Satisfies sourceEnv (renameFreeVars offset literal) ↔
      Satisfies targetEnv literal := by
  cases literal with
  | mk polarity atom =>
      cases polarity
      · exact not_congr (Atom.satisfies_renameFreeVars_iff_of_envMatches hEnv atom)
      · exact Atom.satisfies_renameFreeVars_iff_of_envMatches hEnv atom
end Literal
structure Clause (σ : Signature.{u, v, w}) where
  literals : Array (Literal σ)
namespace Clause
def applySubstitution (substitution : TermSubstitution σ) (clause : Clause σ) : Clause σ where
  literals := clause.literals.map (Literal.applySubstitution substitution)
def renameFreeVars  (offset : Nat) (clause : Clause σ) : Clause σ where
  literals := clause.literals.map (Literal.renameFreeVars offset)
private def literalListEq
      :
    List (Literal σ) → List (Literal σ) → Bool
  | [], [] => true
  | literal :: rest, literal' :: rest' =>
      literal.eq literal' && literalListEq rest rest'
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
        cases Literal.eq_sound literal literal' hLiteral
        cases ih _ hRest
        rfl
def eq (left right : Clause σ) : Bool :=
  literalListEq left.literals.toList right.literals.toList
theorem eq_sound (left right : Clause σ) (hEq : left.eq right = true) :
    left = right := by
  cases left with
  | mk leftLiterals =>
      cases right with
      | mk rightLiterals =>
          simp [eq] at hEq
          have hList := literalListEq_sound _ _ hEq
          cases leftLiterals
          cases rightLiterals
          simp at hList
          simp [hList]
def filterOutList (polarity : Bool) (atom : Atom σ) : List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if literal.matchesAtom polarity atom then
        filterOutList polarity atom rest
      else
        literal :: filterOutList polarity atom rest
def filterOut (polarity : Bool) (atom : Atom σ) (clause : Clause σ) : Clause σ where
  literals := (filterOutList polarity atom clause.literals.toList).toArray
def containsLiteralList (needle : Literal σ) : List (Literal σ) → Bool
  | [] => false
  | literal :: rest => needle.eq literal || containsLiteralList needle rest
def replaceLiteralAtEndList (replacement : Literal σ) : List (Literal σ) → Nat → List (Literal σ)
  | [], _ => []
  | _ :: rest, 0 => rest ++ [replacement]
  | literal :: rest, index + 1 =>
      literal :: replaceLiteralAtEndList replacement rest index
def dedupLiteralList
      :
    List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if containsLiteralList literal rest then
        dedupLiteralList rest
      else
        literal :: dedupLiteralList rest
def replaceLiteralAtEnd (clause : Clause σ) (index : Nat) (replacement : Literal σ) : Clause σ where
  literals := (replaceLiteralAtEndList replacement clause.literals.toList index).toArray
def normalize (clause : Clause σ) : Clause σ where
  literals := (dedupLiteralList clause.literals.toList).toArray
def replaceLiteralList (needle replacement : Literal σ) : List (Literal σ) → List (Literal σ)
  | [] => []
  | literal :: rest =>
      if literal.eq needle then
        replacement :: replaceLiteralList needle replacement rest
      else
        literal :: replaceLiteralList needle replacement rest
def replaceLiteral (clause : Clause σ) (needle replacement : Literal σ) : Clause σ where
  literals := (replaceLiteralList needle replacement clause.literals.toList).toArray
def containsLiteral (clause : Clause σ) (needle : Literal σ) : Bool :=
  containsLiteralList needle clause.literals.toList
def allLiteralsCovered (source target : Clause σ) : Bool :=
  source.literals.toList.all fun literal => target.containsLiteral literal
def coversCheck (source : Clause σ) (components : List (Clause σ)) : Bool := (source.literals.toList.all fun literal =>
    components.any fun component => containsLiteral component literal) &&
    components.all fun component => allLiteralsCovered component source
def containsMatching (clause : Clause σ) (polarity : Bool) (atom : Atom σ) : Bool :=
  clause.literals.toList.any fun literal => literal.matchesAtom polarity atom
def resolutionResult (leftPolarity : Bool) (pivot : Atom σ) (left right : Clause σ) : Clause σ where
  literals := (filterOutList leftPolarity pivot left.literals.toList ++
      filterOutList (!leftPolarity) pivot right.literals.toList).toArray
def equalityResolutionResult (sort : SimpleType σ) (left right : Term σ) (parent : Clause σ) : Clause σ :=
  parent.filterOut false (.equal sort left right)
theorem mem_filterOutList_of_mem_of_not_matches
    {polarity : Bool} {atom : Atom σ} {literal : Literal σ} :
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
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Atom σ}
    {literal : Literal σ} (hMem : literal ∈ left.literals.toList) (hNoMatch : literal.matchesAtom leftPolarity pivot = false) :
    literal ∈ (resolutionResult leftPolarity pivot left right).literals.toList := by
  simp [resolutionResult]
  exact Or.inl (mem_filterOutList_of_mem_of_not_matches hMem hNoMatch)
theorem mem_resolutionResult_right
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Atom σ}
    {literal : Literal σ} (hMem : literal ∈ right.literals.toList) (hNoMatch : literal.matchesAtom (!leftPolarity) pivot = false) :
    literal ∈ (resolutionResult leftPolarity pivot left right).literals.toList := by
  simp [resolutionResult]
  exact Or.inr (mem_filterOutList_of_mem_of_not_matches hMem hNoMatch)
theorem mem_equalityResolutionResult
    {sort : SimpleType σ} {left right : Term σ} {parent : Clause σ}
    {literal : Literal σ} (hMem : literal ∈ parent.literals.toList) (hNoMatch : literal.matchesAtom false (.equal sort left right) = false) :
    literal ∈ (equalityResolutionResult sort left right parent).literals.toList := by
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
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
private theorem satisfies_replaceLiteralAtEndList
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {needle replacement : Literal σ} (hReplacement : needle.Satisfies env → replacement.Satisfies env) :
    ∀ (literals : List (Literal σ)) (index : Nat),
      literals[index]? = some needle → (∃ literal, literal ∈ literals ∧ literal.Satisfies env) →
          ∃ literal,
            literal ∈ replaceLiteralAtEndList replacement literals index ∧
              literal.Satisfies env
  | [], index, hGet, _hSat => by
      simp at hGet
  | head :: rest, 0, hGet, hSat => by
      have hHead : head = needle := by
        simpa using Option.some.inj hGet
      rcases hSat with ⟨literal, hMem, hLiteral⟩
      rcases List.mem_cons.mp hMem with hLiteralHead | hLiteralRest
      · subst literal
        exact ⟨replacement, by simp [replaceLiteralAtEndList],
          hReplacement (by simpa [hHead] using hLiteral)⟩
      · exact ⟨literal, by simp [replaceLiteralAtEndList, hLiteralRest], hLiteral⟩
  | head :: rest, index + 1, hGet, hSat => by
      have hRestGet : rest[index]? = some needle := by
        simpa using hGet
      rcases hSat with ⟨literal, hMem, hLiteral⟩
      rcases List.mem_cons.mp hMem with hLiteralHead | hLiteralRest
      · subst literal
        exact ⟨head, by simp [replaceLiteralAtEndList], hLiteral⟩
      · rcases satisfies_replaceLiteralAtEndList hReplacement rest index hRestGet
            ⟨literal, hLiteralRest, hLiteral⟩ with
          ⟨witness, hWitnessMem, hWitnessSat⟩
        exact ⟨witness, by simp [replaceLiteralAtEndList, hWitnessMem], hWitnessSat⟩
private theorem satisfies_dedupLiteralList
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M} :
    ∀ literals : List (Literal σ), (∃ literal, literal ∈ literals ∧ literal.Satisfies env) →
        ∃ literal, literal ∈ dedupLiteralList literals ∧ literal.Satisfies env
  | [], hSat => by
      rcases hSat with ⟨literal, hMem, _hLiteral⟩
      cases hMem
  | head :: rest, hSat => by
      cases hDuplicate : containsLiteralList head rest with
      | false =>
          rcases hSat with ⟨literal, hMem, hLiteral⟩
          rcases List.mem_cons.mp hMem with hLiteralHead | hLiteralRest
          · subst literal
            exact ⟨head, by simp [dedupLiteralList, hDuplicate], hLiteral⟩
          · rcases satisfies_dedupLiteralList rest
                ⟨literal, hLiteralRest, hLiteral⟩ with
              ⟨witness, hWitnessMem, hWitnessSat⟩
            exact ⟨witness,
              by simp [dedupLiteralList, hDuplicate, hWitnessMem], hWitnessSat⟩
      | true =>
          rcases hSat with ⟨literal, hMem, hLiteral⟩
          have hRestSat :
              ∃ witness, witness ∈ rest ∧ witness.Satisfies env := by
            rcases List.mem_cons.mp hMem with hLiteralHead | hLiteralRest
            · subst literal
              rcases containsLiteralList_sound hDuplicate with
                ⟨duplicate, hDuplicateMem, hDuplicateEq⟩
              exact ⟨duplicate, hDuplicateMem, by simpa [hDuplicateEq] using hLiteral⟩
            · exact ⟨literal, hLiteralRest, hLiteral⟩
          simpa [dedupLiteralList, hDuplicate] using
            satisfies_dedupLiteralList rest hRestSat
theorem allLiteralsCovered_sound
    {source target : Clause σ} (hCovered : allLiteralsCovered source target = true) :
    ∀ {literal : Literal σ}, literal ∈ source.literals.toList →
      ∃ literal', literal' ∈ target.literals.toList ∧ literal' = literal := by
  intro literal hMem
  have hAll := List.all_eq_true.mp hCovered
  have hContains : target.containsLiteral literal = true := hAll literal hMem
  exact containsLiteralList_sound hContains
private theorem satisfies_replaceLiteralList
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {needle replacement : Literal σ} (hReplacement : needle.Satisfies env → replacement.Satisfies env) :
    ∀ {literals : List (Literal σ)}, (∃ literal, literal ∈ literals ∧ literal.Satisfies env) →
        ∃ literal,
          literal ∈ replaceLiteralList needle replacement literals ∧
            literal.Satisfies env
  | [], h => by
      rcases h with ⟨literal, hMem, _hSat⟩
      cases hMem
  | literal :: rest, h => by
      rcases h with ⟨witness, hMem, hSat⟩
      by_cases hMatch : literal.eq needle = true
      · have hLiteralEq : literal = needle := Literal.eq_sound literal needle hMatch
        rw [replaceLiteralList, hMatch]
        rcases List.mem_cons.mp hMem with hHead | hTail
        · have hSatLiteral : literal.Satisfies env := by
            simpa [hHead] using hSat
          exact ⟨replacement, by simp,
            hReplacement (by simpa [hLiteralEq] using hSatLiteral)⟩
        · rcases satisfies_replaceLiteralList hReplacement
              ⟨witness, hTail, hSat⟩ with
            ⟨witness', hMem', hSat'⟩
          exact ⟨witness', by simp [hMem'], hSat'⟩
      · have hNoMatch : literal.eq needle = false := by
          cases hValue : literal.eq needle <;> simp [hValue] at hMatch ⊢
        rw [replaceLiteralList, hNoMatch]
        rcases List.mem_cons.mp hMem with hHead | hTail
        · have hSatLiteral : literal.Satisfies env := by
            simpa [hHead] using hSat
          exact ⟨literal, by simp, hSatLiteral⟩
        · rcases satisfies_replaceLiteralList hReplacement
              ⟨witness, hTail, hSat⟩ with
            ⟨witness', hMem', hSat'⟩
          exact ⟨witness', by simp [hMem'], hSat'⟩
def checkWith (context : Context σ) (clause : Clause σ) : Bool :=
  clause.literals.all fun literal => literal.checkWith context
def check (clause : Clause σ) : Bool :=
  clause.checkWith []
def WellFormed (context : Context σ) (clause : Clause σ) : Prop :=
  ∀ literal, literal ∈ clause.literals → literal.WellFormed context
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem checkWith_sound
    {context : Context σ} {clause : Clause σ} (hCheck : clause.checkWith context = true) :
    clause.WellFormed context := by
  intro literal hMember
  rcases Array.mem_iff_getElem.mp hMember with ⟨index, hIndex, hGet⟩
  have hAll := Array.all_eq_true.mp hCheck
  have hAt := hAll index hIndex
  apply Literal.checkWith_sound
  simpa [hGet] using hAt
def Satisfies  {M : Structure.{u, v, w, x} σ} (env : Logic.HigherOrder.Env M) (clause : Clause σ) : Prop :=
  ∃ literal, literal ∈ clause.literals ∧ literal.Satisfies env
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem Literal.satisfies_iff_of_wellFormed_env
     {M : Structure.{u, v, w, x} σ}
    {context : Context σ} {env₁ env₂ : Logic.HigherOrder.Env M}
    {literal : Literal σ} (hLiteral : literal.WellFormed context) (hBound :
      ∀ index target,
        Context.lookup? context index = some target →
          env₁.boundVal index = env₂.boundVal index) (hFree : ∀ target id, env₁.freeVal target id = env₂.freeVal target id) :
    literal.Satisfies env₁ ↔ literal.Satisfies env₂ := by
  cases literal with
  | mk polarity atom =>
      have hAtom :
          atom.Satisfies env₁ ↔ atom.Satisfies env₂ := by
        have hFormula :=
          Logic.HigherOrder.Formula.satisfies_iff_of_wellFormed_env
            hLiteral hBound hFree
        cases atom <;>
          simpa [Atom.Satisfies, Atom.toFormula,
            Logic.HigherOrder.Formula.Satisfies] using hFormula
      cases polarity with
      | false =>
          exact not_congr hAtom
      | true =>
          exact hAtom
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_iff_of_wellFormed_env
     {M : Structure.{u, v, w, x} σ}
    {context : Context σ} {env₁ env₂ : Logic.HigherOrder.Env M}
    {clause : Clause σ} (hClause : clause.WellFormed context) (hBound :
      ∀ index target,
        Context.lookup? context index = some target →
          env₁.boundVal index = env₂.boundVal index) (hFree : ∀ target id, env₁.freeVal target id = env₂.freeVal target id) :
    clause.Satisfies env₁ ↔ clause.Satisfies env₂ := by
  constructor
  · rintro ⟨literal, hMem, hLiteral⟩
    exact ⟨literal, hMem, (Literal.satisfies_iff_of_wellFormed_env (hClause literal hMem) hBound hFree).mp hLiteral⟩
  · rintro ⟨literal, hMem, hLiteral⟩
    exact ⟨literal, hMem, (Literal.satisfies_iff_of_wellFormed_env (hClause literal hMem) hBound hFree).mpr hLiteral⟩
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_replaceLiteralAtEnd
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} {index : Nat} {needle replacement : Literal σ} (hGet : clause.literals[index]? = some needle)
    (hReplacement : needle.Satisfies env → replacement.Satisfies env) (hClause : clause.Satisfies env) :
    (clause.replaceLiteralAtEnd index replacement).Satisfies env := by
  rcases hClause with ⟨literal, hMem, hLiteral⟩
  rcases satisfies_replaceLiteralAtEndList hReplacement clause.literals.toList
      index (by simpa using hGet)
      ⟨literal, Array.mem_def.mp hMem, hLiteral⟩ with
    ⟨witness, hWitnessMem, hWitnessSat⟩
  exact ⟨witness,
    Array.mem_def.mpr (by simpa [replaceLiteralAtEnd] using hWitnessMem),
    hWitnessSat⟩
theorem satisfies_normalize
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} (hClause : clause.Satisfies env) :
    clause.normalize.Satisfies env := by
  rcases hClause with ⟨literal, hMem, hLiteral⟩
  rcases satisfies_dedupLiteralList clause.literals.toList
      ⟨literal, Array.mem_def.mp hMem, hLiteral⟩ with
    ⟨witness, hWitnessMem, hWitnessSat⟩
  exact ⟨witness,
    Array.mem_def.mpr (by simpa [normalize] using hWitnessMem),
    hWitnessSat⟩
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_of_literal_mem
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} {literal : Literal σ} (hMem : literal ∈ clause.literals.toList) (hLiteral : literal.Satisfies env) :
    clause.Satisfies env :=
  ⟨literal, Array.mem_def.mpr hMem, hLiteral⟩
theorem satisfies_resolutionResult
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {left right : Clause σ} {leftPolarity : Bool} {pivot : Atom σ} (hLeft : left.Satisfies env) (hRight : right.Satisfies env) :
    (resolutionResult leftPolarity pivot left right).Satisfies env := by
  rcases hLeft with ⟨leftLiteral, hLeftMem, hLeftLiteral⟩
  cases hLeftMatch : leftLiteral.matchesAtom leftPolarity pivot with
  | false =>
      exact satisfies_of_literal_mem (mem_resolutionResult_left (Array.mem_def.mp hLeftMem) hLeftMatch)
        hLeftLiteral
  | true =>
      rcases hRight with ⟨rightLiteral, hRightMem, hRightLiteral⟩
      cases hRightMatch : rightLiteral.matchesAtom (!leftPolarity) pivot with
      | false =>
          exact satisfies_of_literal_mem (mem_resolutionResult_right (Array.mem_def.mp hRightMem) hRightMatch)
            hRightLiteral
      | true =>
          exact False.elim (Literal.not_satisfies_matchesAtom_complement
              hLeftMatch hRightMatch hLeftLiteral hRightLiteral)
theorem satisfies_of_allLiteralsCovered
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {source target : Clause σ} (hCovered : source.allLiteralsCovered target = true) (hSource : source.Satisfies env) :
    target.Satisfies env := by
  rcases hSource with ⟨literal, hMem, hLiteral⟩
  rcases allLiteralsCovered_sound hCovered (Array.mem_def.mp hMem) with
    ⟨literal', hTargetMem, hEq⟩
  cases hEq
  exact satisfies_of_literal_mem hTargetMem hLiteral
theorem satisfies_equalityResolutionResult
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {sort : SimpleType σ} {left right : Term σ} {parent : Clause σ} (hTerm : StructuralEq.term left right = true) (hParent : parent.Satisfies env) :
    (equalityResolutionResult sort left right parent).Satisfies env := by
  rcases hParent with ⟨literal, hMem, hLiteral⟩
  cases hMatch : literal.matchesAtom false (.equal sort left right) with
  | false =>
      exact satisfies_of_literal_mem (mem_equalityResolutionResult (Array.mem_def.mp hMem) hMatch) hLiteral
  | true =>
      exact False.elim (Literal.not_satisfies_reflexive_negative_equality hTerm hMatch hLiteral)
def Valid  (M : Structure.{u, v, w, x} σ) (clause : Clause σ) : Prop :=
  ∀ env : Logic.HigherOrder.Env M, env.WellSorted [] → clause.Satisfies env
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_applySubstitution_iff_of_envMatches
    {M : Structure.{u, v, w, x} σ} {substitution : TermSubstitution σ}
    {sourceEnv targetEnv : Logic.HigherOrder.Env M} (hAdmissible : substitution.Admissible)
    (hEnv : TermSubstitution.EnvMatches substitution sourceEnv targetEnv) (clause : Clause σ) :
    Satisfies sourceEnv (applySubstitution substitution clause) ↔
      Satisfies targetEnv clause := by
  constructor
  · rintro ⟨literal, hMem, hLiteral⟩
    have hMemList :
        literal ∈ clause.literals.toList.map (Literal.applySubstitution substitution) := by
      simpa [applySubstitution, Array.toList_map] using Array.mem_def.mp hMem
    rcases List.mem_map.mp hMemList with ⟨sourceLiteral, hSourceMem, rfl⟩
    exact ⟨sourceLiteral, Array.mem_def.mpr hSourceMem, (Literal.satisfies_applySubstitution_iff_of_envMatches
        hAdmissible hEnv sourceLiteral).mp hLiteral⟩
  · rintro ⟨literal, hMem, hLiteral⟩
    refine ⟨Literal.applySubstitution substitution literal, ?_, ?_⟩
    · apply Array.mem_def.mpr
      simpa [applySubstitution, Array.toList_map] using (List.mem_map.mpr ⟨literal, Array.mem_def.mp hMem, rfl⟩)
    · exact (Literal.satisfies_applySubstitution_iff_of_envMatches
        hAdmissible hEnv literal).mpr hLiteral
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_renameFreeVars_iff_of_envMatches
     {M : Structure.{u, v, w, x} σ}
    {offset : Nat} {sourceEnv targetEnv : Logic.HigherOrder.Env M} (hEnv : FreeVarRenaming.EnvMatches offset sourceEnv targetEnv) (clause : Clause σ) :
    Satisfies sourceEnv (renameFreeVars offset clause) ↔ Satisfies targetEnv clause := by
  constructor
  · rintro ⟨literal, hMem, hLiteral⟩
    have hMemList :
        literal ∈ clause.literals.toList.map (Literal.renameFreeVars offset) := by
      simpa [renameFreeVars, Array.toList_map] using Array.mem_def.mp hMem
    rcases List.mem_map.mp hMemList with ⟨sourceLiteral, hSourceMem, rfl⟩
    exact ⟨sourceLiteral, Array.mem_def.mpr hSourceMem, (Literal.satisfies_renameFreeVars_iff_of_envMatches hEnv sourceLiteral).mp hLiteral⟩
  · rintro ⟨literal, hMem, hLiteral⟩
    refine ⟨Literal.renameFreeVars offset literal, ?_, ?_⟩
    · apply Array.mem_def.mpr
      simpa [renameFreeVars, Array.toList_map] using (List.mem_map.mpr ⟨literal, Array.mem_def.mp hMem, rfl⟩)
    · exact (Literal.satisfies_renameFreeVars_iff_of_envMatches hEnv literal).mpr hLiteral
theorem satisfies_replaceLiteral
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} {needle replacement : Literal σ} (hReplacement : needle.Satisfies env → replacement.Satisfies env) (hClause : clause.Satisfies env) :
    (clause.replaceLiteral needle replacement).Satisfies env := by
  rcases hClause with ⟨literal, hMem, hSat⟩
  have hMemList : literal ∈ clause.literals.toList :=
    Array.mem_def.mp hMem
  rcases satisfies_replaceLiteralList hReplacement
      ⟨literal, hMemList, hSat⟩ with
    ⟨witness, hWitnessMem, hWitnessSat⟩
  exact ⟨witness, Array.mem_def.mpr (by simpa [replaceLiteral] using hWitnessMem),
    hWitnessSat⟩
def isEmpty  (clause : Clause σ) : Bool :=
  clause.literals.size == 0
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem literals_eq_empty_of_isEmpty  {clause : Clause σ} (hEmpty : clause.isEmpty = true) :
    clause.literals = #[] := by
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
      exact Array.eq_empty_of_size_eq_zero hSize
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem not_satisfies_of_isEmpty
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {clause : Clause σ} (hEmpty : clause.isEmpty = true) (hSat : clause.Satisfies env) : False := by
  rcases hSat with ⟨literal, hMem, _hLiteral⟩
  rw [literals_eq_empty_of_isEmpty hEmpty] at hMem
  simp at hMem
end Clause
/-! ## AVATAR guard 与命题链接 -/
abbrev GuardLit := Guards.Lit
abbrev GuardSet := Guards.Set
abbrev GuardedClause (σ : Signature.{u, v, w}) := Guards.GuardedClause (Clause σ)
namespace GuardedClause
def plain  (clause : Clause σ) : GuardedClause σ :=
  Guards.GuardedClause.plain clause
def unguarded  (gclause : GuardedClause σ) : Bool :=
  Guards.GuardedClause.unguarded gclause
def globallyEmpty  (gclause : GuardedClause σ) : Bool :=
  Guards.GuardedClause.globallyEmpty Clause.isEmpty gclause
def theoryConflict  (gclause : GuardedClause σ) : Bool :=
  Guards.GuardedClause.theoryConflict Clause.isEmpty gclause
end GuardedClause
namespace BetaEta
/--
βη 等价的原生可回放轨迹。
同余构造每次只改写一个直接子项；`trans` 的中间项由 checker 做结构对齐，
因此材料化器可以组合任意深度的归约而无需信任外部 normalized term。
-/
inductive Trace (σ : Signature.{u, v, w}) where
  | refl (term : Term σ)
  | appArgument (symbol : σ.FuncSymbol) (before : List (Term σ)) (argument : Trace σ) (suffix : List (Term σ))
  | applyFunction (function : Trace σ) (argument : Term σ)
  | applyArgument (function : Term σ) (argument : Trace σ)
  | lam (domain codomain : SimpleType σ) (body : Trace σ)
  | beta (domain codomain : SimpleType σ) (body argument : Term σ)
  | eta (domain codomain : SimpleType σ) (function : Term σ)
  | trans (first second : Trace σ)
namespace Trace
def source : Trace σ → Term σ
  | .refl term => term
  | .appArgument symbol before argument suffix =>
      .app symbol (before ++ [argument.source] ++ suffix)
  | .applyFunction function argument => .apply function.source argument
  | .applyArgument function argument => .apply function argument.source
  | .lam domain codomain body => .lam domain codomain body.source
  | .beta domain codomain body argument =>
      .apply (.lam domain codomain body) argument
  | .eta domain codomain function =>
      .lam domain codomain (.apply (Term.shiftAbove 1 0 function) (.var (.bvar domain 0)))
  | .trans first _second => first.source
def target : Trace σ → Term σ
  | .refl term => term
  | .appArgument symbol before argument suffix =>
      .app symbol (before ++ [argument.target] ++ suffix)
  | .applyFunction function argument => .apply function.target argument
  | .applyArgument function argument => .apply function argument.target
  | .lam domain codomain body => .lam domain codomain body.target
  | .beta _domain _codomain body argument => Term.instantiate argument body
  | .eta _domain _codomain function => function
  | .trans _first second => second.target
def checkWith (context : Context σ) : Trace σ → Bool
  | .refl _ => true
  | .appArgument _ _ argument _ => argument.checkWith context
  | .applyFunction function _ => function.checkWith context
  | .applyArgument _ argument => argument.checkWith context
  | .lam domain _ body => body.checkWith (domain :: context)
  | .beta domain codomain body argument =>
      body.inferSortWith (domain :: context) == some codomain &&
        argument.inferSortWith context == some domain
  | .eta domain codomain function =>
      function.inferSortWith context == some (.arrow domain codomain)
  | .trans first second =>
      first.checkWith context && second.checkWith context &&
        StructuralEq.term first.target second.source
def check (trace : Trace σ) : Bool :=
  trace.checkWith []
omit [DecidableEq σ.RelSymbol] in
theorem sound
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M) (trace : Trace σ) (context : Context σ) (env : Logic.HigherOrder.Env M)
    (hEnv : env.WellSorted context) (hCheck : trace.checkWith context = true) :
    Term.eval env trace.source = Term.eval env trace.target := by
  induction trace generalizing context env with
  | refl term =>
      rfl
  | appArgument symbol before argument suffix ih =>
      simp only [source, target, Term.eval]
      congr 1
      simp [List.map_append, ih context env hEnv hCheck]
  | applyFunction function argument ih =>
      simp only [source, target, Term.eval]
      exact congrArg (fun value => M.applyInterp value (Term.eval env argument)) (ih context env hEnv hCheck)
  | applyArgument function argument ih =>
      simp only [source, target, Term.eval]
      exact congrArg (M.applyInterp (Term.eval env function)) (ih context env hEnv hCheck)
  | lam domain codomain body ih =>
      simp only [source, target, Term.eval]
      apply contract.lambdaCongr
      intro value hValue
      exact ih (domain :: context) (env.push value) (Logic.HigherOrder.Env.wellSorted_push hEnv hValue) hCheck
  | beta domain codomain body argument =>
      have hFields :
          body.inferSortWith (domain :: context) = some codomain ∧
            argument.inferSortWith context = some domain := by
        simpa [checkWith] using hCheck
      rw [source, target, Logic.HigherOrder.ExtensionalContract.eval_beta contract,
        Logic.HigherOrder.Term.eval_instantiate]
      · intro value hValue
        exact
          Logic.HigherOrder.Term.eval_sort_of_inferSortWith (Logic.HigherOrder.Env.wellSorted_push hEnv hValue) hFields.1
      · exact
          Logic.HigherOrder.Term.eval_sort_of_inferSortWith hEnv
            hFields.2
  | eta domain codomain function =>
      have hFunction :
          function.inferSortWith context = some (.arrow domain codomain) := by
        simpa [checkWith] using hCheck
      exact Logic.HigherOrder.ExtensionalContract.eval_eta contract env
        domain codomain function <|
          Logic.HigherOrder.Term.eval_sort_of_inferSortWith hEnv
            hFunction
  | trans first second ihFirst ihSecond =>
      have hFields : (first.checkWith context = true ∧ second.checkWith context = true) ∧
            StructuralEq.term first.target second.source = true := by
        simpa [checkWith] using hCheck
      have hMiddle : first.target = second.source :=
        StructuralEq.term_sound first.target second.source hFields.2
      calc
        Term.eval env first.source = Term.eval env first.target :=
          ihFirst context env hEnv hFields.1.1
        _ = Term.eval env second.source := congrArg (Term.eval env) hMiddle
        _ = Term.eval env second.target := ihSecond context env hEnv hFields.1.2
end Trace
structure Payload (σ : Signature.{u, v, w}) where
  sort : SimpleType σ
  trace : Trace σ
namespace Payload
def conclusion (payload : Payload σ) : Clause σ where
  literals := #[{
    polarity := true
    atom := .equal payload.sort payload.trace.source payload.trace.target
  }]
def check (payload : Payload σ) : Bool :=
  payload.trace.check &&
    payload.trace.source.inferSort? == some payload.sort &&
      payload.trace.target.inferSort? == some payload.sort &&
        payload.conclusion.check
omit [DecidableEq σ.RelSymbol] in
theorem sound
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M) (payload : Payload σ) (env : Logic.HigherOrder.Env M)
    (hEnv : env.WellSorted []) (hCheck : payload.check = true) :
    payload.conclusion.Satisfies env := by
  have hTrace :
      payload.trace.check = true := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hCheck).1).1).1
  let literal : Literal σ := {
    polarity := true
    atom := .equal payload.sort payload.trace.source payload.trace.target
  }
  refine ⟨literal, by simp [conclusion, literal], ?_⟩
  simpa [Literal.Satisfies, Atom.Satisfies, literal] using
    Trace.sound contract payload.trace [] env hEnv hTrace
end Payload
end BetaEta
/-! ## 父节点局部规则 -/
structure ParentClause (σ : Signature.{u, v, w}) where
  id : Nat
  clause : Clause σ
namespace ParentClause
def idIn  (parents : Array Nat) (parent : ParentClause σ) : Bool :=
  parents.contains parent.id
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem mem_toList_of_idIn  {parents : Array Nat}
    {parent : ParentClause σ} (hIn : parent.idIn parents = true) :
    parent.id ∈ parents.toList := by
  have hArray : parent.id ∈ parents := by
    simpa [idIn] using hIn
  exact Array.mem_def.mp hArray
end ParentClause
/--
单父规则 checker 的公共结构契约。
规则专有契约通过扩展本结构补充局部条件，从而统一父边、父快照与结论检查字段。
-/
structure UnaryRuleContract (parents : Array Nat) (parent : ParentClause σ) (conclusion : Clause σ) : Prop where
  parent_id_in : parent.idIn parents = true
  parent_checked : parent.clause.check = true
  conclusion_checked : conclusion.check = true
structure BinaryRuleContract (parents : Array Nat) (left right : ParentClause σ) (conclusion : Clause σ) : Prop where
  left_id_in : left.idIn parents = true
  right_id_in : right.idIn parents = true
  left_checked : left.clause.check = true
  right_checked : right.clause.check = true
  conclusion_checked : conclusion.check = true
/-! ## HO-AVATAR component 描述 -/
namespace Avatar
structure FreeVariable (σ : Signature.{u, v, w}) where
  sort : SimpleType σ
  id : Nat
namespace FreeVariable
def eq (left right : FreeVariable σ) : Bool :=
  decide (left.sort = right.sort) && left.id == right.id
end FreeVariable
def pushFreeVariableUnique (support : Array (FreeVariable σ)) (candidate : FreeVariable σ) : Array (FreeVariable σ) :=
  if support.any fun existing => FreeVariable.eq existing candidate then
    support
  else
    support.push candidate
def mergeFreeSupport (left right : Array (FreeVariable σ)) :
    Array (FreeVariable σ) :=
  right.toList.foldl pushFreeVariableUnique left
mutual
  def termFreeSupport   :
      Term σ → Array (FreeVariable σ)
    | .var (.bvar _ _) => #[]
    | .var (.fvar sort id) => #[{ sort := sort, id := id }]
    | .app _ arguments => termListFreeSupport arguments
    | .apply function argument =>
        mergeFreeSupport (termFreeSupport function) (termFreeSupport argument)
    | .lam _ _ body => termFreeSupport body
  def termListFreeSupport   :
      List (Term σ) → Array (FreeVariable σ)
    | [] => #[]
    | term :: rest =>
        mergeFreeSupport (termFreeSupport term) (termListFreeSupport rest)
end
def atomFreeSupport :
    Atom σ → Array (FreeVariable σ)
  | .rel _ arguments => termListFreeSupport arguments
  | .equal _ left right =>
      mergeFreeSupport (termFreeSupport left) (termFreeSupport right)
def literalFreeSupport (literal : Literal σ) : Array (FreeVariable σ) :=
  atomFreeSupport literal.atom
def clauseFreeSupport (clause : Clause σ) : Array (FreeVariable σ) :=
  clause.literals.toList.foldl (fun support literal => mergeFreeSupport support (literalFreeSupport literal)) #[]
def supportsOverlap (left right : Array (FreeVariable σ)) : Bool :=
  left.any fun candidate =>
    right.any fun existing => FreeVariable.eq candidate existing
def clauseAtIndices  (clause : Clause σ) (indices : Array Nat) : Clause σ := {
  literals := indices.filterMap fun index => clause.literals[index]?
}
def pairwiseSupportDisjoint
     : List (Clause σ) → Bool
  | [] => true
  | head :: rest =>
      rest.all (fun other =>
          !supportsOverlap (clauseFreeSupport head) (clauseFreeSupport other)) &&
        pairwiseSupportDisjoint rest
private structure ComponentScanState (σ : Signature.{u, v, w}) where
  seen : Array Bool
  indices : Array Nat
  support : Array (FreeVariable σ)
  changed : Bool := false
private def scanComponent (clause : Clause σ) : List Nat → ComponentScanState σ → ComponentScanState σ
  | [], state => state
  | index :: rest, state =>
      if hIndex : index < clause.literals.size then
        if Array.getD state.seen index false then
          scanComponent clause rest state
        else
          let candidate := literalFreeSupport clause.literals[index]
          if supportsOverlap state.support candidate then
            scanComponent clause rest {
              seen := Array.set! state.seen index true
              indices := Array.push state.indices index
              support := mergeFreeSupport state.support candidate
              changed := true
            }
          else
            scanComponent clause rest state
      else
        scanComponent clause rest state
private def closeComponent (clause : Clause σ) :
    Nat → ComponentScanState σ → ComponentScanState σ
  | 0, state => state
  | fuel + 1, state =>
      let next := scanComponent clause (List.range clause.literals.size)
        { state with changed := false }
      if next.changed then
        closeComponent clause fuel next
      else
        next
private def splitClauseLoop (clause : Clause σ) :
    List Nat → Array Bool → Array (Array Nat × Clause σ) →
      Array (Array Nat × Clause σ)
  | [], _seen, components => components
  | start :: rest, seen, components =>
      if hStart : start < clause.literals.size then
        if Array.getD seen start false then
          splitClauseLoop clause rest seen components
        else
          let closed := closeComponent clause (clause.literals.size + 1) {
            seen := Array.set! seen start true
            indices := #[start]
            support := literalFreeSupport clause.literals[start]
          }
          splitClauseLoop clause rest closed.seen (components.push (closed.indices, clauseAtIndices clause closed.indices))
      else
        splitClauseLoop clause rest seen components
def splitClause (clause : Clause σ) : Array (Array Nat × Clause σ) :=
  splitClauseLoop clause (List.range clause.literals.size) (List.replicate clause.literals.size false).toArray #[]
end Avatar
namespace Substitution
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  substitution : TermSubstitution σ
namespace Evidence
def conclusion (evidence : Evidence σ) : Clause σ :=
  evidence.parent.clause.applySubstitution evidence.substitution
def check (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  evidence.parent.idIn parents &&
    evidence.parent.clause.check &&
      evidence.substitution.check &&
        evidence.conclusion.check
structure Contract (parents : Array Nat) (evidence : Evidence σ) : Prop
    extends
      UnaryRuleContract parents evidence.parent evidence.conclusion where
  substitution_checked : evidence.substitution.check = true
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem contract_of_check
    {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check parents = true) :
    Contract parents evidence := by
  simp [check] at hCheck
  rcases hCheck with
    ⟨⟨⟨hParentIn, hParentChecked⟩, hSubstitutionChecked⟩,
      hConclusionChecked⟩
  exact {
    parent_id_in := hParentIn
    parent_checked := hParentChecked
    substitution_checked := hSubstitutionChecked
    conclusion_checked := hConclusionChecked
  }
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem sound
    {M : Structure.{u, v, w, x} σ} (evidence : Evidence σ)
    {parents : Array Nat} (hCheck : evidence.check parents = true) (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  have hAdmissible : evidence.substitution.Admissible :=
    TermSubstitution.check_sound (contract_of_check hCheck).substitution_checked
  intro sourceEnv hSource
  let targetEnv :=
    TermSubstitution.semanticEnv evidence.substitution sourceEnv
  have hTarget : targetEnv.WellSorted [] :=
    TermSubstitution.semanticEnv_wellSorted hAdmissible hSource
  have hParentSat : evidence.parent.clause.Satisfies targetEnv :=
    hParent targetEnv hTarget
  exact (Clause.satisfies_applySubstitution_iff_of_envMatches hAdmissible (TermSubstitution.semanticEnv_matches
        (substitution := evidence.substitution) (sourceEnv := sourceEnv))
      evidence.parent.clause).mpr hParentSat
end Evidence
end Substitution
namespace StandardizeApart
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  offset : Nat
namespace Evidence
def conclusion  (evidence : Evidence σ) : Clause σ :=
  evidence.parent.clause.renameFreeVars evidence.offset
def check (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  evidence.parent.idIn parents &&
    evidence.parent.clause.check &&
      evidence.conclusion.check
abbrev Contract (parents : Array Nat) (evidence : Evidence σ) :=
  UnaryRuleContract parents evidence.parent evidence.conclusion
omit [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem contract_of_check
    {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check parents = true) :
    Contract parents evidence := by
  simp [check] at hCheck
  exact ⟨hCheck.1.1, hCheck.1.2, hCheck.2⟩
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem sound  {M : Structure.{u, v, w, x} σ} (evidence : Evidence σ) (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  intro sourceEnv hSource
  let targetEnv := FreeVarRenaming.semanticEnv evidence.offset sourceEnv
  have hTarget : targetEnv.WellSorted [] :=
    FreeVarRenaming.semanticEnv_wellSorted hSource
  have hParentSat : evidence.parent.clause.Satisfies targetEnv :=
    hParent targetEnv hTarget
  exact (Clause.satisfies_renameFreeVars_iff_of_envMatches (FreeVarRenaming.semanticEnv_matches (offset := evidence.offset) (sourceEnv := sourceEnv))
      evidence.parent.clause).mpr hParentSat
end Evidence
end StandardizeApart
namespace Resolution
structure Evidence (σ : Signature.{u, v, w}) where
  left : ParentClause σ
  right : ParentClause σ
  pivot : Atom σ
  leftPolarity : Bool := true
namespace Evidence
def conclusion (evidence : Evidence σ) : Clause σ :=
  Clause.resolutionResult evidence.leftPolarity evidence.pivot
    evidence.left.clause evidence.right.clause
def check (parents : Array Nat) (evidence : Evidence σ) : Bool := (evidence.left.idIn parents && evidence.right.idIn parents) &&
    (evidence.left.clause.check && evidence.right.clause.check) && (evidence.left.clause.containsMatching evidence.leftPolarity evidence.pivot &&
        evidence.right.clause.containsMatching (!evidence.leftPolarity) evidence.pivot) &&
        evidence.conclusion.check
structure Contract (parents : Array Nat) (evidence : Evidence σ) : Prop
    extends
      BinaryRuleContract parents evidence.left evidence.right evidence.conclusion where
  left_contains :
    evidence.left.clause.containsMatching evidence.leftPolarity evidence.pivot = true
  right_contains :
    evidence.right.clause.containsMatching (!evidence.leftPolarity)
      evidence.pivot = true
theorem contract_of_check
    {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check parents = true) :
    Contract parents evidence := by
  simp [check] at hCheck
  exact {
    left_id_in := hCheck.1.1.1.1
    right_id_in := hCheck.1.1.1.2
    left_checked := hCheck.1.1.2.1
    right_checked := hCheck.1.1.2.2
    left_contains := hCheck.1.2.1
    right_contains := hCheck.1.2.2
    conclusion_checked := hCheck.2
  }
theorem sound
    {M : Structure.{u, v, w, x} σ} (evidence : Evidence σ) (hLeft : evidence.left.clause.Valid M) (hRight : evidence.right.clause.Valid M) :
    evidence.conclusion.Valid M :=
  fun env hEnv => Clause.satisfies_resolutionResult (hLeft env hEnv) (hRight env hEnv)
end Evidence
end Resolution
namespace Factoring
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  conclusion : Clause σ
namespace Evidence
def check (parents : Array Nat) (evidence : Evidence σ) : Bool := (evidence.parent.idIn parents && evidence.parent.clause.check) &&
    (evidence.conclusion.check &&
      evidence.parent.clause.allLiteralsCovered evidence.conclusion) && (evidence.conclusion.allLiteralsCovered evidence.parent.clause &&
          decide (evidence.conclusion.literals.size <= evidence.parent.clause.literals.size))
structure Contract (parents : Array Nat) (evidence : Evidence σ) : Prop
    extends
      UnaryRuleContract parents evidence.parent evidence.conclusion where
  parent_covers :
    evidence.parent.clause.allLiteralsCovered evidence.conclusion = true
  conclusion_covers :
    evidence.conclusion.allLiteralsCovered evidence.parent.clause = true
  nonexpansive :
    evidence.conclusion.literals.size <= evidence.parent.clause.literals.size
theorem contract_of_check
    {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check parents = true) :
    Contract parents evidence := by
  simp [check] at hCheck
  exact {
    parent_id_in := hCheck.1.1.1
    parent_checked := hCheck.1.1.2
    conclusion_checked := hCheck.1.2.1
    parent_covers := hCheck.1.2.2
    conclusion_covers := hCheck.2.1
    nonexpansive := hCheck.2.2
  }
theorem sound
    {M : Structure.{u, v, w, x} σ} (evidence : Evidence σ)
    {parents : Array Nat} (hCheck : evidence.check parents = true) (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  have hCovered :
      evidence.parent.clause.allLiteralsCovered evidence.conclusion = true := (contract_of_check hCheck).parent_covers
  intro env hEnv
  exact Clause.satisfies_of_allLiteralsCovered hCovered (hParent env hEnv)
end Evidence
end Factoring
namespace EqualityResolution
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  sort : SimpleType σ
  left : Term σ
  right : Term σ
namespace Evidence
def conclusion (evidence : Evidence σ) : Clause σ :=
  Clause.equalityResolutionResult evidence.sort evidence.left evidence.right
    evidence.parent.clause
def check (parents : Array Nat) (evidence : Evidence σ) : Bool := (evidence.parent.idIn parents && evidence.parent.clause.check) &&
    (StructuralEq.term evidence.left evidence.right &&
      evidence.parent.clause.containsMatching false (.equal evidence.sort evidence.left evidence.right)) &&
        evidence.conclusion.check
structure Contract (parents : Array Nat) (evidence : Evidence σ) : Prop
    extends
      UnaryRuleContract parents evidence.parent evidence.conclusion where
  terms_equal : StructuralEq.term evidence.left evidence.right = true
  parent_contains :
    evidence.parent.clause.containsMatching false (.equal evidence.sort evidence.left evidence.right) = true
theorem contract_of_check
    {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check parents = true) :
    Contract parents evidence := by
  simp [check] at hCheck
  exact {
    parent_id_in := hCheck.1.1.1
    parent_checked := hCheck.1.1.2
    terms_equal := hCheck.1.2.1
    parent_contains := hCheck.1.2.2
    conclusion_checked := hCheck.2
  }
theorem sound
    {M : Structure.{u, v, w, x} σ} (evidence : Evidence σ)
    {parents : Array Nat} (hCheck : evidence.check parents = true) (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  have hTerm : StructuralEq.term evidence.left evidence.right = true := (contract_of_check hCheck).terms_equal
  intro env hEnv
  exact Clause.satisfies_equalityResolutionResult hTerm (hParent env hEnv)
end Evidence
end EqualityResolution
namespace BooleanExtensionality
/--
布尔等词 βη 归一化证据。
证书核实际证明任意 simple type 上的等词归一化；搜索材料化层再把该规则收紧到
`bool`，从而把语义复用与搜索策略边界分离。
-/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  literalIndex : Nat
  sort : SimpleType σ
  polarity : Bool
  left : BetaEta.Trace σ
  right : BetaEta.Trace σ
namespace Evidence
def needle  (evidence : Evidence σ) : Literal σ where
  polarity := evidence.polarity
  atom := .equal evidence.sort evidence.left.source evidence.right.source
def replacement  (evidence : Evidence σ) : Literal σ where
  polarity := evidence.polarity
  atom := .equal evidence.sort evidence.left.target evidence.right.target
def selectedCheck (evidence : Evidence σ) : Bool :=
  match evidence.parent.clause.literals[evidence.literalIndex]? with
  | some literal => literal.eq evidence.needle
  | none => false
def conclusion (evidence : Evidence σ) : Clause σ := (evidence.parent.clause.replaceLiteralAtEnd evidence.literalIndex
    evidence.replacement).normalize
def check (parents : Array Nat) (evidence : Evidence σ) : Bool := ((evidence.parent.idIn parents && evidence.parent.clause.check) &&
    (evidence.selectedCheck && (evidence.left.check && evidence.right.check))) && (((decide (evidence.left.source.inferSort? = some evidence.sort) &&
        decide (evidence.right.source.inferSort? = some evidence.sort)) && (decide (evidence.left.target.inferSort? = some evidence.sort) &&
            decide (evidence.right.target.inferSort? = some evidence.sort))) &&
        evidence.conclusion.check)
structure Contract (parents : Array Nat) (evidence : Evidence σ) : Prop
    extends
      UnaryRuleContract parents evidence.parent evidence.conclusion where
  selected_checked : evidence.selectedCheck = true
  left_trace_checked : evidence.left.check = true
  right_trace_checked : evidence.right.check = true
  left_source_sort : evidence.left.source.inferSort? = some evidence.sort
  right_source_sort : evidence.right.source.inferSort? = some evidence.sort
  left_target_sort : evidence.left.target.inferSort? = some evidence.sort
  right_target_sort : evidence.right.target.inferSort? = some evidence.sort
theorem contract_of_check
    {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check parents = true) :
    Contract parents evidence := by
  simp [check] at hCheck
  exact {
    parent_id_in := hCheck.1.1.1
    parent_checked := hCheck.1.1.2
    selected_checked := hCheck.1.2.1
    left_trace_checked := hCheck.1.2.2.1
    right_trace_checked := hCheck.1.2.2.2
    left_source_sort := hCheck.2.1.1.1
    right_source_sort := hCheck.2.1.1.2
    left_target_sort := hCheck.2.1.2.1
    right_target_sort := hCheck.2.1.2.2
    conclusion_checked := hCheck.2.2
  }
theorem selected_of_check
    {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check parents = true) :
    evidence.parent.clause.literals[evidence.literalIndex]? =
      some evidence.needle := by
  have hSelected : evidence.selectedCheck = true := (contract_of_check hCheck).selected_checked
  unfold selectedCheck at hSelected
  cases hLiteral :
      evidence.parent.clause.literals[evidence.literalIndex]? with
  | none =>
      simp [hLiteral] at hSelected
  | some literal =>
      have hEq : literal.eq evidence.needle = true := by
        simpa [hLiteral] using hSelected
      exact congrArg some (Literal.eq_sound literal evidence.needle hEq)
theorem satisfies_iff_replacement
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M) (evidence : Evidence σ) {parents : Array Nat}
    (hCheck : evidence.check parents = true) (env : Logic.HigherOrder.Env M) (hEnv : env.WellSorted []) :
    evidence.needle.Satisfies env ↔ evidence.replacement.Satisfies env := by
  have hContract := contract_of_check hCheck
  have hLeft :
      Term.eval env evidence.left.source = Term.eval env evidence.left.target :=
    evidence.left.sound contract [] env hEnv hContract.left_trace_checked
  have hRight :
      Term.eval env evidence.right.source = Term.eval env evidence.right.target :=
    evidence.right.sound contract [] env hEnv hContract.right_trace_checked
  have hAtom : (Term.eval env evidence.left.source =
        Term.eval env evidence.right.source) ↔ (Term.eval env evidence.left.target =
        Term.eval env evidence.right.target) := by
    rw [hLeft, hRight]
  cases hPolarity : evidence.polarity with
  | false =>
      simpa [needle, replacement, Literal.Satisfies, Atom.Satisfies, hPolarity]
        using not_congr hAtom
  | true =>
      simpa [needle, replacement, Literal.Satisfies, Atom.Satisfies, hPolarity]
        using hAtom
theorem sound
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M) (evidence : Evidence σ) {parents : Array Nat}
    (hCheck : evidence.check parents = true) (hParent : evidence.parent.clause.Valid M) :
    evidence.conclusion.Valid M := by
  intro env hEnv
  apply Clause.satisfies_normalize
  exact Clause.satisfies_replaceLiteralAtEnd (evidence.selected_of_check hCheck) ((evidence.satisfies_iff_replacement contract hCheck env hEnv).mp)
    (hParent env hEnv)
end Evidence
end BooleanExtensionality
/-! ## 高阶上下文重写与 superposition -/
/--
原生高阶项的一孔上下文。
`app` 处理签名函数的未柯里化参数，两个 `apply` 分支分别进入函数位与实参位；
`lam` 直接进入局部无名 body，不经过 lambda lifting。
-/
inductive TermContext (σ : Signature.{u, v, w}) where
  | hole
  | app (symbol : σ.FuncSymbol) (before : List (Term σ)) (context : TermContext σ) (suffix : List (Term σ))
  | applyFunction (context : TermContext σ) (argument : Term σ)
  | applyArgument (function : Term σ) (context : TermContext σ)
  | lam (domain codomain : SimpleType σ) (context : TermContext σ)
namespace TermContext
def fill : TermContext σ → Term σ → Term σ
  | .hole, term => term
  | .app symbol before context suffix, term =>
      .app symbol (before ++ [context.fill term] ++ suffix)
  | .applyFunction context argument, term =>
      .apply (context.fill term) argument
  | .applyArgument function context, term =>
      .apply function (context.fill term)
  | .lam domain codomain context, term =>
      .lam domain codomain (context.fill term)
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
/--
空绑定上下文中的同类型等值项可在任意原生 HO 项上下文中替换。
`lam` 分支先用闭项的环境不变性把等式搬到 `env.push value`，再由
`ExtensionalContract.lambdaCongr` 封装函数值同余；这也是排除变量捕获的语义边界。
-/
theorem eval_fill_eq_of_eq
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M)
    {env : Logic.HigherOrder.Env M} {context : TermContext σ}
    {lhs rhs : Term σ} {sort : SimpleType σ} (hLhs : TermWellSorted [] lhs sort) (hRhs : TermWellSorted [] rhs sort)
    (hEq : Term.eval env lhs = Term.eval env rhs) :
    Term.eval env (context.fill lhs) = Term.eval env (context.fill rhs) := by
  induction context generalizing env lhs rhs sort with
  | hole =>
      simpa [fill] using hEq
  | app symbol before context suffix ih =>
      simp only [fill, Term.eval]
      congr 1
      simp [List.map_append, ih hLhs hRhs hEq]
  | applyFunction context argument ih =>
      simp only [fill, Term.eval]
      rw [ih hLhs hRhs hEq]
  | applyArgument function context ih =>
      simp only [fill, Term.eval]
      rw [ih hLhs hRhs hEq]
  | lam domain codomain context ih =>
      simp only [fill, Term.eval]
      apply contract.lambdaCongr
      intro value _hValue
      have hLhsPush : Term.eval (env.push value) lhs = Term.eval env lhs := by
        apply Term.eval_eq_of_wellSorted_env hLhs
        · intro index target hLookup
          simp [Context.lookup?] at hLookup
        · intro target id
          rfl
      have hRhsPush : Term.eval (env.push value) rhs = Term.eval env rhs := by
        apply Term.eval_eq_of_wellSorted_env hRhs
        · intro index target hLookup
          simp [Context.lookup?] at hLookup
        · intro target id
          rfl
      exact ih hLhs hRhs (hLhsPush.trans (hEq.trans hRhsPush.symm))
end TermContext
inductive AtomContext (σ : Signature.{u, v, w}) where
  | rel (symbol : σ.RelSymbol) (before : List (Term σ)) (context : TermContext σ) (suffix : List (Term σ))
  | equalLeft (sort : SimpleType σ) (context : TermContext σ) (right : Term σ)
  | equalRight (sort : SimpleType σ) (left : Term σ) (context : TermContext σ)
namespace AtomContext
def isEquality : AtomContext σ → Bool
  | .rel _ _ _ _ => false
  | .equalLeft _ _ _ => true
  | .equalRight _ _ _ => true
def fill : AtomContext σ → Term σ → Atom σ
  | .rel symbol before context suffix, term =>
      .rel symbol (before ++ [context.fill term] ++ suffix)
  | .equalLeft sort context right, term =>
      .equal sort (context.fill term) right
  | .equalRight sort left context, term =>
      .equal sort left (context.fill term)
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem satisfies_iff_of_eval_eq
    {M : Structure.{u, v, w, x} σ} (contract : Logic.HigherOrder.ExtensionalContract M)
    {env : Logic.HigherOrder.Env M} {context : AtomContext σ}
    {lhs rhs : Term σ} {sort : SimpleType σ} (hLhs : TermWellSorted [] lhs sort) (hRhs : TermWellSorted [] rhs sort)
    (hEq : Term.eval env lhs = Term.eval env rhs) : (context.fill lhs).Satisfies env ↔ (context.fill rhs).Satisfies env := by
  cases context with
  | rel symbol before context suffix =>
      have hTerm :=
        TermContext.eval_fill_eq_of_eq contract (context := context) hLhs hRhs hEq
      have hArguments : (before ++ [context.fill lhs] ++ suffix).map (Term.eval env) = (before ++ [context.fill rhs] ++ suffix).map (Term.eval env) := by
        simp [List.map_append, hTerm]
      change
        M.relInterp symbol ((before ++ [context.fill lhs] ++ suffix).map (Term.eval env)) ↔
          M.relInterp symbol ((before ++ [context.fill rhs] ++ suffix).map (Term.eval env))
      rw [hArguments]
  | equalLeft atomSort context right =>
      have hTerm :=
        TermContext.eval_fill_eq_of_eq contract (context := context) hLhs hRhs hEq
      simp only [fill, Atom.Satisfies]
      rw [hTerm]
  | equalRight atomSort left context =>
      have hTerm :=
        TermContext.eval_fill_eq_of_eq contract (context := context) hLhs hRhs hEq
      simp only [fill, Atom.Satisfies]
      rw [hTerm]
end AtomContext
inductive RewriteKind where
  | demodulation
  | positiveSuperposition
  | negativeSuperposition
  | extensionalParamodulation
  deriving Repr, Inhabited, DecidableEq, Lean.ToExpr
namespace Rewrite
/--
正等词驱动的原生 HO 上下文重写证据。
父节点应先完成 standardize-apart 与 typed substitution；这里保存的上下文、方向和类型
全部由 checker 重新核对。规则类别只增加专用边界，不改变机械结论与语义证明。
-/
structure Evidence (σ : Signature.{u, v, w}) where
  equality : ParentClause σ
  target : ParentClause σ
  context : AtomContext σ
  sort : SimpleType σ
  lhs : Term σ
  rhs : Term σ
  equalityReversed : Bool := false
  targetPolarity : Bool := true
namespace Evidence
def equalityAtom  (evidence : Evidence σ) : Atom σ :=
  if evidence.equalityReversed then
    .equal evidence.sort evidence.rhs evidence.lhs
  else
    .equal evidence.sort evidence.lhs evidence.rhs
def needle  (evidence : Evidence σ) : Literal σ where
  polarity := evidence.targetPolarity
  atom := evidence.context.fill evidence.lhs
def replacement  (evidence : Evidence σ) : Literal σ where
  polarity := evidence.targetPolarity
  atom := evidence.context.fill evidence.rhs
def conclusion (evidence : Evidence σ) : Clause σ where
  literals := (Clause.filterOutList true evidence.equalityAtom
        evidence.equality.clause.literals.toList ++ (evidence.target.clause.replaceLiteral evidence.needle
        evidence.replacement).literals.toList).toArray
def kindCheck  (kind : RewriteKind) (evidence : Evidence σ) : Bool :=
  match kind with
  | .demodulation =>
      decide (evidence.equality.clause.literals.size = 1)
  | .positiveSuperposition =>
      evidence.targetPolarity
  | .negativeSuperposition =>
      !evidence.targetPolarity && evidence.context.isEquality
  | .extensionalParamodulation =>
      evidence.targetPolarity && (match evidence.sort with
        | .arrow .. => true
        | .base _ =>
            match evidence.lhs with
            | .apply .. => true
            | .lam .. => true
            | _ => false)
def check (kind : RewriteKind) (parents : Array Nat) (evidence : Evidence σ) : Bool := (((((((evidence.equality.idIn parents && evidence.target.idIn parents) &&
    (evidence.equality.clause.check && evidence.target.clause.check)) &&
      evidence.equality.clause.containsMatching true
        evidence.equalityAtom) &&
        evidence.target.clause.containsLiteral evidence.needle) &&
          decide (evidence.lhs.inferSort? = some evidence.sort)) &&
            decide (evidence.rhs.inferSort? = some evidence.sort)) &&
              kindCheck kind evidence) &&
                evidence.conclusion.check
structure Contract (kind : RewriteKind) (parents : Array Nat) (evidence : Evidence σ) : Prop
    extends
      BinaryRuleContract parents evidence.equality evidence.target evidence.conclusion where
  equality_contains :
    evidence.equality.clause.containsMatching true evidence.equalityAtom = true
  target_contains : evidence.target.clause.containsLiteral evidence.needle = true
  lhs_sort : evidence.lhs.inferSort? = some evidence.sort
  rhs_sort : evidence.rhs.inferSort? = some evidence.sort
  kind_checked : kindCheck kind evidence = true
theorem contract_of_check
    {kind : RewriteKind} {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check kind parents = true) :
    Contract kind parents evidence := by
  simp [check] at hCheck
  exact {
    left_id_in := hCheck.1.1.1.1.1.1.1.1
    right_id_in := hCheck.1.1.1.1.1.1.1.2
    left_checked := hCheck.1.1.1.1.1.1.2.1
    right_checked := hCheck.1.1.1.1.1.1.2.2
    equality_contains := hCheck.1.1.1.1.1.2
    target_contains := hCheck.1.1.1.1.2
    lhs_sort := hCheck.1.1.1.2
    rhs_sort := hCheck.1.1.2
    kind_checked := hCheck.1.2
    conclusion_checked := hCheck.2
  }
private theorem eval_eq_of_parent
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M}
    {evidence : Evidence σ} {literal : Literal σ} (hMatch :
      literal.matchesAtom true evidence.equalityAtom = true) (hLiteral : literal.Satisfies env) :
    Term.eval env evidence.lhs = Term.eval env evidence.rhs := by
  rcases Literal.matchesAtom_sound hMatch with ⟨hPolarity, hAtom⟩
  cases literal with
  | mk polarity atom =>
      cases hPolarity
      cases hReversed : evidence.equalityReversed with
      | false =>
          have hAtom' :
              atom = (.equal evidence.sort evidence.lhs evidence.rhs : Atom σ) := by
            simpa [equalityAtom, hReversed] using hAtom
          cases hAtom'
          simpa [Literal.Satisfies, Atom.Satisfies] using hLiteral
      | true =>
          have hAtom' :
              atom = (.equal evidence.sort evidence.rhs evidence.lhs : Atom σ) := by
            simpa [equalityAtom, hReversed] using hAtom
          cases hAtom'
          have hReverse :
              Term.eval env evidence.rhs = Term.eval env evidence.lhs := by
            simpa [Literal.Satisfies, Atom.Satisfies] using hLiteral
          exact hReverse.symm
private theorem satisfies_iff_replacement
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M} (contract : Logic.HigherOrder.ExtensionalContract M)
    {evidence : Evidence σ} {kind : RewriteKind} {parents : Array Nat} (hCheck : evidence.check kind parents = true)
    (hEq : Term.eval env evidence.lhs = Term.eval env evidence.rhs) :
    evidence.needle.Satisfies env ↔ evidence.replacement.Satisfies env := by
  have hLhsCheck : evidence.lhs.inferSort? = some evidence.sort := (contract_of_check hCheck).lhs_sort
  have hRhsCheck : evidence.rhs.inferSort? = some evidence.sort := (contract_of_check hCheck).rhs_sort
  have hLhs : TermWellSorted [] evidence.lhs evidence.sort :=
    Term.inferSortWith_sound hLhsCheck
  have hRhs : TermWellSorted [] evidence.rhs evidence.sort :=
    Term.inferSortWith_sound hRhsCheck
  have hAtom :=
    AtomContext.satisfies_iff_of_eval_eq contract (context := evidence.context) hLhs hRhs hEq
  cases hPolarity : evidence.targetPolarity with
  | false =>
      simpa [needle, replacement, Literal.Satisfies, hPolarity] using not_congr hAtom
  | true =>
      simpa [needle, replacement, Literal.Satisfies, hPolarity] using hAtom
theorem sound
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M} (contract : Logic.HigherOrder.ExtensionalContract M)
    (evidence : Evidence σ) {kind : RewriteKind} {parents : Array Nat} (hCheck : evidence.check kind parents = true)
    (hEquality : evidence.equality.clause.Satisfies env) (hTarget : evidence.target.clause.Satisfies env) :
    evidence.conclusion.Satisfies env := by
  rcases hEquality with ⟨equalityLiteral, hEqualityMem, hEqualitySat⟩
  cases hMatch :
      equalityLiteral.matchesAtom true evidence.equalityAtom with
  | false =>
      exact Clause.satisfies_of_literal_mem (by
          simp [conclusion]
          exact Or.inl (Clause.mem_filterOutList_of_mem_of_not_matches (Array.mem_def.mp hEqualityMem) hMatch))
        hEqualitySat
  | true =>
      have hEq : Term.eval env evidence.lhs = Term.eval env evidence.rhs :=
        eval_eq_of_parent hMatch hEqualitySat
      have hTarget' : (evidence.target.clause.replaceLiteral evidence.needle
            evidence.replacement).Satisfies env :=
        Clause.satisfies_replaceLiteral ((satisfies_iff_replacement contract hCheck hEq).mp) hTarget
      rcases hTarget' with ⟨literal, hMem, hLiteral⟩
      exact Clause.satisfies_of_literal_mem (by
          simp [conclusion]
          exact Or.inr hMem)
        hLiteral
end Evidence
end Rewrite
namespace ArgumentCongruence
/--
一参数 Argument Congruence 证据。
多参数版本由重复应用本规则得到；函数等式与实参都显式保存，结果字句由证据机械复算。
-/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  domain : SimpleType σ
  codomain : SimpleType σ
  left : Term σ
  right : Term σ
  argument : Term σ
namespace Evidence
def needle  (evidence : Evidence σ) : Literal σ where
  polarity := true
  atom := .equal (.arrow evidence.domain evidence.codomain)
    evidence.left evidence.right
def replacement  (evidence : Evidence σ) : Literal σ where
  polarity := true
  atom := .equal evidence.codomain (.apply evidence.left evidence.argument) (.apply evidence.right evidence.argument)
def conclusion (evidence : Evidence σ) : Clause σ :=
  evidence.parent.clause.replaceLiteral evidence.needle evidence.replacement
def check (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  evidence.parent.idIn parents &&
    evidence.parent.clause.check &&
      evidence.parent.clause.containsLiteral evidence.needle &&
        decide (evidence.argument.inferSort? = some evidence.domain) &&
          evidence.conclusion.check
structure Contract (parents : Array Nat) (evidence : Evidence σ) : Prop
    extends
      UnaryRuleContract parents evidence.parent evidence.conclusion where
  parent_contains : evidence.parent.clause.containsLiteral evidence.needle = true
  argument_sort : evidence.argument.inferSort? = some evidence.domain
theorem contract_of_check
    {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check parents = true) :
    Contract parents evidence := by
  simp [check] at hCheck
  exact {
    parent_id_in := hCheck.1.1.1.1
    parent_checked := hCheck.1.1.1.2
    parent_contains := hCheck.1.1.2
    argument_sort := hCheck.1.2
    conclusion_checked := hCheck.2
  }
omit [DecidableEq σ.BaseSort] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem replacement_satisfies
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M} (evidence : Evidence σ) (hNeedle : evidence.needle.Satisfies env) :
    evidence.replacement.Satisfies env := by
  simp only [needle, replacement, Literal.Satisfies, if_true, Atom.Satisfies,
    Logic.HigherOrder.Term.eval] at hNeedle ⊢
  exact congrArg (fun functionValue =>
      M.applyInterp functionValue (Logic.HigherOrder.Term.eval env evidence.argument))
    hNeedle
theorem sound
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M} (evidence : Evidence σ) (hParent : evidence.parent.clause.Satisfies env) :
    evidence.conclusion.Satisfies env :=
  Clause.satisfies_replaceLiteral (evidence.replacement_satisfies) hParent
end Evidence
end ArgumentCongruence
namespace FunctionExtensionality
/--
函数外延负规则的显式差异见证。
见证项固定为 `witnessSymbol(left, right)`；checker 同时复核符号角色、二元函数参数
类型和结果类型，不能由搜索器交付任意实参替代。
-/
structure Evidence (σ : Signature.{u, v, w}) where
  parent : ParentClause σ
  domain : SimpleType σ
  codomain : SimpleType σ
  left : Term σ
  right : Term σ
  witnessSymbol : σ.FuncSymbol
namespace Evidence
def needle  (evidence : Evidence σ) : Literal σ where
  polarity := false
  atom := .equal (.arrow evidence.domain evidence.codomain)
    evidence.left evidence.right
def witness  (evidence : Evidence σ) : Term σ :=
  .app evidence.witnessSymbol [evidence.left, evidence.right]
def replacement  (evidence : Evidence σ) : Literal σ where
  polarity := false
  atom := .equal evidence.codomain (.apply evidence.left evidence.witness) (.apply evidence.right evidence.witness)
def conclusion (evidence : Evidence σ) : Clause σ :=
  evidence.parent.clause.replaceLiteral evidence.needle evidence.replacement
def check (parents : Array Nat) (evidence : Evidence σ) : Bool :=
  evidence.parent.idIn parents &&
    evidence.parent.clause.check &&
      evidence.parent.clause.containsLiteral evidence.needle &&
        σ.isFunctionExtensionalityWitness evidence.witnessSymbol &&
          decide (σ.funcDomain evidence.witnessSymbol =
              [.arrow evidence.domain evidence.codomain,
                .arrow evidence.domain evidence.codomain]) &&
            decide (σ.funcCodomain evidence.witnessSymbol = evidence.domain) &&
              decide (evidence.left.inferSort? =
                  some (.arrow evidence.domain evidence.codomain)) &&
                decide (evidence.right.inferSort? =
                    some (.arrow evidence.domain evidence.codomain)) &&
                  evidence.conclusion.check
structure Contract (parents : Array Nat) (evidence : Evidence σ) : Prop
    extends
      UnaryRuleContract parents evidence.parent evidence.conclusion where
  parent_contains : evidence.parent.clause.containsLiteral evidence.needle = true
  witness_checked :
    σ.isFunctionExtensionalityWitness evidence.witnessSymbol = true
  witness_domain :
    σ.funcDomain evidence.witnessSymbol =
      [.arrow evidence.domain evidence.codomain,
        .arrow evidence.domain evidence.codomain]
  witness_codomain :
    σ.funcCodomain evidence.witnessSymbol = evidence.domain
  left_sort :
    evidence.left.inferSort? =
      some (.arrow evidence.domain evidence.codomain)
  right_sort :
    evidence.right.inferSort? =
      some (.arrow evidence.domain evidence.codomain)
theorem contract_of_check
    {parents : Array Nat} {evidence : Evidence σ} (hCheck : evidence.check parents = true) :
    Contract parents evidence := by
  simp [check] at hCheck
  exact {
    parent_id_in := hCheck.1.1.1.1.1.1.1.1
    parent_checked := hCheck.1.1.1.1.1.1.1.2
    parent_contains := hCheck.1.1.1.1.1.1.2
    witness_checked := hCheck.1.1.1.1.1.2
    witness_domain := hCheck.1.1.1.1.2
    witness_codomain := hCheck.1.1.1.2
    left_sort := hCheck.1.1.2
    right_sort := hCheck.1.2
    conclusion_checked := hCheck.2
  }
theorem replacement_satisfies
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M} (contract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (hEnv : env.WellSorted []) (evidence : Evidence σ) {parents : Array Nat} (hCheck : evidence.check parents = true)
    (hNeedle : evidence.needle.Satisfies env) :
    evidence.replacement.Satisfies env := by
  have hContract := contract_of_check hCheck
  simp only [needle, replacement, witness, Literal.Satisfies, Atom.Satisfies]
    at hNeedle ⊢
  exact Logic.HigherOrder.ExtensionalWitnessContract.eval_distinguishes
    contract env hEnv evidence.witnessSymbol evidence.domain evidence.codomain
    evidence.left evidence.right hContract.witness_checked hContract.witness_domain
    hContract.witness_codomain hContract.left_sort hContract.right_sort hNeedle
theorem sound
    {M : Structure.{u, v, w, x} σ} {env : Logic.HigherOrder.Env M} (contract : Logic.HigherOrder.ExtensionalWitnessContract M)
    (hEnv : env.WellSorted []) (evidence : Evidence σ) {parents : Array Nat} (hCheck : evidence.check parents = true)
    (hParent : evidence.parent.clause.Satisfies env) :
    evidence.conclusion.Satisfies env :=
  Clause.satisfies_replaceLiteral (evidence.replacement_satisfies contract hEnv hCheck) hParent
end Evidence
end FunctionExtensionality
end HODAGCertificateSignature
end HODAGCertificate
end Automation
end YesMetaZFC
