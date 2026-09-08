import YesMetaZFC.Automation.DAGCertificate.Syntax
import YesMetaZFC.Automation.Guards

/-!
# DAG 证书的局部 evidence 核

本模块只保存局部推理规则的有限数据、结构变换和布尔 checker。旧实现混入的模型环境、
满足关系、替换环境传输与自由变量闭合语义已全部移除。可靠性证明将在原始证书语法
通过检查编译器进入内在类型逻辑后统一建立。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate

open _root_.YesMetaZFC.Automation

section DAGCertificateSignature

variable {σ : Signature}
variable [DecidableEq σ.SortSymbol]
variable [DecidableEq σ.FuncSymbol]
variable [DecidableEq σ.RelSymbol]

/-! ## Guarded 字句 -/

abbrev GuardLit := Guards.Lit
abbrev GuardSet := Guards.Set
abbrev GuardedClause (σ : Signature) :=
  Guards.GuardedClause (Clause σ)

namespace GuardedClause

def plain (clause : Clause σ) : GuardedClause σ :=
  Guards.GuardedClause.plain clause

def unguarded (clause : GuardedClause σ) : Bool :=
  Guards.GuardedClause.unguarded clause

def globallyEmpty (clause : GuardedClause σ) : Bool :=
  Guards.GuardedClause.globallyEmpty Clause.isEmpty clause

def theoryConflict (clause : GuardedClause σ) : Bool :=
  Guards.GuardedClause.theoryConflict Clause.isEmpty clause

def eq (left right : GuardedClause σ) : Bool :=
  Guards.GuardedClause.eq Clause.eq left right

end GuardedClause

/-! ## 父节点快照与变量标准化 -/

structure ParentClause (σ : Signature) where
  id : NodeId
  clause : Clause σ

namespace ParentClause

def idIn (parents : Array NodeId) (parent : ParentClause σ) : Bool :=
  parents.contains parent.id

omit [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol] [DecidableEq σ.RelSymbol] in
theorem mem_toList_of_idIn {parents : Array NodeId}
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

def expected (evidence : StandardizeApartSideEvidence σ) : Clause σ :=
  Clause.renameFreeVars evidence.offset evidence.original

def check (evidence : StandardizeApartSideEvidence σ) : Bool :=
  evidence.renamed.eq evidence.expected

theorem check_sound {evidence : StandardizeApartSideEvidence σ}
    (hCheck : evidence.check = true) :
    evidence.renamed = evidence.expected :=
  Clause.eq_sound evidence.renamed evidence.expected hCheck

end StandardizeApartSideEvidence

/-- 二元规则两侧的显式变量改名证据。 -/
structure StandardizeApartEvidence (σ : Signature) where
  left : StandardizeApartSideEvidence σ
  right : StandardizeApartSideEvidence σ

namespace StandardizeApartEvidence

def check (evidence : StandardizeApartEvidence σ) : Bool :=
  evidence.left.check && evidence.right.check

theorem check_sound {evidence : StandardizeApartEvidence σ}
    (hCheck : evidence.check = true) :
    evidence.left.renamed = evidence.left.expected ∧
      evidence.right.renamed = evidence.right.expected := by
  rcases Bool.and_eq_true_iff.mp hCheck with ⟨hLeft, hRight⟩
  exact ⟨StandardizeApartSideEvidence.check_sound hLeft,
    StandardizeApartSideEvidence.check_sound hRight⟩

def sideEvidence (evidence : StandardizeApartEvidence σ) :
    Bool → StandardizeApartSideEvidence σ
  | false => evidence.left
  | true => evidence.right

def sideParent (left right : ParentClause σ) :
    Bool → ParentClause σ
  | false => left
  | true => right

end StandardizeApartEvidence

def standardizeApartCheck
    (left right : ParentClause σ)
    (evidence? : Option (StandardizeApartEvidence σ)) : Bool :=
  match evidence? with
  | none => true
  | some evidence =>
      evidence.check &&
        left.clause.eq evidence.left.original &&
        right.clause.eq evidence.right.original

namespace StandardizeApartEvidence

theorem check_sound_for_parents
    {left right : ParentClause σ}
    {evidence : StandardizeApartEvidence σ}
    (hCheck :
      standardizeApartCheck left right (some evidence) = true) :
    evidence.left.renamed =
        Clause.renameFreeVars evidence.left.offset left.clause ∧
      evidence.right.renamed =
        Clause.renameFreeVars evidence.right.offset right.clause := by
  simp only [standardizeApartCheck, StandardizeApartEvidence.check,
    StandardizeApartSideEvidence.check, Bool.and_eq_true] at hCheck
  rcases hCheck with
    ⟨⟨⟨hRenameLeft, hRenameRight⟩, hLeftCheck⟩, hRightCheck⟩
  have hLeftOriginal :
      evidence.left.original = left.clause :=
    (Clause.eq_sound left.clause evidence.left.original hLeftCheck).symm
  have hRightOriginal :
      evidence.right.original = right.clause :=
    (Clause.eq_sound right.clause evidence.right.original hRightCheck).symm
  exact ⟨by
      simpa [StandardizeApartSideEvidence.expected, hLeftOriginal] using
        StandardizeApartSideEvidence.check_sound hRenameLeft,
    by
      simpa [StandardizeApartSideEvidence.expected, hRightOriginal] using
        StandardizeApartSideEvidence.check_sound hRenameRight⟩

theorem check_sound_for_side
    {left right : ParentClause σ}
    {evidence : StandardizeApartEvidence σ} (side : Bool)
    (hCheck :
      standardizeApartCheck left right (some evidence) = true) :
    (sideEvidence evidence side).renamed =
      Clause.renameFreeVars (sideEvidence evidence side).offset
        (sideParent left right side).clause := by
  cases side
  · exact (check_sound_for_parents hCheck).1
  · exact (check_sound_for_parents hCheck).2

end StandardizeApartEvidence

/-! ## 局部规则数据 -/

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
  | .parentCdcl => "parent-CDCL"
  | .equality => "equality"
  | .congruence => "congruence"
  | .quantifier => "quantifier"
  | .theory => "theory"
  | .composite => "composite"

def ruleTags : LocalRuleFamily → Array Certificate.RuleTag
  | .parentCdcl =>
      #[.localRuleWitness, .parentCdclSkeleton, .firstOrderResolution]
  | .equality =>
      #[.localRuleWitness, .termEquality, .demodulation,
        .firstOrderSuperposition]
  | .congruence =>
      #[.localRuleWitness, .formulaCongruence, .argumentCongruence]
  | .quantifier =>
      #[.localRuleWitness, .quantifierCongruence]
  | .theory =>
      #[.localRuleWitness, .theoryFact]
  | .composite =>
      #[.localRuleWitness, .composite]

end LocalRuleFamily

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
  | .demodulation => "demodulation"
  | .positiveSuperposition => "positive superposition"
  | .negativeSuperposition => "negative superposition"

end RewriteKind

inductive TermContext (σ : Signature) where
  | hole
  | app (function : σ.FuncSymbol) (before : List (Term σ))
      (context : TermContext σ) (suffix : List (Term σ))

namespace TermContext

def fill : TermContext σ → Term σ → Term σ
  | .hole, term => term
  | .app function before context suffix, term =>
      .app function
        (before ++ [fill context term] ++ suffix)

end TermContext

inductive AtomContext (σ : Signature) where
  | rel (relation : σ.RelSymbol) (before : List (Term σ))
      (context : TermContext σ) (suffix : List (Term σ))
  | equalLeft (context : TermContext σ) (right : Term σ)
  | equalRight (left : Term σ) (context : TermContext σ)

namespace AtomContext

def isEquality : AtomContext σ → Bool
  | .rel .. => false
  | .equalLeft .. => true
  | .equalRight .. => true

def fill : AtomContext σ → Term σ → Formula σ
  | .rel relation before context suffix, term =>
      .rel relation
        (before ++ [context.fill term] ++ suffix)
  | .equalLeft context right, term =>
      .equal (context.fill term) right
  | .equalRight left context, term =>
      .equal left (context.fill term)

end AtomContext

def literalOfContext (polarity : Bool)
    (context : AtomContext σ) (term : Term σ) : Literal σ :=
  { polarity := polarity, atom := context.fill term }

def rewriteLiteralList
    (needle replacement : Literal σ) :
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
  Clause.applySubstitution evidence.substitution
    evidence.equalityBaseClause

def targetClause (evidence : RewriteEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution
    evidence.targetBaseClause

def equalityAtom (evidence : RewriteEvidence σ) : Formula σ :=
  if evidence.equalityReversed then
    .equal evidence.rhs evidence.lhs
  else
    .equal evidence.lhs evidence.rhs

def needle (evidence : RewriteEvidence σ) : Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.lhs

def replacement (evidence : RewriteEvidence σ) : Literal σ :=
  literalOfContext evidence.targetPolarity evidence.context evidence.rhs

def result (evidence : RewriteEvidence σ) : Clause σ where
  literals :=
    (Clause.filterOutList true evidence.equalityAtom
      evidence.equalityClause.literals.toList ++
      rewriteLiteralList evidence.needle evidence.replacement
        evidence.targetClause.literals.toList).toArray

def kindCheck (kind : RewriteKind)
    (evidence : RewriteEvidence σ) : Bool :=
  match kind with
  | .demodulation =>
      decide (evidence.equalityClause.literals.size = 1)
  | .positiveSuperposition =>
      evidence.targetPolarity
  | .negativeSuperposition =>
      !evidence.targetPolarity && evidence.context.isEquality

def check (kind : RewriteKind) (conclusion : Clause σ)
    (evidence : RewriteEvidence σ) : Bool :=
  standardizeApartCheck evidence.equality evidence.target
      evidence.standardizeApart? &&
    TermSubstitution.checkAdmissible evidence.substitution &&
    evidence.equalityClause.containsMatching true evidence.equalityAtom &&
    evidence.targetClause.containsLiteral evidence.needle &&
    kindCheck kind evidence &&
    conclusion.eq evidence.result

theorem check_admissible
    {kind : RewriteKind} {conclusion : Clause σ}
    {evidence : RewriteEvidence σ}
    (hCheck : check kind conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  simp only [check, Bool.and_eq_true] at hCheck
  rcases hCheck with
    ⟨⟨⟨⟨⟨_hStandardize, hAdmissible⟩, _hEquality⟩,
      _hTarget⟩, _hKind⟩, _hConclusion⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

theorem check_conclusion
    {kind : RewriteKind} {conclusion : Clause σ}
    {evidence : RewriteEvidence σ}
    (hCheck : check kind conclusion evidence = true) :
    conclusion = evidence.result := by
  simp only [check, Bool.and_eq_true] at hCheck
  rcases hCheck with
    ⟨⟨⟨⟨⟨_hStandardize, _hAdmissible⟩, _hEquality⟩,
      _hTarget⟩, _hKind⟩, hConclusion⟩
  exact Clause.eq_sound conclusion evidence.result hConclusion

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
  Clause.applySubstitution evidence.substitution
    evidence.leftBaseClause

def rightClause (evidence : ResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution
    evidence.rightBaseClause

def check (conclusion : Clause σ)
    (evidence : ResolutionEvidence σ) : Bool :=
  standardizeApartCheck evidence.left evidence.right
      evidence.standardizeApart? &&
    TermSubstitution.checkAdmissible evidence.substitution &&
    evidence.leftClause.containsMatching
      evidence.leftPolarity evidence.pivot &&
    evidence.rightClause.containsMatching
      (!evidence.leftPolarity) evidence.pivot &&
    conclusion.eq
      (Clause.resolutionResult evidence.leftPolarity evidence.pivot
        evidence.leftClause evidence.rightClause)

theorem check_admissible
    {conclusion : Clause σ} {evidence : ResolutionEvidence σ}
    (hCheck : check conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  simp only [check, Bool.and_eq_true] at hCheck
  rcases hCheck with
    ⟨⟨⟨⟨_hStandardize, hAdmissible⟩, _hLeft⟩,
      _hRight⟩, _hConclusion⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

theorem check_conclusion
    {conclusion : Clause σ} {evidence : ResolutionEvidence σ}
    (hCheck : check conclusion evidence = true) :
    conclusion =
      Clause.resolutionResult evidence.leftPolarity evidence.pivot
      evidence.leftClause evidence.rightClause := by
  simp only [check, Bool.and_eq_true] at hCheck
  rcases hCheck with
    ⟨⟨⟨⟨_hStandardize, _hAdmissible⟩, _hLeft⟩,
      _hRight⟩, hConclusion⟩
  exact Clause.eq_sound conclusion
    (Clause.resolutionResult evidence.leftPolarity evidence.pivot
      evidence.leftClause evidence.rightClause)
    hConclusion

end ResolutionEvidence

namespace FactoringEvidence

def parentClause (evidence : FactoringEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.parent.clause

def check (conclusion : Clause σ)
    (evidence : FactoringEvidence σ) : Bool :=
  TermSubstitution.checkAdmissible evidence.substitution &&
    evidence.parentClause.allLiteralsCovered conclusion &&
    conclusion.allLiteralsCovered evidence.parentClause &&
    decide (conclusion.literals.size <= evidence.parentClause.literals.size)

theorem check_admissible
    {conclusion : Clause σ} {evidence : FactoringEvidence σ}
    (hCheck : check conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  simp only [check, Bool.and_eq_true] at hCheck
  rcases hCheck with
    ⟨⟨⟨hAdmissible, _hForward⟩, _hBackward⟩, _hSize⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

theorem check_sound
    {conclusion : Clause σ} {evidence : FactoringEvidence σ}
    (hCheck : check conclusion evidence = true) :
    evidence.parentClause.allLiteralsCovered conclusion = true ∧
      conclusion.allLiteralsCovered evidence.parentClause = true ∧
      conclusion.literals.size <= evidence.parentClause.literals.size := by
  simp only [check, Bool.and_eq_true] at hCheck
  rcases hCheck with
    ⟨⟨⟨_hAdmissible, hForward⟩, hBackward⟩, hSize⟩
  exact ⟨hForward, hBackward, by simpa using hSize⟩

end FactoringEvidence

namespace EqualityResolutionEvidence

def parentClause (evidence : EqualityResolutionEvidence σ) : Clause σ :=
  Clause.applySubstitution evidence.substitution evidence.parent.clause

def check (conclusion : Clause σ)
    (evidence : EqualityResolutionEvidence σ) : Bool :=
  TermSubstitution.checkAdmissible evidence.substitution &&
    StructuralEq.term evidence.left evidence.right &&
    evidence.parentClause.containsMatching false
      (.equal evidence.left evidence.right) &&
    conclusion.eq
      (Clause.equalityResolutionResult evidence.left evidence.right
        evidence.parentClause)

theorem check_admissible
    {conclusion : Clause σ}
    {evidence : EqualityResolutionEvidence σ}
    (hCheck : check conclusion evidence = true) :
    TermSubstitution.BoundClosed evidence.substitution ∧
      TermSubstitution.WellSorted evidence.substitution := by
  simp only [check, Bool.and_eq_true] at hCheck
  rcases hCheck with
    ⟨⟨⟨hAdmissible, _hTerm⟩, _hParent⟩, _hConclusion⟩
  exact TermSubstitution.checkAdmissible_sound hAdmissible

theorem check_sound
    {conclusion : Clause σ}
    {evidence : EqualityResolutionEvidence σ}
    (hCheck : check conclusion evidence = true) :
    StructuralEq.term evidence.left evidence.right = true ∧
      evidence.parentClause.containsMatching false
        (.equal evidence.left evidence.right) = true ∧
      conclusion =
        Clause.equalityResolutionResult evidence.left evidence.right
          evidence.parentClause := by
  simp only [check, Bool.and_eq_true] at hCheck
  rcases hCheck with
    ⟨⟨⟨_hAdmissible, hTerm⟩, hParent⟩, hConclusion⟩
  exact ⟨hTerm, hParent,
    Clause.eq_sound conclusion
      (Clause.equalityResolutionResult evidence.left evidence.right
        evidence.parentClause)
      hConclusion⟩

end EqualityResolutionEvidence

end DAGCertificateSignature

end DAGCertificate
end Automation
end YesMetaZFC
