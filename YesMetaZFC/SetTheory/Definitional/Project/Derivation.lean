import YesMetaZFC.SetTheory.Language
import YesMetaZFC.SetTheory.Theory
import YesMetaZFC.Logic.Theory
import YesMetaZFC.Logic.FirstOrder.Derivation.Consistency
import YesMetaZFC.Logic.FirstOrder.Hilbert.Adequacy

/-!
# Project 集合论的裸一阶推导

本模块把 `Definitional.Project` 公式完全翻译到纯集合论签名 `ℒ`：

* 项只保留 bound/free 变量；
* 隶属原子映射到 `ℒ` 的唯一关系符号；
* 外延等同与子集原子直接展开为纯隶属公式；
* 理论像进入公共 `Derives` 与 `HilbertDerives` 证明核。

因此这里定义的 `Project.Derives`、`Project.HilbertDerives` 与
`Project.Consistent` 真正作用于原始集合论语言，而不是 FormalSystem 的定义扩张
签名。后续定义扩张保守性只需把支持理论证明消去到本模块的理论像。
-/

namespace YesMetaZFC
namespace SetTheory
namespace Definitional
namespace Project

open Logic FirstOrder

universe u

set_option autoImplicit false

/-- Project 项在纯集合论一阶签名中的像。 -/
def fo_term {depth : Nat} :
    Term depth → FirstOrder.Term ℒ
  | .bound entry =>
      .var (.bvar SetSort.set entry.val)
  | .free id =>
      .var (.fvar SetSort.set id)

/-- 深度索引在纯集合论签名中对应的单 sort scope。 -/
def fo_scope (depth : Nat) : Scope ℒ :=
  fun _ => depth

@[simp]
theorem fo_scope_zero :
    fo_scope 0 = (Scope.empty : Scope ℒ) := by
  funext sort
  cases sort
  rfl

@[simp]
theorem fo_scope_push (depth : Nat) :
    Scope.push (fo_scope depth) SetSort.set =
      fo_scope (depth + 1) := by
  funext sort
  cases sort
  simp [fo_scope, Scope.push]

/-- 纯集合论中的隶属原子。 -/
def fo_mem (left right : FirstOrder.Term ℒ) :
    FirstOrder.Formula ℒ :=
  .rel RelationSymbol.membership [left, right]

/--
Project 公式到纯集合论一阶公式。

定义原子在翻译时立即消去。外延等同在外延模型上翻译为原生一阶等号；这一步
保留了裸 ZFC 的外延公理，避免把外延性误压成纯成员等价。
-/
def fo_formula :
    {availableStage depth : Nat} →
      Formula availableStage depth →
        FirstOrder.Formula ℒ
  | _, _, .falsum =>
      .falsum
  | _, _, .truth =>
      .truth
  | _, _, .mem left right =>
      fo_mem (fo_term left) (fo_term right)
  | _, depth, .atom .extensionalEq _ arguments =>
      .equal
        (fo_term (arguments 0))
        (fo_term (arguments 1))
  | _, depth, .atom .subset _ arguments =>
      .forallE SetSort.set <|
        .imp
          (fo_mem
            (fo_term (Term.newest (depth := depth)))
            (fo_term (arguments 0).weaken))
          (fo_mem
            (fo_term (Term.newest (depth := depth)))
            (fo_term (arguments 1).weaken))
  | _, _, .neg body =>
      .neg (fo_formula body)
  | _, _, .conj left right =>
      .conj (fo_formula left) (fo_formula right)
  | _, _, .disj left right =>
      .disj (fo_formula left) (fo_formula right)
  | _, _, .imp left right =>
      .imp (fo_formula left) (fo_formula right)
  | _, _, .iff left right =>
      .iff (fo_formula left) (fo_formula right)
  | _, _, .forallE body =>
      .forallE SetSort.set (fo_formula body)
  | _, _, .existsE body =>
      .existsE SetSort.set (fo_formula body)

/-- 翻译后的任意 Project 项具有集合 sort。 -/
theorem fo_term_well_sorted
    {depth : Nat} (term : Term depth) :
    TermWellSorted (fo_term term) SetSort.set := by
  cases term with
  | bound entry =>
      exact TermWellSorted.bvar
        (σ := ℒ) SetSort.set entry.val
  | free id =>
      exact TermWellSorted.fvar
        (σ := ℒ) SetSort.set id

/-- Project 项的深度索引给出翻译后项的精确 scope。 -/
theorem fo_term_scoped
    {depth : Nat} (term : Term depth) :
    TermScoped (fo_scope depth) (fo_term term) := by
  cases term with
  | bound entry =>
      exact TermScoped.bvar (σ := ℒ) <| by
        simp [fo_scope, entry.isLt]
  | free id =>
      exact TermScoped.fvar
        (σ := ℒ) SetSort.set id

private theorem fo_pair_well_sorted
    (left right : FirstOrder.Term ℒ)
    (hLeft : TermWellSorted left SetSort.set)
    (hRight : TermWellSorted right SetSort.set) :
    ArgsWellSorted [left, right]
      [SetSort.set, SetSort.set] :=
  .cons hLeft (.cons hRight .nil)

private theorem fo_pair_scoped
    {scope : Scope ℒ}
    (left right : FirstOrder.Term ℒ)
    (hLeft : TermScoped scope left)
    (hRight : TermScoped scope right) :
    ∀ term, term ∈ [left, right] →
      TermScoped scope term := by
  intro term hTerm
  rcases List.mem_cons.mp hTerm with rfl | hTerm
  · exact hLeft
  · have : term = right := List.mem_singleton.mp hTerm
    subst term
    exact hRight

private theorem fo_mem_well_formed
    (left right : FirstOrder.Term ℒ)
    (hLeft : TermWellSorted left SetSort.set)
    (hRight : TermWellSorted right SetSort.set) :
    FormulaWellFormed (fo_mem left right) := by
  apply FormulaWellFormed.rel
  simpa [PureSetLanguage, signature] using
    fo_pair_well_sorted left right hLeft hRight

private theorem fo_mem_scoped
    {scope : Scope ℒ}
    (left right : FirstOrder.Term ℒ)
    (hLeft : TermScoped scope left)
    (hRight : TermScoped scope right) :
    FormulaScoped scope (fo_mem left right) := by
  exact FormulaScoped.rel RelationSymbol.membership
    [left, right]
    (fo_pair_scoped left right hLeft hRight)

/-- 纯翻译保持公式的 sort/arity 良构性。 -/
theorem fo_formula_well_formed :
    {availableStage depth : Nat} →
      (formula : Formula availableStage depth) →
        FormulaWellFormed (fo_formula formula)
  | _, _, .falsum =>
      by simpa [fo_formula] using
        (FormulaWellFormed.falsum :
          FormulaWellFormed
            (FirstOrder.Formula.falsum : FirstOrder.Formula ℒ))
  | _, _, .truth =>
      by simpa [fo_formula] using
        (FormulaWellFormed.truth :
          FormulaWellFormed
            (FirstOrder.Formula.truth : FirstOrder.Formula ℒ))
  | _, _, .mem left right =>
      by
        simpa [fo_formula] using
          fo_mem_well_formed
            (fo_term left) (fo_term right)
            (fo_term_well_sorted left)
            (fo_term_well_sorted right)
  | _, _, .atom .extensionalEq _ arguments => by
      rw [fo_formula]
      exact FormulaWellFormed.equal
        (fo_term_well_sorted (arguments 0))
        (fo_term_well_sorted (arguments 1))
  | _, _, .atom .subset _ arguments => by
      rw [fo_formula]
      apply FormulaWellFormed.forallE
      apply FormulaWellFormed.imp
      · exact fo_mem_well_formed
          (fo_term Term.newest)
          (fo_term (arguments 0).weaken)
          (fo_term_well_sorted Term.newest)
          (fo_term_well_sorted (arguments 0).weaken)
      · exact fo_mem_well_formed
          (fo_term Term.newest)
          (fo_term (arguments 1).weaken)
          (fo_term_well_sorted Term.newest)
          (fo_term_well_sorted (arguments 1).weaken)
  | _, _, .neg body =>
      by simpa [fo_formula] using
        FormulaWellFormed.neg
          (fo_formula_well_formed body)
  | _, _, .conj left right =>
      by simpa [fo_formula] using
        FormulaWellFormed.conj
          (fo_formula_well_formed left)
          (fo_formula_well_formed right)
  | _, _, .disj left right =>
      by simpa [fo_formula] using
        FormulaWellFormed.disj
          (fo_formula_well_formed left)
          (fo_formula_well_formed right)
  | _, _, .imp left right =>
      by simpa [fo_formula] using
        FormulaWellFormed.imp
          (fo_formula_well_formed left)
          (fo_formula_well_formed right)
  | _, _, .iff left right =>
      by simpa [fo_formula] using
        FormulaWellFormed.iff
          (fo_formula_well_formed left)
          (fo_formula_well_formed right)
  | _, _, .forallE body =>
      by simpa [fo_formula] using
        FormulaWellFormed.forallE SetSort.set
          (fo_formula_well_formed body)
  | _, _, .existsE body =>
      by simpa [fo_formula] using
        FormulaWellFormed.existsE SetSort.set
          (fo_formula_well_formed body)

/-- 纯翻译保持公式的精确 bound scope。 -/
theorem fo_formula_scoped :
    {availableStage depth : Nat} →
      (formula : Formula availableStage depth) →
        FormulaScoped (fo_scope depth)
          (fo_formula formula)
  | _, _, .falsum =>
      by simpa [fo_formula] using
        (FormulaScoped.falsum :
          FormulaScoped (fo_scope _)
            (FirstOrder.Formula.falsum :
              FirstOrder.Formula ℒ))
  | _, _, .truth =>
      by simpa [fo_formula] using
        (FormulaScoped.truth :
          FormulaScoped (fo_scope _)
            (FirstOrder.Formula.truth :
              FirstOrder.Formula ℒ))
  | _, _, .mem left right =>
      by
        simpa [fo_formula] using
          fo_mem_scoped
            (fo_term left) (fo_term right)
            (fo_term_scoped left)
            (fo_term_scoped right)
  | _, _, .atom .extensionalEq _ arguments => by
      rw [fo_formula]
      exact FormulaScoped.equal
        (fo_term_scoped (arguments 0))
        (fo_term_scoped (arguments 1))
  | _, _, .atom .subset _ arguments => by
      rw [fo_formula]
      apply FormulaScoped.forallE
      rw [fo_scope_push]
      apply FormulaScoped.imp
      · exact fo_mem_scoped
          (fo_term Term.newest)
          (fo_term (arguments 0).weaken)
          (fo_term_scoped Term.newest)
          (fo_term_scoped (arguments 0).weaken)
      · exact fo_mem_scoped
          (fo_term Term.newest)
          (fo_term (arguments 1).weaken)
          (fo_term_scoped Term.newest)
          (fo_term_scoped (arguments 1).weaken)
  | _, _, .neg body =>
      by simpa [fo_formula] using
        FormulaScoped.neg (fo_formula_scoped body)
  | _, _, .conj left right =>
      by simpa [fo_formula] using
        FormulaScoped.conj
          (fo_formula_scoped left)
          (fo_formula_scoped right)
  | _, _, .disj left right =>
      by simpa [fo_formula] using
        FormulaScoped.disj
          (fo_formula_scoped left)
          (fo_formula_scoped right)
  | _, _, .imp left right =>
      by simpa [fo_formula] using
        FormulaScoped.imp
          (fo_formula_scoped left)
          (fo_formula_scoped right)
  | _, _, .iff left right =>
      by simpa [fo_formula] using
        FormulaScoped.iff
          (fo_formula_scoped left)
          (fo_formula_scoped right)
  | _, _, .forallE body => by
      rw [fo_formula]
      apply FormulaScoped.forallE
      simpa only [fo_scope_push] using
        fo_formula_scoped body
  | _, _, .existsE body => by
      rw [fo_formula]
      apply FormulaScoped.existsE
      simpa only [fo_scope_push] using
        fo_formula_scoped body

/-- 自由闭合的 Project 项翻译后没有自由变量。 -/
theorem fo_term_free_support_nil
    {depth : Nat} (term : Term depth)
    (hClosed : term.freeSupport = []) :
    FirstOrder.Term.freeSupport (fo_term term) = [] := by
  cases term <;>
    simp_all [fo_term, FirstOrder.Term.freeSupport]

/-- 自由闭合的 Project 公式翻译后仍没有自由变量。 -/
theorem fo_formula_free_support_nil :
    {availableStage depth : Nat} →
      (formula : Formula availableStage depth) →
      Formula.FreeClosed formula →
        FirstOrder.Formula.freeSupport
          (fo_formula formula) = []
  | _, _, .falsum, _ => by
      simp [fo_formula, FirstOrder.Formula.freeSupport]
  | _, _, .truth, _ => by
      simp [fo_formula, FirstOrder.Formula.freeSupport]
  | _, _, .mem left right, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      simp [fo_formula, fo_mem,
        FirstOrder.Formula.freeSupport,
        FirstOrder.Term.freeSupportList,
        fo_term_free_support_nil left hClosed.1,
        fo_term_free_support_nil right hClosed.2]
  | _, _, .atom symbol hStage arguments, hClosed => by
      simp only [Formula.FreeClosed,
        TermVector.FreeClosed] at hClosed
      cases symbol with
      | extensionalEq =>
          simp [fo_formula, FirstOrder.Formula.freeSupport,
            fo_term_free_support_nil
              (arguments 0)
              (by simpa using hClosed 0),
            fo_term_free_support_nil
              (arguments 1)
              (by simpa using hClosed 1)]
      | subset =>
          simp [fo_formula, fo_mem,
            FirstOrder.Formula.freeSupport,
            FirstOrder.Term.freeSupportList,
            fo_term_free_support_nil
              (Term.newest (depth := _)) rfl,
            fo_term_free_support_nil
              (arguments 0).weaken
              (by simpa using hClosed 0),
            fo_term_free_support_nil
              (arguments 1).weaken
              (by simpa using hClosed 1)]
  | _, _, .neg body, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      simpa [fo_formula,
        FirstOrder.Formula.freeSupport] using
        fo_formula_free_support_nil body hClosed
  | _, _, .conj left right, hClosed
  | _, _, .disj left right, hClosed
  | _, _, .imp left right, hClosed
  | _, _, .iff left right, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      simp [fo_formula,
        FirstOrder.Formula.freeSupport,
        fo_formula_free_support_nil left hClosed.1,
        fo_formula_free_support_nil right hClosed.2]
  | _, _, .forallE body, hClosed
  | _, _, .existsE body, hClosed => by
      simp only [Formula.FreeClosed] at hClosed
      simpa [fo_formula,
        FirstOrder.Formula.freeSupport] using
        fo_formula_free_support_nil body hClosed

/-- Project 句子的纯一阶公式像。 -/
def fo_sentence (sentence : Sentence) :
    FirstOrder.Formula ℒ :=
  fo_formula sentence.formula

/-- 每个 Project 句子都翻译为公共证明核中的闭句。 -/
theorem fo_sentence_sentence (sentence : Sentence) :
    FirstOrder.Formula.Sentence
      (fo_sentence sentence) := by
  constructor
  · constructor
    · exact fo_formula_well_formed sentence.formula
    · simpa only [fo_scope_zero] using
        fo_formula_scoped sentence.formula
  · exact fo_formula_free_support_nil
      sentence.formula sentence.freeClosed

/-- Project 理论在纯集合论一阶签名中的公式像。 -/
def fo_theory (T : Theory) :
    FirstOrder.Theory ℒ :=
  fun formula =>
    ∃ sentence,
      T sentence ∧
        formula = fo_sentence sentence

/-- 裸 Project 理论像只含 admissible 闭句。 -/
theorem fo_theory_sentence
    {T : Theory} {formula : FirstOrder.Formula ℒ}
    (hFormula : fo_theory T formula) :
    FirstOrder.Formula.Sentence formula := by
  rcases hFormula with
    ⟨sentence, _, rfl⟩
  exact fo_sentence_sentence sentence

/-- 裸 Project 理论像满足公共证明核的理论合法性边界。 -/
theorem fo_theory_admissible
    (T : Theory) :
    FirstOrder.Theory.Admissible (fo_theory T) := by
  intro formula hFormula
  exact (fo_theory_sentence hFormula).1

/-- 原始 Project 理论中的自然演绎可证性。 -/
def Derives (T : Theory) (sentence : Sentence) : Prop :=
  FirstOrder.Derives
    (fo_theory T) []
    (fo_sentence sentence)

/-- 原始 Project 理论中的 Hilbert 可证性。 -/
def HilbertDerives
    (T : Theory) (sentence : Sentence) : Prop :=
  FirstOrder.HilbertDerives
    (fo_theory T)
    (fo_sentence sentence)

/-- 原始 Project 理论的一致性。 -/
def Consistent (T : Theory) : Prop :=
  FirstOrder.Derives.Consistent
    (fo_theory T) []

/-- Project 的 Hilbert 证明可直接回放为裸自然演绎证明。 -/
theorem derives_of_hilbert
    {T : Theory} {sentence : Sentence}
    (hDerives : HilbertDerives T sentence) :
    Derives T sentence :=
  hDerives.to_derives

end Project
end Definitional
end SetTheory
end YesMetaZFC
