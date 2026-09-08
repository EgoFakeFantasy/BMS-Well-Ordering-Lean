import YesMetaZFC.Automation.DAGCertificate.IntrinsicReplay.Substitution

/-!
# compiled clause 的析取列表视图

本层把 raw 字面列表逐项编译为内在公式列表。成员对齐一经建立，因子化、归结与等式
归结只需处理有限列表成员关系，不再重复展开整个字句公式。
-/

namespace YesMetaZFC
namespace Automation
namespace DAGCertificate
namespace Compile

open _root_.YesMetaZFC.Logic
open _root_.YesMetaZFC.Logic.FirstOrder

universe x

variable {σ : Signature}

/-- 按 raw 顺序逐项编译字面公式。 -/
def literalList? [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    List (Literal σ) →
      Option (List (OpenFormula σ registry.context))
  | [] => some []
  | literal :: rest => do
      let formula ← formula? registry [] literal.toFormula
      let formulas ← literalList? registry rest
      pure (formula :: formulas)

/-- 非空 raw 字面列表成功编译后仍非空。 -/
theorem literalList?_ne_nil
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ)
    {literal : Literal σ} {rest : List (Literal σ)} {formulas}
    (hCompile : literalList? registry (literal :: rest) = some formulas) :
    formulas ≠ [] := by
  cases hLiteral : formula? registry [] literal.toFormula with
  | none =>
      simp [literalList?, hLiteral] at hCompile
  | some formula =>
      cases hRest : literalList? registry rest with
      | none =>
          simp [literalList?, hLiteral, hRest] at hCompile
      | some restFormulas =>
          simp [literalList?, hLiteral, hRest] at hCompile
          subst formulas
          simp

/-- 整体字句公式编译成功时，存在唯一顺序对齐的字面公式列表。 -/
theorem literalList?_exists_of_formula?
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    ∀ (literals : List (Literal σ))
      (source : OpenFormula σ registry.context),
      formula? registry []
          (Formula.disjunctionList (literals.map Literal.toFormula)) =
        some source →
      ∃ formulas,
        literalList? registry literals = some formulas ∧
          source = Logic.FirstOrder.Formula.disjunctionList formulas
  | [], source, hSource => by
      simp [Formula.disjunctionList, formula?] at hSource
      subst source
      exact ⟨[], rfl, rfl⟩
  | [literal], source, hSource => by
      cases hLiteral : formula? registry [] literal.toFormula with
      | none =>
          simp [Formula.disjunctionList, hLiteral] at hSource
      | some formula =>
          simp [Formula.disjunctionList, hLiteral] at hSource
          subst source
          exact ⟨[formula], by simp [literalList?, hLiteral], rfl⟩
  | literal :: next :: rest, source, hSource => by
      cases hLiteral : formula? registry [] literal.toFormula with
      | none =>
          simp [Formula.disjunctionList, formula?, hLiteral] at hSource
      | some formula =>
          cases hTail : formula? registry []
              (Formula.disjunctionList
                ((next :: rest).map Literal.toFormula)) with
          | none =>
              change formula? registry []
                (Formula.disjunctionList
                  (next.toFormula :: rest.map Literal.toFormula)) = none at hTail
              simp [Formula.disjunctionList, formula?, hLiteral, hTail] at hSource
          | some tailFormula =>
              change formula? registry []
                (Formula.disjunctionList
                  (next.toFormula :: rest.map Literal.toFormula)) =
                    some tailFormula at hTail
              simp [Formula.disjunctionList, formula?, hLiteral, hTail] at hSource
              subst source
              rcases literalList?_exists_of_formula? registry
                  (next :: rest) tailFormula hTail with
                ⟨tailFormulas, hCompileTail, hTailFormula⟩
              have hTailNonempty := literalList?_ne_nil registry hCompileTail
              cases tailFormulas with
              | nil => exact False.elim (hTailNonempty rfl)
              | cons nextFormula restFormulas =>
                  exact ⟨formula :: nextFormula :: restFormulas, by
                      rw [literalList?, hLiteral, hCompileTail]
                      rfl, by
                      simp [Logic.FirstOrder.Formula.disjunctionList,
                        hTailFormula]⟩

/-- compiled 公式成员可反查同位置 raw 字面。 -/
theorem literalList?_raw_of_mem
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    ∀ {literals formulas},
      literalList? registry literals = some formulas →
      ∀ {formula}, formula ∈ formulas →
        ∃ literal ∈ literals,
          formula? registry [] literal.toFormula = some formula
  | [], formulas, hCompile, formula, hMem => by
      simp [literalList?] at hCompile
      subst formulas
      simp at hMem
  | literal :: rest, formulas, hCompile, formula, hMem => by
      cases hLiteral : formula? registry [] literal.toFormula with
      | none =>
          simp [literalList?, hLiteral] at hCompile
      | some compiledLiteral =>
          cases hRest : literalList? registry rest with
          | none =>
              simp [literalList?, hLiteral, hRest] at hCompile
          | some compiledRest =>
              simp [literalList?, hLiteral, hRest] at hCompile
              subst formulas
              simp at hMem
              rcases hMem with hHead | hTail
              · subst formula
                exact ⟨literal, by simp, hLiteral⟩
              · rcases literalList?_raw_of_mem registry hRest hTail with
                  ⟨raw, hRawMem, hRawCompile⟩
                exact ⟨raw, by simp [hRawMem], hRawCompile⟩

/-- raw 字面成员可取得同位置 compiled 公式。 -/
theorem literalList?_compiled_of_mem
    [DecidableEq σ.SortSymbol]
    (registry : FreeRegistry σ) :
    ∀ {literals formulas},
      literalList? registry literals = some formulas →
      ∀ {literal}, literal ∈ literals →
        ∃ formula ∈ formulas,
          formula? registry [] literal.toFormula = some formula
  | [], formulas, hCompile, literal, hMem => by
      simp at hMem
  | head :: rest, formulas, hCompile, literal, hMem => by
      cases hHead : formula? registry [] head.toFormula with
      | none =>
          simp [literalList?, hHead] at hCompile
      | some compiledHead =>
          cases hRest : literalList? registry rest with
          | none =>
              simp [literalList?, hHead, hRest] at hCompile
          | some compiledRest =>
              simp [literalList?, hHead, hRest] at hCompile
              subst formulas
              simp at hMem
              rcases hMem with hLiteral | hTail
              · subst literal
                exact ⟨compiledHead, by simp, hHead⟩
              · rcases literalList?_compiled_of_mem registry hRest hTail with
                  ⟨formula, hFormulaMem, hFormulaCompile⟩
                exact ⟨formula, by simp [hFormulaMem], hFormulaCompile⟩

/-- 单个 compiled clause 的顺序对齐析取列表。 -/
theorem CompiledClause.literal_view
    [DecidableEq σ.SortSymbol]
    {registry : FreeRegistry σ} (compiled : CompiledClause registry) :
    ∃ formulas,
      literalList? registry compiled.raw.literals.toList = some formulas ∧
        compiled.formula = Logic.FirstOrder.Formula.disjunctionList formulas := by
  exact literalList?_exists_of_formula? registry
    compiled.raw.literals.toList compiled.formula compiled.compiled

/-- raw 字面覆盖把源 compiled clause 的全称真实性传给目标。 -/
theorem CompiledClause.trueIn_of_allLiteralsCovered
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    (M : Structure.{0, 0, 0, x} σ)
    {registry : FreeRegistry σ}
    (source target : CompiledClause registry)
    (hCovered : source.raw.allLiteralsCovered target.raw = true)
    (hSource : source.TrueIn M) :
    target.TrueIn M := by
  rcases source.literal_view with
    ⟨sourceFormulas, hSourceCompile, hSourceFormula⟩
  rcases target.literal_view with
    ⟨targetFormulas, hTargetCompile, hTargetFormula⟩
  apply (forallFree_trueIn_iff target.formula).mpr
  intro assignment
  rw [hTargetFormula,
    Logic.FirstOrder.Formula.satisfies_disjunctionList_iff]
  have hValid := (forallFree_trueIn_iff source.formula).mp hSource
  have hSourceSat := hValid assignment
  rw [hSourceFormula,
    Logic.FirstOrder.Formula.satisfies_disjunctionList_iff] at hSourceSat
  rcases hSourceSat with ⟨sourceFormula, hSourceMem, hFormulaSat⟩
  rcases literalList?_raw_of_mem registry hSourceCompile hSourceMem with
    ⟨literal, hLiteralSource, hLiteralCompile⟩
  have hLiteralTarget : literal ∈ target.raw.literals.toList :=
    Clause.allLiteralsCovered_sound hCovered hLiteralSource
  rcases literalList?_compiled_of_mem registry hTargetCompile
      hLiteralTarget with
    ⟨targetFormula, hTargetMem, hTargetLiteralCompile⟩
  have hFormulaEq : targetFormula = sourceFormula :=
    Option.some.inj (hTargetLiteralCompile.symm.trans hLiteralCompile)
  exact ⟨targetFormula, hTargetMem, hFormulaEq ▸ hFormulaSat⟩

/-- 若被过滤字面在每个赋值下均为假，则字句过滤保持全称真实性。 -/
theorem CompiledClause.trueIn_filterOut
    [DecidableEq σ.SortSymbol] [DecidableEq σ.FuncSymbol]
    [DecidableEq σ.RelSymbol]
    (M : Structure.{0, 0, 0, x} σ)
    {registry : FreeRegistry σ}
    (source target : CompiledClause registry)
    (polarity : Bool) (atom : Formula σ)
    (hRaw : target.raw = source.raw.filterOut polarity atom)
    (hRemovedFalse :
      ∀ {literal formula},
        literal ∈ source.raw.literals.toList →
        literal.matchesAtom polarity atom = true →
        formula? registry [] literal.toFormula = some formula →
        ∀ assignment : Assignment M registry.context,
          ¬ formula.satisfies (openEnv assignment))
    (hSource : source.TrueIn M) :
    target.TrueIn M := by
  rcases source.literal_view with
    ⟨sourceFormulas, hSourceCompile, hSourceFormula⟩
  rcases target.literal_view with
    ⟨targetFormulas, hTargetCompile, hTargetFormula⟩
  apply (forallFree_trueIn_iff target.formula).mpr
  intro assignment
  rw [hTargetFormula,
    Logic.FirstOrder.Formula.satisfies_disjunctionList_iff]
  have hValid := (forallFree_trueIn_iff source.formula).mp hSource
  have hSourceSat := hValid assignment
  rw [hSourceFormula,
    Logic.FirstOrder.Formula.satisfies_disjunctionList_iff] at hSourceSat
  rcases hSourceSat with ⟨sourceFormula, hSourceMem, hFormulaSat⟩
  rcases literalList?_raw_of_mem registry hSourceCompile hSourceMem with
    ⟨literal, hLiteralSource, hLiteralCompile⟩
  by_cases hMatches : literal.matchesAtom polarity atom = true
  · exact False.elim <|
      (hRemovedFalse hLiteralSource hMatches hLiteralCompile assignment)
        hFormulaSat
  · have hMatchesFalse : literal.matchesAtom polarity atom = false := by
      cases hValue : literal.matchesAtom polarity atom <;> simp_all
    have hFilteredMem :
        literal ∈ Clause.filterOutList polarity atom
          source.raw.literals.toList :=
      Clause.mem_filterOutList_of_mem_of_not_matches
        polarity atom hLiteralSource hMatchesFalse
    have hLiteralTarget : literal ∈ target.raw.literals.toList := by
      rw [hRaw]
      simpa [Clause.filterOut] using hFilteredMem
    rcases literalList?_compiled_of_mem registry hTargetCompile
        hLiteralTarget with
      ⟨targetFormula, hTargetMem, hTargetLiteralCompile⟩
    have hFormulaEq : targetFormula = sourceFormula :=
      Option.some.inj (hTargetLiteralCompile.symm.trans hLiteralCompile)
    exact ⟨targetFormula, hTargetMem, hFormulaEq ▸ hFormulaSat⟩

end Compile
end DAGCertificate
end Automation
end YesMetaZFC
