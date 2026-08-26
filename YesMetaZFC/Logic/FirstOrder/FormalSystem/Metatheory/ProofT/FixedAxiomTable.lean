import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NumeralArithmetic
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy

/-!
# `ProofT` 的固定公理表

固定公理表只保存“证书自然数—闭合公式码项”的有限对应。接受条件、成员回放、
逐行拒绝、证书号拒绝和公式内容拒绝均在此处一次性证明；理论扩张只需追加新表，
不再复制一条按表长递归的 rejection 链。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace ProofT

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/-- 可被对象 verifier 消费的有限固定公理表。 -/
structure FixedAxiomTable where
  rows : List (Nat × SetTerm)
  row_admissible :
    ∀ row, row ∈ rows →
      Term.Admissible row.2 SetSort.set

namespace FixedAxiomTable

/-- 固定表的逐项有限析取。 -/
def condition_rows
    (rows : List (Nat × SetTerm))
    (formula certificate : SetTerm) : SetFormula :=
  rows.foldr
    (fun row rest =>
      (((certificate ≐ₘ numₘ(row.1)) ∧ₘ
          (formula ≐ₘ row.2)) ∨ₘ rest))
    Formula.falsum

/-- 一张固定公理表的对象 verifier 条件。 -/
def condition
    (A : FixedAxiomTable)
    (formula certificate : SetTerm) : SetFormula :=
  condition_rows A.rows formula certificate

/-- 空固定表。 -/
def empty : FixedAxiomTable where
  rows := []
  row_admissible := by simp

/-- 单条固定公理。 -/
def singleton
    (certificate : Nat)
    (formula : SetTerm)
    (hFormula : Term.Admissible formula SetSort.set) :
    FixedAxiomTable where
  rows := [(certificate, formula)]
  row_admissible := by
    intro row hRow
    simp only [List.mem_singleton] at hRow
    subst row
    exact hFormula

/-- 有限扩张通过追加表实现，所有通用接受与拒绝定理自动复用。 -/
def append
    (A B : FixedAxiomTable) :
    FixedAxiomTable where
  rows := A.rows ++ B.rows
  row_admissible := by
    intro row hRow
    rcases List.mem_append.mp hRow with hRow | hRow
    · exact A.row_admissible row hRow
    · exact B.row_admissible row hRow

theorem condition_rows_admissible
    (rows : List (Nat × SetTerm))
    (formula certificate : SetTerm)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hRows :
      ∀ row, row ∈ rows →
        Term.Admissible row.2 SetSort.set) :
    Formula.Admissible
      (condition_rows rows formula certificate) := by
  induction rows with
  | nil =>
      simpa [condition_rows] using
        (Formula.Admissible.falsum :
          Formula.Admissible (Formula.falsum : SetFormula))
  | cons row rows ih =>
      have hTail :=
        ih (fun item hItem =>
          hRows item (by simp [hItem]))
      simpa [condition_rows] using
        Formula.Admissible.disj
          (Formula.Admissible.conj
            (Formula.Admissible.equal hCertificate
              (finite_numeral_term_admissible row.1))
            (Formula.Admissible.equal hFormula
              (hRows row (by simp))))
          hTail

theorem condition_admissible
    (A : FixedAxiomTable)
    (formula certificate : SetTerm)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set) :
    Formula.Admissible
      (A.condition formula certificate) :=
  condition_rows_admissible
    A.rows formula certificate hFormula hCertificate
    A.row_admissible

/-- 固定公理表条件不含对象量词，因而是正式的 `Delta0` 公式。 -/
theorem condition_rows_delta0
    (rows : List (Nat × SetTerm))
    (formula certificate : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (condition_rows rows formula certificate) := by
  induction rows with
  | nil =>
      simpa [condition_rows] using
        (Formula.IsDelta0.falsum :
          Formula.IsDelta0 set_levy_bound
            (Formula.falsum : SetFormula))
  | cons row rows ih =>
      simpa [condition_rows] using
        Formula.IsDelta0.disj
          (Formula.IsDelta0.conj
            (Formula.IsDelta0.equal certificate
              (numₘ(row.1)))
            (Formula.IsDelta0.equal formula row.2))
          ih

/-- 固定公理表 verifier 的正式 `Delta0` 分类。 -/
theorem condition_delta0
    (A : FixedAxiomTable)
    (formula certificate : SetTerm) :
    Formula.IsDelta0 set_levy_bound
      (A.condition formula certificate) :=
  condition_rows_delta0 A.rows formula certificate

/-- 固定公理表直接给出一个 `Delta0` proof graph。 -/
def proof_graph
    (A : FixedAxiomTable) : Delta0ProofGraph where
  condition := A.condition
  delta0 := A.condition_delta0

/-- 固定公理表条件同时可作为 `Sigma1` 公式使用。 -/
theorem condition_sigma1
    (A : FixedAxiomTable)
    (formula certificate : SetTerm) :
    Formula.IsSigma1 set_levy_bound
      (A.condition formula certificate) :=
  (A.condition_delta0 formula certificate).to_sigma1

/-- 固定公理表条件同时可作为 `Pi1` 公式使用。 -/
theorem condition_pi1
    (A : FixedAxiomTable)
    (formula certificate : SetTerm) :
    Formula.IsPi1 set_levy_bound
      (A.condition formula certificate) :=
  (A.condition_delta0 formula certificate).to_pi1

@[formula_check]
theorem condition_check
    (A : FixedAxiomTable)
    (formula certificate : SetTerm)
    (hFormula : Term.CheckCertificate formula SetSort.set)
    (hCertificate : Term.CheckCertificate certificate SetSort.set) :
    Formula.CheckCertificate
      (A.condition formula certificate) :=
  Formula.check_certificate_of_admissible
    (A.condition_admissible formula certificate
      hFormula.admissible hCertificate.admissible)

/-- 表中任意一行都满足同一张表的对象 verifier 条件。 -/
theorem condition_rows_of_mem
    {T : SetTheory}
    {rows : List (Nat × SetTerm)}
    (hRows :
      ∀ row, row ∈ rows →
        Term.Admissible row.2 SetSort.set)
    {row : Nat × SetTerm}
    (hRow : row ∈ rows) :
    Derives T [] (
      condition_rows rows row.2 (numₘ(row.1))) := by
  induction rows generalizing row with
  | nil =>
      simp at hRow
  | cons head tail ih =>
      have hHead :
          Term.Admissible head.2 SetSort.set :=
        hRows head (by simp)
      have hTail :
          ∀ item, item ∈ tail →
            Term.Admissible item.2 SetSort.set := by
        intro item hItem
        exact hRows item (by simp [hItem])
      simp only [List.mem_cons] at hRow
      rcases hRow with hRow | hRow
      · subst row
        have hHeadCondition :
            Derives T [] (
              (numₘ(head.1) ≐ₘ numₘ(head.1)) ∧ₘ
                (head.2 ≐ₘ head.2)) :=
          FirstOrder.Derives.conjIntro
            (FirstOrder.Derives.eq_refl_m
              (T := T) (Γ := [])
              (sort := SetSort.set) (numₘ(head.1)))
            (FirstOrder.Derives.eq_refl_m
              (T := T) (Γ := [])
              (sort := SetSort.set) head.2)
        simpa [condition_rows] using
          FirstOrder.Derives.disjIntroLeft
            (hRightCheck :=
              Formula.check_admissible_complete
                (condition_rows_admissible
                  tail head.2 (numₘ(head.1)) hHead
                  (finite_numeral_term_admissible head.1)
                  hTail))
            hHeadCondition
      · have hHeadCondition :
            Formula.Admissible
              ((numₘ(row.1) ≐ₘ numₘ(head.1)) ∧ₘ
                (row.2 ≐ₘ head.2)) :=
          Formula.Admissible.conj
            (Formula.Admissible.equal
              (finite_numeral_term_admissible row.1)
              (finite_numeral_term_admissible head.1))
            (Formula.Admissible.equal
              (hRows row (by simp [hRow])) hHead)
        simpa [condition_rows] using
          FirstOrder.Derives.disjIntroRight
            (hLeftCheck :=
              Formula.check_admissible_complete hHeadCondition)
            (ih hTail hRow)

theorem condition_of_mem
    {T : SetTheory}
    (A : FixedAxiomTable)
    {row : Nat × SetTerm}
    (hRow : row ∈ A.rows) :
    Derives T [] (
      A.condition row.2 (numₘ(row.1))) :=
  condition_rows_of_mem A.row_admissible hRow

/-- 逐行排除全部分支即可否定整张有限表。 -/
theorem condition_rows_neg
    {T : SetTheory}
    (rows : List (Nat × SetTerm))
    (formula certificate : SetTerm)
    (hFormula : Term.Admissible formula SetSort.set)
    (hCertificate : Term.Admissible certificate SetSort.set)
    (hRows :
      ∀ row, row ∈ rows →
        Term.Admissible row.2 SetSort.set)
    (hReject :
      ∀ row, row ∈ rows →
        Derives T [] (
          ¬ₘ ((certificate ≐ₘ numₘ(row.1)) ∧ₘ
            (formula ≐ₘ row.2)))) :
    Derives T [] (
      ¬ₘ condition_rows rows formula certificate) := by
  induction rows with
  | nil =>
      nd_apply FirstOrder.Derives.negIntro
        (T := T) (Γ := ([] : Context signature))
        (body := condition_rows [] formula certificate)
      exact FirstOrder.Derives.assumption (by
        simp [condition_rows])
  | cons row rows ih =>
      let head : SetFormula :=
        (certificate ≐ₘ numₘ(row.1)) ∧ₘ
          (formula ≐ₘ row.2)
      let tail : SetFormula :=
        condition_rows rows formula certificate
      let body : SetFormula := head ∨ₘ tail
      have hTailRows :
          ∀ item, item ∈ rows →
            Term.Admissible item.2 SetSort.set := by
        intro item hItem
        exact hRows item (by simp [hItem])
      have hHeadNeg : Derives T [] (¬ₘ head) := by
        simpa [head] using hReject row (by simp)
      have hTailNeg : Derives T [] (¬ₘ tail) := by
        simpa [tail] using
          ih hTailRows
            (fun item hItem =>
              hReject item (by simp [hItem]))
      have hBody : Formula.Admissible body := by
        simpa [body, head, tail, condition_rows] using
          condition_rows_admissible
            (row :: rows) formula certificate
            hFormula hCertificate hRows
      nd_apply FirstOrder.Derives.negIntro
        (T := T) (Γ := ([] : Context signature))
        (body := body)
        (hBodyCheck :=
          Formula.check_admissible_complete hBody)
      let Γ : Context signature := [body]
      have hBodyAt : Γ ⊢ₘ[T] body :=
        FirstOrder.Derives.assumption (by simp [Γ])
      apply FirstOrder.Derives.disjElim hBodyAt
      · exact FirstOrder.Derives.negElim
          (FirstOrder.Derives.assumption
            (Γ := head :: Γ) (by simp))
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := head :: Γ) (by simp) hHeadNeg)
      · exact FirstOrder.Derives.negElim
          (FirstOrder.Derives.assumption
            (Γ := tail :: Γ) (by simp))
          (FirstOrder.Derives.context_weaken
            (Γ := []) (Δ := tail :: Γ) (by simp) hTailNeg)

/-- 不同于全部行号的标准证书码被固定表统一拒绝。 -/
theorem condition_rows_neg_of_certificate_ne
    {T : SetTheory}
    (N : NumeralArithmetic T)
    (rows : List (Nat × SetTerm))
    (formula : SetTerm)
    (certificate : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hRows :
      ∀ row, row ∈ rows →
        Term.Admissible row.2 SetSort.set)
    (hInvalid :
      ∀ row, row ∈ rows → certificate ≠ row.1) :
    Derives T [] (
      ¬ₘ condition_rows
        rows formula (numₘ(certificate))) := by
  apply condition_rows_neg
    rows formula (numₘ(certificate))
    hFormula (finite_numeral_term_admissible certificate)
    hRows
  intro row hRow
  let body : SetFormula :=
    (numₘ(certificate) ≐ₘ numₘ(row.1)) ∧ₘ
      (formula ≐ₘ row.2)
  have hBody : Formula.Admissible body :=
    Formula.Admissible.conj
      (Formula.Admissible.equal
        (finite_numeral_term_admissible certificate)
        (finite_numeral_term_admissible row.1))
      (Formula.Admissible.equal hFormula
        (hRows row hRow))
  nd_apply FirstOrder.Derives.negIntro
    (T := T) (Γ := ([] : Context signature))
    (body := body)
    (hBodyCheck :=
      Formula.check_admissible_complete hBody)
  let Γ : Context signature := [body]
  have hBodyAt : Γ ⊢ₘ[T] body :=
    FirstOrder.Derives.assumption (by simp [Γ])
  have hEquality :
      Γ ⊢ₘ[T] numₘ(certificate) ≐ₘ numₘ(row.1) :=
    FirstOrder.Derives.conjElimLeft hBodyAt
  exact FirstOrder.Derives.negElim hEquality
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
      (N.numeral_ne (hInvalid row hRow)))

/-- 唯一指定公式码与当前位置不同时，固定表分支被统一拒绝。 -/
theorem condition_rows_neg_of_formula_ne
    {T : SetTheory}
    (N : NumeralArithmetic T)
    (rows : List (Nat × SetTerm))
    (formula expected : SetTerm)
    (certificate : Nat)
    (hFormula : Term.Admissible formula SetSort.set)
    (hRows :
      ∀ row, row ∈ rows →
        Term.Admissible row.2 SetSort.set)
    (hFunctional :
      ∀ row, row ∈ rows →
        certificate = row.1 →
          row.2 = expected)
    (hFormulaNe :
      Derives T [] (
        ¬ₘ (formula ≐ₘ expected))) :
    Derives T [] (
      ¬ₘ condition_rows
        rows formula (numₘ(certificate))) := by
  apply condition_rows_neg
    rows formula (numₘ(certificate))
    hFormula (finite_numeral_term_admissible certificate)
    hRows
  intro row hRow
  let body : SetFormula :=
    (numₘ(certificate) ≐ₘ numₘ(row.1)) ∧ₘ
      (formula ≐ₘ row.2)
  have hBody : Formula.Admissible body :=
    Formula.Admissible.conj
      (Formula.Admissible.equal
        (finite_numeral_term_admissible certificate)
        (finite_numeral_term_admissible row.1))
      (Formula.Admissible.equal hFormula
        (hRows row hRow))
  nd_apply FirstOrder.Derives.negIntro
    (T := T) (Γ := ([] : Context signature))
    (body := body)
    (hBodyCheck :=
      Formula.check_admissible_complete hBody)
  let Γ : Context signature := [body]
  have hBodyAt : Γ ⊢ₘ[T] body :=
    FirstOrder.Derives.assumption (by simp [Γ])
  by_cases hCertificate : certificate = row.1
  · have hFormulaEquality :
        Γ ⊢ₘ[T] formula ≐ₘ expected := by
      simpa [hFunctional row hRow hCertificate] using
        FirstOrder.Derives.conjElimRight hBodyAt
    exact FirstOrder.Derives.negElim hFormulaEquality
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp) hFormulaNe)
  · exact FirstOrder.Derives.negElim
      (FirstOrder.Derives.conjElimLeft hBodyAt)
      (FirstOrder.Derives.context_weaken
        (Γ := []) (Δ := Γ) (by simp)
        (N.numeral_ne hCertificate))

/-- 固定表条件只在两个可变项上执行自由变量替换。 -/
theorem condition_rows_substitute
    (rows : List (Nat × SetTerm))
    (formula certificate formulaResult certificateResult
      replacement : SetTerm)
    (sourceId : FreeVarId)
    (hRowsClosed :
      ∀ row, row ∈ rows →
        Term.freeSupport row.2 = [])
    (hFormulaSubstitution :
      Term.substituteFree SetSort.set sourceId replacement formula =
        formulaResult)
    (hCertificateSubstitution :
      Term.substituteFree SetSort.set sourceId replacement certificate =
        certificateResult) :
    Formula.substituteFree SetSort.set sourceId replacement
        (condition_rows rows formula certificate) =
      condition_rows rows formulaResult certificateResult := by
  induction rows with
  | nil =>
      rfl
  | cons row rows ih =>
      have hRowSubstitution :
          Term.substituteFree SetSort.set sourceId replacement row.2 =
            row.2 :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set sourceId replacement row.2 (by
            rw [hRowsClosed row (by simp)]
            exact List.not_mem_nil)
      have hNumeralSubstitution :
          Term.substituteFree SetSort.set sourceId replacement
              (numₘ(row.1)) =
            numₘ(row.1) :=
        Term.substituteFree_eq_self_of_not_mem
          SetSort.set sourceId replacement (numₘ(row.1)) (by
            rw [finite_numeral_term_freeSupport]
            exact List.not_mem_nil)
      have hTail :=
        ih (fun item hItem =>
          hRowsClosed item (by simp [hItem]))
      change Formula.substituteFree SetSort.set sourceId replacement
          ((((certificate ≐ₘ numₘ(row.1)) ∧ₘ
              (formula ≐ₘ row.2)) ∨ₘ
            condition_rows rows formula certificate)) =
        (((certificateResult ≐ₘ numₘ(row.1)) ∧ₘ
            (formulaResult ≐ₘ row.2)) ∨ₘ
          condition_rows rows formulaResult certificateResult)
      simp [
        Formula.substituteFree,
        hFormulaSubstitution, hCertificateSubstitution,
        hRowSubstitution, hNumeralSubstitution, hTail]

end FixedAxiomTable
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
