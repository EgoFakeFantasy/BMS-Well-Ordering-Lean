import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay

/-!
# checked 逻辑公理证书的逐层反演

`fs_logical_axiom_check_rows` 的成功计算精确给出一条有限轨迹：轨迹首项是待验证
公式，每个非末项都是下一项的一次 canonical 全称闭包，末项由基础逻辑公理
checker 接受。本模块只记录这份可计算语法信息，不经过 `HilbertLogicalAxiom`。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open ProofCode
open GodelQuotation
open Rosser

set_option autoImplicit false

namespace CertifiedProof

/--
checked 逻辑公理证书的精确轨迹。

`codes` 与 `formulas` 等长；闭包构造器中的 `eigen` 同时是当前证书行的数值，
而递归见证以打开后的公式继续。
-/
inductive FSLogicalAxiomCheckTrace
    (baseCheck : SetFormula → Nat → Bool) :
    List Nat → SetFormula → List SetFormula → Prop
  | base
      {baseCode : Nat} {formula : SetFormula}
      (hCheck :
        baseCheck formula baseCode = true) :
      FSLogicalAxiomCheckTrace
        baseCheck [baseCode] formula [formula]
  | forall_closure
      {eigen : Nat} {rest : List Nat}
      {body : SetFormula} {formulas : List SetFormula}
      (hFresh :
        (SetSort.set, eigen) ∉ Formula.freeSupport body)
      (hRest :
        FSLogicalAxiomCheckTrace baseCheck rest
          (Formula.openAt SetSort.set 0
            (Term.var (.fvar SetSort.set eigen)) body)
          formulas) :
      FSLogicalAxiomCheckTrace baseCheck (eigen :: rest)
        (Formula.forallE SetSort.set body)
        (Formula.forallE SetSort.set body :: formulas)

/-- 任意基础 checker 的成功计算可直接反演为逐层轨迹。 -/
theorem fs_logical_axiom_check_rows_with_trace_exists
    {baseCheck : SetFormula → Nat → Bool}
    {codes : List Nat} {formula : SetFormula}
    (hCheck :
      fs_logical_axiom_check_rows_with
        baseCheck codes formula = true) :
    ∃ formulas,
      FSLogicalAxiomCheckTrace
        baseCheck codes formula formulas := by
  cases codes with
  | nil =>
      simp [fs_logical_axiom_check_rows_with] at hCheck
  | cons eigen tail =>
      cases tail with
      | nil =>
          refine ⟨([formula] : List SetFormula), ?_⟩
          exact FSLogicalAxiomCheckTrace.base hCheck
      | cons baseCode rest =>
          cases formula with
          | falsum =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | truth =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | rel relation arguments =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | equal left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | neg body =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | conj left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | disj left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | imp left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | iff left right =>
              simp [fs_logical_axiom_check_rows_with] at hCheck
          | forallE sort body =>
              cases sort
              simp only [fs_logical_axiom_check_rows_with] at hCheck
              rcases Bool.and_eq_true_iff.mp hCheck with
                ⟨hFreshCheck, hRestCheck⟩
              have hFresh :
                  (SetSort.set, eigen) ∉
                    Formula.freeSupport body :=
                of_decide_eq_true hFreshCheck
              rcases
                  fs_logical_axiom_check_rows_with_trace_exists
                    hRestCheck with
                ⟨formulas, hTrace⟩
              exact ⟨
                Formula.forallE SetSort.set body :: formulas,
                FSLogicalAxiomCheckTrace.forall_closure
                  hFresh hTrace⟩
          | existsE sort body =>
              simp [fs_logical_axiom_check_rows_with] at hCheck

/-- 具名逻辑 checker 的成功计算轨迹。 -/
theorem fs_logical_axiom_check_rows_trace_exists
    {freeBase : Nat}
    {codes : List Nat} {formula : SetFormula}
    (hCheck :
      fs_logical_axiom_check_rows
        freeBase codes formula = true) :
    ∃ formulas,
      FSLogicalAxiomCheckTrace
        (fs_logical_base_axiom_check freeBase)
        codes formula formulas := by
  exact fs_logical_axiom_check_rows_with_trace_exists
    (by
      simpa [fs_logical_axiom_check_rows] using hCheck)

/-- 规范逻辑 checker 的成功计算轨迹。 -/
theorem fs_logical_axiom_canonical_check_rows_trace_exists
    {codes : List Nat} {formula : SetFormula}
    (hCheck :
      fs_logical_axiom_canonical_check_rows
        codes formula = true) :
    ∃ formulas,
      FSLogicalAxiomCheckTrace
        fs_logical_base_axiom_canonical_check
        codes formula formulas := by
  exact fs_logical_axiom_check_rows_with_trace_exists
    (by
      simpa [fs_logical_axiom_canonical_check_rows] using hCheck)

/-- 轨迹的公式表与证书行表严格等长。 -/
theorem FSLogicalAxiomCheckTrace.formulas_length
    {baseCheck : SetFormula → Nat → Bool}
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        baseCheck codes formula formulas) :
    formulas.length = codes.length := by
  induction hTrace with
  | base =>
      rfl
  | forall_closure hFresh hRest ih =>
      simp [ih]

/-- 成功轨迹的 code 列表非空。 -/
theorem FSLogicalAxiomCheckTrace.codes_nonempty
    {baseCheck : SetFormula → Nat → Bool}
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        baseCheck codes formula formulas) :
    codes ≠ [] := by
  cases hTrace <;> simp

/-- 成功轨迹的公式列表非空。 -/
theorem FSLogicalAxiomCheckTrace.formulas_nonempty
    {baseCheck : SetFormula → Nat → Bool}
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        baseCheck codes formula formulas) :
    formulas ≠ [] := by
  cases hTrace <;> simp

/-- 轨迹第零项就是 checker 的输入公式。 -/
theorem FSLogicalAxiomCheckTrace.formulas_head
    {baseCheck : SetFormula → Nat → Bool}
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        baseCheck codes formula formulas) :
    formulas[0]? = some formula := by
  cases hTrace <;> rfl

/--
轨迹末端的共同索引精确落在唯一基础逻辑公理行。

等式 `index + 1 = codes.length` 同时避免在后续对象层证明中使用截断减法。
-/
theorem FSLogicalAxiomCheckTrace.base_at_last
    {baseCheck : SetFormula → Nat → Bool}
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        baseCheck codes formula formulas) :
    ∃ index baseCode baseFormula,
      codes[index]? = some baseCode ∧
        formulas[index]? = some baseFormula ∧
        baseCheck baseFormula baseCode = true ∧
        index + 1 = codes.length := by
  induction hTrace with
  | @base baseCode formula hCheck =>
      exact ⟨0, baseCode, formula, by simp [hCheck]⟩
  | @forall_closure eigen rest body formulas hFresh hRest ih =>
      rcases ih with
        ⟨index, baseCode, baseFormula,
          hCode, hFormula, hCheck, hLength⟩
      refine ⟨index + 1, baseCode, baseFormula, ?_, ?_, hCheck, ?_⟩
      · simpa only [List.getElem?_cons_succ] using hCode
      · simpa only [List.getElem?_cons_succ] using hFormula
      · simp only [List.length_cons]
        omega

/--
任意非末索引都精确描述一次 checker 的 canonical 全称闭包递归步。
-/
theorem FSLogicalAxiomCheckTrace.forall_closure_at
    {baseCheck : SetFormula → Nat → Bool}
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        baseCheck codes formula formulas)
    {index : Nat}
    (hIndex : index + 1 < codes.length) :
    ∃ eigen body,
      codes[index]? = some eigen ∧
        formulas[index]? =
          some (Formula.forallE SetSort.set body) ∧
        formulas[index + 1]? =
          some
            (Formula.openAt SetSort.set 0
              (Term.var (.fvar SetSort.set eigen)) body) ∧
        (SetSort.set, eigen) ∉ Formula.freeSupport body := by
  induction hTrace generalizing index with
  | base =>
      simp at hIndex
  | @forall_closure eigen rest body formulas hFresh hRest ih =>
      cases index with
      | zero =>
          refine ⟨eigen, body, by simp, by simp, ?_, hFresh⟩
          simpa only [List.getElem?_cons_succ] using
            hRest.formulas_head
      | succ index =>
          have hRestIndex : index + 1 < rest.length := by
            simp only [List.length_cons] at hIndex
            omega
          rcases ih hRestIndex with
            ⟨innerEigen, innerBody,
              hCode, hFormula, hNext, hInnerFresh⟩
          refine ⟨innerEigen, innerBody, ?_, ?_, ?_, hInnerFresh⟩
          · simpa only [List.getElem?_cons_succ] using hCode
          · simpa only [List.getElem?_cons_succ] using hFormula
          · simpa only [Nat.succ_eq_add_one,
              Nat.add_assoc, List.getElem?_cons_succ] using hNext

/-- 自由变量项在纯集合论语言中 admissible。 -/
theorem fs_set_fvar_term_admissible
    (identifier : FreeVarId) :
    Term.Admissible
      ((Term.var (.fvar SetSort.set identifier)) : SetTerm)
      SetSort.set := by
  change
    TermWellSorted
        ((Term.var (.fvar SetSort.set identifier)) : SetTerm)
        SetSort.set ∧
      TermScoped Scope.empty
        ((Term.var (.fvar SetSort.set identifier)) : SetTerm)
  constructor
  · exact
      TermWellSorted.fvar
        (σ := Nonlogical.BasicSetTheory.signature)
        SetSort.set identifier
  · exact
      TermScoped.fvar
        (σ := Nonlogical.BasicSetTheory.signature)
        (ctx := Scope.empty)
        SetSort.set identifier

/-- 输入公式 admissible 时，checked 轨迹中的每个公式都 admissible。 -/
theorem FSLogicalAxiomCheckTrace.formulas_admissible
    {baseCheck : SetFormula → Nat → Bool}
    {codes : List Nat} {formula : SetFormula}
    {formulas : List SetFormula}
    (hTrace :
      FSLogicalAxiomCheckTrace
        baseCheck codes formula formulas)
    (hFormula : Formula.Admissible formula) :
    ∀ item, item ∈ formulas → Formula.Admissible item := by
  induction hTrace with
  | base =>
      intro item hItem
      simp only [List.mem_singleton] at hItem
      subst item
      exact hFormula
  | @forall_closure eigen rest body formulas hFresh hRest ih =>
      intro item hItem
      simp only [List.mem_cons] at hItem
      rcases hItem with rfl | hItem
      · exact hFormula
      · have hOpened :
            Formula.Admissible
              (Formula.openAt SetSort.set 0
                (Term.var (.fvar SetSort.set eigen)) body) :=
          Formula.Admissible.forall_openAt
            (body := body)
            (term :=
              (Term.var (.fvar SetSort.set eigen) : SetTerm))
            SetSort.set hFormula
            (fs_set_fvar_term_admissible eigen)
        exact ih hOpened item hItem

end CertifiedProof

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
