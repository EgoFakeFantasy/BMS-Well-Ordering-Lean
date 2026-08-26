import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.CheckedReplay

/-!
# checked 逻辑公理的单路径失败反演

本模块把 `fs_logical_axiom_check_rows = false` 反演为通往首个失败位置的唯一路径。
它只保存成功闭包前缀与最终失败原因，不保存完整 transcript，也不携带任何对象
理论假设。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace Rosser

open Nonlogical.BasicSetTheory

set_option autoImplicit false

/--
checked 逻辑公理检查的单路径失败见证。

`tail` 只记录继续递归所必需的新鲜性事实；最终失败严格落在空表、基础检查、
非全称形状或新鲜性四类之一。
-/
inductive FSLogicalAxiomCheckFailure
    (freeBase : Nat) :
    List Nat → SetFormula → Prop
  | empty
      {formula : SetFormula} :
      FSLogicalAxiomCheckFailure freeBase [] formula
  | base
      {baseCode : Nat} {formula : SetFormula}
      (h_check :
        fs_logical_base_axiom_check
          freeBase formula baseCode = false) :
      FSLogicalAxiomCheckFailure
        freeBase [baseCode] formula
  | non_forall
      {eigen next : Nat} {rest : List Nat}
      {formula : SetFormula}
      (h_shape :
        ¬ ∃ body,
          formula = Formula.forallE SetSort.set body) :
      FSLogicalAxiomCheckFailure freeBase
        (eigen :: next :: rest) formula
  | freshness
      {eigen next : Nat} {rest : List Nat}
      {body : SetFormula}
      (h_fresh :
        (SetSort.set, eigen) ∈
          Formula.freeSupport body) :
      FSLogicalAxiomCheckFailure freeBase
        (eigen :: next :: rest)
        (Formula.forallE SetSort.set body)
  | tail
      {eigen next : Nat} {rest : List Nat}
      {body : SetFormula}
      (h_fresh :
        (SetSort.set, eigen) ∉
          Formula.freeSupport body)
      (h_failure :
        FSLogicalAxiomCheckFailure freeBase
          (next :: rest)
          (Formula.openAt SetSort.set 0
            (Term.var (.fvar SetSort.set eigen)) body)) :
      FSLogicalAxiomCheckFailure freeBase
        (eigen :: next :: rest)
        (Formula.forallE SetSort.set body)

/-- 布尔检查失败精确产生一条首失败路径。 -/
theorem fs_logical_axiom_check_rows_failure_of_false
    {freeBase : Nat}
    {codes : List Nat} {formula : SetFormula}
    (h_check :
      fs_logical_axiom_check_rows
        freeBase codes formula = false) :
    FSLogicalAxiomCheckFailure
      freeBase codes formula := by
  induction codes generalizing formula with
  | nil =>
      exact .empty
  | cons eigen tail ih =>
      cases tail with
      | nil =>
          exact .base h_check
      | cons next rest =>
          cases formula with
          | forallE sort body =>
              cases sort
              by_cases h_fresh :
                  (SetSort.set, eigen) ∉
                    Formula.freeSupport body
              · have h_tail :
                    fs_logical_axiom_check_rows
                        freeBase (next :: rest)
                        (Formula.openAt SetSort.set 0
                          (Term.var
                            (.fvar SetSort.set eigen))
                          body) =
                      false := by
                  have h_decide :
                      decide
                          ((SetSort.set, eigen) ∉
                            Formula.freeSupport body) =
                        true := by
                    simp [h_fresh]
                  rw [
                    fs_logical_axiom_check_rows,
                    fs_logical_axiom_check_rows_with.eq_3
                      (fs_logical_base_axiom_check freeBase)
                      eigen (next :: rest)
                      SetSort.set body (by simp)] at h_check
                  cases h_tail_check :
                      fs_logical_axiom_check_rows
                        freeBase (next :: rest)
                        (Formula.openAt SetSort.set 0
                          (Term.var
                            (.fvar SetSort.set eigen))
                          body) with
                  | false =>
                      rfl
                  | true =>
                      have h_tail_with :
                          fs_logical_axiom_check_rows_with
                              (fs_logical_base_axiom_check freeBase)
                              (next :: rest)
                              (Formula.openAt SetSort.set 0
                                (Term.var
                                  (.fvar SetSort.set eigen))
                                body) =
                            true := by
                        simpa [fs_logical_axiom_check_rows] using
                          h_tail_check
                      have h_decide_false :
                          decide
                              ((SetSort.set, eigen) ∉
                                Formula.freeSupport body) =
                            false := by
                        simpa only [h_tail_with, Bool.and_true] using
                          h_check
                      exact False.elim <|
                        Bool.noConfusion <|
                          h_decide.symm.trans h_decide_false
                exact .tail h_fresh (ih h_tail)
              · exact .freshness (by simpa using h_fresh)
          | falsum =>
              exact .non_forall (by simp)
          | truth =>
              exact .non_forall (by simp)
          | rel relation arguments =>
              exact .non_forall (by simp)
          | equal left right =>
              exact .non_forall (by simp)
          | neg body =>
              exact .non_forall (by simp)
          | conj left right =>
              exact .non_forall (by simp)
          | disj left right =>
              exact .non_forall (by simp)
          | imp left right =>
              exact .non_forall (by simp)
          | iff left right =>
              exact .non_forall (by simp)
          | existsE sort body =>
              exact .non_forall (by simp)

/-- 结构化失败见证可重新计算为原检查器的 `false`。 -/
theorem FSLogicalAxiomCheckFailure.check_eq_false
    {freeBase : Nat}
    {codes : List Nat} {formula : SetFormula}
    (h_failure :
      FSLogicalAxiomCheckFailure
        freeBase codes formula) :
    fs_logical_axiom_check_rows
      freeBase codes formula = false := by
  induction h_failure with
  | empty =>
      rfl
  | base h_check =>
      exact h_check
  | @non_forall eigen next rest formula h_shape =>
      cases formula with
      | forallE sort body =>
          cases sort
          exact False.elim <| h_shape ⟨body, rfl⟩
      | falsum | truth | rel | equal | neg | conj | disj |
          imp | iff | existsE =>
          rfl
  | @freshness eigen next rest body h_fresh =>
      have h_decide :
          decide
              ((SetSort.set, eigen) ∉
                Formula.freeSupport body) =
            false := by
        simp [h_fresh]
      rw [
        fs_logical_axiom_check_rows,
        fs_logical_axiom_check_rows_with.eq_3
          (fs_logical_base_axiom_check freeBase)
          eigen (next :: rest)
          SetSort.set body (by simp)]
      calc
        (decide
              ((SetSort.set, eigen) ∉
                Formula.freeSupport body) &&
            fs_logical_axiom_check_rows
              freeBase (next :: rest)
              (Formula.openAt SetSort.set 0
                (Term.var
                  (.fvar SetSort.set eigen))
                body)) =
            (false &&
              fs_logical_axiom_check_rows
                freeBase (next :: rest)
                (Formula.openAt SetSort.set 0
                  (Term.var
                    (.fvar SetSort.set eigen))
                  body)) := by
          rw [h_decide]
        _ = false := rfl
  | @tail eigen next rest body h_fresh h_tail ih =>
      have h_decide :
          decide
              ((SetSort.set, eigen) ∉
                Formula.freeSupport body) =
            true := by
        simp [h_fresh]
      rw [
        fs_logical_axiom_check_rows,
        fs_logical_axiom_check_rows_with.eq_3
          (fs_logical_base_axiom_check freeBase)
          eigen (next :: rest)
          SetSort.set body (by simp)]
      calc
        (decide
              ((SetSort.set, eigen) ∉
                Formula.freeSupport body) &&
            fs_logical_axiom_check_rows
              freeBase (next :: rest)
              (Formula.openAt SetSort.set 0
                (Term.var
                  (.fvar SetSort.set eigen))
                body)) =
            (true &&
              fs_logical_axiom_check_rows
                freeBase (next :: rest)
                (Formula.openAt SetSort.set 0
                  (Term.var
                    (.fvar SetSort.set eigen))
                  body)) := by
          rw [h_decide]
        _ =
            fs_logical_axiom_check_rows
              freeBase (next :: rest)
              (Formula.openAt SetSort.set 0
                (Term.var
                  (.fvar SetSort.set eigen))
                body) := rfl
        _ = false := ih

end Rosser
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
