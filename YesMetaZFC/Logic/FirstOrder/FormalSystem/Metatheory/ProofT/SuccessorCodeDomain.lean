import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.CodeDomain
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Core

/-!
# ProofT 的无穷无关后继链码域

Rosser 比较只需要把任意候选证明码与一个标准 numeral 比较，并不需要“全体自然数”
作为集合存在。本模块使用一个更弱的局部条件：

* `point = 0` 或 `0 ∈ point`；
* 若 `x ∈ point`，则 `S(x) = point` 或 `S(x) ∈ point`。

对每个外部标准边界 `q`，在 Lean 元层对 `q` 归纳即可推出
`point ∈ S(q) ∨ q ∈ point`。整个证明只消费空集、后继及有限 numeral 消去，
不使用无穷公理、分离或对象层自然数归纳。
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

/-! ## 有限 numeral 的后继步 -/

theorem numeral_successor_step
    {T : SetTheory}
    (C : FiniteCore T)
    (hSuccessor :
      ∀ {formula},
        successor_operator_theory formula → T formula)
    {free : SetContext}
    (n : Nat)
    (point : SetOpenTerm free) :
    Derives T ([] : Context signature free) (
      (point ∈ₘ numₘ(n)) ⟶ₘ
        ((Sₘ(point) ≐ₘ numₘ(n)) ∨ₘ
          (Sₘ(point) ∈ₘ numₘ(n)))) := by
  apply FirstOrder.Derives.imp_intro
  let member : SetOpenFormula free :=
    point ∈ₘ numₘ(n)
  let conclusion : SetOpenFormula free :=
    (Sₘ(point) ≐ₘ numₘ(n)) ∨ₘ
      (Sₘ(point) ∈ₘ numₘ(n))
  let Γ : Context signature free := [member]
  have hMember :
      Γ ⊢ₘ[T] point ∈ₘ numₘ(n) := by
    simpa [member, Γ] using
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := Γ)
        (formula := member)
        (by simp [Γ]))
  apply C.member_elim n point conclusion hMember
  intro i hi
  let Δ : Context signature free :=
    (point ≐ₘ numₘ(i)) :: Γ
  have hEquality :
      Δ ⊢ₘ[T] point ≐ₘ numₘ(i) :=
    FirstOrder.Derives.assumption (by simp [Δ])
  have hSuccessorEquality :
      Δ ⊢ₘ[T] Sₘ(point) ≐ₘ Sₘ(numₘ(i)) :=
    successor_term_congr_of_equality
      point (numₘ(i)) hEquality
  by_cases hNext : i + 1 = n
  · apply FirstOrder.Derives.disj_intro_left
    simpa [conclusion, finite_numeral_term, ← hNext] using
      hSuccessorEquality
  · have hlt : i + 1 < n := by
      omega
    have hStandardMember :
        Δ ⊢ₘ[T] numₘ(i + 1) ∈ₘ numₘ(n) :=
      by
        exact FirstOrder.Derives.context_weaken
          (Γ := ([] : Context signature free))
          (Δ := Δ)
          (by simp)
          (numeral_mem_of_lt hSuccessor hlt)
    have hTransport :
        Δ ⊢ₘ[T]
          (Sₘ(point) ∈ₘ numₘ(n)) ↔ₘ
            (Sₘ(numₘ(i)) ∈ₘ numₘ(n)) :=
      membership_left_iff_of_equality
        (Sₘ(point)) (Sₘ(numₘ(i))) (numₘ(n))
        hSuccessorEquality
    apply FirstOrder.Derives.disj_intro_right
    exact FirstOrder.Derives.iff_elim_right hTransport
      (by simpa [finite_numeral_term] using hStandardMember)

/-! ## 标准 numeral 的码域实例 -/

theorem successor_code_domain_numeral
    {T : SetTheory}
    (C : FiniteCore T)
    (hSuccessor :
      ∀ {formula},
        successor_operator_theory formula → T formula)
    (n : Nat) :
    Derives T ([] : Context signature []) (
      successor_code_domain (numₘ(n))) := by
  have hBase :
      Derives T ([] : Context signature []) (
        (numₘ(n) ≐ₘ ∅ₘ) ∨ₘ
          (∅ₘ ∈ₘ numₘ(n))) := by
    cases n with
    | zero =>
        apply FirstOrder.Derives.disj_intro_left
        simpa [finite_numeral_term] using
          (Metatheory.Derives.equality_refl
            (T := T)
            (Γ := ([] : Context signature []))
            (∅ₘ : SetOpenTerm []))
    | succ n =>
        apply FirstOrder.Derives.disj_intro_right
        simpa [finite_numeral_term] using
          (numeral_mem_of_lt
            hSuccessor
            (Nat.zero_lt_succ n))
  have hOpenStep :
      Derives T ([] : Context signature [SetSort.set]) (
        ((.fvar .here : SetOpenTerm [SetSort.set]) ∈ₘ numₘ(n)) ⟶ₘ
          ((Sₘ((.fvar .here : SetOpenTerm [SetSort.set])) ≐ₘ numₘ(n)) ∨ₘ
            (Sₘ((.fvar .here : SetOpenTerm [SetSort.set])) ∈ₘ numₘ(n)))) :=
    numeral_successor_step C hSuccessor n (.fvar .here)
  have hStep :
      Derives T ([] : Context signature []) (
        set_levy_bound.boundedForall (numₘ(n))
          ((Sₘ(bₘ[.here]) ≐ₘ (numₘ(n)).weakenBound SetSort.set) ∨ₘ
            (Sₘ(bₘ[.here]) ∈ₘ (numₘ(n)).weakenBound SetSort.set))) := by
    simpa [Formula.LevyBound.boundedForall,
      Formula.forallFreeTop, Formula.abstractFreeTop,
      Formula.substitute, Formula.substituteMapped,
      Term.substituteMapped, Arguments.substituteMapped,
      finite_numeral_term_substituteMapped,
      finite_numeral_term_weakenBound,
      Substitution.abstractFreeTop,
      VariableSubstitution.abstractBound,
      VariableSubstitution.abstractFreeTop,
      VariableSubstitution.liftBound,
      VariableSubstitution.weakenBound] using!
      (FirstOrder.Derives.forall_intro
        (sort := SetSort.set)
        (Γ := ([] : Context signature []))
        (body :=
          ((.fvar .here : SetOpenTerm [SetSort.set]) ∈ₘ numₘ(n)) ⟶ₘ
            ((Sₘ((.fvar .here : SetOpenTerm [SetSort.set])) ≐ₘ numₘ(n)) ∨ₘ
              (Sₘ((.fvar .here : SetOpenTerm [SetSort.set])) ∈ₘ numₘ(n))))
        hOpenStep)
  simpa [successor_code_domain, FormulaTemplate.apply_one,
    FormulaTemplate.instantiate, VariableSubstitution.cons,
    VariableSubstitution.empty, Term.substituteMapped,
    Arguments.substituteMapped, Formula.substituteMapped,
    VariableSubstitution.weakenBound, Term.weakenBound] using!
    FirstOrder.Derives.conj_intro hBase hStep

/-! ## 任意有限边界的码域切分 -/

theorem successor_code_cut
    {T : SetTheory}
    (hSuccessor :
      ∀ {formula},
        successor_operator_theory formula → T formula)
    (q : Nat)
    {free : SetContext}
    (point : SetOpenTerm free) :
    Derives T ([] : Context signature free) (
      successor_code_domain point ⟶ₘ
        ((point ∈ₘ Sₘ(numₘ(q))) ∨ₘ
          (numₘ(q) ∈ₘ point))) := by
  induction q with
  | zero =>
      apply FirstOrder.Derives.imp_intro
      let domain : SetOpenFormula free :=
        successor_code_domain point
      let Γ : Context signature free := [domain]
      have hDomain :
          Γ ⊢ₘ[T] domain :=
        FirstOrder.Derives.assumption (by simp [Γ])
      have hBase :
          Γ ⊢ₘ[T] (point ≐ₘ ∅ₘ) ∨ₘ (∅ₘ ∈ₘ point) := by
        simpa [domain, successor_code_domain] using!
          FirstOrder.Derives.conj_elim_left hDomain
      apply FirstOrder.Derives.disj_elim hBase
      · let Δ : Context signature free :=
          (point ≐ₘ ∅ₘ) :: Γ
        have hEquality :
            Δ ⊢ₘ[T] point ≐ₘ ∅ₘ :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hSelf :
            Δ ⊢ₘ[T] ∅ₘ ∈ₘ Sₘ(∅ₘ) :=
          FirstOrder.Derives.context_weaken
            (Γ := ([] : Context signature free))
            (Δ := Δ)
            (by simp)
            (FirstOrder.Derives.theory_weaken
              hSuccessor
              (mem_successor_self (Γ := ([] : Context signature free))
                (∅ₘ : SetOpenTerm free)))
        have hTransport :
            Δ ⊢ₘ[T]
              (point ∈ₘ Sₘ(∅ₘ)) ↔ₘ
                (∅ₘ ∈ₘ Sₘ(∅ₘ)) :=
          membership_left_iff_of_equality
            point ∅ₘ (Sₘ(∅ₘ)) hEquality
        apply FirstOrder.Derives.disj_intro_left
        simpa [finite_numeral_term] using
          FirstOrder.Derives.iff_elim_right hTransport hSelf
      · let Δ : Context signature free :=
          (∅ₘ ∈ₘ point) :: Γ
        apply FirstOrder.Derives.disj_intro_right
        simpa [finite_numeral_term] using
          (FirstOrder.Derives.assumption
            (T := T)
            (Γ := Δ)
            (formula := (∅ₘ : SetOpenTerm free) ∈ₘ point)
            (by simp [Δ]))
  | succ q ih =>
      apply FirstOrder.Derives.imp_intro
      let domain : SetOpenFormula free :=
        successor_code_domain point
      let Γ : Context signature free := [domain]
      have hDomain :
          Γ ⊢ₘ[T] domain :=
        FirstOrder.Derives.assumption (by simp [Γ])
      have hPrevious :
          Γ ⊢ₘ[T]
            (point ∈ₘ Sₘ(numₘ(q))) ∨ₘ
              (numₘ(q) ∈ₘ point) :=
        FirstOrder.Derives.imp_elim
          (FirstOrder.Derives.context_weaken
            (Γ := ([] : Context signature free))
            (Δ := Γ)
            (by simp)
            ih)
          hDomain
      apply FirstOrder.Derives.disj_elim hPrevious
      · let Δ : Context signature free :=
          (point ∈ₘ Sₘ(numₘ(q))) :: Γ
        have hMember :
            Δ ⊢ₘ[T] point ∈ₘ Sₘ(numₘ(q)) :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hLift :
            Δ ⊢ₘ[T]
              (point ∈ₘ Sₘ(numₘ(q))) ⟶ₘ
                (point ∈ₘ Sₘ(Sₘ(numₘ(q)))) :=
          FirstOrder.Derives.context_weaken
            (Γ := ([] : Context signature free))
            (Δ := Δ)
            (by simp)
            (FirstOrder.Derives.theory_weaken
              hSuccessor
              (mem_successor_of_mem
                (Γ := ([] : Context signature free))
                (Sₘ(numₘ(q))) point))
        apply FirstOrder.Derives.disj_intro_left
        simpa [finite_numeral_term] using
          FirstOrder.Derives.imp_elim hLift hMember
      · let Δ : Context signature free :=
          (numₘ(q) ∈ₘ point) :: Γ
        have hDomainAt :
            Δ ⊢ₘ[T] domain :=
          FirstOrder.Derives.context_weaken_cons hDomain
        have hStepAll :
            Δ ⊢ₘ[T]
              set_levy_bound.boundedForall point
                ((Sₘ(bₘ[.here]) ≐ₘ point.weakenBound SetSort.set) ∨ₘ
                  (Sₘ(bₘ[.here]) ∈ₘ point.weakenBound SetSort.set)) := by
          simpa [domain, successor_code_domain] using!
            FirstOrder.Derives.conj_elim_right hDomainAt
        have hStepAt :
            Δ ⊢ₘ[T]
              (numₘ(q) ∈ₘ point) ⟶ₘ
                ((Sₘ(numₘ(q)) ≐ₘ point) ∨ₘ
                  (Sₘ(numₘ(q)) ∈ₘ point)) := by
          simpa [Formula.LevyBound.boundedForall,
            Formula.LevyBound.membership, set_levy_bound,
            finite_numeral_term_weakenBound] using!
            (FirstOrder.Derives.forall_elim
              (numₘ(q)) hStepAll)
        have hMember :
            Δ ⊢ₘ[T] numₘ(q) ∈ₘ point :=
          FirstOrder.Derives.assumption (by simp [Δ])
        have hCases :
            Δ ⊢ₘ[T]
              (Sₘ(numₘ(q)) ≐ₘ point) ∨ₘ
                (Sₘ(numₘ(q)) ∈ₘ point) :=
          FirstOrder.Derives.imp_elim hStepAt hMember
        apply FirstOrder.Derives.disj_elim hCases
        · let Ε : Context signature free :=
            (Sₘ(numₘ(q)) ≐ₘ point) :: Δ
          have hEquality :
              Ε ⊢ₘ[T] Sₘ(numₘ(q)) ≐ₘ point :=
            FirstOrder.Derives.assumption (by simp [Ε])
          have hSelf :
              Ε ⊢ₘ[T]
                Sₘ(numₘ(q)) ∈ₘ Sₘ(Sₘ(numₘ(q))) :=
            FirstOrder.Derives.context_weaken
              (Γ := ([] : Context signature free))
              (Δ := Ε)
              (by simp)
              (FirstOrder.Derives.theory_weaken
                hSuccessor
                (mem_successor_self
                  (Γ := ([] : Context signature free))
                  (Sₘ(numₘ(q)))))
          have hTransport :
              Ε ⊢ₘ[T]
                (Sₘ(numₘ(q)) ∈ₘ Sₘ(Sₘ(numₘ(q)))) ↔ₘ
                  (point ∈ₘ Sₘ(Sₘ(numₘ(q)))) :=
            membership_left_iff_of_equality
              (Sₘ(numₘ(q))) point (Sₘ(Sₘ(numₘ(q)))) hEquality
          apply FirstOrder.Derives.disj_intro_left
          simpa [finite_numeral_term] using
            FirstOrder.Derives.iff_elim_left hTransport hSelf
        · let Δ' : Context signature free :=
            (Sₘ(numₘ(q)) ∈ₘ point) :: Δ
          apply FirstOrder.Derives.disj_intro_right
          simpa [finite_numeral_term] using
            (FirstOrder.Derives.assumption
              (T := T)
              (Γ := Δ')
              (formula := (Sₘ(numₘ(q)) : SetOpenTerm free) ∈ₘ point)
              (by simp [Δ']))

/-! ## 后继码域对象算术核 -/

def successor_core
    {T : SetTheory}
    (C : FiniteCore T)
    (hSuccessor :
      ∀ {formula},
        successor_operator_theory formula → T formula) :
    Core T where
  toFiniteCore := C
  code_domain := {
    condition := successor_code_domain
    delta0 := successor_code_domain_delta0
  }
  code_cut := fun {_free} q point =>
    successor_code_cut hSuccessor q point

end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
