import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NumeralArithmetic
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.Hierarchy
import YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofCode

/-!
# ProofT 的最小对象算术核心

本模块只记录 Rosser 有限比较真正消费的对象算术能力。项和公式均采用内在上下文
索引，码域的良构性、自由变量支撑以及替换交换律不再作为额外证明合同出现。
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

/--
只用空集与后继定义合同消去有限 numeral 成员关系。

证明按外部 `bound` 归纳；它不依赖对象理论中的自然数集合、quotation 或序列编码。
-/
theorem numeral_member_elim
    {T : SetTheory}
    (hEmpty :
      ∀ {formula},
        empty_set_symbol_theory formula → T formula)
    (hSuccessor :
      ∀ {formula},
        successor_operator_theory formula → T formula)
    {free : SetContext}
    {Γ : Context signature free}
    (bound : Nat)
    (point : SetOpenTerm free)
    (conclusion : SetOpenFormula free)
    (hMember :
      Γ ⊢ₘ[T] point ∈ₘ numₘ(bound))
    (hBranch :
      ∀ index, index < bound →
        (point ≐ₘ numₘ(index)) :: Γ
          ⊢ₘ[T] conclusion) :
    Γ ⊢ₘ[T] conclusion := by
  induction bound generalizing Γ with
  | zero =>
      have hNotMember :
          Γ ⊢ₘ[T] ¬ₘ (point ∈ₘ numₘ(0)) := by
        simpa [finite_numeral_term] using
          FirstOrder.Derives.context_weaken
            (Γ := [])
            (Δ := Γ)
            (by simp)
            (FirstOrder.Derives.theory_weaken
              hEmpty
              (empty_set_term_has_no_members point))
      exact FirstOrder.Derives.falsum_elim
        (FirstOrder.Derives.neg_elim
          hMember hNotMember)
  | succ bound ih =>
      have hMembershipIff :
          Γ ⊢ₘ[T]
            (point ∈ₘ Sₘ(numₘ(bound))) ↔ₘ
              ((point ≐ₘ numₘ(bound)) ∨ₘ
                (point ∈ₘ numₘ(bound))) :=
        FirstOrder.Derives.context_weaken
          (Γ := [])
          (Δ := Γ)
          (by simp)
          (FirstOrder.Derives.theory_weaken
            hSuccessor
            (successor_term_membership_iff
              (Γ := [])
              (numₘ(bound)) point))
      have hCases :
          Γ ⊢ₘ[T]
            (point ≐ₘ numₘ(bound)) ∨ₘ
              (point ∈ₘ numₘ(bound)) :=
        FirstOrder.Derives.iff_elim_left
          hMembershipIff
          (by
            simpa [finite_numeral_term] using hMember)
      apply FirstOrder.Derives.disj_elim hCases
      · exact hBranch bound (Nat.lt_succ_self bound)
      · let member : SetOpenFormula free :=
          point ∈ₘ numₘ(bound)
        let Δ : Context signature free := member :: Γ
        have hMember' :
            Δ ⊢ₘ[T] point ∈ₘ numₘ(bound) := by
          simpa [member, Δ] using
            (FirstOrder.Derives.assumption
              (T := T)
              (Γ := Δ)
              (formula := member)
              (by simp [Δ]))
        apply ih hMember'
        intro index hIndex
        exact FirstOrder.Derives.context_weaken
          (Γ := (point ≐ₘ numₘ(index)) :: Γ)
          (Δ := (point ≐ₘ numₘ(index)) :: Δ)
          (by
            intro formula hFormula
            simp only [List.mem_cons] at hFormula ⊢
            rcases hFormula with rfl | hFormula
            · exact Or.inl rfl
            · exact Or.inr <| by
                simp [Δ, hFormula])
          (hBranch index
            (Nat.lt_trans hIndex
              (Nat.lt_succ_self bound)))

/-- 有限证书反演所需的对象算术核心。 -/
structure FiniteCore (T : SetTheory) extends NumeralArithmetic T where
  /-- `point ∈ n` 可按全部标准 `i < n` 穷尽为 `point = i`。 -/
  member_elim :
    ∀ {free : SetContext}
      {Γ : Context signature free}
      (bound : Nat)
      (point : SetOpenTerm free)
      (conclusion : SetOpenFormula free),
      Γ ⊢ₘ[T] point ∈ₘ numₘ(bound) →
      (∀ index, index < bound →
        (point ≐ₘ numₘ(index)) :: Γ
          ⊢ₘ[T] conclusion) →
      Γ ⊢ₘ[T] conclusion

/-- 有限对象算术宿主的最小公理合同。 -/
structure ArithmeticSupport (T : SetTheory) where
  contains_membership_irreflexive :
    ∀ {formula},
      membership_irreflexive_theory formula → T formula
  contains_empty_set :
    ∀ {formula},
      empty_set_symbol_theory formula → T formula
  contains_successor :
    ∀ {formula},
      successor_operator_theory formula → T formula

namespace ArithmeticSupport

/-- 最小算术宿主沿理论包含直接提升。 -/
theorem theory_weaken
    {T U : SetTheory}
    (A : ArithmeticSupport T)
    (hTU : Theory.Extends U T) :
    ArithmeticSupport U where
  contains_membership_irreflexive := fun hSentence =>
    hTU (A.contains_membership_irreflexive hSentence)
  contains_empty_set := fun hSentence =>
    hTU (A.contains_empty_set hSentence)
  contains_successor := fun hSentence =>
    hTU (A.contains_successor hSentence)

/-- 从最小算术宿主派生标准 numeral 判异接口。 -/
theorem numeral_arithmetic
    {T : SetTheory}
    (A : ArithmeticSupport T) :
    NumeralArithmetic T where
  numeral_ne := fun hNe =>
    ProofT.numeral_ne
      A.contains_membership_irreflexive
      A.contains_successor
      hNe

/-- 从最小算术宿主派生有限 numeral 穷尽核心。 -/
theorem finite_core
    {T : SetTheory}
    (A : ArithmeticSupport T) :
    FiniteCore T where
  toNumeralArithmetic := A.numeral_arithmetic
  member_elim := by
    intro free Γ bound point conclusion hMember hBranch
    exact ProofT.numeral_member_elim
      A.contains_empty_set
      A.contains_successor
      bound point conclusion hMember hBranch

end ArithmeticSupport

/-- 证书标签与配对 payload 反演所需的有限算术核心。 -/
structure CertificateCore (T : SetTheory) extends FiniteCore T where
  /-- 两个标准 numeral 的 Gödel 配对项计算为对应的标准 numeral。 -/
  pair_value :
    ∀ left right,
      Derives T ([] : Context signature []) (
        godel_pairₘ(numₘ(left), numₘ(right)) ≐ₘ
          numₘ(ProofCode.godel_pair_value left right))

/-- Rosser 有限比较所需的完整对象算术核心。 -/
structure Core (T : SetTheory) extends FiniteCore T where
  /-- 对象语言中的证明码域。 -/
  code_domain : Delta0CodeDomain
  /-- 码域元素相对标准 numeral `q` 可切分为 `≤ q` 或 `> q`。 -/
  code_cut :
    ∀ {free : SetContext}
      (q : Nat)
      (point : SetOpenTerm free),
      Derives T [] (
        code_domain.condition point ⟶ₘ
          ((point ∈ₘ Sₘ(numₘ(q))) ∨ₘ
            (numₘ(q) ∈ₘ point)))

namespace Core

/-- 在任意局部上下文中按标准边界消去证明码域元素。 -/
theorem cut_elim
    {T : SetTheory}
    (C : Core T)
    {free : SetContext}
    {Γ : Context signature free}
    (q : Nat)
    (point : SetOpenTerm free)
    (conclusion : SetOpenFormula free)
    (hDomain :
      Γ ⊢ₘ[T] C.code_domain.condition point)
    (hLower :
      ∀ index, index ≤ q →
        (point ≐ₘ numₘ(index)) :: Γ
          ⊢ₘ[T] conclusion)
    (hUpper :
      (numₘ(q) ∈ₘ point) :: Γ
        ⊢ₘ[T] conclusion) :
    Γ ⊢ₘ[T] conclusion := by
  have hCut :
      Γ ⊢ₘ[T]
        (point ∈ₘ Sₘ(numₘ(q))) ∨ₘ
          (numₘ(q) ∈ₘ point) :=
    FirstOrder.Derives.imp_elim
      (FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ := Γ)
        (by simp)
        (C.code_cut q point))
      hDomain
  apply FirstOrder.Derives.disj_elim hCut
  · let member : SetOpenFormula free :=
      point ∈ₘ Sₘ(numₘ(q))
    let Δ : Context signature free := member :: Γ
    have hMember :
        Δ ⊢ₘ[T] point ∈ₘ numₘ(q + 1) := by
      simpa [member, Δ, finite_numeral_term] using
        (FirstOrder.Derives.assumption
          (T := T)
          (Γ := Δ)
          (formula := member)
          (by simp [Δ]))
    apply C.member_elim
      (q + 1) point conclusion hMember
    intro index hIndex
    exact FirstOrder.Derives.context_weaken
      (Γ := (point ≐ₘ numₘ(index)) :: Γ)
      (Δ := (point ≐ₘ numₘ(index)) :: Δ)
      (by
        intro formula hFormula
        simp only [List.mem_cons] at hFormula ⊢
        rcases hFormula with rfl | hFormula
        · exact Or.inl rfl
        · exact Or.inr <| by
            simp [Δ, hFormula])
      (hLower index (Nat.lt_succ_iff.mp hIndex))
  · exact hUpper

end Core
end ProofT
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
