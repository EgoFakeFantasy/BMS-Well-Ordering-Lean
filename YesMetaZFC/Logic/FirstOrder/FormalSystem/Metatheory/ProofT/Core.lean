import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NumeralArithmetic
import YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofCode

/-!
# ProofT 的最小对象算术核心

`ProofT.Core` 只记录 Rosser 有限比较真正消费的对象算术能力，不要求理论逐字包含
quotation、有限序列、替换、分离、收集或幂集等具体定义层。

当前集合论实现使用 von Neumann numeral 与成员关系表示自然数次序。这里要求的有限
numeral 消去和标准边界切分均属于 PA 级算术强度；KPω 可以用 `Δ₀` 分离实现后者。
quotation、对角化和证明图表示将在后续接口中建立于本核心之上。
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

证明按外部 `bound` 归纳；它不依赖标准序列、函数编码或 quotation。调用方只需证明
目标理论包含这两层最基本的定义扩张。
-/
theorem numeral_member_elim
    {T : SetTheory}
    (hEmpty :
      ∀ formula,
        empty_set_symbol_theory formula → T formula)
    (hSuccessor :
      ∀ formula,
        successor_operator_theory formula → T formula)
    {Γ : Context signature}
    (bound : Nat)
    (point : SetTerm)
    (conclusion : SetFormula)
    (hPoint : Term.Admissible point SetSort.set)
    (hConclusion : Formula.Admissible conclusion)
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
              (empty_set_term_has_no_members
                point hPoint))
      exact FirstOrder.Derives.falsumElim
        (FirstOrder.Derives.negElim
          hMember hNotMember)
        (Formula.check_admissible_complete hConclusion)
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
            (by
              simpa [successor_member_condition] using
                successor_term_membership_iff
                  (numₘ(bound)) point
                  (finite_numeral_term_admissible bound)
                  hPoint))
      have hCases :
          Γ ⊢ₘ[T]
            (point ≐ₘ numₘ(bound)) ∨ₘ
              (point ∈ₘ numₘ(bound)) :=
        FirstOrder.Derives.iffElimRight
          hMembershipIff
          (by
            simpa [finite_numeral_term] using hMember)
      apply FirstOrder.Derives.disjElim hCases
      · exact hBranch bound (Nat.lt_succ_self bound)
      · let member : SetFormula :=
          point ∈ₘ numₘ(bound)
        let Δ : Context signature := member :: Γ
        have hMember' :
            Δ ⊢ₘ[T] point ∈ₘ numₘ(bound) := by
          simpa [member, Δ] using
            (FirstOrder.Derives.assumption
              (T := T)
              (Γ := Δ)
              (φ := member)
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

/--
有限证书反演所需的对象算术核心。

该层只包含标准 numeral 判异、理论闭句边界与有限 numeral 穷尽；它不要求自然数
切分，因而可直接服务于证书标签、有限 payload 和固定公理表的拒绝算法。
-/
structure FiniteCore (T : SetTheory) extends NumeralArithmetic T where
  /-- 理论公理均为闭句，供对象全称化与存在消去的新鲜性检查使用。 -/
  theory_sentence :
    ∀ {formula : SetFormula},
      T formula → Formula.Sentence formula
  /-- `point ∈ n` 可按全部标准 `i < n` 穷尽为 `point = i`。 -/
  member_elim :
    ∀ {Γ : Context signature}
      (bound : Nat)
      (point : SetTerm)
      (conclusion : SetFormula)
      (_hPoint : Term.Admissible point SetSort.set)
      (_hConclusion : Formula.Admissible conclusion),
      Γ ⊢ₘ[T] point ∈ₘ numₘ(bound) →
      (∀ index, index < bound →
        (point ≐ₘ numₘ(index)) :: Γ
          ⊢ₘ[T] conclusion) →
      Γ ⊢ₘ[T] conclusion

/--
证书标签与配对 payload 反演所需的有限算术核心。

相较 `FiniteCore` 只增加标准输入上的 Gödel 配对地面计算；不要求一般配对函数
的总性，也不要求 Rosser 自然数切分。
-/
structure CertificateCore (T : SetTheory) extends FiniteCore T where
  /-- 两个标准 numeral 的 Gödel 配对项计算为对应的标准 numeral。 -/
  pair_value :
    ∀ left right,
      Derives T [] (
        godel_pairₘ(⟨numₘ(left), numₘ(right)⟩ₘ) ≐ₘ
          numₘ(ProofCode.godel_pair_value left right))

/--
未知对象自然数坐标的 Gödel 配对反演核心。

该层在有限证书算术上追加标准 numeral 的自然数性，以及沿一般配对等式得到左右
坐标有限上界的能力。它只供需要反演未知 payload 的模块使用；普通标签拒绝仍停留
在更弱的 `CertificateCore`。
-/
structure PairingCore (T : SetTheory) extends CertificateCore T where
  /-- 每个标准 numeral 都属于对象自然数。 -/
  numeral_natural :
    ∀ value,
      Derives T [] (
        numₘ(value) ∈ₘ ωₘ)
  /-- 一般配对等式把左坐标压入配对值的后继。 -/
  left_bound :
    ∀ {Γ : Context signature}
      (certificate left right : SetTerm),
      Term.Admissible certificate SetSort.set →
      Term.Admissible left SetSort.set →
      Term.Admissible right SetSort.set →
      Γ ⊢ₘ[T] left ∈ₘ ωₘ →
      Γ ⊢ₘ[T] right ∈ₘ ωₘ →
      Γ ⊢ₘ[T]
        certificate ≐ₘ godel_pairₘ(⟨left, right⟩ₘ) →
      Γ ⊢ₘ[T] left ∈ₘ Sₘ(certificate)
  /-- 一般配对等式把右坐标压入配对值的后继。 -/
  right_bound :
    ∀ {Γ : Context signature}
      (certificate left right : SetTerm),
      Term.Admissible certificate SetSort.set →
      Term.Admissible left SetSort.set →
      Term.Admissible right SetSort.set →
      Γ ⊢ₘ[T] left ∈ₘ ωₘ →
      Γ ⊢ₘ[T] right ∈ₘ ωₘ →
      Γ ⊢ₘ[T]
        certificate ≐ₘ godel_pairₘ(⟨left, right⟩ₘ) →
      Γ ⊢ₘ[T] right ∈ₘ Sₘ(certificate)

/--
Rosser 有限比较所需的完整对象算术核心。

该结构在 `FiniteCore` 上只追加相对标准 numeral 的自然数切分；quotation、
有限序列、替换和 schema 定义仍不进入公共签名。
-/
structure Core (T : SetTheory) extends FiniteCore T where
  /-- 任意对象自然数相对标准 numeral `q` 可切分为 `≤ q` 或 `> q`。 -/
  natural_cut :
    ∀ (q : Nat)
      (point : SetTerm),
      Term.Admissible point SetSort.set →
      Derives T [] (
        (point ∈ₘ ωₘ) ⟶ₘ
          ((point ∈ₘ Sₘ(numₘ(q))) ∨ₘ
            (numₘ(q) ∈ₘ point)))

namespace Core

/--
在任意局部上下文中按标准边界消去对象自然数。

较小分支只暴露标准等式 `point = i`，不泄漏有限 numeral 的成员见证；较大分支
保留严格成员关系，正好对应 Rosser 的“存在更小右证明码”矛盾。
-/
theorem cut_elim
    {T : SetTheory}
    (C : Core T)
    {Γ : Context signature}
    (q : Nat)
    (point : SetTerm)
    (conclusion : SetFormula)
    (hPoint : Term.Admissible point SetSort.set)
    (hConclusion : Formula.Admissible conclusion)
    (hNatural :
      Γ ⊢ₘ[T] point ∈ₘ ωₘ)
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
    FirstOrder.Derives.impElim
      (FirstOrder.Derives.context_weaken
        (Γ := [])
        (Δ := Γ)
        (by simp)
        (C.natural_cut q point hPoint))
      hNatural
  apply FirstOrder.Derives.disjElim hCut
  · let member : SetFormula :=
      point ∈ₘ Sₘ(numₘ(q))
    let Δ : Context signature := member :: Γ
    have hMember :
        Δ ⊢ₘ[T] point ∈ₘ numₘ(q + 1) := by
      simpa [member, Δ, finite_numeral_term] using
        (FirstOrder.Derives.assumption
          (T := T)
          (Γ := Δ)
          (φ := member)
          (by simp [Δ]))
    apply C.member_elim
      (q + 1) point conclusion
      hPoint hConclusion hMember
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
