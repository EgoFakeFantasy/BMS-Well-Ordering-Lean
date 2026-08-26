import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.GodelQuotation.QuotationValue.Sequence

/-!
# 有限序列拼接的对象长度上界

本模块把公共对象自然加法上界运输到有限序列定义域。它不依赖 token、项码或公式
码，供 `flattenₘ`、函数应用参数族和谓词参数族共同复用。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem
namespace GodelQuotation

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/--
对象自然数的 `≤`-`<` 混合传递。

该接口只把公共对象算术实例嵌入 Gödel quotation 理论；不展开任何序列或编码
定义。
-/
theorem gq_natural_le_lt_transitivity
    {Γ : Context signature}
    (point middle upper : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hMiddle : Term.Admissible middle SetSort.set)
    (hUpper : Term.Admissible upper SetSort.set)
    (hMiddleOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        middle ∈ₘ ωₘ)
    (hUpperOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        upper ∈ₘ ωₘ)
    (hLe :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ Sₘ(middle))
    (hLt :
      Γ ⊢ₘ[godel_quotation_theory]
        middle ∈ₘ upper) :
    Γ ⊢ₘ[godel_quotation_theory]
      point ∈ₘ upper := by
  have hInstance :
      Γ ⊢ₘ[godel_quotation_theory]
        natural_le_lt_transitivity_instance
          point middle upper :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_weaken_natural_addition_bound <|
            natural_le_lt_transitivity_instance_derives
              point middle upper
              hPoint hMiddle hUpper
  exact FirstOrder.Derives.impElim hInstance <|
    FirstOrder.Derives.conjIntro hMiddleOmega <|
      FirstOrder.Derives.conjIntro hUpperOmega <|
        FirstOrder.Derives.conjIntro hLe hLt

/--
若 `point` 不超过任一分段长度，则它不超过拼接后的总长度。
-/
theorem gq_concatenation_domain_upper_bound
    {Γ : Context signature}
    (point left right : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hPointOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ ωₘ)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hBound :
      Γ ⊢ₘ[godel_quotation_theory]
        (point ∈ₘ Sₘ(domₘ(left))) ∨ₘ
          (point ∈ₘ Sₘ(domₘ(right)))) :
    Γ ⊢ₘ[godel_quotation_theory]
      point ∈ₘ Sₘ(domₘ(left ⌢ₘ right)) := by
  let leftDomain : SetTerm := domₘ(left)
  let rightDomain : SetTerm := domₘ(right)
  let domainSum : SetTerm :=
    leftDomain +ₘ rightDomain
  have hLeftDomain :
      Term.Admissible leftDomain SetSort.set := by
    simpa [leftDomain] using
      domain_term_admissible left hLeft
  have hRightDomain :
      Term.Admissible rightDomain SetSort.set := by
    simpa [rightDomain] using
      domain_term_admissible right hRight
  have hLeftOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        leftDomain ∈ₘ ωₘ := by
    simpa [leftDomain, finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hLeftFinite
  have hRightOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        rightDomain ∈ₘ ωₘ := by
    simpa [rightDomain, finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hRightFinite
  have hInstance :
      Γ ⊢ₘ[godel_quotation_theory]
        natural_addition_upper_bound_instance
          point leftDomain rightDomain :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_weaken_natural_addition_bound <|
            natural_addition_upper_bound_instance_derives
              point leftDomain rightDomain
              hPoint hLeftDomain hRightDomain
  have hPointInSum :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ Sₘ(domainSum) := by
    apply FirstOrder.Derives.impElim
      (by simpa [domainSum] using hInstance)
    exact FirstOrder.Derives.conjIntro hPointOmega <|
      FirstOrder.Derives.conjIntro hLeftOmega <|
        FirstOrder.Derives.conjIntro hRightOmega <| by
          simpa [leftDomain, rightDomain] using hBound
  have hDomainEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left ⌢ₘ right) ≐ₘ domainSum := by
    simpa [domainSum, leftDomain, rightDomain] using
      gq_concatenation_domain_eq_sum_of_theory
        (fun _ hFormula => hFormula)
        left right hLeftFinite hRightFinite
        (hLeft := Term.check_admissible_complete hLeft)
        (hRight := Term.check_admissible_complete hRight)
  have hSuccessorEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        Sₘ(domₘ(left ⌢ₘ right)) ≐ₘ
          Sₘ(domainSum) :=
    successor_term_congr_of_equality
      (domₘ(left ⌢ₘ right)) domainSum
      (domain_term_admissible
        (left ⌢ₘ right)
        (finite_sequence_concatenation_term_admissible
          left right hLeft hRight))
      (natural_addition_term_admissible
        leftDomain rightDomain
        hLeftDomain hRightDomain)
      hDomainEquality
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      point
      (Sₘ(domₘ(left ⌢ₘ right)))
      (Sₘ(domainSum))
      hPoint
      (successor_term_admissible
        (domₘ(left ⌢ₘ right))
        (domain_term_admissible
          (left ⌢ₘ right)
          (finite_sequence_concatenation_term_admissible
            left right hLeft hRight)))
      (successor_term_admissible domainSum
        (natural_addition_term_admissible
          leftDomain rightDomain
          hLeftDomain hRightDomain))
      hSuccessorEquality)
    hPointInSum

/-- 右段长度不超过拼接后的总长度。 -/
theorem gq_concatenation_right_domain_le
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right) :
    Γ ⊢ₘ[godel_quotation_theory]
      domₘ(right) ∈ₘ
        Sₘ(domₘ(left ⌢ₘ right)) := by
  have hRightDomain :
      Term.Admissible (domₘ(right)) SetSort.set :=
    domain_term_admissible right hRight
  have hRightOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ∈ₘ ωₘ := by
    simpa [finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hRightFinite
  have hReflexive :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(right) ∈ₘ Sₘ(domₘ(right)) :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_weaken_successor <|
            mem_successor_self
              (domₘ(right)) hRightDomain
  exact gq_concatenation_domain_upper_bound
    (domₘ(right)) left right
    hRightDomain hLeft hRight
    hRightOmega hLeftFinite hRightFinite <|
      FirstOrder.Derives.disjIntroRight
        (left := domₘ(right) ∈ₘ Sₘ(domₘ(left)))
        hReflexive

/-- 左段上的非严格长度上界可沿一次右追加传播。 -/
theorem gq_concatenation_left_bound_le
    {Γ : Context signature}
    (point left right : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hPointOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ ωₘ)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hBound :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ Sₘ(domₘ(left))) :
    Γ ⊢ₘ[godel_quotation_theory]
      point ∈ₘ Sₘ(domₘ(left ⌢ₘ right)) :=
  gq_concatenation_domain_upper_bound
    point left right hPoint hLeft hRight
    hPointOmega hLeftFinite hRightFinite <|
      FirstOrder.Derives.disjIntroLeft hBound

/--
若左段长度为正，且 `point` 不超过右段长度，则 `point` 严格小于拼接总长度。
-/
theorem gq_concatenation_positive_left_strict_bound
    {Γ : Context signature}
    (point left right : SetTerm)
    (hPoint : Term.Admissible point SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hPointOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ ωₘ)
    (hLeftFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition left)
    (hRightFinite :
      Γ ⊢ₘ[godel_quotation_theory]
        finite_sequence_condition right)
    (hLeftPositive :
      Γ ⊢ₘ[godel_quotation_theory]
        ∅ₘ ∈ₘ domₘ(left))
    (hBound :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ Sₘ(domₘ(right))) :
    Γ ⊢ₘ[godel_quotation_theory]
      point ∈ₘ domₘ(left ⌢ₘ right) := by
  let leftDomain : SetTerm := domₘ(left)
  let rightDomain : SetTerm := domₘ(right)
  let domainSum : SetTerm :=
    leftDomain +ₘ rightDomain
  have hLeftDomain :
      Term.Admissible leftDomain SetSort.set := by
    simpa [leftDomain] using
      domain_term_admissible left hLeft
  have hRightDomain :
      Term.Admissible rightDomain SetSort.set := by
    simpa [rightDomain] using
      domain_term_admissible right hRight
  have hLeftOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        leftDomain ∈ₘ ωₘ := by
    simpa [leftDomain, finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hLeftFinite
  have hRightOmega :
      Γ ⊢ₘ[godel_quotation_theory]
        rightDomain ∈ₘ ωₘ := by
    simpa [rightDomain, finite_sequence_condition] using
      FirstOrder.Derives.conjElimRight hRightFinite
  have hInstance :
      Γ ⊢ₘ[godel_quotation_theory]
        natural_positive_left_addition_strict_bound_instance
          point leftDomain rightDomain :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        gq_weaken_standard_sequence <|
          standard_sequence_weaken_natural_addition_bound <|
            natural_positive_left_addition_strict_bound_instance_derives
              point leftDomain rightDomain
              hPoint hLeftDomain hRightDomain
  have hPointInSum :
      Γ ⊢ₘ[godel_quotation_theory]
        point ∈ₘ domainSum := by
    apply FirstOrder.Derives.impElim
      (by simpa [domainSum] using hInstance)
    exact FirstOrder.Derives.conjIntro hPointOmega <|
      FirstOrder.Derives.conjIntro hLeftOmega <|
        FirstOrder.Derives.conjIntro hRightOmega <|
          FirstOrder.Derives.conjIntro
            (by simpa [leftDomain] using hLeftPositive) <| by
              simpa [rightDomain] using hBound
  have hDomainEquality :
      Γ ⊢ₘ[godel_quotation_theory]
        domₘ(left ⌢ₘ right) ≐ₘ domainSum := by
    simpa [domainSum, leftDomain, rightDomain] using
      gq_concatenation_domain_eq_sum_of_theory
        (fun _ hFormula => hFormula)
        left right hLeftFinite hRightFinite
        (hLeft := Term.check_admissible_complete hLeft)
        (hRight := Term.check_admissible_complete hRight)
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      point (domₘ(left ⌢ₘ right)) domainSum
      hPoint
      (domain_term_admissible
        (left ⌢ₘ right)
        (finite_sequence_concatenation_term_admissible
          left right hLeft hRight))
      (natural_addition_term_admissible
        leftDomain rightDomain
        hLeftDomain hRightDomain)
      hDomainEquality)
    hPointInSum

end GodelQuotation
end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
