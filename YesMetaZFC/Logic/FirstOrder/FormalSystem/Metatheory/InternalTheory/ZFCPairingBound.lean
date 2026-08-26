import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFC

/-!
# ZFC 对象算术中的 Gödel 配对坐标上界

本模块把公共自然数配对上界合同提升到 ZFC raw 支持理论，并提供沿配对值等式
运输后的右坐标界。证明码、逻辑证书与 schema 证书均可共享该接口。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols

set_option autoImplicit false

/--
两个对象自然数的 Gödel 配对值仍属于对象理论的 `ωₘ`。

证明只消费配对定义契约：规范有序对属于 `ωₘ ×ₘ ωₘ`，而配对项与自身相等，
故定义条件的首个合取给出所需闭包。
-/
theorem fs_zfc_support_raw_godel_pairing_mem_omega
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ ωₘ)
    (hRightNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ ωₘ) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      godel_pairₘ(⟨left, right⟩ₘ) ∈ₘ ωₘ := by
  let pair : SetTerm := ⟨left, right⟩ₘ
  let candidate : SetTerm := godel_pairₘ(pair)
  have hPair :
      Term.Admissible pair SetSort.set := by
    simpa [pair] using
      ordered_pair_term_admissible
        left right hLeft hRight
  have hCandidate :
      Term.Admissible candidate SetSort.set := by
    simpa [candidate] using
      godel_pairing_term_admissible pair hPair
  have hPairMember :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        pair ∈ₘ (ωₘ ×ₘ ωₘ) := by
    have hRule :
        Derives fs_zfc_support_raw_theory [] (
          (left ∈ₘ ωₘ) ⟶ₘ
            (right ∈ₘ ωₘ) ⟶ₘ
              (pair ∈ₘ (ωₘ ×ₘ ωₘ))) := by
      apply FirstOrder.Derives.theory_weaken
        (fun _ hFormula =>
          fs_zfc_support_raw_contains_relation_plane
            hFormula)
      simpa [pair] using
        ordered_pair_mem_cartesian_product
          ωₘ ωₘ left right
          omega_term_admissible omega_term_admissible
          hLeft hRight
    exact FirstOrder.Derives.impElim
      (FirstOrder.Derives.impElim
        (FirstOrder.Derives.context_weaken
          (Γ := []) (Δ := Γ) (by simp) hRule)
        hLeftNatural)
      hRightNatural
  have hDefinition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        godel_pairing_definition_instance
          pair candidate := by
    apply FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp)
    apply FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_godel_pairing
          hFormula)
    exact godel_pairing_definition_instance_derives
      pair candidate hPair hCandidate
  have hCondition :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        godel_pairing_condition pair candidate :=
    FirstOrder.Derives.iffElimRight
      (FirstOrder.Derives.impElim
        hDefinition hPairMember)
      (FirstOrder.Derives.eq_refl_m
        (sort := SetSort.set) candidate)
  simpa [pair, candidate, godel_pairing_condition] using
    FirstOrder.Derives.conjElimLeft hCondition

/-- 沿对象等式把 Gödel 配对的自然数闭包运输到给定 payload。 -/
theorem fs_zfc_support_raw_godel_pairing_mem_omega_of_equality
    {Γ : Context signature}
    (payload left right : SetTerm)
    (hPayload : Term.Admissible payload SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] left ∈ₘ ωₘ)
    (hRightNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory] right ∈ₘ ωₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        payload ≐ₘ godel_pairₘ(⟨left, right⟩ₘ)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory] payload ∈ₘ ωₘ := by
  have hPair :
      Term.Admissible
        (godel_pairₘ(⟨left, right⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible _ <|
      ordered_pair_term_admissible left right hLeft hRight
  exact FirstOrder.Derives.iffElimLeft
    (membership_left_iff_of_equality
      payload (godel_pairₘ(⟨left, right⟩ₘ)) ωₘ
      hPayload hPair omega_term_admissible hEquality)
    (fs_zfc_support_raw_godel_pairing_mem_omega
      left right hLeft hRight hLeftNatural hRightNatural)

/-- 两个对象自然数坐标均不超过其 Gödel 配对值。 -/
theorem fs_zfc_support_raw_godel_pairing_coordinate_bound
    {Γ : Context signature}
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ ωₘ)
    (hRightNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ ωₘ) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      (left ∈ₘ
          Sₘ(godel_pairₘ(⟨left, right⟩ₘ))) ∧ₘ
        (right ∈ₘ
          Sₘ(godel_pairₘ(⟨left, right⟩ₘ))) := by
  have hInstance :
      Derives fs_zfc_support_raw_theory [] (
        natural_godel_pairing_coordinate_bound_instance
          left right) :=
    FirstOrder.Derives.theory_weaken
      (fun _ hFormula =>
        fs_zfc_support_raw_contains_natural_addition_bound
          hFormula)
      (natural_godel_pairing_coordinate_bound_instance_derives
        left right hLeft hRight)
  exact FirstOrder.Derives.impElim
    (FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) hInstance)
    (FirstOrder.Derives.conjIntro
      hLeftNatural hRightNatural)

/--
若某项等于两个对象自然数的 Gödel 配对值，则左坐标属于该项的后继。
-/
theorem fs_zfc_support_raw_godel_pairing_left_bound_of_equality
    {Γ : Context signature}
    (certificate left right : SetTerm)
    (hCertificate :
      Term.Admissible certificate SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ ωₘ)
    (hRightNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ ωₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        certificate ≐ₘ
          godel_pairₘ(⟨left, right⟩ₘ)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      left ∈ₘ Sₘ(certificate) := by
  have hPair :
      Term.Admissible
        (godel_pairₘ(⟨left, right⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible
      (⟨left, right⟩ₘ)
      (ordered_pair_term_admissible
        left right hLeft hRight)
  have hLeftBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ
          Sₘ(godel_pairₘ(⟨left, right⟩ₘ)) :=
    FirstOrder.Derives.conjElimLeft
      (fs_zfc_support_raw_godel_pairing_coordinate_bound
        left right hLeft hRight
        hLeftNatural hRightNatural)
  have hSuccessorEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Sₘ(certificate) ≐ₘ
          Sₘ(godel_pairₘ(⟨left, right⟩ₘ)) :=
    successor_term_congr_of_equality
      certificate
      (godel_pairₘ(⟨left, right⟩ₘ))
      hCertificate hPair hEquality
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      left
      (Sₘ(certificate))
      (Sₘ(godel_pairₘ(⟨left, right⟩ₘ)))
      hLeft
      (successor_term_admissible
        certificate hCertificate)
      (successor_term_admissible
        (godel_pairₘ(⟨left, right⟩ₘ)) hPair)
      hSuccessorEquality)
    hLeftBound

/--
若某项等于两个对象自然数的 Gödel 配对值，则右坐标属于该项的后继。
-/
theorem fs_zfc_support_raw_godel_pairing_right_bound_of_equality
    {Γ : Context signature}
    (certificate left right : SetTerm)
    (hCertificate :
      Term.Admissible certificate SetSort.set)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        left ∈ₘ ωₘ)
    (hRightNatural :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ ωₘ)
    (hEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        certificate ≐ₘ
          godel_pairₘ(⟨left, right⟩ₘ)) :
    Γ ⊢ₘ[fs_zfc_support_raw_theory]
      right ∈ₘ Sₘ(certificate) := by
  have hPair :
      Term.Admissible
        (godel_pairₘ(⟨left, right⟩ₘ)) SetSort.set :=
    godel_pairing_term_admissible
      (⟨left, right⟩ₘ)
      (ordered_pair_term_admissible
        left right hLeft hRight)
  have hRightBound :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        right ∈ₘ
          Sₘ(godel_pairₘ(⟨left, right⟩ₘ)) :=
    FirstOrder.Derives.conjElimRight
      (fs_zfc_support_raw_godel_pairing_coordinate_bound
        left right hLeft hRight
        hLeftNatural hRightNatural)
  have hSuccessorEquality :
      Γ ⊢ₘ[fs_zfc_support_raw_theory]
        Sₘ(certificate) ≐ₘ
          Sₘ(godel_pairₘ(⟨left, right⟩ₘ)) :=
    successor_term_congr_of_equality
      certificate
      (godel_pairₘ(⟨left, right⟩ₘ))
      hCertificate hPair hEquality
  exact FirstOrder.Derives.iffElimLeft
    (membership_right_iff_of_equality
      right
      (Sₘ(certificate))
      (Sₘ(godel_pairₘ(⟨left, right⟩ₘ)))
      hRight
      (successor_term_admissible
        certificate hCertificate)
      (successor_term_admissible
        (godel_pairₘ(⟨left, right⟩ₘ)) hPair)
      hSuccessorEquality)
    hRightBound

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
