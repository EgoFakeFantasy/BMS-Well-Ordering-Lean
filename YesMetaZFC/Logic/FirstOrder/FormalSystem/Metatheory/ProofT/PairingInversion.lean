import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCPairingBound
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.InternalTheory.ZFCCheckedCertificateRejection

/-!
# ProofT Gödel 配对反演

本模块只处理一端为标准自然数码的配对等式。坐标上界先把右坐标压入
`S(raw)`，随后有限枚举并用地面配对单射性锁定规范反配对值。
-/

namespace YesMetaZFC
namespace Logic
namespace FirstOrder
namespace FormalSystem

open Nonlogical.BasicSetTheory
open scoped Nonlogical.BasicSetTheory.Symbols
open scoped Symbols
open ProofCode
open GodelQuotation

set_option autoImplicit false

/--
地面配对等式唯一锁定右坐标。

该接口只要求右坐标已经是对象自然数；左坐标是标准 numeral，因而无需额外前提。
-/
theorem ProofT.pair_right_unique
    {T : SetTheory}
    (P : ProofT.PairingCore T)
    {Γ : Context signature}
    (raw tag : Nat)
    (payload : SetTerm)
    (hPayload : Term.Admissible payload SetSort.set)
    (hPayloadNatural :
      Γ ⊢ₘ[T]
        payload ∈ₘ ωₘ)
    (hPair :
      Γ ⊢ₘ[T]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(tag), payload⟩ₘ)) :
    Γ ⊢ₘ[T]
      payload ≐ₘ
        numₘ((godel_unpair_value raw).2) := by
  have hTagNatural :
      Γ ⊢ₘ[T]
        numₘ(tag) ∈ₘ ωₘ :=
    FirstOrder.Derives.context_weaken
      (Γ := []) (Δ := Γ) (by simp) <|
        P.numeral_natural tag
  have hPayloadBound :
      Γ ⊢ₘ[T]
        payload ∈ₘ Sₘ(numₘ(raw)) :=
    P.right_bound
      (numₘ(raw)) (numₘ(tag)) payload
      (finite_numeral_term_admissible raw)
      (finite_numeral_term_admissible tag)
      hPayload hTagNatural hPayloadNatural hPair
  have hPayloadMember :
      Γ ⊢ₘ[T]
        payload ∈ₘ numₘ(raw + 1) := by
    simpa [finite_numeral_term, successor_term] using
      hPayloadBound
  let conclusion : SetFormula :=
    payload ≐ₘ numₘ((godel_unpair_value raw).2)
  have hConclusion :
      Formula.Admissible conclusion := by
    simpa [conclusion] using
      Formula.Admissible.equal hPayload
        (finite_numeral_term_admissible
          (godel_unpair_value raw).2)
  apply
    P.member_elim
      (raw + 1) payload conclusion
      hPayload hConclusion hPayloadMember
  intro value hValueBound
  let equality : SetFormula := payload ≐ₘ numₘ(value)
  let Δ : Context signature := equality :: Γ
  change Δ ⊢ₘ[T] conclusion
  have hPayloadEquality :
      Δ ⊢ₘ[T]
        payload ≐ₘ numₘ(value) := by
    simpa [Δ, equality] using
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := Δ)
        (φ := equality)
        (by simp [Δ]))
  by_cases hCode :
      raw = godel_pair_value tag value
  · have hCoordinates :
        tag = (godel_unpair_value raw).1 ∧
          value = (godel_unpair_value raw).2 := by
      apply godel_pair_value_eq_iff.mp
      rw [← hCode, godel_unpair_value_spec]
    simpa [conclusion, hCoordinates.2] using
      hPayloadEquality
  · have hPairAt :
        Δ ⊢ₘ[T]
          numₘ(raw) ≐ₘ
            godel_pairₘ(⟨numₘ(tag), payload⟩ₘ) :=
      FirstOrder.Derives.context_weaken_cons hPair
    have hFalse :
        Δ ⊢ₘ[T]
          Formula.falsum :=
      ProofT.falsum_of_tagged_code
        P.toCertificateCore
        tag value raw
        (numₘ(raw)) payload
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (numₘ(raw)))
        hPairAt hPayload hPayloadEquality hCode
    exact FirstOrder.Derives.falsumElim hFalse

/--
地面配对等式唯一锁定左坐标。

该接口与右坐标版本共同构成嵌套 payload 的二元地面反演核。
-/
theorem ProofT.pair_left_unique
    {T : SetTheory}
    (P : ProofT.PairingCore T)
    {Γ : Context signature}
    (raw : Nat)
    (left right : SetTerm)
    (hLeft : Term.Admissible left SetSort.set)
    (hRight : Term.Admissible right SetSort.set)
    (hLeftNatural :
      Γ ⊢ₘ[T]
        left ∈ₘ ωₘ)
    (hRightNatural :
      Γ ⊢ₘ[T]
        right ∈ₘ ωₘ)
    (hPair :
      Γ ⊢ₘ[T]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨left, right⟩ₘ)) :
    Γ ⊢ₘ[T]
      left ≐ₘ
        numₘ((godel_unpair_value raw).1) := by
  have hLeftBound :
      Γ ⊢ₘ[T]
        left ∈ₘ Sₘ(numₘ(raw)) :=
    P.left_bound
      (numₘ(raw)) left right
      (finite_numeral_term_admissible raw)
      hLeft hRight hLeftNatural hRightNatural hPair
  have hLeftMember :
      Γ ⊢ₘ[T]
        left ∈ₘ numₘ(raw + 1) := by
    simpa [finite_numeral_term, successor_term] using
      hLeftBound
  let conclusion : SetFormula :=
    left ≐ₘ numₘ((godel_unpair_value raw).1)
  have hConclusion :
      Formula.Admissible conclusion := by
    simpa [conclusion] using
      Formula.Admissible.equal hLeft
        (finite_numeral_term_admissible
          (godel_unpair_value raw).1)
  apply
    P.member_elim
      (raw + 1) left conclusion
      hLeft hConclusion hLeftMember
  intro value hValueBound
  let equality : SetFormula := left ≐ₘ numₘ(value)
  let Δ : Context signature := equality :: Γ
  change Δ ⊢ₘ[T] conclusion
  have hLeftEquality :
      Δ ⊢ₘ[T]
        left ≐ₘ numₘ(value) := by
    simpa [Δ, equality] using
      (FirstOrder.Derives.assumption
        (T := T)
        (Γ := Δ)
        (φ := equality)
        (by simp [Δ]))
  have hPairAt :
      Δ ⊢ₘ[T]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨left, right⟩ₘ) :=
    FirstOrder.Derives.context_weaken_cons hPair
  have hGroundPair :
      Δ ⊢ₘ[T]
        numₘ(raw) ≐ₘ
          godel_pairₘ(⟨numₘ(value), right⟩ₘ) := by
    exact Metatheory.Derives.equality_trans hPairAt <|
      godel_pairing_term_congr_of_equalities
        left (numₘ(value)) right right
        hLeft (finite_numeral_term_admissible value)
        hRight hRight hLeftEquality
        (FirstOrder.Derives.eq_refl_m right)
  have hRightEquality :
      Δ ⊢ₘ[T]
        right ≐ₘ numₘ((godel_unpair_value raw).2) :=
    ProofT.pair_right_unique
      P
      raw value right hRight
      (FirstOrder.Derives.context_weaken_cons hRightNatural)
      hGroundPair
  by_cases hCode :
      raw =
        godel_pair_value value
          (godel_unpair_value raw).2
  · have hCoordinates :
        value = (godel_unpair_value raw).1 := by
      apply And.left <| godel_pair_value_eq_iff.mp
        (show
          godel_pair_value value (godel_unpair_value raw).2 =
            godel_pair_value
              (godel_unpair_value raw).1
              (godel_unpair_value raw).2 by
          calc
            _ = raw := hCode.symm
            _ = _ := (godel_unpair_value_spec raw).symm)
    simpa [conclusion, hCoordinates] using hLeftEquality
  · exact FirstOrder.Derives.falsumElim <|
      ProofT.falsum_of_tagged_code
        P.toCertificateCore
        value (godel_unpair_value raw).2 raw
        (numₘ(raw)) right
        (FirstOrder.Derives.eq_refl_m
          (sort := SetSort.set) (numₘ(raw)))
        hGroundPair hRight hRightEquality hCode

end FormalSystem
end FirstOrder
end Logic
end YesMetaZFC
