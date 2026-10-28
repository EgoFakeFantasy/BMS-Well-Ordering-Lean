import BMSConstructibleBridge.PowerlessCanonicalOrderCandidateBounded
import BMSConstructibleBridge.SecondOrderCanonicalIndexUnique
import BMSConstructibleBridge.SecondOrderWellOrderEndExtensionUnique

/-! # 有界规范后继证书的 raw 输出唯一性

两份证书可使用不同母界。有限函数覆盖恢复原指标规格后，实际指标、
干净查询图、精确行族、完整行序及完整末端扩张逐项认同。
无需 Class 输出、Sat 正确性或父序良序性；这些是存在性与可靠性的义务，
不是固定数据下输出唯一性的额外前提。不从 Prop 抽取 Type 数据。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderCandidateUnique

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem proper_l {Q I A : type_l hℳ}
    (h : PowerlessRelationBounded.clean_l (𝒩 := 𝒱) Q I A) :
    PowerlessRelativeClassSatisfactionIndexCanonical.proper_l (ℳ₀ := 𝒱) Q := by
  intro p hp
  obtain ⟨x, y, _hx, _hy, hPair⟩ := h p hp
  exact ⟨x, y, hPair⟩

/-- 完整成员规格不可省略；仅有相同 Value 仍允许非有序对垃圾。 -/
theorem unique_l {C C' ω A P Sat D E E' : type_l hℳ}
    (hCoverage : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C)
    (hCoverage' : ∀ f, PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω A f → mem_l hℳ f C')
    (h : PowerlessCanonicalOrderCandidateBounded.holds_l (𝒩 := 𝒱) C ω A P Sat D E)
    (h' : PowerlessCanonicalOrderCandidateBounded.holds_l (𝒩 := 𝒱) C' ω A P Sat D E') : E = E' := by
  obtain ⟨S, _hS, I, _hI, J, _hJ, N, _hN, T, _hT, K, _hK,
    U, _hU, Q, _hQ, Y, _hY, L, _hL, hData⟩ := h
  obtain ⟨S', _hS', I', _hI', J', _hJ', N', _hN', T', _hT', K', _hK',
    U', _hU', Q', _hQ', Y', _hY', L', _hL', hData'⟩ := h'
  have hRaw := (PowerlessCanonicalOrderCandidateBounded.reading_l hCoverage).mp hData
  have hRaw' := (PowerlessCanonicalOrderCandidateBounded.reading_l hCoverage').mp hData'
  have hIndex := PowerlessCanonicalIndexBounded.canonical_spec_l hCoverage hData.1
  have hIndex' := PowerlessCanonicalIndexBounded.canonical_spec_l hCoverage' hData'.1
  obtain ⟨rfl, rfl, rfl, rfl⟩ := SecondOrderCanonicalIndexUnique.unique_l hIndex hIndex'
  have hQEq : Q = Q' := SecondOrderCanonicalIndexUnique.proper_unique_l
    (proper_l hRaw.queryClean) (proper_l hRaw'.queryClean)
    (fun i x => (hRaw.queryRead i x).trans (hRaw'.queryRead i x).symm)
  subst Q'
  have hYEq : Y = Y' := SecondOrderQuotient.ext_l hℳ Y Y'
    (fun y => (hRaw.family y).trans (hRaw'.family y).symm)
  subst Y'
  have hLEq : L = L' := PowerlessRelativeClassRowOrderCanonical.graph_unique_l
    hRaw.rowGraph hRaw'.rowGraph
  subst L'
  exact SecondOrderWellOrderEndExtensionUnique.unique_l hRaw.extension hRaw'.extension

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderCandidateUnique
