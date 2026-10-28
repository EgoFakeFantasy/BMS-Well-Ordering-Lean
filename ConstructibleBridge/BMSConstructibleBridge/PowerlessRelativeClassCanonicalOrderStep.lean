import BMSConstructibleBridge.PowerlessLegacyMemberDefCanonicalAmbient
import BMSConstructibleBridge.PowerlessRelativeClassWellOrderEndExtension

/-! # 规范候选到完整后继扩张的实际接口

步骤参数保留同一 Sat 图；对其所有读值等价的图，步骤关系不变。
候选的内部辅助表示全部由规范规格固定。最终扩张保留完整成员规格、
环境良序和旧序初段，未使用一般 Collection 或实码选择。
尚未给出跨层历史或最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalOrderStep

open Logic FirstOrder ThirdOrderSemantics
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, SecondOrderQuotient.mem_l hℳ x B →
    ∀ y, SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B}

local notation "𝒞" => structure_l hℳ B hBase
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def candidate_l (ω A P R D L : type_l hℳ B) : Prop :=
  ∃ S I J U Q Y : type_l hℳ B,
    PowerlessRelativeClassSatisfactionIndexCanonical.spec_l (ℳ₀ := 𝒞) ω A P S I J U ∧
    (∀ t x, value_l (ℳ := 𝒱) Q.val t x ↔ SecondOrderQuotient.mem_l hℳ t J.val ∧
      SecondOrderQuotient.mem_l hℳ x A.val ∧ PowerlessRelativeClassSatisfactionAllSlots.query_l
        (ℳ₀ := 𝒱) ω.val A.val S.val I.val R.val t x) ∧
    PowerlessRelativeClassRowOrderCanonical.family_l (ℳ₀ := 𝒞) J A Q Y ∧
    PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) J.val U.val A.val Q.val Y.val L.val ∧
    subset_l (ℳ := 𝒱) D.val Y.val ∧ wellOrder_l (ℳ := 𝒱) Y.val L.val

def step_l (ω A P R D E : type_l hℳ B) : Prop :=
  ∃ L : type_l hℳ B, candidate_l (hBase := hBase) ω A P R D L ∧
    SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒱) A.val D.val P.val L.val E.val

theorem candidate_congr_l {ω A P R R' D L : type_l hℳ B}
    (hR : ∀ c f, value_l (ℳ := 𝒱) R.val c f ↔ value_l (ℳ := 𝒱) R'.val c f) :
    candidate_l (hBase := hBase) ω A P R D L ↔ candidate_l (hBase := hBase) ω A P R' D L := by
  have transfer {T T' : type_l hℳ B}
      (h : ∀ c f, value_l (ℳ := 𝒱) T.val c f ↔ value_l (ℳ := 𝒱) T'.val c f)
      (hCandidate : candidate_l (hBase := hBase) ω A P T D L) :
      candidate_l (hBase := hBase) ω A P T' D L := by
    obtain ⟨S, I, J, U, Q, Y, hIndex, hRead, hRows, hGraph, hSubset, hOrder⟩ := hCandidate
    refine ⟨S, I, J, U, Q, Y, hIndex, ?_, hRows, hGraph, hSubset, hOrder⟩
    intro t x
    exact (hRead t x).trans (and_congr Iff.rfl (and_congr Iff.rfl
      (PowerlessRelativeClassSatisfactionQueryUnique.slots_congr_l
        (fun _ => Iff.rfl) (fun _ => Iff.rfl) h)))
  exact ⟨transfer hR, transfer (fun c f => (hR c f).symm)⟩

theorem candidate_unique_l {ω A P R D L L' : type_l hℳ B}
    (h : candidate_l (hBase := hBase) ω A P R D L)
    (h' : candidate_l (hBase := hBase) ω A P R D L') : L = L' := by
  obtain ⟨S, I, J, U, Q, Y, hIndex, hRead, hRows, hGraph, _, _⟩ := h
  obtain ⟨S', I', J', U', Q', Y', hIndex', hRead', hRows', hGraph', _, _⟩ := h'
  obtain ⟨hS, hI, hJ, hU⟩ := PowerlessRelativeClassSatisfactionIndexCanonical.unique_l hIndex hIndex'
  subst S'
  subst I'
  subst J'
  subst U'
  have hQ t x := (hRead t x).trans (hRead' t x).symm
  exact (PowerlessRelativeClassSatisfactionAllSlotsCanonical.unique_l
    hIndex hIndex' hQ hRows hRows' hGraph hGraph').2.2.2.2.2

theorem step_congr_l {ω A P R R' D E : type_l hℳ B}
    (hR : ∀ c f, value_l (ℳ := 𝒱) R.val c f ↔ value_l (ℳ := 𝒱) R'.val c f) :
    step_l (hBase := hBase) ω A P R D E ↔ step_l (hBase := hBase) ω A P R' D E :=
  exists_congr fun L => and_congr (candidate_congr_l (L := L) hR) Iff.rfl

theorem unique_l {ω A P R D E E' : type_l hℳ B}
    (h : step_l (hBase := hBase) ω A P R D E) (h' : step_l (hBase := hBase) ω A P R D E') : E = E' := by
  obtain ⟨L, hL, hGraph⟩ := h
  obtain ⟨L', hL', hGraph'⟩ := h'
  have hEq := candidate_unique_l hL' hL
  subst L'
  exact Subtype.ext (SecondOrderWellOrderEndExtensionUnique.unique_l hGraph hGraph')

theorem exists_l {ω A P R D : type_l hℳ B}
    (hP : wellOrder_l (ℳ := 𝒱) A.val P.val) (hAD : subset_l (ℳ := 𝒱) A.val D.val)
    (hCandidate : ∃ L, candidate_l (hBase := hBase) ω A P R D L) :
    ∃ E : type_l hℳ B, step_l (hBase := hBase) ω A P R D E ∧ wellOrder_l (ℳ := 𝒱) D.val E.val ∧
      (∀ x y, SecondOrderQuotient.mem_l hℳ x A.val → SecondOrderQuotient.mem_l hℳ y A.val →
        (value_l (ℳ := 𝒱) E.val x y ↔ value_l (ℳ := 𝒱) P.val x y)) ∧
      (∀ x y, SecondOrderQuotient.mem_l hℳ x A.val → value_l (ℳ := 𝒱) E.val y x →
        SecondOrderQuotient.mem_l hℳ y A.val) := by
  obtain ⟨L, hL⟩ := hCandidate
  have hCopy := hL
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hSubset, hOrder⟩ := hCopy
  have hD := PowerlessRelativeClassAmbientWellOrder.of_subset_l hOrder hSubset
  obtain ⟨E, ⟨hGraph, hE⟩, _⟩ := PowerlessRelativeClassWellOrderEndExtension.exists_unique_l
    (hBase := hBase) hP hD
  have hRead := SecondOrderWellOrderEndExtensionUnique.reading_l hGraph
  exact ⟨E, ⟨L, hL, hGraph⟩, hE, fun x y hx hy => SecondOrderWellOrderEndExtension.old_l hAD hRead hx hy,
    fun x y hx hyx => SecondOrderWellOrderEndExtension.initial_l hRead hx hyx⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalOrderStep
