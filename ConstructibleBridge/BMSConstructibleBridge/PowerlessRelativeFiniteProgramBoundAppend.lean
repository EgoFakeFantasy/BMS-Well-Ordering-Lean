import BMSConstructibleBridge.PowerlessRelativeFiniteProgramAppendExists

/-! # 原末态见证带绑定参数的程序延拓

旧 run 中的历史长度和新指令都是对象量词的见证。本辅助模块将
同一历史开放到参数环境，复用原程序存在性定理，再传回原算子。
这里只提供语义装配接口，由后续合法调用的原 Z₂ 对象出口消费。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundAppend

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l computed_l good_l)
open PowerlessRelativeFiniteProgramBoundOutput (prefix_m prefix_formula_l step_m step_formula_l run_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def history_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (B C ω w n e t₀ t₁ t₂ a S D F : type_l hℳ) : Prop :=
  PowerlessNatural.successor_l (ℳ := 𝒱) n S ∧ map_l (ℳ := 𝒱) F S D ∧
    value_l (ℳ := 𝒱) F e a ∧ ∀ i j x z, mem_l hℳ i n →
      PowerlessNatural.successor_l (ℳ := 𝒱) i j → value_l (ℳ := 𝒱) F i x →
        value_l (ℳ := 𝒱) F j z →
          PowerlessRelativeFiniteProgramStep.step_l φ η B C ω w e t₀ t₁ t₂ x z

theorem history_open_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w n e t₀ t₁ t₂ a S : Term ℒ Γ Δ .set) (D F : type_l hℳ) :
    PowerlessDefinableFiniteTrace.trace_l (step_m φ B C ω w e t₀ t₁ t₂)
      (PowerlessSourceOpening.env_l η) (e.eval η) (a.eval η) (n.eval η) (S.eval η) D F ↔
        history_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
          (n.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (S.eval η) D F := by
  simp only [PowerlessDefinableFiniteTrace.trace_l, history_l, step_formula_l K]
  rfl

theorem exists_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w n Q q S e t₀ t₁ t₂ a : Term ℒ Γ Δ .set) {D F s E f y : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ z, mem_l hℳ z x → mem_l hℳ z (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hwC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (w.eval η))
    (hnC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (n.eval η))
    (hQC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hq : mem_l hℳ (q.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ (parameters_l η) (B.eval η))
    (hn : mem_l hℳ (n.eval η) K.omega)
    (hDC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) D)
    (hFC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) F)
    (hF : history_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
      (n.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (S.eval η) D F)
    (hs : value_l (ℳ := 𝒱) F (n.eval η) s)
    (hValid : PowerlessRelativeFiniteProgramStep.valid_l (B.eval η) (ω.eval η) (n.eval η) E f s)
    (hy : computed_l φ (parameters_l η) (B.eval η) (C.eval η) f
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) y) :
    ∃ v, PowerlessRelativeFiniteProgramWordAppend.append_l
      (B.eval η) (w.eval η) (n.eval η) (Q.eval η) (q.eval η) (S.eval η) v ∧
        run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) v (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (S.eval η) (n.eval η) y := by
  let ξ := PowerlessSourceOpening.env_l η
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  let φ' := prefix_m Γ.length φ
  have ht (u : Term ℒ Γ Δ .set) : (t u).eval ξ = u.eval η :=
    PowerlessSourceRebinding.term_l u η
  have hFunctional' : functional_l φ' ξ (B.eval η) := by
    simpa only [φ', ξ, functional_l, prefix_formula_l] using hFunctional
  have hy' : computed_l φ' ξ (B.eval η) (C.eval η) f
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (q.eval η) y := by
    simpa only [φ', ξ, computed_l, good_l, prefix_formula_l] using hy
  have hF' := (history_open_l K φ η B C ω w n e t₀ t₁ t₂ a S D F).mpr hF
  obtain ⟨v, hAppend, hRun⟩ := PowerlessRelativeFiniteProgramAppendExists.exists_l K φ' ξ
    (t B) (t C) (t ω) (t w) (t n) (t Q) (t q) (t S) (t e) (t t₀) (t t₁) (t t₂) (t a)
    (by simpa only [ht] using hBase) (by simpa only [ht] using hC)
    (by simpa only [ht] using hω) (by simpa only [ht] using he)
    (by simpa only [ht] using hInitial) (by simpa only [ht] using hwC)
    (by simpa only [ht] using hnC) (by simpa only [ht] using hQC)
    (by simpa only [ht] using hw) (by simpa only [ht] using hq)
    (by simpa only [ht] using hTags) (by simpa only [ht] using hFunctional')
    (by simpa only [ht] using hn) (by simpa only [ht] using hDC)
    (by simpa only [ht] using hFC) (by simpa only [step_m, φ', t, ξ, ht] using hF')
    (by simpa only [ht] using hs) (by simpa only [ht] using hValid)
    (by simpa only [ht] using hy')
  refine ⟨v, ?_, ?_⟩
  · simpa only [ht] using hAppend
  · simpa only [run_l, PowerlessRelativeFiniteProgramStep.step_l,
      PowerlessRelativeFiniteProgramStep.good_l, PowerlessRelativeFiniteProgramStore.store_l,
      computed_l, good_l, ht, φ', ξ, prefix_formula_l] using hRun

#print axioms history_open_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundAppend
