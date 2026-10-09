import BMSConstructibleBridge.PowerlessRelativeFiniteProgramPair

/-! # 绑定参数上的真实程序配对桥

新词和长度作为绑定变量时，只开放算子参数尾，保持输入／输出首槽。
复用同词配对的实际构造；本模块是对象配对闭包的语义辅助，不单独
冒充原 Z₂ 推导，也不抽取 Type 层见证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundPair

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l)
open PowerlessRelativeFiniteProgramBoundOutput (run_l prefix_m prefix_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω w n Q e t₀ t₁ t₂ a k x l z : Term ℒ Γ Δ .set)
    (hB : ∀ y, mem_l hℳ y (B.eval η) → ∀ u, mem_l hℳ u y → mem_l hℳ u (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : ω.eval η = K.omega) (he : ∀ y, ¬mem_l hℳ y (e.eval η))
    (ha : PowerlessRelativeFiniteProgramStep.record_l (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hwC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (w.eval η))
    (hQ : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (Q.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (ht : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hφ : functional_l φ (parameters_l η) (B.eval η))
    (hn : mem_l hℳ (n.eval η) K.omega)
    (hQω : ∀ q, mem_l hℳ q (Q.eval η) ↔
      PowerlessRelativeFiniteProgramAlphabet.instruction_l (C.eval η) (ω.eval η)
        (t₀.eval η) (t₁.eval η) (t₂.eval η) q)
    (hx : run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (x.eval η))
    (hz : run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (l.eval η) (z.eval η)) :
    ∃ S v q y p, ordered_l (ℳ := 𝒱) (x.eval η) (z.eval η) y ∧
      ordered_l (ℳ := 𝒱) (k.eval η) (l.eval η) p ∧ ordered_l (ℳ := 𝒱) (t₂.eval η) p q ∧
        PowerlessRelativeFiniteProgramWordAppend.append_l
          (B.eval η) (w.eval η) (n.eval η) (Q.eval η) q S v ∧
            run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) v (e.eval η)
              (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) S (n.eval η) y := by
  let ξ := PowerlessSourceOpening.env_l η
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  let ψ := prefix_m Γ.length φ
  have ht' (s : Term ℒ Γ Δ .set) : (t s).eval ξ = s.eval η :=
    PowerlessSourceRebinding.term_l s η
  have hφ' : functional_l ψ ξ (B.eval η) := by
    simpa only [ψ, ξ, functional_l, prefix_formula_l] using hφ
  have hx' : run_l ψ ξ (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) (x.eval η) := by
    simpa only [ψ, ξ, run_l, PowerlessRelativeFiniteProgramStep.step_l,
      PowerlessRelativeFiniteProgramStep.good_l, PowerlessRelativeFiniteProgramStore.store_l,
      PowerlessRelativeFiniteProgramInstruction.computed_l,
      PowerlessRelativeFiniteProgramInstruction.good_l, prefix_formula_l] using hx
  have hz' : run_l ψ ξ (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
      (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (l.eval η) (z.eval η) := by
    simpa only [ψ, ξ, run_l, PowerlessRelativeFiniteProgramStep.step_l,
      PowerlessRelativeFiniteProgramStep.good_l, PowerlessRelativeFiniteProgramStore.store_l,
      PowerlessRelativeFiniteProgramInstruction.computed_l,
      PowerlessRelativeFiniteProgramInstruction.good_l, prefix_formula_l] using hz
  obtain ⟨S, v, q, y, p, hxy, hkl, hqp, hv, hy⟩ :=
    PowerlessRelativeFiniteProgramPair.exists_l K ψ ξ
      (t B) (t C) (t ω) (t w) (t n) (t Q) (t e) (t t₀) (t t₁) (t t₂) (t a)
        (t k) (t x) (t l) (t z)
      (by simpa only [ht'] using hB) (by simpa only [ht'] using hC)
      (by simpa only [ht'] using hω) (by simpa only [ht'] using he)
      (by simpa only [ht'] using ha) (by simpa only [ht'] using hwC)
      (by simpa only [ht'] using hQ) (by simpa only [ht'] using hw)
      (by simpa only [ht'] using ht) (by simpa only [ht'] using hφ')
      (by simpa only [ht'] using hn) (by simpa only [ht'] using hQω)
      (by simpa only [ht'] using hx') (by simpa only [ht'] using hz')
  refine ⟨S, v, q, y, p, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ht'] using hxy
  · simpa only [ht'] using hkl
  · simpa only [ht'] using hqp
  · simpa only [ht'] using hv
  · simpa only [ht', ψ, ξ, run_l, PowerlessRelativeFiniteProgramStep.step_l,
      PowerlessRelativeFiniteProgramStep.good_l, PowerlessRelativeFiniteProgramStore.store_l,
      PowerlessRelativeFiniteProgramInstruction.computed_l,
      PowerlessRelativeFiniteProgramInstruction.good_l, prefix_formula_l] using hy

#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramBoundPair
