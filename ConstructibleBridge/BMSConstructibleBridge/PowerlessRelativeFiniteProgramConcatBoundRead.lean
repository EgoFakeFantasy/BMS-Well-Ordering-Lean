import BMSConstructibleBridge.PowerlessRelativeFiniteProgramConcatRightRead
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramConcatLeftRead
import BMSConstructibleBridge.PowerlessRelativeFiniteProgramBoundRun

/-! # 绑定拼接参数的两侧真实读数桥

将新词、加法图、长度和输出坐标作为绑定变量时，开放原参数环境，
并只在二元算子的参数尾增加槽位。读数仍属于同一原算子与实际历史。
本模块是下一存在句的语义辅助，不冒充独立的对象层完成结果。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatBoundRead

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeFiniteProgramInstruction (functional_l)
open PowerlessRelativeFiniteProgramBoundOutput (run_l prefix_m prefix_formula_l step_m run_open_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem readings_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒱 Γ Δ)
    (B C ω e t₀ t₁ t₂ a n w m z Q A r c v k l : Term ℒ Γ Δ .set)
    (hBase : ∀ x, mem_l hℳ x (B.eval η) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η))
    (hC : PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (C.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) (he : ∀ x, ¬mem_l hℳ x (e.eval η))
    (hInitial : PowerlessRelativeFiniteProgramStep.record_l
      (e.eval η) (e.eval η) (e.eval η) (a.eval η))
    (hw : map_l (ℳ := 𝒱) (w.eval η) (n.eval η) (Q.eval η))
    (hz : map_l (ℳ := 𝒱) (z.eval η) (m.eval η) (Q.eval η))
    (hTags : t₀.eval η ≠ t₁.eval η ∧ t₀.eval η ≠ t₂.eval η ∧ t₁.eval η ≠ t₂.eval η)
    (hFunctional : functional_l φ (parameters_l η) (B.eval η))
    (hn : mem_l hℳ (n.eval η) (ω.eval η)) (hm : mem_l hℳ (m.eval η) (ω.eval η))
    (hJoined : PowerlessRelativeFiniteProgramConcat.joined_l
      (B.eval η) (C.eval η) (ω.eval η) (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η)
        (n.eval η) (w.eval η) (m.eval η) (z.eval η) (Q.eval η) (A.eval η)
          (r.eval η) (c.eval η) (v.eval η)) (y : type_l hℳ) :
    (run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (w.eval η)
      (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (n.eval η) (k.eval η) y →
        run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (v.eval η)
          (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (c.eval η) (k.eval η) y) ∧
    (value_l (ℳ := 𝒱) (A.eval η) (k.eval η) (l.eval η) →
      run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (z.eval η)
        (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (m.eval η) (k.eval η) y →
          run_l φ (parameters_l η) (B.eval η) (C.eval η) (ω.eval η) (v.eval η)
            (e.eval η) (t₀.eval η) (t₁.eval η) (t₂.eval η) (a.eval η) (c.eval η) (l.eval η) y) := by
  let ξ := PowerlessSourceOpening.env_l η
  let t := @PowerlessSourceRebinding.term_m Γ Δ
  let ψ := prefix_m Γ.length φ
  have ht (s : Term ℒ Γ Δ .set) : (t s).eval ξ = s.eval η :=
    PowerlessSourceRebinding.term_l s η
  have hFunctional' : functional_l ψ ξ (B.eval η) := by
    simpa only [ψ, ξ, functional_l, prefix_formula_l] using hFunctional
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨hc, hnc⟩ := PowerlessRelativeFiniteProgramWordConcat.length_l K hωEq he (hωEq ▸ hn) hJoined.2
  have hAgree := PowerlessRelativeFiniteProgramWordConcat.prefix_l K hωEq he (hωEq ▸ hn) hJoined.2
  have hv := hJoined.2.2.2.2.2.2.2.1
  constructor
  · intro hy
    have hy' := (run_open_l K φ η B C ω w e t₀ t₁ t₂ a n k y).mpr hy
    have hRun := PowerlessRelativeFiniteProgramPrefixLength.run_transfer_l K ψ ξ
      (t B) (t C) (t ω) (t w) (t n) (t v) (t c) (t Q) (t e) (t t₀) (t t₁) (t t₂) (t a)
        (t n) (t c) (t k)
      (by simpa only [ht] using hBase) (by simpa only [ht] using hC)
      (by simpa only [ht] using hω) (by simpa only [ht] using he)
      (by simpa only [ht] using hInitial) (by simpa only [ht] using hw)
      (by simpa only [ht] using hv) (by simpa only [ht] using hTags)
      (by simpa only [ht] using hFunctional') (by simpa only [ht] using hn)
      (by simpa only [ht] using (hωEq.symm ▸ hc)) (by simpa only [ht] using hnc)
      (by simpa only [ht] using hAgree)
      (by simpa only [step_m, ψ, ξ, t, ht] using hy')
    apply (run_open_l K φ η B C ω v e t₀ t₁ t₂ a c k y).mp
    simpa only [step_m, ψ, ξ, t, ht] using hRun
  · intro hkl hy
    have hy' := (run_open_l K φ η B C ω z e t₀ t₁ t₂ a m k y).mpr hy
    have hRun := PowerlessRelativeFiniteProgramConcatRightRead.run_transfer_l K ψ ξ
      (t B) (t C) (t ω) (t e) (t t₀) (t t₁) (t t₂) (t a) (t n) (t w) (t m) (t z) (t Q)
        (t A) (t r) (t c) (t v) (t k) (t l)
      (by simpa only [ht] using hBase) (by simpa only [ht] using hC)
      (by simpa only [ht] using hω) (by simpa only [ht] using he)
      (by simpa only [ht] using hInitial) (by simpa only [ht] using hz)
      (by simpa only [ht] using hTags) (by simpa only [ht] using hFunctional')
      (by simpa only [ht] using hn) (by simpa only [ht] using hm)
      (by simpa only [ht] using hJoined) (by simpa only [ht] using hkl)
      (by simpa only [step_m, ψ, ξ, t, ht] using hy')
    apply (run_open_l K φ η B C ω v e t₀ t₁ t₂ a c l y).mp
    simpa only [step_m, ψ, ξ, t, ht] using hRun

#print axioms readings_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteProgramConcatBoundRead
