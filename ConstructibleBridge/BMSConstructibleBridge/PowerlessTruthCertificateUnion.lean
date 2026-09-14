import BMSConstructibleBridge.PowerlessTruthMonotone
import BMSConstructibleBridge.PowerlessTruthCertificate

/-!
# 两个局部真值证书的并集保持

给定实际集合并的成员方程，原成员分别沿记录集单调性传入并集。
证明的是检查公式本身，不调用含 H 的语义可靠性作为接受条件。
本定理不构造任意集合多个子证书的收集上界。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthCertificateUnion

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem union_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ D E F : Term ℒ Γ Δ .set)
    (hF : ∀ r, member_l ℳ r (F.eval η) ↔ member_l ℳ r (D.eval η) ∨ member_l ℳ r (E.eval η))
    (hD : (PowerlessTruthCertificate.certificate_m ω e T t₁ t₂ t₃ D).satisfies η)
    (hE : (PowerlessTruthCertificate.certificate_m ω e T t₁ t₂ t₃ E).satisfies η) :
    (PowerlessTruthCertificate.certificate_m ω e T t₁ t₂ t₃ F).satisfies η := by
  let q (s : Term ℒ Γ Δ .set) :=
    (((s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
      SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let P (K : Term ℒ Γ Δ .set) : Prop := ∀ r : carrier_l ℳ,
    member_l ℳ r ((K.weakenBound SetTheory.SetSort.set).eval (η.pushBound r)) →
    ∃ p c f : carrier_l ℳ, PowerlessTruthRecord.record_l p c f r ∧
      member_l ℳ c ((q ω).eval ((((η.pushBound r).pushBound p).pushBound c).pushBound f)) ∧
      (PowerlessTruthStep.step_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q K)
        (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies
          ((((η.pushBound r).pushBound p).pushBound c).pushBound f)
  change P D at hD
  change P E at hE
  change P F
  have h₀ (K : Term ℒ Γ Δ .set) (hK : subset_l (K.eval η) (F.eval η)) (h : P K)
      (r : carrier_l ℳ) (hr : member_l ℳ r (K.eval η)) :
      ∃ p c f : carrier_l ℳ, PowerlessTruthRecord.record_l p c f r ∧
        member_l ℳ c ((q ω).eval ((((η.pushBound r).pushBound p).pushBound c).pushBound f)) ∧
        (PowerlessTruthStep.step_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q F)
          (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)).satisfies
            ((((η.pushBound r).pushBound p).pushBound c).pushBound f) := by
    obtain ⟨p, c, f, hp, hc, hf⟩ := h r (by rw [Term.eval_weakenBound]; exact hr)
    refine ⟨p, c, f, hp, hc, ?_⟩
    exact PowerlessTruthMonotone.step_l
      ((((η.pushBound r).pushBound p).pushBound c).pushBound f)
      (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q K) (q F)
      (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)
      (by simpa only [q, Term.eval_weakenBound] using hK) hf
  intro r hr
  rw [Term.eval_weakenBound] at hr
  rcases (hF r).mp hr with hr | hr
  · exact h₀ D (fun r hr => (hF r).mpr (Or.inl hr)) hD r hr
  · exact h₀ E (fun r hr => (hF r).mpr (Or.inr hr)) hE r hr

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthCertificateUnion
