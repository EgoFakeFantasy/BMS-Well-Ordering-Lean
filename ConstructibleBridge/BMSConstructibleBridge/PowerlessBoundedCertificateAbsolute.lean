import BMSConstructibleBridge.PowerlessBoundedCodeAbsolute
import BMSConstructibleBridge.PowerlessBoundedCertificate
import BMSConstructibleBridge.PowerlessStageFiniteSubsets

/-!
# 原有界公式有限证书的绝对性

局部生成规则的见证由自然数 guard 取回；整个证书由内部有限子集闭包
取回。区分给定证书的正确性与存在一个证书，不将 D⊆B 当成 D∈B。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCertificateAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
  {ω e T : type_l B} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hI : ∀ x, member_l ℳ x ω.val → ∀ F,
    PowerlessAddition.iteration_l ω.val e.val x F → member_l ℳ F B)

include hℳ hBT hω he hT hI

theorem step_l {t₁ t₂ t₃ D c : type_l B} :
    PowerlessBoundedCertificate.step_l (ℳ := structure_l B hB) ω e T t₁ t₂ t₃ D c ↔
      PowerlessBoundedCertificate.step_l ω.val e.val T.val t₁.val t₂.val t₃.val D.val c.val := by
  have h₀ (t : type_l B) :
      (∃ a b, PowerlessFormulaConstructor.constructor_l (ℳ := structure_l B hB) ω e T t a b c) ↔
        ∃ a b, PowerlessFormulaConstructor.constructor_l ω.val e.val T.val t.val a b c.val := by
    constructor
    · rintro ⟨a, b, hc⟩
      exact ⟨a.val, b.val,
        (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hc⟩
    · rintro ⟨a, b, hc⟩
      have haB := hBT ω.val a ω.property hc.1
      have hbB := hBT ω.val b ω.property hc.2.1
      exact ⟨⟨a, haB⟩, ⟨b, hbB⟩,
        (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hc⟩
  unfold PowerlessBoundedCertificate.step_l
  apply or_congr Subtype.ext_iff
  apply or_congr (h₀ e)
  apply or_congr (h₀ t₁)
  apply or_congr
  · constructor
    · rintro ⟨a, b, ha, hb, hc⟩
      exact ⟨a.val, b.val, ha, hb,
        (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mp hc⟩
    · rintro ⟨a, b, ha, hb, hc⟩
      exact ⟨⟨a, hBT D.val a D.property ha⟩, ⟨b, hBT D.val b D.property hb⟩, ha, hb,
        (PowerlessFormulaCodeAbsolute.constructor_l hℳ hBT hω he hT hI).mpr hc⟩
  · constructor
    · rintro ⟨i, j, b, hb, hc⟩
      exact ⟨i.val, j.val, b.val, hb,
        (PowerlessBoundedCodeAbsolute.code_l hℳ hBT hω he hT hI).mp hc⟩
    · rintro ⟨i, j, b, hb, hc⟩
      have hij : member_l ℳ i ω.val ∧ member_l ℳ j ω.val := by
        obtain ⟨_, d, p, q, hd, _, _, _⟩ := hc
        exact ⟨hd.1, hd.2.1⟩
      exact ⟨⟨i, hBT ω.val i ω.property hij.1⟩, ⟨j, hBT ω.val j ω.property hij.2⟩,
        ⟨b, hBT D.val b D.property hb⟩, hb,
        (PowerlessBoundedCodeAbsolute.code_l hℳ hBT hω he hT hI).mpr hc⟩

theorem certificate_l {t₁ t₂ t₃ D : type_l B} :
    PowerlessBoundedCertificate.certificate_l (ℳ := structure_l B hB) ω e T t₁ t₂ t₃ D ↔
      PowerlessBoundedCertificate.certificate_l ω.val e.val T.val t₁.val t₂.val t₃.val D.val := by
  constructor
  · rintro ⟨⟨n, hn, hDn⟩, h⟩
    refine ⟨⟨n.val, hn, (PowerlessSourceNaturalAbsolute.subset_l hBT).mp hDn⟩, ?_⟩
    intro c hc
    exact (step_l hℳ hBT hω he hT hI).mp (h ⟨c, hBT D.val c D.property hc⟩ hc)
  · rintro ⟨⟨n, hn, hDn⟩, h⟩
    exact ⟨⟨⟨n, hBT ω.val n ω.property hn⟩, hn,
      (PowerlessSourceNaturalAbsolute.subset_l hBT).mpr hDn⟩,
      fun c hc => (step_l hℳ hBT hω he hT hI).mpr (h c.val hc)⟩

theorem recognizes_l {t₁ t₂ t₃ c : type_l B}
    (hD : ∀ n, member_l ℳ n ω.val → ∀ D, subset_l D n → member_l ℳ D B) :
    PowerlessBoundedCertificate.recognizes_l (ℳ := structure_l B hB) ω e T t₁ t₂ t₃ c ↔
      PowerlessBoundedCertificate.recognizes_l ω.val e.val T.val t₁.val t₂.val t₃.val c.val := by
  constructor
  · rintro ⟨D, h, hc⟩
    exact ⟨D.val, (certificate_l hℳ hBT hω he hT hI).mp h, hc⟩
  · rintro ⟨D, h, hc⟩
    obtain ⟨n, hn, hDn⟩ := h.1
    exact ⟨⟨D, hD n hn D hDn⟩, (certificate_l hℳ hBT hω he hT hI).mpr h, hc⟩

theorem source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (w z U t₁ t₂ t₃ c : Term ℒ Γ Δ .set)
    (hw : w.eval η = ω) (hz : z.eval η = e) (hU : U.eval η = T)
    (hD : ∀ n, member_l ℳ n ω.val → ∀ D, subset_l D n → member_l ℳ D B) :
    Formula.satisfies η (PowerlessBoundedCertificate.recognizes_m w z U t₁ t₂ t₃ c) ↔
      PowerlessBoundedCertificate.recognizes_l ω.val e.val T.val
        (t₁.eval η).val (t₂.eval η).val (t₃.eval η).val (c.eval η).val := by
  rw [PowerlessBoundedCertificate.recognizes_formula_l, hw, hz, hU]
  exact recognizes_l hℳ hBT hω he hT hI hD

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCertificateAbsolute
