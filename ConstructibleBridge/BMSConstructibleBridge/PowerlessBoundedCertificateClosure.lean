import BMSConstructibleBridge.PowerlessBoundedCertificate
import BMSConstructibleBridge.PowerlessNaturalBounds

/-!
# 实际有限证书的合并与生成闭包

先取内部自然数的共同界，再在该界中分离实际并集或添点集合。
每一步都保留自然数界和局部生成规则，不用外部有限集合代替证书。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCertificateClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessBoundedCertificate

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem empty_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) :
    certificate_l ω e T t₁ t₂ t₃ e :=
  ⟨⟨e, PowerlessNatural.zero_mem_l hℳ hω he, fun _ hx => hx⟩, fun c hc => (he c hc).elim⟩

theorem union_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ D E : carrier_l ℳ} (hω : omega_l ω)
    (hD : certificate_l ω e T t₁ t₂ t₃ D) (hE : certificate_l ω e T t₁ t₂ t₃ E) :
    ∃ K, certificate_l ω e T t₁ t₂ t₃ K ∧ subset_l D K ∧ subset_l E K := by
  obtain ⟨n, hn, hDn⟩ := hD.1
  obtain ⟨m, hm, hEm⟩ := hE.1
  obtain ⟨k, hk, hnk, hmk⟩ := PowerlessNaturalBounds.upper_l hℳ hω hn hm
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases D (fun _ => E), free := fun _ => k }
  let φ : Formula ℒ [] [.set, .set, .set] := .disj
    (SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here)))
    (SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there (.there .here))))
  have h : ∀ x, φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) ↔
      member_l ℳ x D ∨ member_l ℳ x E := by
    intro x
    simp only [φ, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  obtain ⟨K, hK⟩ := PowerlessComprehension.separation_l hℳ φ η k
  have h₀ : ∀ x, member_l ℳ x K ↔ member_l ℳ x D ∨ member_l ℳ x E := by
    intro x
    constructor
    · intro hx
      exact (h x).mp ((hK x).mp hx).2
    · intro hx
      exact (hK x).mpr ⟨hx.elim (fun hx => hnk x (hDn x hx)) (fun hx => hmk x (hEm x hx)), (h x).mpr hx⟩
  have hDK : subset_l D K := fun x hx => (h₀ x).mpr (Or.inl hx)
  have hEK : subset_l E K := fun x hx => (h₀ x).mpr (Or.inr hx)
  exact ⟨K, ⟨⟨k, hk, fun x hx => ((hK x).mp hx).1⟩,
    fun c hc => ((h₀ c).mp hc).elim (fun hc => monotone_l hDK (hD.2 c hc))
      (fun hc => monotone_l hEK (hE.2 c hc))⟩, hDK, hEK⟩

theorem extend_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ D c : carrier_l ℳ} (hω : omega_l ω)
    (hD : certificate_l ω e T t₁ t₂ t₃ D) (hc : member_l ℳ c ω) (hC : step_l ω e T t₁ t₂ t₃ D c) :
    ∃ E, certificate_l ω e T t₁ t₂ t₃ E ∧ member_l ℳ c E ∧ subset_l D E := by
  obtain ⟨n, hn, hDn⟩ := hD.1
  obtain ⟨k, hk, hnk, hck⟩ := PowerlessNaturalBounds.strict_l hℳ hω hn hc
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases D (fun _ => c), free := fun _ => k }
  let φ : Formula ℒ [] [.set, .set, .set] := .disj
    (SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here)))
    (.equal (.fvar .here) (.fvar (.there (.there .here))))
  have h : ∀ x, φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) ↔
      member_l ℳ x D ∨ x = c := by
    intro x
    simp only [φ, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  obtain ⟨E, hE⟩ := PowerlessComprehension.separation_l hℳ φ η k
  have h₀ : ∀ x, member_l ℳ x E ↔ member_l ℳ x D ∨ x = c := by
    intro x
    constructor
    · intro hx
      exact (h x).mp ((hE x).mp hx).2
    · intro hx
      exact (hE x).mpr ⟨hx.elim
        (fun hx => PowerlessNaturalOrder.member_transitive_l hℳ hω k hk n x hnk (hDn x hx))
        (fun hx => hx.symm ▸ hck), (h x).mpr hx⟩
  have hDE : subset_l D E := fun x hx => (h₀ x).mpr (Or.inl hx)
  refine ⟨E, ⟨⟨k, hk, fun x hx => ((hE x).mp hx).1⟩, ?_⟩, (h₀ c).mpr (Or.inr rfl), hDE⟩
  intro x hx
  rcases (h₀ x).mp hx with hx | rfl
  · exact monotone_l hDE (hD.2 x hx)
  · exact monotone_l hDE hC

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) :
    recognizes_l ω e T t₁ t₂ t₃ e := by
  obtain ⟨D, hD, he₀, _⟩ := extend_l hℳ hω (empty_l hℳ hω he)
    (PowerlessNatural.zero_mem_l hℳ hω he) (Or.inl rfl)
  exact ⟨D, hD, he₀⟩

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ i j c : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hc : PowerlessFormulaConstructor.constructor_l ω e T e i j c) : recognizes_l ω e T t₁ t₂ t₃ c := by
  obtain ⟨D, hD, hc₀, _⟩ := extend_l hℳ hω (empty_l hℳ hω he)
    (PowerlessFormulaConstructor.natural_l hℳ hω he hT hc) (Or.inr (Or.inl ⟨i, j, hc⟩))
  exact ⟨D, hD, hc₀⟩

theorem equal_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ i j c : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hc : PowerlessFormulaConstructor.constructor_l ω e T t₁ i j c) : recognizes_l ω e T t₁ t₂ t₃ c := by
  obtain ⟨D, hD, hc₀, _⟩ := extend_l hℳ hω (empty_l hℳ hω he)
    (PowerlessFormulaConstructor.natural_l hℳ hω he hT hc) (Or.inr (Or.inr (Or.inl ⟨i, j, hc⟩)))
  exact ⟨D, hD, hc₀⟩

theorem nand_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ a b c : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (ha : recognizes_l ω e T t₁ t₂ t₃ a) (hb : recognizes_l ω e T t₁ t₂ t₃ b)
    (hc : PowerlessFormulaConstructor.constructor_l ω e T t₂ a b c) : recognizes_l ω e T t₁ t₂ t₃ c := by
  obtain ⟨D, hD, ha⟩ := ha
  obtain ⟨E, hE, hb⟩ := hb
  obtain ⟨K, hK, hDK, hEK⟩ := union_l hℳ hω hD hE
  obtain ⟨H, hH, hc₀, _⟩ := extend_l hℳ hω hK (PowerlessFormulaConstructor.natural_l hℳ hω he hT hc)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, hDK a ha, hEK b hb, hc⟩))))
  exact ⟨H, hH, hc₀⟩

theorem bounded_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ i j b c : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hb : recognizes_l ω e T t₁ t₂ t₃ b) (hc : PowerlessBoundedCode.code_l ω e T t₂ t₃ i j b c) :
    recognizes_l ω e T t₁ t₂ t₃ c := by
  obtain ⟨D, hD, hb⟩ := hb
  have hc₀ : ThirdOrderSemantics.member_l ℳ c ω := by
    obtain ⟨_, _, _, _, _, _, _, hc⟩ := hc
    exact PowerlessFormulaConstructor.natural_l hℳ hω he hT hc
  obtain ⟨E, hE, hc₁, _⟩ := extend_l hℳ hω hD hc₀ (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, b, hb, hc⟩))))
  exact ⟨E, hE, hc₁⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBoundedCertificateClosure
