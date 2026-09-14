import BMSConstructibleBridge.PowerlessLevyCertificate

/-!
# 层级证书的实际合并、扩充与层号单调性

在内部自然数共同界中分离记录集。添入新判断后，用记录编码的单射性
逐项检查新表；提高根层号只放宽局部上界，不增添同码自依赖规则。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyCertificateClosure

open Logic FirstOrder ThirdOrderSemantics PowerlessLevyEntry PowerlessLevyCertificate

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem empty_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) :
    certificate_l ω e T t₁ t₂ t₃ e := by
  refine ⟨⟨e, PowerlessNatural.zero_mem_l hℳ hω he, fun _ hx => hx⟩, ?_⟩
  rintro _ _ _ ⟨z, hz, _⟩
  exact (he z hz).elim

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
  have h : ∀ z, φ.satisfies ((PowerlessComprehension.env_l η).pushFree z) ↔
      member_l ℳ z D ∨ member_l ℳ z E := by
    intro z
    simp only [φ, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  obtain ⟨K, hK⟩ := PowerlessComprehension.separation_l hℳ φ η k
  have h₀ : ∀ z, member_l ℳ z K ↔ member_l ℳ z D ∨ member_l ℳ z E := by
    intro z
    constructor
    · intro hz
      exact (h z).mp ((hK z).mp hz).2
    · intro hz
      exact (hK z).mpr ⟨hz.elim (fun hz => hnk z (hDn z hz)) (fun hz => hmk z (hEm z hz)), (h z).mpr hz⟩
  have hDK : subset_l D K := fun z hz => (h₀ z).mpr (Or.inl hz)
  have hEK : subset_l E K := fun z hz => (h₀ z).mpr (Or.inr hz)
  refine ⟨K, ⟨⟨k, hk, fun z hz => ((hK z).mp hz).1⟩, ?_⟩, hDK, hEK⟩
  rintro c n p ⟨z, hz, hC⟩
  rcases (h₀ z).mp hz with hz | hz
  · obtain ⟨hp, hc⟩ := hD.2 c n p ⟨z, hz, hC⟩
    exact ⟨hp, PowerlessLevyRule.monotone_l hDK hc⟩
  · obtain ⟨hp, hc⟩ := hE.2 c n p ⟨z, hz, hC⟩
    exact ⟨hp, PowerlessLevyRule.monotone_l hEK hc⟩

theorem extend_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ D c n p : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : certificate_l ω e T t₁ t₂ t₃ D) (hc : member_l ℳ c ω) (hn : member_l ℳ n ω)
    (hp : member_l ℳ p ω) (hP : polarity_l e t₁ p) (hC : PowerlessLevyRule.step_l ω e T t₁ t₂ t₃ D c n p) :
    ∃ E, certificate_l ω e T t₁ t₂ t₃ E ∧ entry_l ω e T E c n p ∧ subset_l D E := by
  obtain ⟨z, hz, hZ⟩ := PowerlessFormulaConstructor.exists_l hℳ hω he hT hc hn hp
  obtain ⟨m, hm, hDm⟩ := hD.1
  obtain ⟨k, hk, hmk, hzk⟩ := PowerlessNaturalBounds.strict_l hℳ hω hm hz
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases D (fun _ => z), free := fun _ => k }
  let φ : Formula ℒ [] [.set, .set, .set] := .disj
    (SecondOrderObjectSyntax.member_m (.fvar .here) (.fvar (.there .here)))
    (.equal (.fvar .here) (.fvar (.there (.there .here))))
  have h : ∀ y, φ.satisfies ((PowerlessComprehension.env_l η).pushFree y) ↔
      member_l ℳ y D ∨ y = z := by
    intro y
    simp only [φ, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  obtain ⟨E, hE⟩ := PowerlessComprehension.separation_l hℳ φ η k
  have h₀ : ∀ y, member_l ℳ y E ↔ member_l ℳ y D ∨ y = z := by
    intro y
    constructor
    · intro hy
      exact (h y).mp ((hE y).mp hy).2
    · intro hy
      exact (hE y).mpr ⟨hy.elim
        (fun hy => PowerlessNaturalOrder.member_transitive_l hℳ hω k hk m y hmk (hDm y hy))
        (fun hy => hy.symm ▸ hzk), (h y).mpr hy⟩
  have hDE : subset_l D E := fun y hy => (h₀ y).mpr (Or.inl hy)
  refine ⟨E, ⟨⟨k, hk, fun y hy => ((hE y).mp hy).1⟩, ?_⟩,
    ⟨z, (h₀ z).mpr (Or.inr rfl), hZ⟩, hDE⟩
  rintro d m q ⟨y, hy, hY⟩
  rcases (h₀ y).mp hy with hy | rfl
  · obtain ⟨hq, hd⟩ := hD.2 d m q ⟨y, hy, hY⟩
    exact ⟨hq, PowerlessLevyRule.monotone_l hDE hd⟩
  · obtain ⟨rfl, rfl, rfl⟩ := PowerlessFormulaConstructor.injective_l hℳ hω he hT hY hZ
    exact ⟨hP, PowerlessLevyRule.monotone_l hDE hC⟩

theorem base_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c n p : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hn : member_l ℳ n ω) (hp : member_l ℳ p ω) (hP : polarity_l e t₁ p)
    (hc : PowerlessBoundedCertificate.recognizes_l ω e T t₁ t₂ t₃ c) :
    class_l ω e T t₁ t₂ t₃ c n p := by
  obtain ⟨D, hD, hc₀⟩ := hc
  have hc₁ := PowerlessBoundedCertificate.natural_l hℳ hω hD hc₀
  obtain ⟨E, hE, h, _⟩ := extend_l hℳ hω he hT (empty_l hℳ hω he)
    hc₁ hn hp hP (Or.inl ⟨D, hD, hc₀⟩)
  exact ⟨E, hE, h⟩

theorem monotone_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c n m p : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hm : member_l ℳ m ω) (hnm : subset_l n m) (h : class_l ω e T t₁ t₂ t₃ c n p) :
    class_l ω e T t₁ t₂ t₃ c m p := by
  obtain ⟨D, hD, hc⟩ := h
  obtain ⟨hc₀, _, hp⟩ := PowerlessLevyEntry.natural_l hc
  obtain ⟨hP, hC⟩ := hD.2 c n p hc
  obtain ⟨E, hE, h, _⟩ := extend_l hℳ hω he hT hD hc₀ hm hp hP (PowerlessLevyRule.level_l hnm hC)
  exact ⟨E, hE, h⟩

theorem raise_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ c n m p q : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hn : member_l ℳ n ω) (hmn : member_l ℳ m n) (hp : member_l ℳ p ω)
    (hP : polarity_l e t₁ p) (h : class_l ω e T t₁ t₂ t₃ c m q) :
    class_l ω e T t₁ t₂ t₃ c n p := by
  obtain ⟨D, hD, hc⟩ := h
  obtain ⟨E, hE, h, _⟩ := extend_l hℳ hω he hT hD (PowerlessLevyEntry.natural_l hc).1 hn hp hP
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, q, hmn, hc⟩))))
  exact ⟨E, hE, h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessLevyCertificateClosure
