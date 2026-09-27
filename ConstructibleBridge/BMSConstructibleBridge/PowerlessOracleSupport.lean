import BMSConstructibleBridge.PowerlessOracleClosure
import BMSConstructibleBridge.PowerlessFiniteSupport
import YesMetaZFC.Automation.ModelClosure

/-!
# 低层公式证书构造的有限核心支持

对每个实际原公式 B，收集和添入都有真实 Hilbert 推导及有限公理列表。
任意小结构只需满足该列表即可使用对应原闭句；这里尚未证明指定层
满足列表，也不将此有限性视为逐层真值正确性或稳定对存在性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleSupport

open Logic FirstOrder ThirdOrderSemantics PowerlessTruthOracle

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def collection_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  let v (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  .imp
    (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (q A))
      (.existsE .set (.conj
        (certificate_m B (v ω) (v e) (v T) (v t₁) (v t₂) (v t₃) (v n) (.bvar .here))
        (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))))))
    (.existsE .set (.conj
      (certificate_m B (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q n) (.bvar .here))
      (ThirdOrderTheory.subset_m (q A) (.bvar .here))))

def extension_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n D p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .imp (.conj (certificate_m B ω e T t₁ t₂ t₃ n D)
    (.conj (SecondOrderObjectSyntax.member_m c ω)
      (.disj (instance_m B ω e T t₁ t₂ t₃ n p c f)
        (PowerlessTruthStep.step_m ω e T t₁ t₂ t₃ D p c f))))
    (accepts_m B ω e T t₁ t₂ t₃ n p c f)

theorem collection_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n A : Term ℒ Γ Δ .set) :
    (collection_m B ω e T t₁ t₂ t₃ n A).satisfies η := by
  simp only [collection_m, Formula.satisfies, PowerlessOracleClosure.certificate_formula_l B hℳ,
    subset_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  exact PowerlessOracleClosure.collect_l B hℳ

theorem extension_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t₁ t₂ t₃ n D p c f : Term ℒ Γ Δ .set) :
    (extension_m B ω e T t₁ t₂ t₃ n D p c f).satisfies η := by
  simp only [extension_m, Formula.satisfies, PowerlessOracleClosure.certificate_formula_l B hℳ,
    PowerlessOracleClosure.accepts_formula_l B hℳ, instance_formula_l,
    PowerlessTruthClosure.step_formula_l hℳ, SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro h
  obtain ⟨E, _, hE, he⟩ := PowerlessOracleClosure.adjoin_l B hℳ h.1 h.2.1 h.2.2
  exact ⟨E, hE, he⟩

def collection_formula_m (B : Formula ℒ [] context_m) :
    Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
  collection_m B (.fvar .here)
    (.fvar (.there .here))
    (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))

def extension_formula_m (B : Formula ℒ [] context_m) :
    Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
  extension_m B (.fvar .here)
    (.fvar (.there .here))
    (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))

def sentence_m (B : Formula ℒ [] context_m) : Sentence ℒ :=
  .conj (Metatheory.Formula.forall_close (collection_formula_m B))
    (Metatheory.Formula.forall_close (extension_formula_m B))

attribute [local irreducible] collection_formula_m extension_formula_m Metatheory.Formula.forall_close

theorem sentence_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : (sentence_m B).TrueIn ℳ := by
  constructor
  · apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff (ℳ := ℳ) (collection_formula_m B)).mpr
    intro η
    unfold collection_formula_m
    exact collection_l B hℳ η _ _ _ _ _ _ _ _
  · apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff (ℳ := ℳ) (extension_formula_m B)).mpr
    intro η
    unfold extension_formula_m
    exact extension_l B hℳ η _ _ _ _ _ _ _ _ _ _ _

theorem finite_m (B : Formula ℒ [] context_m) :
    Nonempty (Derives.FiniteTheorySupport PowerlessTheory.theory_m [] (sentence_m B)) :=
  PowerlessFiniteSupport.finite_m (fun _ hℳ => sentence_l B hℳ)

noncomputable def support_m (B : Formula ℒ [] context_m) :
    Derives.FiniteTheorySupport PowerlessTheory.theory_m [] (sentence_m B) :=
  Classical.choice (finite_m B)

def theory_m (B : Formula ℒ [] context_m) : Theory ℒ := Theory.ofList (support_m B).sentences

theorem core_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) : Theory.Models ℳ (theory_m B) :=
  fun φ hφ => hℳ φ ((support_m B).subset φ hφ)

theorem models_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (theory_m B)) : (sentence_m B).TrueIn ℳ :=
  (support_m B).derivation.semantically_entails ℳ hℳ

/-- 只使用有限支持模型假设，返回原公式在任意自由参数环境中的满足性。 -/
theorem collection_model_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (theory_m B))
    (η : Env ℳ [] [.set, .set, .set, .set, .set, .set, .set, .set]) :
    (collection_formula_m B).satisfies η :=
  (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff (ℳ := ℳ) (collection_formula_m B)).mp
    (models_l B hℳ).1 η

theorem extension_model_l (B : Formula ℒ [] context_m)
    {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ (theory_m B))
    (η : Env ℳ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set]) :
    (extension_formula_m B).satisfies η :=
  (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff (ℳ := ℳ) (extension_formula_m B)).mp
    (models_l B hℳ).2 η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleSupport
