import BMSConstructibleBridge.PowerlessTruthOracle
import BMSConstructibleBridge.PowerlessLevyCertificate
import BMSConstructibleBridge.PowerlessLevyZero
import BMSConstructibleBridge.PowerlessTruthClosure
import BMSConstructibleBridge.PowerlessOracleClosure

/-!
# 外部固定层号的部分真值公式递推

低层 Σ 的正接受和 Π 的负接受，经双向正确性给出两种真值标记。
内部层号通过真实后继关系连接；公式族本身只按宿主 Nat 有限展开。
下列极性传输已证明，但整族的分类完备性与指定层内证书存在仍待证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruth

open Logic FirstOrder ThirdOrderSemantics PowerlessTruthOracle

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def lower_l (B : Formula ℒ [] context_m) (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) : Prop :=
  ∃ m, member_l ℳ m ω ∧ PowerlessNatural.successor_l m n ∧
    PowerlessAmbientAssignments.finite_l ω f ∧
    ((PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m e ∧
      ((p = e ∧ B.satisfies (env_l ω e T t₁ t₂ t₃ m e c f)) ∨
        (p = t₁ ∧ ¬B.satisfies (env_l ω e T t₁ t₂ t₃ m e c f)))) ∨
    (PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m t₁ ∧
      ((p = t₁ ∧ B.satisfies (env_l ω e T t₁ t₂ t₃ m t₁ c f)) ∨
        (p = e ∧ ¬B.satisfies (env_l ω e T t₁ t₂ t₃ m t₁ c f)))))

def lower_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) : Term ℒ (SetTheory.SetSort.set :: Γ) Δ .set :=
    s.weakenBound SetTheory.SetSort.set
  let m : Term ℒ (.set :: Γ) Δ .set := .bvar .here
  let P := instance_m B (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) m (q e) (q c) (q f)
  let Q := instance_m B (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) m (q t₁) (q c) (q f)
  let A : Formula ℒ (.set :: Γ) Δ :=
    .conj (PowerlessLevyCertificate.class_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q c) m (q e))
      (.disj (.conj (.equal (q p) (q e)) P) (.conj (.equal (q p) (q t₁)) (.neg P)))
  let C : Formula ℒ (.set :: Γ) Δ :=
    .conj (PowerlessLevyCertificate.class_m (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q c) m (q t₁))
      (.disj (.conj (.equal (q p) (q t₁)) Q) (.conj (.equal (q p) (q e)) (.neg Q)))
  .existsE .set (.conj (SecondOrderObjectSyntax.member_m m (q ω))
    (.conj (PowerlessNaturalStep.successor_m m (q n))
      (.conj (PowerlessAmbientAssignments.finite_m (q ω) (q f)) (.disj A C))))

theorem lower_formula_l (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) :
    (lower_m B ω e T t₁ t₂ t₃ n p c f).satisfies η ↔
      lower_l B (ω.eval η) (e.eval η) (T.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (n.eval η) (p.eval η) (c.eval η) (f.eval η) := by
  simp only [lower_m, lower_l, Formula.satisfies, PowerlessNaturalStep.successor_formula_l,
    PowerlessAmbientAssignments.finite_formula_l, PowerlessLevyCertificate.class_formula_l,
    instance_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

/-- 取反分支需要低层双向正确性，不能只消费低层可靠性。 -/
theorem lower_sound_l (B : Formula ℒ [] context_m)
    {ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ} {P : Prop}
    (h₀ : ∀ m, member_l ℳ m ω → PowerlessNatural.successor_l m n →
      PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m e →
        (B.satisfies (env_l ω e T t₁ t₂ t₃ m e c f) ↔ P))
    (h₁ : ∀ m, member_l ℳ m ω → PowerlessNatural.successor_l m n →
      PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m t₁ →
        (B.satisfies (env_l ω e T t₁ t₂ t₃ m t₁ c f) ↔ ¬P))
    (h : lower_l B ω e T t₁ t₂ t₃ n p c f) : (p = e ∧ P) ∨ (p = t₁ ∧ ¬P) := by
  classical
  obtain ⟨m, hm, hn, _, h⟩ := h
  rcases h with ⟨hc, h⟩ | ⟨hc, h⟩
  · simpa only [h₀ m hm hn hc] using h
  · rw [h₁ m hm hn hc] at h
    tauto

theorem lower_complete_l (B : Formula ℒ [] context_m)
    {ω e T t₁ t₂ t₃ m n p c f : carrier_l ℳ} {P : Prop}
    (hm : member_l ℳ m ω) (hn : PowerlessNatural.successor_l m n)
    (hf : PowerlessAmbientAssignments.finite_l ω f)
    (hc : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m e ∨
      PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m t₁)
    (h₀ : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m e →
      (B.satisfies (env_l ω e T t₁ t₂ t₃ m e c f) ↔ P))
    (h₁ : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c m t₁ →
      (B.satisfies (env_l ω e T t₁ t₂ t₃ m t₁ c f) ↔ ¬P))
    (h : (p = e ∧ P) ∨ (p = t₁ ∧ ¬P)) : lower_l B ω e T t₁ t₂ t₃ n p c f := by
  classical
  refine ⟨m, hm, hn, hf, ?_⟩
  rcases hc with hc | hc
  · exact Or.inl ⟨hc, by simpa only [h₀ hc] using h⟩
  · exact Or.inr ⟨hc, by rw [h₁ hc]; tauto⟩

def lift_m (B : Formula ℒ [] context_m) : Formula ℒ [] context_m :=
  let ω : Term ℒ [] context_m .set := .fvar .here
  let e : Term ℒ [] context_m .set := .fvar (.there .here)
  let T : Term ℒ [] context_m .set := .fvar (.there (.there .here))
  let t₁ : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))
  let t₂ : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there .here))))
  let t₃ : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let n : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let p : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there .here)))))))
  let c : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
  let f : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
  PowerlessTruthOracle.accepts_m (lower_m B ω e T t₁ t₂ t₃ n p c f) ω e T t₁ t₂ t₃ n p c f

def zero_m : Formula ℒ [] context_m :=
  PowerlessTruthCertificate.accepts_m (.fvar .here) (.fvar (.there .here))
    (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
    (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
    (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))

/-- 每个外部层号给出一份实际有限原公式，不把内部层号当作外部递归指标。 -/
def formula_m : Nat → Formula ℒ [] context_m
  | 0 => zero_m
  | n + 1 => lift_m (formula_m n)

/-- 零层分类给出有界识别，从有符号有界真值构造公式族的真实起点。 -/
theorem zero_complete_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ p q c f : carrier_l ℳ} (hω : omega_l ω)
    (he : PowerlessNatural.zero_l e) (hT : PowerlessTriangular.triangular_l ω e T)
    (hC : PowerlessLevyCertificate.class_l ω e T t₁ t₂ t₃ c e q)
    (hf : PowerlessAmbientAssignments.finite_l ω f)
    (h : (p = e ∧ PowerlessBoundedTruth.truth_l ω e T t₁ t₂ t₃ c f) ∨
      (p = t₁ ∧ ¬PowerlessBoundedTruth.truth_l ω e T t₁ t₂ t₃ c f)) :
    (formula_m 0).satisfies (env_l ω e T t₁ t₂ t₃ e p c f) := by
  have hc : member_l ℳ c ω := by
    obtain ⟨D, _, hD⟩ := hC
    exact (PowerlessLevyEntry.natural_l hD).1
  rw [formula_m, zero_m, PowerlessTruthClosure.accepts_formula_l hℳ]
  exact PowerlessTruthClosure.base_l hℳ hc (PowerlessLevyZero.class_l hℳ hω he hT hC) hf h


/-- 低层公式的传输结果实际进入后继公式，而非仅产生宿主层判断。 -/
theorem lift_complete_l (B : Formula ℒ [] context_m)
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ} (hc : member_l ℳ c ω)
    (h : lower_l B ω e T t₁ t₂ t₃ n p c f) :
    (lift_m B).satisfies (env_l ω e T t₁ t₂ t₃ n p c f) := by
  unfold lift_m
  rw [PowerlessOracleClosure.accepts_formula_l]
  apply PowerlessOracleClosure.base_l _ hℳ hc
  · exact (lower_formula_l B _ _ _ _ _ _ _ _ _ _ _).mpr h
  · exact hℳ


end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPartialTruth
