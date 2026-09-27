import BMSConstructibleBridge.PowerlessOracleBounded

/-!
# 子公式接受生成父证书的原公式规则

这里读取的是各子公式已有的实际接受证书，而非一个预先共同选好的
记录集。有界负分支保留真实界集合的全称条件和非法槽位情形。
各规则沿用原公式 AST；完整环境核心用于证明构造有效，有限支持另行抽取。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleRules

open Logic FirstOrder ThirdOrderSemantics PowerlessTruthOracle

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def witness_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n p b f i a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (PowerlessAmbientAssignments.finite_m (q ω) (.bvar .here))
    (.conj (PowerlessAssignmentUpdate.update_m (q f) (q i) (q a) (.bvar .here))
      (accepts_m B (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q n) (q p) (q b) (.bvar .here))))

def nand_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n p a b f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessAmbientAssignments.finite_m ω f)
    (.disj (.conj (.equal p e)
      (.disj (accepts_m B ω e T t₁ t₂ t₃ n t₁ a f) (accepts_m B ω e T t₁ t₂ t₃ n t₁ b f)))
      (.conj (.equal p t₁)
        (.conj (accepts_m B ω e T t₁ t₂ t₃ n e a f) (accepts_m B ω e T t₁ t₂ t₃ n e b f))))

def existential_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n b f i : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .conj (PowerlessAmbientAssignments.slot_m ω f i)
    (.existsE .set (witness_m B (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃)
      (q n) (q e) (q b) (q f) (q i) (.bvar .here)))

def positive_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n b f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  let v (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  .conj (PowerlessAmbientAssignments.slot_m ω f i)
    (.existsE .set (.conj (SecondOrderObjectSyntax.value_m (q f) (q j) (.bvar .here))
      (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
        (witness_m B (v ω) (v e) (v T) (v t₁) (v t₂) (v t₃)
          (v n) (v e) (v b) (v f) (v i) (.bvar .here))))))

def negative_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n b f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  let v (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  .conj (PowerlessAmbientAssignments.finite_m ω f)
    (.disj (.neg (PowerlessAmbientAssignments.slot_m ω f i))
      (.forallE .set (.imp (SecondOrderObjectSyntax.value_m (q f) (q j) (.bvar .here))
        (.forallE .set (.imp (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here)))
          (witness_m B (v ω) (v e) (v T) (v t₁) (v t₂) (v t₃)
            (v n) (v t₁) (v b) (v f) (v i) (.bvar .here)))))))

def bounded_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n p b f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (.equal p e) (positive_m B ω e T t₁ t₂ t₃ n b f i j))
    (.conj (.equal p t₁) (negative_m B ω e T t₁ t₂ t₃ n b f i j))

def step_m (B : Formula ℒ [] context_m) {Γ Δ : SortContext ℒ}
    (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let q (s : Term ℒ Γ Δ .set) := (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let r (s : Term ℒ Γ Δ .set) := (q s).weakenBound SetTheory.SetSort.set
  .disj (instance_m B ω e T t₁ t₂ t₃ n p c f)
    (.disj (PowerlessTruthCertificate.accepts_m ω e T t₁ t₂ t₃ p c f)
      (.disj
        (.existsE .set (.existsE .set (.conj
          (PowerlessFormulaConstructor.constructor_m (q ω) (q e) (q T) (q t₂)
            (.bvar (.there .here)) (.bvar .here) (q c))
          (nand_m B (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃) (q n) (q p)
            (.bvar (.there .here)) (.bvar .here) (q f)))))
        (.disj
          (.conj (.equal p e) (.existsE .set (.existsE .set (.conj
            (PowerlessFormulaConstructor.constructor_m (q ω) (q e) (q T) (q t₃)
              (.bvar (.there .here)) (.bvar .here) (q c))
            (existential_m B (q ω) (q e) (q T) (q t₁) (q t₂) (q t₃)
              (q n) (.bvar .here) (q f) (.bvar (.there .here)))))))
          (.existsE .set (.existsE .set (.existsE .set (.conj
            (PowerlessBoundedCode.code_m (r ω) (r e) (r T) (r t₂) (r t₃)
              (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here) (r c))
            (bounded_m B (r ω) (r e) (r T) (r t₁) (r t₂) (r t₃) (r n) (r p)
              (.bvar .here) (r f) (.bvar (.there (.there .here))) (.bvar (.there .here))))))))))

theorem step_l (B : Formula ℒ [] context_m) {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T t₁ t₂ t₃ n p c f : Term ℒ Γ Δ .set)
    (hc : member_l ℳ (c.eval η) (ω.eval η))
    (h : (step_m B ω e T t₁ t₂ t₃ n p c f).satisfies η) :
    (accepts_m B ω e T t₁ t₂ t₃ n p c f).satisfies η := by
  apply (PowerlessOracleClosure.accepts_formula_l B hℳ η ω e T t₁ t₂ t₃ n p c f).mpr
  simp only [step_m, nand_m, existential_m, bounded_m, positive_m, negative_m, witness_m,
    Formula.satisfies, instance_formula_l, PowerlessTruthClosure.accepts_formula_l hℳ,
    PowerlessOracleClosure.accepts_formula_l B hℳ,
    PowerlessFormulaConstructor.constructor_formula_l, PowerlessBoundedCode.code_formula_l,
    PowerlessAmbientAssignments.finite_formula_l, PowerlessAmbientAssignments.slot_formula_l,
    PowerlessAssignmentUpdate.update_formula_l, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound] at h
  rcases h with h | h | ⟨a, b, hC, hf, h⟩ | ⟨hp, i, b, hC, hi, a, g, hg, hfg, h⟩ |
    ⟨i, j, b, hC, h⟩
  · exact PowerlessOracleClosure.base_l B hℳ hc h
  · exact PowerlessOracleClosure.original_l B h
  · exact PowerlessOracleClosure.nand_l B hℳ hc hC hf h
  · rw [hp]
    exact PowerlessOracleClosure.exists_l B hℳ hc hC hi hg hfg h
  · rcases h with ⟨hp, hi, z, hz, a, ha, g, hg, hfg, h⟩ | ⟨hp, hf, h⟩
    · rw [hp]
      exact PowerlessOracleBounded.positive_l B hℳ hc hC hi hz ha hg hfg h
    · rw [hp]
      exact PowerlessOracleBounded.negative_l B hℳ hc hC hf h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOracleRules

