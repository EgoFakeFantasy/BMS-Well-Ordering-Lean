import BMSConstructibleBridge.PowerlessSourceReflectionSupport
import BMSConstructibleBridge.PowerlessTruthFiniteStage

/-!
# 保留任意内部代码参数的部分真值反射层

六个编码参数固定；层号、极性、代码与赋值图放入四个绑定槽。
共同语义在实际层次类中解释原公式，不含某个上端点的求值图。
任意有限核心与这一反射在同一个实际极限层上同时成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthReflection

open Logic FirstOrder ThirdOrderSemantics PowerlessSourcePadding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set]

def formula_m (B : Formula ℒ [] PowerlessTruthOracle.context_m) :
    Formula ℒ [.set, .set, .set, .set] context_m :=
  PowerlessTruthOracle.instance_m B omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m
    (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
    (.bvar (.there .here)) (.bvar .here)

def environment_l (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) :
    Env ℳ [.set, .set, .set, .set] context_m :=
  ((((env_l Env.empty ω e T t₁ t₂ t₃ e).pushBound n).pushBound p).pushBound c).pushBound f

def truth_l (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) : Prop :=
  (PowerlessSourceClass.form_m
    (PowerlessHierarchyClass.domain_m omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m)
      (formula_m B)).satisfies (environment_l ω e T t₁ t₂ t₃ n p c f)

theorem formula_l (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (ω e T t₁ t₂ t₃ n p c f : carrier_l ℳ) :
    (formula_m B).satisfies (environment_l ω e T t₁ t₂ t₃ n p c f) ↔
      B.satisfies (PowerlessTruthOracle.env_l ω e T t₁ t₂ t₃ n p c f) :=
  PowerlessTruthOracle.instance_formula_l B _ _ _ _ _ _ _ _ _ _ _

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (B : Formula ℒ [] PowerlessTruthOracle.context_m)
    (Ξ : List (Sentence ℒ)) (hΞ : ∀ φ ∈ Ξ, PowerlessTheory.theory_m φ)
    (α : carrier_l ℳ) (hα : PowerlessOrdinal.ordinal_l α) :
    ∃ δ U, ∃ hU₀ : ∃ x, member_l ℳ x U,
      PowerlessStagePair.limit_l δ ∧ member_l ℳ α δ ∧ member_l ℳ ω δ ∧
      PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ δ U ∧
      Theory.Models (PowerlessMemberStructure.structure_l U hU₀) (Theory.ofList Ξ) ∧
      ∀ w z V s₁ s₂ s₃ n p c f : PowerlessMemberStructure.type_l U,
        w.val = ω → z.val = e → V.val = T → s₁.val = t₁ → s₂.val = t₂ → s₃.val = t₃ →
          (truth_l B ω e T t₁ t₂ t₃ n.val p.val c.val f.val ↔
            B.satisfies (PowerlessTruthOracle.env_l
              (ℳ := PowerlessMemberStructure.structure_l U hU₀) w z V s₁ s₂ s₃ n p c f)) := by
  obtain ⟨A, hA⟩ := PowerlessBasic.pairing_l hℳ α ω
  obtain ⟨β, hβ, h₀⟩ := PowerlessOrdinalCollection.bound_l hℳ (A := A) (by
    intro γ hγ
    rcases (hA γ).mp hγ with rfl | rfl
    · exact hα
    · exact PowerlessOmegaOrdinal.ordinal_l hℳ hω)
  let ρ := env_l Env.empty ω e T t₁ t₂ t₃ e
  obtain ⟨η, hη⟩ := PowerlessSourceParameters.env_exists_l ρ
  have hω₀ : omega_l (omega_m.eval (PowerlessComprehension.env_l η)) := by rw [hη]; exact hω
  have ht₀ : PowerlessEvaluationTags.tags_l (zero_m.eval (PowerlessComprehension.env_l η))
      (tag₁_m.eval (PowerlessComprehension.env_l η)) (tag₂_m.eval (PowerlessComprehension.env_l η))
      (tag₃_m.eval (PowerlessComprehension.env_l η)) := by rw [hη]; exact ht
  have hT₀ : PowerlessTriangular.triangular_l (omega_m.eval (PowerlessComprehension.env_l η))
      (zero_m.eval (PowerlessComprehension.env_l η)) (triangle_m.eval (PowerlessComprehension.env_l η)) := by
    rw [hη]; exact hT
  have hP := PowerlessClassBasic.parameters_l hℳ hω ht hT
  obtain ⟨δ, U, hU₀, hδ, hβδ, hU, h𝒩, _, h₁⟩ :=
    PowerlessSourceReflectionSupport.exists_l hℳ [formula_m B] Ξ hΞ η
      omega_m zero_m triangle_m tag₁_m tag₂_m tag₃_m β hω₀ ht₀ hT₀ hβ (by
        intro v
        rw [hη]
        repeat' first
          | exact hP.1
          | exact hP.2.1
          | exact hP.2.2.1
          | exact hP.2.2.2.1
          | exact hP.2.2.2.2.1
          | exact hP.2.2.2.2.2
          | cases ‹Variable _ _›)
  rw [hη] at hU
  refine ⟨δ, U, hU₀, hδ,
    PowerlessOrdinal.transitive_l hδ.1 β α hβδ (h₀ α ((hA α).mpr (Or.inl rfl))),
    PowerlessOrdinal.transitive_l hδ.1 β ω hβδ (h₀ ω ((hA ω).mpr (Or.inr rfl))), hU, h𝒩, ?_⟩
  rintro w z V s₁ s₂ s₃ n p c f rfl rfl rfl rfl rfl rfl
  let θ := environment_l w.val z.val V.val s₁.val s₂.val s₃.val n.val p.val c.val f.val
  let ξ := environment_l (ℳ := PowerlessSourceClass.structure_l (fun x => member_l ℳ x U) hU₀)
    w z V s₁ s₂ s₃ n p c f
  have hξ : PowerlessSourceClass.env_l ξ = θ := by
    apply Env.ext <;> intro s v <;> cases s
    all_goals repeat' first | rfl | cases ‹Variable _ _›
  have hθ : ∀ t : Term ℒ [.set, .set, .set, .set] context_m .set, member_l ℳ (t.eval θ) U := by
    intro t
    rw [← hξ]
    rw [PowerlessSourceClass.term_l]
    exact (t.eval ξ).property
  have h₂ := h₁ (formula_m B) (List.mem_singleton_self _) θ (by
    rw [hη]
    apply Env.ext
    · intro s v; nomatch v
    · intro s v; cases s
      rfl) hθ
  have h₃ : PowerlessHierarchyClass.lift_l hU₀ θ hθ = ξ := by
    apply Env.ext
    · intro s v
      cases s
      apply Subtype.ext
      exact (congrArg (fun η => η.boundVal v) hξ).symm
    · intro s v
      cases s
      apply Subtype.ext
      exact (congrArg (fun η => η.freeVal v) hξ).symm
  have h₄ : truth_l B w.val z.val V.val s₁.val s₂.val s₃.val n.val p.val c.val f.val ↔
      B.satisfies (PowerlessTruthOracle.env_l
        (ℳ := PowerlessSourceClass.structure_l (fun x => member_l ℳ x U) hU₀) w z V s₁ s₂ s₃ n p c f) :=
    h₂.trans (by
      rw [h₃]
      exact formula_l (ℳ := PowerlessSourceClass.structure_l (fun x => member_l ℳ x U) hU₀)
        B w z V s₁ s₂ s₃ n p c f)
  have hQ (M N : FirstOrder.Structure.{0, 0, 0, u} ℒ) (h : M = N) :
      HEq (fun w z V s₁ s₂ s₃ n p c f : carrier_l M =>
        B.satisfies (PowerlessTruthOracle.env_l (ℳ := M) w z V s₁ s₂ s₃ n p c f))
        (fun w z V s₁ s₂ s₃ n p c f : carrier_l N =>
          B.satisfies (PowerlessTruthOracle.env_l (ℳ := N) w z V s₁ s₂ s₃ n p c f)) := by
    cases h
    rfl
  have hQ₀ := hQ (PowerlessSourceClass.structure_l (fun x => member_l ℳ x U) hU₀)
    (PowerlessMemberStructure.structure_l U hU₀) (PowerlessClassSeparation.structure_l U hU₀)
  have hE := eq_of_heq hQ₀
  exact h₄.trans (Iff.of_eq (congrArg (fun q => q w z V s₁ s₂ s₃ n p c f) hE))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTruthReflection
