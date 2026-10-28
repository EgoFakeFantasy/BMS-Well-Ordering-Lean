import BMSConstructibleBridge.PowerlessCodedStageAbsoluteness
import BMSConstructibleBridge.PowerlessFiniteStageSystem
import BMSConstructibleBridge.PowerlessStabilitySupport

/-!
# 有限核心早层中编码好标签条件的源解释

补齐 §16 条目 4 的接口：小层只需原有限层核心，正是反射端点实际携带的强度。
编码有限理论满足性的原公式 holds_m 在环境层中按原语义读出，因此固定 AST
条件可以充当共同见证矩阵的条目；同一对自然数码 c,N 表示指定有限支持 Ξ。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageSource

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure
open PowerlessCodedStageTheory PowerlessCodedStageAbsoluteness

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {U δ : carrier_l ℳ}
  {hU₀ : ∃ x, ThirdOrderSemantics.member_l ℳ x U} (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {ω e T t₁ t₂ t₃ : type_l U} (hω : omega_l ω.val)
  (ht : PowerlessEvaluationTags.tags_l e.val t₁.val t₂.val t₃.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hU : PowerlessHierarchyStage.stage_l ω.val e.val T.val t₁.val t₂.val t₃.val δ U)
  (hδ : PowerlessStagePair.limit_l δ)
  (h𝒩 : Theory.Models (structure_l U hU₀) PowerlessFiniteStageHierarchy.theory_m)
  (hωδ : ThirdOrderSemantics.member_l ℳ ω.val δ)

/-- 编码式内部四个量词对原参数的弱化。 -/
private def q4 {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :
    Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
  ((((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
      SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)

/-- 四个绑定值压入后的环境。 -/
private def η4 {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (a s f g : type_l U) : Env (structure_l U hU₀) (.set :: .set :: .set :: .set :: Γ) Δ :=
  ((((η.pushBound a).pushBound s).pushBound f).pushBound g)

private theorem q4_eval {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (a s f g : type_l U) (t : Term ℒ Γ Δ .set) :
    (q4 t).eval (η4 η a s f g) = t.eval η := by
  simp only [q4, η4, Term.eval_weakenBound]

/-- 压入四个绑定值后，编码式内部的四个绑定槽按原索引读回见证。 -/
private theorem η4_eval_a {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (a s f g : type_l U) :
    ((.bvar (.there (.there (.there .here)))) : Term ℒ _ _ .set).eval (η4 η a s f g) = a := rfl

private theorem η4_eval_s {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (a s f g : type_l U) :
    ((.bvar (.there (.there .here))) : Term ℒ _ _ .set).eval (η4 η a s f g) = s := rfl

private theorem η4_eval_f {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (a s f g : type_l U) :
    ((.bvar (.there .here)) : Term ℒ _ _ .set).eval (η4 η a s f g) = f := rfl

private theorem η4_eval_g {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (a s f g : type_l U) :
    ((.bvar .here) : Term ℒ _ _ .set).eval (η4 η a s f g) = g := rfl

include hℳ hω ht hT hU hδ h𝒩 hωδ

/-- 四个绑定值下的原系统式与环境层求值系统一致。 -/
private theorem system_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (a s f g : type_l U) (w z V s₁ s₂ s₃ α : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val)
    (hs₃ : (s₃.eval η).val = t₃.val) :
    (PowerlessStageEvaluation.system_m (q4 w) (q4 z) (q4 V) (q4 s₁) (q4 s₂) (q4 s₃) (q4 α)
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
      (.bvar (.there .here))).satisfies (η4 η a s f g) ↔
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val
        (α.eval η).val a.val s.val f.val := by
  refine ((PowerlessFiniteStageSystem.source_l hℳ hω ht hT hU hδ h𝒩 hωδ (η4 η a s f g)
    (q4 w) (q4 z) (q4 V) (q4 s₁) (q4 s₂) (q4 s₃) (q4 α)
    (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar (.there .here))
    ?_ ?_ ?_ ?_ ?_ ?_).trans ?_)
  · rw [q4_eval η a s f g w]; exact hw
  · rw [q4_eval η a s f g z]; exact hz
  · rw [q4_eval η a s f g V]; exact hV
  · rw [q4_eval η a s f g s₁]; exact hs₁
  · rw [q4_eval η a s f g s₂]; exact hs₂
  · rw [q4_eval η a s f g s₃]; exact hs₃
  · rw [q4_eval η a s f g α, η4_eval_a, η4_eval_s, η4_eval_f]

omit hδ h𝒩 hωδ in
/-- 四个绑定值下的原赋值图式与环境层图成员一致。 -/
private theorem map_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (a s f g : type_l U) (n : Term ℒ Γ Δ .set) :
    (SecondOrderObjectSyntax.map_m (.bvar .here) (q4 n)
      (.bvar (.there (.there (.there .here))))).satisfies (η4 η a s f g) ↔
      map_l g.val (n.eval η).val a.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  exact ((map_formula_l (η4 η a s f g) (.bvar .here) (q4 n)
    (.bvar (.there (.there (.there .here))))).trans (PowerlessSourceGraphAbsolute.map_l hUT)).trans
    (by rw [q4_eval η a s f g n, η4_eval_g, η4_eval_a])

omit hδ h𝒩 hωδ in
/-- 四个绑定值下的原求值查询式与环境层查询一致。 -/
private theorem query_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (a s f g : type_l U) (c : Term ℒ Γ Δ .set) :
    (PowerlessEvaluationClause.query_m (.bvar (.there .here)) (q4 c)
      (.bvar .here)).satisfies (η4 η a s f g) ↔
      PowerlessEvaluationClause.query_l f.val (c.eval η).val g.val := by
  have hUT := PowerlessStageStructure.transitive_l hℳ hω ht hT hU
  exact ((PowerlessEvaluationClause.query_formula_l (η4 η a s f g) (.bvar (.there .here)) (q4 c)
    (.bvar .here)).trans (PowerlessValueAbsolute.query_l hUT)).trans
    (by rw [q4_eval η a s f g c, η4_eval_f, η4_eval_g])

/-- 编码理论满足式在只满足原有限层核心的小结构中按环境层语义读出。
赋值图与数码长度按原有限层系统吸收进传递上层。 -/
theorem holds_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l U hU₀) Γ Δ)
    (w z V s₁ s₂ s₃ c n α : Term ℒ Γ Δ .set)
    (hw : (w.eval η).val = ω.val) (hz : (z.eval η).val = e.val) (hV : (V.eval η).val = T.val)
    (hs₁ : (s₁.eval η).val = t₁.val) (hs₂ : (s₂.eval η).val = t₂.val) (hs₃ : (s₃.eval η).val = t₃.val)
    (hn : member_l ℳ (n.eval η).val ω.val) (hα : member_l ℳ (α.eval η).val δ) :
    (holds_m w z V s₁ s₂ s₃ c n α).satisfies η ↔
      holds_l ω.val e.val T.val t₁.val t₂.val t₃.val (c.eval η).val (n.eval η).val (α.eval η).val := by
  constructor
  · intro h
    obtain ⟨a, s, f, g, hsys, hg, hq⟩ := h
    exact ⟨a.val, s.val, f.val,
      (system_source_l hℳ hω ht hT hU hδ h𝒩 hωδ η a s f g w z V s₁ s₂ s₃ α hw hz hV hs₁ hs₂ hs₃).mp hsys,
      ⟨g.val, (map_source_l hℳ hω ht hT hU η a s f g n).mp hg,
        (query_source_l hℳ hω ht hT hU η a s f g c).mp hq⟩⟩
  · intro h
    obtain ⟨A, S, F, hsys, ⟨g, hg, hq⟩⟩ := h
    have hASF := PowerlessFiniteStageSystem.member_l hℳ hω ht hT hU hδ h𝒩 hωδ hα hsys
    have hgU := graph_member_l hℳ hω ht hT hU hδ hωδ hn hASF.1 hg
    refine ⟨⟨A, hASF.1⟩, ⟨S, hASF.2.1⟩, ⟨F, hASF.2.2⟩, ⟨g, hgU⟩, ?_, ?_, ?_⟩
    · exact (system_source_l hℳ hω ht hT hU hδ h𝒩 hωδ η ⟨A, hASF.1⟩ ⟨S, hASF.2.1⟩
        ⟨F, hASF.2.2⟩ ⟨g, hgU⟩ w z V s₁ s₂ s₃ α hw hz hV hs₁ hs₂ hs₃).mpr hsys
    · exact (map_source_l hℳ hω ht hT hU η ⟨A, hASF.1⟩ ⟨S, hASF.2.1⟩
        ⟨F, hASF.2.2⟩ ⟨g, hgU⟩ n).mpr hg
    · exact (query_source_l hℳ hω ht hT hU η ⟨A, hASF.1⟩ ⟨S, hASF.2.1⟩
        ⟨F, hASF.2.2⟩ ⟨g, hgU⟩ c).mpr hq

omit hU hδ h𝒩 hωδ in
/-- §16 条目 4 的固定支持实例：对 Ξ = StabilitySupport.basis_m k 调用原 code_l，
好标签条件由同一对自然数码 c,N 编码，公式正文不展开 Ξ。 -/
lemma good_label_code_l (k : Nat) : ∃ c N, member_l ℳ c ω.val ∧ member_l ℳ N ω.val ∧
    ∀ {α A S F : carrier_l ℳ}, ∀ hA₀ : ∃ x, member_l ℳ x A,
      PowerlessStageEvaluation.system_l ω.val e.val T.val t₁.val t₂.val t₃.val α A S F →
      (holds_l ω.val e.val T.val t₁.val t₂.val t₃.val c N α ↔
        Theory.Models (structure_l A hA₀) (Theory.ofList (PowerlessStabilitySupport.basis_m k))) :=
  PowerlessCodedStageTheory.code_l hℳ hω ht hT (PowerlessStabilitySupport.basis_m k)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedStageSource
