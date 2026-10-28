import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparation

/-! # 固定极限层 Δ₀ 分离模式的原 Z₂ 推导

闭模式显式带传递基集、层值、非零极限和全部自由参数的层内 guard。
分离子集仍在指定层，元素规格量化全部原商对象。外部模式索引不被改写为
内部统一真值断言；经原图翻译及已核验解释回传原 Derives 核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives

open Logic FirstOrder StabilityFrame SecondOrderObjectSyntax PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 全部自由参数属于同一层；供具体分离及递归句复用。 -/
def parameters_m {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ)
    (C : Term ℒ Γ Ε .set) (τ : VariableSubstitution ℒ Δ Γ Ε) : Formula ℒ Γ Ε :=
  match Δ with
  | [] => .truth
  | .set :: Δ => .conj (member_m (τ .here) C) (parameters_m Δ C (fun v => τ (.there v)))

theorem parameters_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Ε : SortContext ℒ} (Δ : SortContext ℒ) (η : Env 𝒩 Γ Ε)
    (C : Term ℒ Γ Ε .set) (τ : VariableSubstitution ℒ Δ Γ Ε) :
    (parameters_m Δ C τ).satisfies η ↔
      ∀ s (v : Variable Δ s), 𝒩.relInterp .membership (.cons ((τ v).eval η) (.cons (C.eval η) .nil)) := by
  induction Δ with
  | nil =>
      constructor
      · intro _ _ v; nomatch v
      · intro _; trivial
  | cons s Δ ih =>
      cases s
      change (_ ∧ (parameters_m Δ C (fun v => τ (.there v))).satisfies η) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hHead, hTail⟩ t v
        cases t
        cases v with
        | here => exact hHead
        | there v => exact hTail _ v
      · intro h
        exact ⟨h _ .here, fun _ v => h _ (.there v)⟩

private def insert_m {Δ : SortContext ℒ} :
    VariableSubstitution ℒ (.set :: Δ) [.set, .set, .set] (.set :: .set :: .set :: Δ)
  | _, .here => .bvar .here
  | _, .there v => .fvar (.there (.there (.there v)))

private def body_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [.set, .set, .set] (.set :: .set :: .set :: Δ) :=
  φ.substitute (.map (fun {s} (v : Variable ([] : SortContext ℒ) s) => nomatch v) insert_m)

private def separation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  .forallE .set <| .imp (member_m (.bvar .here) (.fvar (.there (.there .here)))) <|
    .existsE .set <| .conj (member_m (.bvar .here) (.fvar (.there (.there .here)))) <|
      .forallE .set <| .iff (member_m (.bvar .here) (.bvar (.there .here)))
        (.conj (member_m (.bvar .here) (.bvar (.there (.there .here)))) (body_m φ))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Formula ℒ [] (.set :: .set :: .set :: Δ) :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m (.fvar .here) (.fvar (.there .here))
      (.fvar (.there (.there .here)))) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m (.fvar (.there .here))) <|
        .imp (parameters_m Δ (.fvar (.there (.there .here)))
          (fun v => .fvar (.there (.there (.there v))))) (separation_m φ)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    (sentence_m φ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hC hLimit hParams
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K η
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l
    (hℳ := hℳ) η (.fvar (.there .here))).mp hLimit
  have hParams' := (parameters_formula_l Δ η (.fvar (.there (.there .here)))
    (fun v => .fvar (.there (.there (.there v))))).mp hParams
  let ξ : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun v => η.freeVal (.there (.there (.there v))) }
  change ∀ X : type_l hℳ, mem_l hℳ X (η.freeVal (.there (.there .here))) →
    ∃ Y, mem_l hℳ Y (η.freeVal (.there (.there .here))) ∧ ∀ x,
      mem_l hℳ x Y ↔ mem_l hℳ x X ∧ (body_m φ).satisfies (((η.pushBound X).pushBound Y).pushBound x)
  intro X hX
  obtain ⟨Y, hY, hRead⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l
    hBase' hLimit' hC' hφ ξ hX hParams'
  refine ⟨Y, hY, fun x => (hRead x).trans (and_congr Iff.rfl ?_)⟩
  refine ((Formula.satisfies_substitute (((η.pushBound X).pushBound Y).pushBound x) _ φ).trans ?_).symm
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext
  · intro _ v; nomatch v
  · intro s v
    cases s
    cases v with
    | here => rfl
    | there v => rfl

theorem derives_m {Δ : SortContext ℒ} {φ : Formula ℒ [] (.set :: Δ)}
    (hφ : Formula.IsDelta0 membershipLevyBound φ) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ hφ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitDeltaSeparationDerives
