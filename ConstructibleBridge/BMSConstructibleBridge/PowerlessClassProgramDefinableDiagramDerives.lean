import BMSConstructibleBridge.PowerlessClassProgramDefinableDiagram
import BMSConstructibleBridge.PowerlessClassProgramSeparationDerives
import BMSConstructibleBridge.PowerlessRelativeClassFormulaInstances

/-! # 同一类内数码隶属图存在性的原 Z₂ 推导

纯隶属 ℒ，背景原 num/set Z₂，经原 GraphTranslation 与 interpretation_m
回到 Derives。任意原求值矩阵的图由实际程序分离构造；规范编码包在
证明内先于程序域产生。原种子、枚举、数码积及参数界仍是显式构造
守卫，不含 ClassA、反射对应或完整源理论前提，不宣称最终良序已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramDefinableDiagramDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_m guard_l guard_formula_l)
open PowerlessRelativeClassFormulaInstances (instance_m instance_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up t)
private abbrev up₃ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up (up₂ t)
private abbrev up₅ {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) := up₂ (up₃ t)

def product_m {Γ Δ : SortContext ℒ} (ω X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up X))
    (PowerlessRelativeClassProduct.body_m (up ω) (up ω) (.bvar .here))

theorem product_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω X : Term ℒ Γ Δ .set) :
    (product_m ω X).satisfies η ↔ ∀ p, member_l 𝒩 p (X.eval η) ↔
      ∃ n m, member_l 𝒩 n (ω.eval η) ∧ member_l 𝒩 m (ω.eval η) ∧ ordered_l n m p := by
  simp only [product_m, Formula.satisfies, PowerlessRelativeClassProduct.body_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def conclusion_m {Θ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Θ)) :
    Formula ℒ [] (.set :: Θ) :=
  .existsE .set <| PowerlessDefinableMembershipDiagram.spec_m
    (PowerlessDefinableFiniteTrace.lift_m φ) (.fvar .here) (.bvar .here)

theorem conclusion_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Θ)) (χ : Env 𝒩 [] Θ) (ω : carrier_l 𝒩) :
    (conclusion_m φ).satisfies (χ.pushFree ω) ↔
      ∃ Z, PowerlessDefinableMembershipDiagram.spec_l φ χ ω Z := by
  simp only [conclusion_m, Formula.satisfies, PowerlessDefinableMembershipDiagram.spec_formula_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_pushBound_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_empty_l,
    PowerlessDefinableMembershipDiagram.spec_l, PowerlessDefinableMembershipDiagram.edge_l,
    PowerlessDefinableFiniteTrace.lift_formula_l, Term.eval]
  rfl

private def mode_m {Θ Ε : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Θ))
    (ω e _r₁ _r₂ _r₃ _Pair _Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D X : Term ℒ [] Ε .set)
    (ν : VariableSubstitution ℒ Θ [] Ε) : Formula ℒ [] Ε :=
  .imp (guard_m B P₀) <| .imp (PowerlessRelativeHierarchySyntax.class_m B C) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B Q) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B G) <|
          .imp (PowerlessRelativeHierarchySyntax.class_m B t₀) <|
            .imp (PowerlessRelativeHierarchySyntax.class_m B t₁) <|
              .imp (PowerlessRelativeHierarchySyntax.class_m B t₂) <|
                .imp (SecondOrderObjectSyntax.map_m G ω C) <|
                  .imp (PowerlessRelativeClassEnumerationSectionDerives.onto_m G ω C) <|
                    .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
                      .imp (PowerlessRelativeFiniteProgramStep.record_m e e e a) <|
                        .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂) <|
                          .imp (PowerlessRelativeFiniteProgramAlphabet.alphabet_m C ω t₀ t₁ t₂ Q) <|
                            .imp (PowerlessRelativeFiniteProgramDomain.domain_m B ω Q S P) <|
                              .imp (SecondOrderObjectSyntax.member_m B C) <|
                                .imp (SecondOrderObjectSyntax.member_m s C) <|
                                  .imp (SecondOrderObjectSyntax.member_m t C) <| .imp (.neg (.equal s t)) <|
                                    .imp (PowerlessRelativeHierarchyDerives.transitive_m D) <|
                                      .imp (ThirdOrderTheory.subset_m D C) <|
                                        .imp (SecondOrderObjectSyntax.member_m D C) <|
                                          .imp (SecondOrderObjectSyntax.member_m B D) <|
                                            .imp (SecondOrderObjectSyntax.member_m ω D) <|
                                              .imp (product_m ω X) <| .imp (SecondOrderObjectSyntax.member_m X D) <|
                                                .imp (PowerlessRelativeClassParameterSeed.members_m Θ D ν)
                                                  (instance_m (conclusion_m φ) B (fun v => match v with | .here => ω | .there v => ν v))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ


private theorem mode_l (K : source_coding_l hℳ) {Θ Ε : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Θ)) (η : Env 𝒱 [] Ε)
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D X : Term ℒ [] Ε .set)
    (ν : VariableSubstitution ℒ Θ [] Ε)
    (hCoding : SecondOrderComparisonStageTotal.coding_l K (r₁.eval η) (r₂.eval η)
      (r₃.eval η) (Pair.eval η) (Valid.eval η))
    (hω : SecondOrderOmega.omega_l hℳ (ω.eval η)) :
    (mode_m φ ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D X ν).satisfies η := by
  simp only [mode_m, Formula.satisfies, guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, map_formula_l,
    PowerlessRelativeClassEnumerationSectionDerives.onto_formula_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    PowerlessRelativeFiniteProgramStep.record_formula_l,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    PowerlessRelativeFiniteProgramAlphabet.alphabet_formula_l,
    PowerlessRelativeFiniteProgramDomain.domain_formula_l K,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, subset_formula_l,
    PowerlessRelativeClassParameterSeed.members_formula_l, product_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet hDomain
    hBC hs htC hst hD hDC hDC₀ hBD hωD hProduct hXD hParams
  change (∀ x : Raw, ε x (D.eval η) → ε x (C.eval η)) at hDC
  have hBase : ∀ x, ε x (B.eval η) → ∀ z, ε z x → ε z (B.eval η) :=
    fun x hx z hz => hGuard.2.1 x z hx hz
  let χ : Env (PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase) [] Θ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {r} v => match r with
        | .set => ⟨(ν v).eval η, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hC
            (hDC _ (hParams _ v))⟩ }
  let O : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) := ⟨ω.eval η, hωC⟩
  let X₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
    ⟨X.eval η, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hC (hDC _ hXD)⟩
  have hProduct' (p : PowerlessRelativeClassStructure.type_l hℳ (B.eval η)) :
      ε p.val X₀.val ↔ ∃ n m : PowerlessRelativeClassStructure.type_l hℳ (B.eval η),
        ε n.val O.val ∧ ε m.val O.val ∧
          ordered_l (ℳ := PowerlessRelativeClassStructure.structure_l hℳ (B.eval η) hBase) n m p := by
    constructor
    · intro hp
      obtain ⟨n, m, hn, hm, hPair⟩ := (hProduct p.val).mp hp
      let n₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
        ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC hn⟩
      let m₀ : PowerlessRelativeClassStructure.type_l hℳ (B.eval η) :=
        ⟨m, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC hm⟩
      exact ⟨n₀, m₀, hn, hm,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) n₀ m₀ p).mpr hPair⟩
    · rintro ⟨n, m, hn, hm, hPair⟩
      exact (hProduct p.val).mpr ⟨n.val, m.val, hn, hm,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) n m p).mp hPair⟩
  have hExists := PowerlessClassProgramDefinableDiagram.exists_l K η
    ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D
    hCoding hω hGuard hC hωC hQ hG h₀ h₁ h₂ hMap hOnto he ha ht hAlphabet
    hDomain hBC hs htC hst hD hDC hDC₀ hBD hωD φ χ X₀ hProduct' hXD (fun v => hParams _ v)
  apply (instance_l K (conclusion_m φ) η B
    (fun v => match v with | .here => ω | .there v => ν v)
    (χ.pushFree O) rfl (by intro v; cases v <;> rfl)).mpr
  exact (conclusion_formula_l φ χ O).mpr hExists

private def body_m {Θ Γ Ε : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Θ))
    (ω e r₁ r₂ r₃ Pair Valid B P₀ C Q t₀ t₁ t₂ a G S P s t D X : Term ℒ Γ Ε .set)
    (ν : VariableSubstitution ℒ Θ Γ Ε) : Formula ℒ Γ Ε :=
  let τ := @PowerlessSourceRebinding.term_m Γ Ε
  PowerlessSourceRebinding.formula_m <|
    mode_m φ (τ ω) (τ e) (τ r₁) (τ r₂) (τ r₃) (τ Pair) (τ Valid) (τ B) (τ P₀)
      (τ C) (τ Q) (τ t₀) (τ t₁) (τ t₂) (τ a) (τ G) (τ S) (τ P) (τ s) (τ t) (τ D)
      (τ X) (fun v => τ (ν v))

/-- 只重绑原参数替换；原公式上下文不增加规范编码前缀。 -/
def schema_m {Θ Ε : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Θ))
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D X : Term ℒ [] Ε .set)
    (ν : VariableSubstitution ℒ Θ [] Ε) : Formula ℒ [] Ε :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
      body_m φ (up₅ ω) (up₅ e) (.bvar (.there (.there (.there (.there .here)))))
        (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
        (.bvar (.there .here)) (.bvar .here) (up₅ B) (up₅ P₀) (up₅ C) (up₅ Q)
        (up₅ t₀) (up₅ t₁) (up₅ t₂) (up₅ a) (up₅ G) (up₅ S) (up₅ P) (up₅ s) (up₅ t)
        (up₅ D) (up₅ X) (fun v => up₅ (ν v))

def sentence_m {Θ Ε : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Θ))
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D X : Term ℒ [] Ε .set)
    (ν : VariableSubstitution ℒ Θ [] Ε) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D X ν)

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Ε : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Θ))
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D X : Term ℒ [] Ε .set)
    (ν : VariableSubstitution ℒ Θ [] Ε) :
    (sentence_m φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D X ν).TrueIn
      (SecondOrderQuotient.structure_l h𝒩) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, omega_formula_l]
  intro hω
  have hω' := (SecondOrderOmegaSyntax.omega_l h𝒩 η ω).mp ((omega_formula_l η ω).mpr hω)
  obtain ⟨K, _, r₁, r₂, r₃, Pair, Valid, _, _, hCoding⟩ := SecondOrderComparisonCoding.exists_l hω
  refine ⟨r₁, r₂, r₃, Pair, Valid, ?_⟩
  simp only [body_m, PowerlessSourceRebinding.formula_l]
  apply mode_l K
  · simpa only [PowerlessSourceRebinding.term_l, Term.eval,
      Env.pushBound_bound_here, Env.pushBound_bound_there] using hCoding
  · simpa only [PowerlessSourceRebinding.term_l, up₅, up₃, up₂, up,
      Term.eval_weakenBound] using hω'

theorem derives_m {Θ Ε : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Θ))
    (ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D X : Term ℒ [] Ε .set)
    (ν : VariableSubstitution ℒ Θ [] Ε) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D X ν)) :=
  SecondOrderAxioms.interpretation_m _
    (fun _ h𝒩 => models_l h𝒩 φ ω e B P₀ C Q t₀ t₁ t₂ a G S P s t D X ν)

#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassProgramDefinableDiagramDerives
