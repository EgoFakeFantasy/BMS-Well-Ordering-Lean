import BMSConstructibleBridge.PowerlessRelativeCutoffSeedFamilyElementaryImage
import BMSConstructibleBridge.PowerlessRelativeFiniteNumeralTags

/-!
# 原有限公式族的实际截断元素性像：消去标签守卫

对象语言为纯隶属 ℒ，背景为原 Z₂，正式出口为原 Derives 的图翻译句。
调用者只提供原 Δ 参数，装配上下文 Θ 与源上下文 Δ 分别保留。
按实际请求数 m 存在绑定有限标签槽，再保留旧截断出口的全部 R/e/a、
原种子程序域、同一图族与同一个有限元素性像正文。
标签为原 ω 中实际 numeral 根码，Class 与 W 成员及互异由原守卫推出，
不要求调用者预供标签，也不假设首不可数截断在每个模型中必存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffFiniteElementaryImage

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

abbrev context_m {Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ) (Θ : SortContext ℒ) :=
  List.replicate (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length .set ++ Θ

/-- 原装配项只跨过有限标签前缀；不改变任何原变量。 -/
def term_m {Θ : SortContext ℒ} (m : Nat) (t : Term ℒ [] Θ .set) :
    Term ℒ [] (List.replicate m .set ++ Θ) .set :=
  PowerlessSourceRequestParameters.term_m 0 m t

/-- 源标签槽读取装配标签槽，源原 Δ 通过原 τ 接入独立的 Θ。 -/
def binding_m {Θ Δ : SortContext ℒ} : (m : Nat) →
    (Variable Δ .set → Term ℒ [] Θ .set) →
    Variable (List.replicate m .set ++ Δ) .set →
      Term ℒ [] (List.replicate m .set ++ Θ) .set
  | 0, τ, v => τ v
  | m + 1, _, .here => .fvar .here
  | m + 1, τ, .there v => by
      simpa only [List.replicate_succ, List.cons_append] using
        (binding_m m τ v).weakenFree SetTheory.SetSort.set

theorem binding_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Θ Δ : SortContext ℒ}
    (η : Env 𝒩 [] Θ) (ν : Env 𝒩 [] Δ) (m : Nat)
    (v : Values 𝒩.Carrier (List.replicate m .set))
    (τ : Variable Δ .set → Term ℒ [] Θ .set)
    (hτ : ∀ w, (τ w).eval η = ν.freeVal w)
    (w : Variable (List.replicate m .set ++ Δ) .set) :
    (binding_m m τ w).eval (PowerlessSourceTuple.env_l η m v) =
      (PowerlessSourceTuple.env_l ν m v).freeVal w := by
  match m, v, w with
  | 0, .nil, w => exact hτ w
  | m + 1, .cons x v, .here => rfl
  | m + 1, .cons x v, .there w =>
    change ((binding_m m τ w).weakenFree SetTheory.SetSort.set).eval
        ((PowerlessSourceTuple.env_l η m v).pushFree x) =
      ((PowerlessSourceTuple.env_l ν m v).pushFree x).freeVal (.there w)
    rw [Term.eval_weakenFree]
    exact binding_l η ν m v τ hτ w

def payload_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] (context_m Φ Θ) :=
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  PowerlessRelativeCutoffSeedFamilyElementaryImage.conclusion_m Φ
    (term_m m B) (term_m m W) (term_m m ω) (term_m m t₀) (term_m m t₁) (term_m m t₂)
    (binding_m m τ)

/-- 旧截断完整正文整体保留在有限标签存在量词块内部。 -/
def conclusion_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B W ω t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  PowerlessRelativeFiniteNumeralTags.exists_m
    (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
    (payload_m Φ B W ω t₀ t₁ t₂ τ)

def schema_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeFiniteProgramEvaluationGraph.parameters_m Θ B (fun v => .fvar v)) <|
    .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .imp (SecondOrderObjectSyntax.member_m B W) <|
              .imp (parameters_m Δ W τ) <|
                .imp (SecondOrderObjectSyntax.member_m t₀ W) <|
                  .imp (SecondOrderObjectSyntax.member_m t₁ W) <|
                    .imp (SecondOrderObjectSyntax.member_m t₂ W) <|
                      .imp (PowerlessRelativeFiniteProgramInstruction.tags_m t₀ t₁ t₂)
                        (conclusion_m Φ B W ω t₀ t₁ t₂ τ)

def sentence_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m Φ B P₀ ω Ω W t₀ t₁ t₂ τ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem class_l (K : source_coding_l hℳ) {Θ : SortContext ℒ}
    (η : Env 𝒱 [] Θ) (m : Nat) {B ω : SecondOrderQuotient.type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hωC : PowerlessRelativeClassCorrespondence.member_l hℳ B ω)
    (hClass : ∀ s (v : Variable Θ s),
      PowerlessRelativeClassCorrespondence.member_l hℳ B (η.freeVal v)) :
    ∀ s (v : Variable (List.replicate m .set ++ Θ) s),
      PowerlessRelativeClassCorrespondence.member_l hℳ B
        ((PowerlessSourceTuple.env_l η m (PowerlessRelativeFiniteNumeralTags.values_l K m)).freeVal v) := by
  induction m with
  | zero => exact hClass
  | succ m ih =>
    intro s v
    cases s
    cases v with
    | here =>
      exact PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hωC
        (PowerlessRelativeFiniteNumeralTags.member_l K hω m)
    | there v => exact ih _ v

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    (sentence_m Φ B P₀ ω Ω W t₀ t₁ t₂ τ).TrueIn
      (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K,
    SecondOrderCanonicalLevelDerives.guard_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    SecondOrderObjectSyntax.member_m, Arguments.eval]
  intro η hClass hSeed hω hΩ hW hBW hParams h₀ h₁ h₂ ht
  let m := (PowerlessRelativeFiniteRequestFamilyClosure.requests_m Φ).length
  let v := PowerlessRelativeFiniteNumeralTags.values_l K m
  let ζ := PowerlessSourceTuple.env_l η m v
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun w => nomatch w
      freeVal := fun {s} w => match s with | .set => (τ w).eval η }
  let ξ := PowerlessSourceTuple.env_l ν m v
  have hTerm (t : Term ℒ [] Θ .set) :
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (t.eval η) := by
    match t with
    | .bvar w => nomatch w
    | .fvar w => exact hClass _ w
    | .app f _ => nomatch f
  have hBase : ∀ x, mem_l hℳ x (B.eval η) →
      ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval η) :=
    fun x hx y hy => hSeed.2.1 x y hx hy
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase (Ω.eval η) (W.eval η) hW (ω.eval η)
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  have hTrans := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hW
  have hv (t : Term ℒ [] Θ .set) : (term_m m t).eval ζ = t.eval η :=
    PowerlessSourceRequestParameters.term_l η 0 m .nil v t
  have hτ (w : Variable (List.replicate m .set ++ Δ) .set) :
      (binding_m m τ w).eval ζ = ξ.freeVal w :=
    binding_l η ν m v τ (fun _ => rfl) w
  have hClass' : ∀ s (w : Variable (context_m Φ Θ) s),
      PowerlessRelativeClassCorrespondence.member_l hℳ (B.eval η) (ζ.freeVal w) := by
    intro s w
    exact class_l K η m hBase hω (hTerm ω) hClass s w
  have hParams' := (parameters_formula_l (PowerlessRelativeSourceFamilyElementaryImage.context_m Φ)
    ζ (term_m m W) (binding_m m τ)).mpr (by
      intro s w
      cases s
      rw [hτ w, hv W]
      exact PowerlessRelativeFiniteNumeralTags.parameters_l K ν m hω
        (fun x hx => hTrans (ω.eval η) hωW x hx)
        (fun s w => by cases s; exact (parameters_formula_l Δ η W τ).mp hParams _ w) _ w)
  have hDistinct' := (PowerlessRelativeSourceSkolemFamily.distinct_formula_l
    (PowerlessSourceRequestParameters.tags_m Δ m) (binding_m m τ) ζ).mpr (by
      simpa only [hτ] using PowerlessRelativeFiniteNumeralTags.distinct_l K ν m)
  have h := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp
    (PowerlessRelativeCutoffSeedFamilyElementaryImage.models_l hℳ Φ
      (term_m m B) (term_m m P₀) (term_m m ω) (term_m m Ω) (term_m m W)
      (term_m m t₀) (term_m m t₁) (term_m m t₂) (binding_m m τ)) ζ
  simp only [PowerlessRelativeCutoffSeedFamilyElementaryImage.schema_m, Formula.satisfies,
    PowerlessRelativeFiniteProgramEvaluationGraph.parameters_formula_l K,
    SecondOrderCanonicalLevelDerives.guard_formula_l, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeFiniteProgramInstruction.tags_m,
    SecondOrderObjectSyntax.member_m, Arguments.eval, hv] at h
  apply (PowerlessRelativeFiniteNumeralTags.exists_formula_l m
    (payload_m Φ B W ω t₀ t₁ t₂ τ) η).mpr
  exact ⟨v, h hClass' hSeed hω hΩ hW hBW hParams' hDistinct' h₀ h₁ h₂ ht⟩

theorem derives_m {Θ Δ : SortContext ℒ}
    (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (B P₀ ω Ω W t₀ t₁ t₂ : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m Φ B P₀ ω Ω W t₀ t₁ t₂ τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 =>
    models_l h𝒩 Φ B P₀ ω Ω W t₀ t₁ t₂ τ)

#print axioms binding_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffFiniteElementaryImage
