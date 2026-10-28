import BMSConstructibleBridge.PowerlessBMSQuotientSubsetImage
import YesMetaZFC.Automation.ModelClosure

/-!
# 自然数索引、子集有界替换的对象模式

源闭句只用纯隶属语言，显式量化 ω、共同母集及原公式的所有有限参数。
每个实例的原图翻译由原 Z₂ 推导；不把完整 Collection 加入背景。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSubsetImageDerives

open Logic FirstOrder SecondOrderObjectSyntax PowerlessBMSQuotientCoding

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private def insert_m {Γ Δ : SortContext ℒ} (x y : Term ℒ Γ Δ .set) :
    VariableSubstitution ℒ (.set :: .set :: Δ) Γ Δ
  | _, .here => y
  | _, .there .here => x
  | _, .there (.there v) => .fvar v

def at_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  φ.substitute (show Substitution ℒ [] (.set :: .set :: Δ) Γ Δ from
    .map (fun v => nomatch v) (insert_m x y))

def parameters_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) : Env 𝒩 [] Δ := ⟨Assignment.empty, η.freeVal⟩

theorem parameters_pushBound_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (x : 𝒩.Carrier .set) :
    parameters_l (η.pushBound x) = parameters_l η := rfl

theorem parameters_empty_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Δ : SortContext ℒ} (η : Env 𝒩 [] Δ) : parameters_l η = η := by
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    rfl

theorem at_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ) (x y : Term ℒ Γ Δ .set) :
    (at_m φ x y).satisfies η ↔
      φ.satisfies (((parameters_l η).pushFree (x.eval η)).pushFree (y.eval η)) := by
  refine (Formula.satisfies_substitute η _ φ).trans ?_
  apply Iff.of_eq
  apply congrArg (fun η => φ.satisfies η)
  apply Env.ext (bound := []) (fun {_} v => nomatch v)
  · intro s v
    cases v with
    | here => rfl
    | there v => cases v <;> rfl

private def total_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member_m (.bvar .here) (ω.weakenBound SetTheory.SetSort.set))
    (.existsE .set (at_m φ (.bvar (.there .here)) (.bvar .here))))

def unique_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.forallE .set (.forallE .set (.imp
    (.conj (member_m (.bvar (.there (.there .here))) (((ω.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))
      (.conj (at_m φ (.bvar (.there (.there .here))) (.bvar (.there .here)))
        (at_m φ (.bvar (.there (.there .here))) (.bvar .here))))
    (.equal (.bvar (.there .here)) (.bvar .here)))))

def bounded_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.forallE .set (.imp
    (.conj (member_m (.bvar (.there .here)) ((ω.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))
      (at_m φ (.bvar (.there .here)) (.bvar .here)))
    (ThirdOrderTheory.subset_m (.bvar .here) ((A.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))))

def image_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω B : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (member_m (.bvar .here) (B.weakenBound SetTheory.SetSort.set))
    (.existsE .set (.conj (member_m (.bvar .here) ((ω.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set))
      (at_m φ (.bvar .here) (.bvar (.there .here))))))

/-- 自由槽仅为原公式参数；ω、母集和输出集全部显式绑定。 -/
def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Formula ℒ [] Δ :=
  .forallE .set (.forallE .set (
    let ω : Term ℒ [.set, .set] Δ .set := .bvar (.there .here)
    let A : Term ℒ [.set, .set] Δ .set := .bvar .here
    .imp (SecondOrderOmegaSyntax.omega_m ω)
      (.imp (.conj (total_m φ ω) (.conj (unique_m φ ω) (bounded_m φ ω A)))
        (.existsE .set (image_m φ (ω.weakenBound SetTheory.SetSort.set) (.bvar .here))))))

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)

private abbrev quotient_l := SecondOrderQuotient.structure_l hℳ

theorem schema_formula_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) :
    (schema_m φ).satisfies η ↔ ∀ ω A : SecondOrderQuotient.type_l hℳ,
      SecondOrderOmega.omega_l hℳ ω →
      (∀ x, SecondOrderQuotient.mem_l hℳ x ω → ∃ y, φ.satisfies ((η.pushFree x).pushFree y)) →
      (∀ x y z, SecondOrderQuotient.mem_l hℳ x ω →
        φ.satisfies ((η.pushFree x).pushFree y) →
        φ.satisfies ((η.pushFree x).pushFree z) → y = z) →
      (∀ x y, SecondOrderQuotient.mem_l hℳ x ω →
        φ.satisfies ((η.pushFree x).pushFree y) →
        ∀ t, SecondOrderQuotient.mem_l hℳ t y → SecondOrderQuotient.mem_l hℳ t A) →
      ∃ B, ∀ y, SecondOrderQuotient.mem_l hℳ y B ↔
        ∃ x, SecondOrderQuotient.mem_l hℳ x ω ∧ φ.satisfies ((η.pushFree x).pushFree y) := by
  simp only [schema_m, total_m, unique_m, bounded_m, image_m, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, ThirdOrderSemantics.subset_formula_l,
    at_formula_l, member_m, Arguments.eval, Term.eval_weakenBound, Term.eval,
    parameters_pushBound_l, parameters_empty_l,
    ThirdOrderSemantics.subset_l, ThirdOrderSemantics.member_l]
  simp only [and_imp]
  rfl

theorem models_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env (quotient_l hℳ) [] Δ) : (schema_m φ).satisfies η := by
  apply (schema_formula_l hℳ φ η).mpr
  intro ω A hω hTotal hUnique hBound
  obtain ⟨C⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain rfl := SecondOrderOmega.unique_l hℳ hω C.omega_spec
  obtain ⟨B, hB⟩ := PowerlessBMSQuotientSubsetImage.exists_l C φ η A
    (fun n => hTotal (numberCode_l C n).val (numberCode_l C n).property)
    (fun n y z => hUnique (numberCode_l C n).val y z (numberCode_l C n).property)
    (fun n y => hBound (numberCode_l C n).val y (numberCode_l C n).property)
  refine ⟨B, fun y => (hB y).trans ?_⟩
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨(numberCode_l C n).val, (numberCode_l C n).property, hn⟩
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨n, hn⟩ := numberCode_surjective_l C ⟨x, hx⟩
    have hn' : (numberCode_l C n).val = x := congrArg Subtype.val hn
    exact ⟨n, hn'.symm ▸ hxy⟩

/-- 每个纯源公式实例经同一图翻译后，由原 Z₂ 正式推出。 -/
theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ)) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  exact (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr (models_l hℳ φ)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientSubsetImageDerives
