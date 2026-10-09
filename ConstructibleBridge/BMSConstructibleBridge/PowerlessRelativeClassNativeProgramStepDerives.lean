import BMSConstructibleBridge.PowerlessRelativeClassProgramStepReading
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalSkolemReading
import BMSConstructibleBridge.PowerlessDefinableFiniteTraceUnique

/-! # 同一类内程序总单值状态转移的原 Z₂ 推导

对象语言纯隶属 ℒ，原 num/set Z₂ 为背景，出口为原 Derives。
任意类内算子矩阵先通过实际 Class 请求与原指令对应。单步总唯一性
保留无效状态的 B 缺省值；尚不能代替全程序闭包和最终良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNativeProgramStepDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassFormulaInstances (instance_m instance_l members_m members_l)
open PowerlessRelativeClassCanonicalSkolemReading (request_m request_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_l parameters_pushBound_l parameters_empty_l)
open PowerlessRelativeFiniteProgramInstruction (tags_m)
open PowerlessDefinableFiniteTraceUnique (functional_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)
private abbrev up₃ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up₂ t)

def result_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w e t₀ t₁ t₂ : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .existsE .set <| .conj
    (PowerlessFiniteProgramStepSyntax.step_m φ (up₂ B) (up₂ C) (up₂ ω) (up₂ w)
      (up₂ e) (up₂ t₀) (up₂ t₁) (up₂ t₂) (.bvar (.there .here)) (.bvar .here)) <|
      .forallE .set <| .imp
        (PowerlessFiniteProgramStepSyntax.step_m φ (up₃ B) (up₃ C) (up₃ ω) (up₃ w)
          (up₃ e) (up₃ t₀) (up₃ t₁) (up₃ t₂) (.bvar (.there (.there .here))) (.bvar .here))
        (.equal (.bvar .here) (.bvar (.there .here)))

theorem result_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ)) (η : Env 𝒩 Γ Δ)
    (B C ω w e t₀ t₁ t₂ : Term ℒ Γ Δ .set) :
    (result_m φ B C ω w e t₀ t₁ t₂).satisfies η ↔
      ∀ s, ∃! t, PowerlessFiniteProgramStepSyntax.step_l φ (parameters_l η)
        (B.eval η) (C.eval η) (ω.eval η) (w.eval η) (e.eval η)
          (t₀.eval η) (t₁.eval η) (t₂.eval η) s t := by
  simp only [result_m, Formula.satisfies, PowerlessFiniteProgramStepSyntax.step_formula_l,
    parameters_pushBound_l, up₃, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem result_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (b : Term ℒ [] Δ .set) (η : Env 𝒩₀ [] Δ)
    (hb : (b.eval η).val = B) (C ω w N Q e t₀ t₁ t₂ s : M)
    (hw : map_l (ℳ := 𝒩₀) w N Q) (hTags : t₀ ≠ t₁ ∧ t₀ ≠ t₂ ∧ t₁ ≠ t₂)
    (hFunctional : ∀ x y z : M, φ.satisfies ((η.pushFree x).pushFree y) →
      φ.satisfies ((η.pushFree x).pushFree z) → y = z) :
    ∃! t, PowerlessFiniteProgramStepSyntax.step_l φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ C ω w e t₀ t₁ t₂ s t := by
  let ξ := PowerlessRelativeClassRelativization.env_l η
  have hwRaw : map_l (ℳ := 𝒱) w.val N.val Q.val :=
    (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) w N Q).mp hw
  have hTagsRaw : t₀.val ≠ t₁.val ∧ t₀.val ≠ t₂.val ∧ t₁.val ≠ t₂.val :=
    ⟨fun h => hTags.1 (Subtype.ext h), fun h => hTags.2.1 (Subtype.ext h),
      fun h => hTags.2.2 (Subtype.ext h)⟩
  have hFunctionalRaw : PowerlessRelativeFiniteProgramInstruction.functional_l (request_m φ b) ξ B := by
    intro x y z hx hy hz hxy hxz
    let x₀ : M := ⟨x, hx⟩
    let y₀ : M := ⟨y, hy⟩
    let z₀ : M := ⟨z, hz⟩
    exact congrArg Subtype.val (hFunctional x₀ y₀ z₀
      ((request_formula_l K φ b η hb x₀ y₀).mp hxy)
      ((request_formula_l K φ b η hb x₀ z₀).mp hxz))
  obtain ⟨t, ht, hUnique⟩ := PowerlessRelativeFiniteProgramStep.exists_unique_l
    (hℳ := hℳ) (request_m φ b) ξ hBase C.property hwRaw hTagsRaw hFunctionalRaw s.val
  let t₀' : M := ⟨t, ht.1⟩
  have hReading (v : M) := PowerlessRelativeClassProgramStepReading.step_l φ (request_m φ b) η ξ
    (fun x y => request_formula_l K φ b η hb x y) C ω w e t₀ t₁ t₂ s v
  exact ⟨t₀', (hReading t₀').mpr ht, fun v hv => Subtype.ext (hUnique v.val ((hReading v).mp hv))⟩

def guarded_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderObjectSyntax.map_m w N Q) <| .imp (tags_m t₀ t₁ t₂) <|
    .imp (functional_m φ) (result_m φ B C ω w e t₀ t₁ t₂)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (members_m Δ B (fun v => .fvar v)) <|
      instance_m (guarded_m φ B C ω w N Q e t₀ t₁ t₂) B (fun v => .fvar v)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B C ω w N Q e t₀ t₁ t₂)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (b C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    (sentence_m φ b C ω w N Q e t₀ t₁ t₂).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, members_l K]
  intro hBase hMembers
  let ξ : Env (structure_l hℳ (b.eval η) hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hMembers v⟩ }
  have hEnv : PowerlessRelativeClassRelativization.env_l ξ = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v; cases s; rfl
  have hb : (b.eval ξ).val = b.eval η := by
    have hRead := PowerlessRelativeClassRelativization.term_l ξ b
    simpa only [Term.eval_weakenFree, hEnv] using hRead.symm
  apply (instance_l K (guarded_m φ b C ω w N Q e t₀ t₁ t₂)
    η b (fun v => .fvar v) ξ rfl (fun _ => rfl)).mpr
  simp only [guarded_m, functional_m, tags_m, Formula.satisfies,
    map_formula_l, result_formula_l, PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    parameters_pushBound_l, parameters_empty_l, Term.eval,
    Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro hw hTags hFunctional s
  have hb' : b.eval ξ = ⟨b.eval η, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ :=
    Subtype.ext hb
  rw [hb']
  exact result_l (hBase := hBase) K φ b ξ hb (C.eval ξ) (ω.eval ξ) (w.eval ξ)
    (N.eval ξ) (Q.eval ξ) (e.eval ξ) (t₀.eval ξ) (t₁.eval ξ) (t₂.eval ξ) s hw hTags hFunctional

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B C ω w N Q e t₀ t₁ t₂ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m φ B C ω w N Q e t₀ t₁ t₂)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B C ω w N Q e t₀ t₁ t₂)

#print axioms result_formula_l
#print axioms result_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNativeProgramStepDerives
