import BMSConstructibleBridge.PowerlessRelativeClassNativeFiniteTraceDerives
import BMSConstructibleBridge.PowerlessDefinableFiniteTraceUnique

/-! # 同一类内有限历史图的唯一性及原 Z₂ 推导

纯隶属 ℒ，背景原 num/set Z₂。原唯一性归纳要求 raw 关系单值，
因此显式给原请求加输入资格守卫，而非把类内单值性外推到域外。
两个历史的陪域可以不同；结论只认同实际图对象。最终良序仍另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNativeFiniteTraceUniqueDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassFormulaInstances (instance_m instance_l members_m members_l)
open PowerlessRelativeClassCanonicalSkolemReading (request_m request_formula_l output_class_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l parameters_pushBound_l)
open PowerlessDefinableFiniteTraceUnique (functional_m conclusion_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev free₂ {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) :=
  (t.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

/-- 两端资格都显式守卫，只用于原归纳的读数，不修改原请求接口。 -/
def relation_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B : Term ℒ [] Δ .set) : Formula ℒ [] (.set :: .set :: Δ) :=
  .conj (PowerlessRelativeHierarchySyntax.class_m (free₂ B) (.fvar (.there .here))) (request_m φ B)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem relation_formula_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (b : Term ℒ [] Δ .set)
    (η : Env 𝒱 [] Δ) (hb : b.eval η = B) (x y : SecondOrderQuotient.type_l hℳ) :
    (relation_m φ b).satisfies ((η.pushFree x).pushFree y) ↔
      PowerlessRelativeClassCorrespondence.member_l hℳ B x ∧
        (request_m φ b).satisfies ((η.pushFree x).pushFree y) := by
  change ((PowerlessRelativeHierarchySyntax.class_m (free₂ b)
    (show Term ℒ [] (.set :: .set :: Δ) .set from .fvar (.there .here))).satisfies
      ((η.pushFree x).pushFree y) ∧ _) ↔ _
  rw [PowerlessRelativeHierarchySemantics.class_formula_l K]
  have hb' : (free₂ b).eval ((η.pushFree x).pushFree y) = B := by
    simpa only [free₂, Term.eval_weakenFree] using hb
  rw [hb']
  rfl

theorem unique_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (b : Term ℒ [] Δ .set) (η : Env 𝒩₀ [] Δ)
    (hb : (b.eval η).val = B) (e a n S D f T E g : M)
    (hn : mem_l hℳ n.val K.omega)
    (he : e.val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hF : PowerlessDefinableFiniteTrace.trace_l φ η e a n S D f)
    (hG : PowerlessDefinableFiniteTrace.trace_l φ η e a n T E g)
    (hUnique : ∀ x y z : M, φ.satisfies ((η.pushFree x).pushFree y) →
      φ.satisfies ((η.pushFree x).pushFree z) → y = z) : f = g := by
  let ξ := PowerlessRelativeClassRelativization.env_l η
  have hbRaw : b.eval ξ = B := by
    have hTerm := PowerlessRelativeClassRelativization.term_l η b
    simp only [Term.eval_weakenFree] at hTerm
    exact hTerm.trans hb
  have hReading (x y : M) : (relation_m φ b).satisfies ((ξ.pushFree x.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree x).pushFree y) := by
    have hRel := relation_formula_l K φ b ξ hbRaw x.val y.val
    have hRequest := request_formula_l K φ b η hb x y
    exact ⟨fun h => hRequest.mp (hRel.mp h).2, fun h => hRel.mpr ⟨x.property, hRequest.mpr h⟩⟩
  have hUniqueRaw : ∀ x y z, (relation_m φ b).satisfies ((ξ.pushFree x).pushFree y) →
      (relation_m φ b).satisfies ((ξ.pushFree x).pushFree z) → y = z := by
    intro x y z hxy hxz
    have hxy' := (relation_formula_l K φ b ξ hbRaw x y).mp hxy
    have hxz' := (relation_formula_l K φ b ξ hbRaw x z).mp hxz
    let x₀ : M := ⟨x, hxy'.1⟩
    let y₀ : M := ⟨y, output_class_l K φ b ξ hbRaw x y hxy'.2⟩
    let z₀ : M := ⟨z, output_class_l K φ b ξ hbRaw x z hxz'.2⟩
    exact congrArg Subtype.val (hUnique x₀ y₀ z₀
      ((request_formula_l K φ b η hb x₀ y₀).mp hxy'.2)
      ((request_formula_l K φ b η hb x₀ z₀).mp hxz'.2))
  have hF' := (PowerlessRelativeClassDefinableTraceReading.trace_l
    φ (relation_m φ b) η ξ hReading e a n S D f).mp hF
  have hG' := (PowerlessRelativeClassDefinableTraceReading.trace_l
    φ (relation_m φ b) η ξ hReading e a n T E g).mp hG
  exact Subtype.ext (PowerlessDefinableFiniteTraceUnique.unique_l
    K (relation_m φ b) ξ hn he hF' hG' hUniqueRaw)

def guarded_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (functional_m φ) <| .imp (SecondOrderObjectSyntax.member_m n ω) (conclusion_m φ e a n)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (PowerlessDefinableFiniteTraceDerives.zero_m e) <|
      .imp (members_m Δ B (fun v => .fvar v)) <|
        instance_m (guarded_m φ ω e a n) B (fun v => .fvar v)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B ω e a n)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (b ω e a n : Term ℒ [] Δ .set) :
    (sentence_m φ b ω e a n).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies,
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ, SecondOrderOmegaSyntax.omega_l,
    PowerlessDefinableFiniteTraceDerives.zero_formula_l, members_l K]
  intro hBase hω he hMembers
  let ξ : Env (structure_l hℳ (b.eval η) hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hMembers v⟩ }
  have hEnv : PowerlessRelativeClassRelativization.env_l ξ = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v; cases s; rfl
  have hTerm (t : Term ℒ [] Δ .set) : (t.eval ξ).val = t.eval η := by
    have hRead := PowerlessRelativeClassRelativization.term_l ξ t
    simpa only [Term.eval_weakenFree, hEnv] using hRead.symm
  have he' : (e.eval ξ).val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val := by
    rw [hTerm]
    exact SecondOrderQuotient.ext_l hℳ _ _
      (fun x => iff_of_false (he x) (PowerlessBMSQuotientSuccessor.zero_l K x))
  apply (instance_l K (guarded_m φ ω e a n) η b (fun v => .fvar v) ξ rfl (fun _ => rfl)).mpr
  simp only [guarded_m, functional_m, conclusion_m, Formula.satisfies,
    PowerlessDefinableFiniteTrace.trace_formula_l, PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    parameters_pushBound_l, parameters_empty_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    Term.eval_weakenBound, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro hUnique hn S D f T E g hF hG
  change mem_l hℳ (n.eval ξ).val (ω.eval ξ).val at hn
  have hn' : mem_l hℳ (n.eval ξ).val K.omega := by
    simpa only [hTerm ω, SecondOrderOmega.unique_l hℳ hω K.omega_spec] using hn
  exact unique_l (hBase := hBase) K φ b ξ (hTerm b) (e.eval ξ) (a.eval ξ) (n.eval ξ)
    S D f T E g hn' he' hF hG hUnique

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ B ω e a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B ω e a n)

#print axioms relation_formula_l
#print axioms unique_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNativeFiniteTraceUniqueDerives
