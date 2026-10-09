import BMSConstructibleBridge.PowerlessRelativeClassDefinableTraceReading
import BMSConstructibleBridge.PowerlessRelativeClassCanonicalSkolemReading
import BMSConstructibleBridge.PowerlessRelativeClassDefinableFiniteTraceDerives

/-! # 类内任意总关系的有限历史及原 Z₂ 对象推导

对象语言纯隶属 ℒ，背景为原 num/set Z₂；交付句经原 GraphTranslation
进入 Derives。每个外部有限矩阵实例允许所有内部自然数长度。构造沿用
原公式归纳得到的同一图，不能把本定理解读为无限轨迹或 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNativeFiniteTraceDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessRelativeClassFormulaInstances (instance_m instance_l members_m members_l)
open PowerlessRelativeClassCanonicalSkolemReading (request_m request_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l)
open PowerlessDefinableFiniteTraceDerives (total_m zero_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem exists_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (b e a n : Term ℒ [] Δ .set)
    (η : Env 𝒩₀ [] Δ) (hb : (b.eval η).val = B)
    (he : (e.eval η).val = (numberCode_l K (SecondOrderModel.zero_l ℳ)).val)
    (hTotal : ∀ x : M, ∃ y : M, φ.satisfies ((η.pushFree x).pushFree y))
    (hn : mem_l hℳ (n.eval η).val K.omega) :
    ∃ S D f : M, PowerlessDefinableFiniteTrace.trace_l φ η (e.eval η) (a.eval η) (n.eval η) S D f := by
  let ξ := PowerlessRelativeClassRelativization.env_l η
  have hTerm (t : Term ℒ [] Δ .set) : t.eval ξ = (t.eval η).val := by
    simpa only [ξ, Term.eval_weakenFree] using PowerlessRelativeClassRelativization.term_l η t
  have hbRaw : b.eval ξ = B := (hTerm b).trans hb
  have hBaseRaw : ∀ x, mem_l hℳ x (b.eval ξ) → ∀ y, mem_l hℳ y x → mem_l hℳ y (b.eval ξ) := by
    simpa only [hbRaw] using hBase
  have haRaw : PowerlessRelativeClassCorrespondence.member_l hℳ (b.eval ξ) (a.eval ξ) := by
    simpa only [hbRaw, hTerm a] using (a.eval η).property
  have hTotalRaw : ∀ x, PowerlessRelativeClassCorrespondence.member_l hℳ (b.eval ξ) x →
      ∃ y, PowerlessRelativeClassCorrespondence.member_l hℳ (b.eval ξ) y ∧
        (request_m φ b).satisfies ((ξ.pushFree x).pushFree y) := by
    intro x hx
    let x₀ : M := ⟨x, hbRaw ▸ hx⟩
    obtain ⟨y, hy⟩ := hTotal x₀
    exact ⟨y.val, hbRaw.symm ▸ y.property, (request_formula_l K φ b η hb x₀ y).mpr hy⟩
  obtain ⟨i, hi⟩ := numberCode_surjective_l K ⟨(n.eval η).val, hn⟩
  have hi' : (numberCode_l K i).val = (n.eval η).val := congrArg Subtype.val hi
  obtain ⟨S, D, f, hD, hf, hTrace⟩ := PowerlessRelativeClassDefinableFiniteTrace.exists_l
    K (request_m φ b) ξ b e a hBaseRaw haRaw ((hTerm e).trans he) hTotalRaw i
  apply (PowerlessRelativeClassDefinableTraceReading.finite_l φ (request_m φ b) η ξ
    (fun x y => request_formula_l K φ b η hb x y) (e.eval η) (a.eval η) (n.eval η)).mpr
  exact ⟨S, D, f, hbRaw ▸ hD, hbRaw ▸ hf, by
    simpa only [hTerm e, hTerm a, hi'] using hTrace⟩

def conclusion_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (ω e a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (total_m φ) <| .imp (SecondOrderObjectSyntax.member_m n ω)
    (PowerlessDefinableFiniteTrace.finite_m φ e a n)

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (zero_m e) <|
      .imp (members_m Δ B (fun v => .fvar v)) <|
        instance_m (conclusion_m φ ω e a n) B (fun v => .fvar v)

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
    PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ,
    SecondOrderOmegaSyntax.omega_l, PowerlessDefinableFiniteTraceDerives.zero_formula_l,
    members_l K]
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
  apply (instance_l K (conclusion_m φ ω e a n) η b (fun v => .fvar v) ξ rfl (fun _ => rfl)).mpr
  simp only [conclusion_m, total_m, Formula.satisfies,
    PowerlessBMSQuotientSubsetImageDerives.at_formula_l,
    PowerlessBMSQuotientSubsetImageDerives.parameters_pushBound_l, parameters_empty_l,
    PowerlessDefinableFiniteTrace.finite_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval, Env.pushBound_bound_here, Env.pushBound_bound_there]
  intro hTotal hn
  change mem_l hℳ (n.eval ξ).val (ω.eval ξ).val at hn
  have hn' : mem_l hℳ (n.eval ξ).val K.omega := by
    have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
    simpa only [hTerm ω, hωEq] using hn
  exact exists_l (hBase := hBase) K φ b e a n ξ (hTerm b) he' hTotal hn'

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω e a n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ B ω e a n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B ω e a n)

#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassNativeFiniteTraceDerives
