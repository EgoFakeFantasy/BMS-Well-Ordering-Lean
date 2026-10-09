import BMSConstructibleBridge.PowerlessRelativeClassCanonicalSkolemReading
import BMSConstructibleBridge.SecondOrderComparisonCoding

/-! # 类内原最小见证的总唯一性及原 Z₂ 推导

纯隶属 ℒ 的原请求，背景仅原 Z₂，出口为原 num/set 核中的 Derives。
总唯一性由原全局算子与完整覆盖比较的同值读数取得，参数和值保持同一。
种子良序、内部 ω 和实际参数 Class 资格仍是显式守卫；不宣称最终
BMS 良序、内部程序全轨迹资格或 Collection 已由本模块完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalSkolemDerives

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassFormulaInstances (instance_m instance_l members_m members_l)
open PowerlessRelativeClassCanonicalSkolemReading (request_m)
open SecondOrderCanonicalLevelDerives (guard_m guard_formula_l)
open PowerlessBMSQuotientSubsetImageDerives (parameters_empty_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.structure_l PowerlessRelativeClassStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => PowerlessRelativeClassStructure.structure_l hℳ B hBase
local notation "M" => PowerlessRelativeClassStructure.type_l hℳ B

/-- 原关系的实际输出只在 Prop 中包上已有资格，不抽取选择函数。 -/
theorem result_l (K : source_coding_l hℳ) {Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (b : Term ℒ [] Δ .set) (η : Env 𝒩₀ [] Δ)
    (hb : (b.eval η).val = B) (ω P₀ x : M) (hω : ω.val = K.omega)
    {t₁ t₂ t₃ Pair Valid : SecondOrderQuotient.type_l hℳ}
    (hCoding : SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid)
    (hGuard : SecondOrderCanonicalLevelDerives.guard_l B P₀.val) :
    ∃! y, PowerlessCanonicalCodedSkolemSyntax.relation_l (𝒩 := 𝒩₀) φ η
      ⟨B, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ ω P₀ x y := by
  let ξ := PowerlessRelativeClassRelativization.env_l η
  obtain ⟨y, hy, hUnique⟩ := SecondOrderCanonicalClassSkolem.result_l K hCoding hGuard
    (request_m φ b) ξ x.val
  let y₀ : M := ⟨y, SecondOrderCanonicalClassSkolem.class_l (request_m φ b) ξ hGuard hy⟩
  have hReading (z : M) := PowerlessRelativeClassCanonicalSkolemReading.relation_l
    (hBase := hBase) K φ b η hb ω P₀ x z hω hCoding
      hGuard.1 hGuard.2.2.1 hGuard.2.2.2
  refine ⟨y₀, (hReading y₀).mpr hy, ?_⟩
  intro z hz
  exact Subtype.ext (hUnique z.val ((hReading z).mp hz))

def schema_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω P₀ : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (guard_m B P₀) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (members_m Δ B (fun v => .fvar v)) <|
      instance_m (PowerlessCanonicalCodedSkolemSyntax.conclusion_m φ B ω P₀) B (fun v => .fvar v)

def sentence_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω P₀ : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m φ B ω P₀)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (b ω P₀ : Term ℒ [] Δ .set) :
    (sentence_m φ b ω P₀).TrueIn 𝒱 := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, guard_formula_l, SecondOrderOmegaSyntax.omega_l,
    members_l K₀, Term.eval]
  intro hGuard hω hMembers
  have hBase : ∀ z, mem_l hℳ z (b.eval η) → ∀ t,
      mem_l hℳ t z → mem_l hℳ t (b.eval η) :=
    fun z hz t ht => hGuard.2.1 z t hz ht
  let ξ : Env (PowerlessRelativeClassStructure.structure_l hℳ (b.eval η) hBase) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => ⟨η.freeVal v, hMembers v⟩ }
  have hEnv : PowerlessRelativeClassRelativization.env_l ξ = η := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro s v; cases s; rfl
  have hTerm (t : Term ℒ [] Δ .set) : (t.eval ξ).val = t.eval η := by
    have hRead := PowerlessRelativeClassRelativization.term_l ξ t
    simpa only [Term.eval_weakenFree, hEnv] using hRead.symm
  have hΩ : omega_l (ℳ := 𝒱) (ω.eval η) :=
    (omega_formula_l η ω).mp ((SecondOrderOmegaSyntax.omega_l hℳ η ω).mpr hω)
  obtain ⟨K, e, t₁, t₂, t₃, Pair, Valid, hωEq, _he, hCoding⟩ :=
    SecondOrderComparisonCoding.exists_l (hℳ := hℳ) hΩ
  apply (instance_l K₀ (PowerlessCanonicalCodedSkolemSyntax.conclusion_m φ b ω P₀)
    η b (fun v => .fvar v) ξ rfl (fun _ => rfl)).mpr
  apply (PowerlessCanonicalCodedSkolemSyntax.conclusion_formula_l
    (PowerlessRelativeClassStructure.ext_l hℳ (b.eval η) hBase) φ ξ b ω P₀).mpr
  simp only [parameters_empty_l]
  intro x
  have hGuard' : SecondOrderCanonicalLevelDerives.guard_l (b.eval η) (P₀.eval ξ).val := by
    rw [hTerm]
    exact hGuard
  obtain ⟨y, hy, hUnique⟩ := result_l (hBase := hBase) K φ b ξ (hTerm b)
    (ω.eval ξ) (P₀.eval ξ) x ((hTerm ω).trans hωEq) hCoding hGuard'
  have hb : b.eval ξ =
      ⟨b.eval η, PowerlessRelativeClassCorrespondence.base_object_l hℳ hBase⟩ :=
    Subtype.ext (hTerm b)
  rw [hb]
  exact ⟨y, hy, hUnique⟩

theorem derives_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (B ω P₀ : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m φ B ω P₀)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩 φ B ω P₀)

#print axioms result_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassCanonicalSkolemDerives
