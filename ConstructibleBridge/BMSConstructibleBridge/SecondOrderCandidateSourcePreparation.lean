import BMSConstructibleBridge.SecondOrderCanonicalBaseGuard
import BMSConstructibleBridge.SecondOrderAllCountableSourceCore
import BMSConstructibleBridge.PowerlessRelativeClassArithmeticCandidate
import BMSConstructibleBridge.SecondOrderFiniteSequencesDerives
import BMSConstructibleBridge.PowerlessRealSeedEnumeration

/-! # 逐候选的实际源准备与剩余截断分支

对每个原模型实数 X，给出实际商代表、包含它的传递基集、完整
环境初始良序、统一编码及内部有限序列集合。精确基集为 ω∪{A}，
并另给真正属于相对类的基集满射；不以环境可数枚举替代它。全类可数时已得到
旧 candidate_source_l 的 Prop 存在性；另一分支明确保留首个类内
不可数序数，不以该序数的存在代替截断源模型的完整公理。
本模块是对象推导终局的语义中间构造，尚非最终 Z₂ Derives。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateSourcePreparation

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open SecondOrderCanonicalLevelDerives (guard_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessRelativeClassStructure.type_l PowerlessRelativeClassStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Ambient" => SecondOrderQuotient.structure_l hℳ

def context_l (K : source_coding_l hℳ) (t₁ t₂ t₃ Pair Valid B P₀ S : SecondOrderQuotient.type_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := Ambient) K.omega) (X : ℳ.Carrier .set) : Prop :=
  SecondOrderComparisonStageTotal.coding_l K t₁ t₂ t₃ Pair Valid ∧ guard_l B P₀ ∧
    PowerlessFiniteSequencesSyntax.spec_l (ℳ := Ambient) K.omega K.omega S ∧
      setRel_l K A X ∧ mem_l hℳ A.val B

def seed_context_l (K : source_coding_l hℳ) (t₁ t₂ t₃ Pair Valid B P₀ S : SecondOrderQuotient.type_l hℳ)
    (A : PowerlessArithmetic.set_l (ℳ := Ambient) K.omega) (X : ℳ.Carrier .set) : Prop :=
  context_l K t₁ t₂ t₃ Pair Valid B P₀ S A X ∧
    (∀ x, mem_l hℳ x B ↔ mem_l hℳ x K.omega ∨ x = A.val) ∧
      ∃ f, PowerlessRelativeClassCorrespondence.member_l hℳ B f ∧
        SecondOrderFunctionObjects.map_l hℳ f K.omega B ∧ ∀ y, mem_l hℳ y B →
          ∃ n, mem_l hℳ n K.omega ∧ SecondOrderFunctionObjects.value_l hℳ f n y

theorem seed_exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (X : ℳ.Carrier .set) :
    ∃ K : source_coding_l hℳ, ∃ t₁ t₂ t₃ Pair Valid B P₀ S,
      ∃ A : PowerlessArithmetic.set_l (ℳ := Ambient) K.omega,
        seed_context_l K t₁ t₂ t₃ Pair Valid B P₀ S A X := by
  obtain ⟨K₀⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  obtain ⟨K, _, t₁, t₂, t₃, Pair, Valid, _, _, hCoding⟩ :=
    SecondOrderComparisonCoding.exists_l (SecondOrderCanonicalBaseGuard.omega_l K₀)
  obtain ⟨A, hA⟩ := representative_exists_l K X
  obtain ⟨B, hSpec, hBase⟩ := PowerlessRealSeed.exists_l hℳ K.omega A.val K.omega_spec A.property
  have hAB := (hSpec A.val).mpr (Or.inr rfl)
  obtain ⟨P₀, hGuard⟩ := SecondOrderCanonicalBaseGuard.exists_l K hBase ⟨A.val, hAB⟩
  obtain ⟨S, hS⟩ := SecondOrderFiniteSequencesDerives.exists_l hℳ K.omega K.omega_spec K.omega
  exact ⟨K, t₁, t₂, t₃, Pair, Valid, B, P₀, S, A, ⟨hCoding, hGuard, hS, hA, hAB⟩,
    hSpec, PowerlessRealSeedEnumeration.enumeration_l K A.val B hSpec hBase⟩

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (X : ℳ.Carrier .set) :
    ∃ K : source_coding_l hℳ, ∃ t₁ t₂ t₃ Pair Valid B P₀ S,
      ∃ A : PowerlessArithmetic.set_l (ℳ := Ambient) K.omega,
        context_l K t₁ t₂ t₃ Pair Valid B P₀ S A X := by
  obtain ⟨K, t₁, t₂, t₃, Pair, Valid, B, P₀, S, A, hSeed⟩ := seed_exists_l hℳ X
  exact ⟨K, t₁, t₂, t₃, Pair, Valid, B, P₀, S, A, hSeed.1⟩

theorem all_countable_l (K : source_coding_l hℳ)
    {t₁ t₂ t₃ Pair Valid B P₀ S : SecondOrderQuotient.type_l hℳ}
    {A : PowerlessArithmetic.set_l (ℳ := Ambient) K.omega} {X : ℳ.Carrier .set}
    (hContext : context_l K t₁ t₂ t₃ Pair Valid B P₀ S A X)
    (hAll : ∀ a, SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct Ambient) a →
        PowerlessRelativeOrdinalCutoff.countable_l B K.omega a) :
    Nonempty (PowerlessBMSMatrixTransfer.candidate_source_l.{u, u} (M := ℳ) X) := by
  obtain ⟨hCoding, hGuard, hS, hA, hAB⟩ := hContext
  have hBase x hx y hy := hGuard.2.1 x y hx hy
  let ClassModel := PowerlessRelativeClassStructure.structure_l hℳ B hBase
  let ω : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨K.omega, PowerlessRelativeOrdinalCoverage.class_l hℳ K hBase
      (SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec)⟩
  let e : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
      PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
        (numberCode_l K (SecondOrderModel.zero_l ℳ)).property⟩
  let A' : PowerlessArithmetic.set_l (ℳ := ClassModel) ω :=
    ⟨⟨A.val, PowerlessRelativeClassCorrespondence.base_l hℳ hBase hAB⟩,
      fun x hx => A.property x.val hx⟩
  have hSource := SecondOrderAllCountableSourceCore.models_l (hBase := hBase)
    K hCoding hGuard hS hAll
  exact PowerlessRelativeClassArithmeticCandidate.candidate_l (hBase := hBase)
    K hSource (ω := ω) (e := e) rfl rfl X A' hA

/-- 已完成分支提供源证书；未完成分支返回同一候选准备数据及唯一截断序数。 -/
theorem candidate_or_cutoff_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (X : ℳ.Carrier .set) :
    Nonempty (PowerlessBMSMatrixTransfer.candidate_source_l.{u, u} (M := ℳ) X) ∨
      ∃ K : source_coding_l hℳ, ∃ t₁ t₂ t₃ Pair Valid B P₀ S,
        ∃ A : PowerlessArithmetic.set_l (ℳ := Ambient) K.omega,
          context_l K t₁ t₂ t₃ Pair Valid B P₀ S A X ∧
            ∃! α, PowerlessRelativeOrdinalCutoff.first_l B K.omega α := by
  obtain ⟨K, t₁, t₂, t₃, Pair, Valid, B, P₀, S, A, hContext⟩ := exists_l hℳ X
  rcases PowerlessRelativeOrdinalCutoff.dichotomy_l K B K.omega with hAll | hFirst
  · exact Or.inl (all_countable_l K hContext hAll)
  · exact Or.inr ⟨K, t₁, t₂, t₃, Pair, Valid, B, P₀, S, A, hContext, hFirst⟩

/-- 截断支保留精确基集与真正的类内满射，供较小层的可数性证明消费。 -/
theorem candidate_or_seed_cutoff_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (X : ℳ.Carrier .set) :
    Nonempty (PowerlessBMSMatrixTransfer.candidate_source_l.{u, u} (M := ℳ) X) ∨
      ∃ K : source_coding_l hℳ, ∃ t₁ t₂ t₃ Pair Valid B P₀ S,
        ∃ A : PowerlessArithmetic.set_l (ℳ := Ambient) K.omega,
          seed_context_l K t₁ t₂ t₃ Pair Valid B P₀ S A X ∧
            ∃! α, PowerlessRelativeOrdinalCutoff.first_l B K.omega α := by
  obtain ⟨K, t₁, t₂, t₃, Pair, Valid, B, P₀, S, A, hSeed⟩ := seed_exists_l hℳ X
  rcases PowerlessRelativeOrdinalCutoff.dichotomy_l K B K.omega with hAll | hFirst
  · exact Or.inl (all_countable_l K hSeed.1 hAll)
  · exact Or.inr ⟨K, t₁, t₂, t₃, Pair, Valid, B, P₀, S, A, hSeed, hFirst⟩

#print axioms exists_l
#print axioms all_countable_l
#print axioms candidate_or_cutoff_l
#print axioms seed_exists_l
#print axioms candidate_or_seed_cutoff_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCandidateSourcePreparation
