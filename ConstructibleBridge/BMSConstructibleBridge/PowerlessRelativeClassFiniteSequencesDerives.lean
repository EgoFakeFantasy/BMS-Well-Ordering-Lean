import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequences
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassBounded

/-! # 相对类中内部有限序列集合存在的原 Z₂ 推导

任意类参数与 ω 先取共同层界，再扩大到非零极限层。
成员检查由已验证的 Δ₀ 绝对性双向搬运；没有加入完整源模型假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem sequence_absolute_l (ω X f : type_l hℳ B) :
    PowerlessFiniteSequencesSyntax.sequence_l (ℳ := structure_l hℳ B hBase) ω X f ↔
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val X.val f.val := by
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set] :=
    (((Env.empty).pushFree X).pushFree ω).pushFree f
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessRelativeClassFiniteSequences.sequence_m
    (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  exact (PowerlessRelativeClassFiniteSequences.sequence_formula_l η
    (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)).symm.trans
      ((PowerlessRelativeClassBounded.formula_l (hBase := hBase) (φ := φ)
        (PowerlessRelativeClassFiniteSequences.sequence_delta_l _ _ _) η).trans
          (PowerlessRelativeClassFiniteSequences.sequence_formula_l
            (PowerlessRelativeClassRelativization.env_l η) (.fvar (.there .here))
            (.fvar (.there (.there .here))) (.fvar .here)))

theorem exists_ambient_l {ω X : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ S : type_l hℳ B,
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω.val X.val S.val ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω X S := by
  obtain ⟨α, C₀, hC₀, hωC₀, hXC₀⟩ := PowerlessRelativeClassBounds.common_l hℳ hBase ω.property X.property
  obtain ⟨β, hβ, hαβ, hNoMax⟩ := SecondOrderOrdinalLimitDerives.exists_l hℳ α
    (PowerlessRelativeLevelClosure.ordinal_l hℳ hC₀)
  obtain ⟨C, hC⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase hβ
  obtain ⟨S, hSClass, hS⟩ := PowerlessRelativeClassFiniteSequences.exists_l hℳ hBase
    ⟨⟨α, hαβ⟩, hNoMax⟩ hC
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω)
    (PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC ω.val hωC₀)
    (PowerlessRelativeLevelClosure.subset_l hℳ hBase hαβ hC₀ hC X.val hXC₀)
  let S' : type_l hℳ B := ⟨S, hSClass⟩
  exact ⟨S', hS, fun f => (hS f.val).trans (sequence_absolute_l (hBase := hBase) ω X f).symm⟩

theorem exists_l {ω X : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ S : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω X S := by
  obtain ⟨S, _, hS⟩ := exists_ambient_l (hBase := hBase) hω
  exact ⟨S, hS⟩

theorem sentence_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} :
    PowerlessFiniteSequencesSyntax.sentence_m.TrueIn 𝒩 ↔
      ∀ ω : carrier_l 𝒩, omega_l (ℳ := 𝒩) ω → ∀ X,
        ∃ S, PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω X S := by
  simp only [PowerlessFiniteSequencesSyntax.sentence_m, Formula.TrueIn, Formula.satisfies,
    omega_formula_l, PowerlessFiniteSequencesSyntax.spec_formula_l, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    PowerlessFiniteSequencesSyntax.sentence_m.TrueIn (structure_l hℳ B hBase) :=
  sentence_l.mpr (fun _ hω _ => exists_l (hBase := hBase) hω)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m PowerlessFiniteSequencesSyntax.sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms sequence_absolute_l
#print axioms exists_ambient_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteSequencesDerives
