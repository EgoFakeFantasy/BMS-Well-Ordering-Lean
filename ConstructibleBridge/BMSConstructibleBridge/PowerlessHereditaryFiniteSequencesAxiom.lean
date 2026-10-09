import BMSConstructibleBridge.PowerlessHereditaryFiniteSequencesDerives
import BMSConstructibleBridge.PowerlessHereditaryOmegaAbsolute
import BMSConstructibleBridge.PowerlessHereditaryBounded

/-! # 实际遗传子模型内的有限序列集存在

统一可数传递包络先证明 S 遗传，再用纯 Δ₀ 序列检查在原商、相对类与
遗传子模型之间双向搬运。正式出口回到原 Z₂ 的 Derives 核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFiniteSequencesAxiom

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  PowerlessRelativeClassStructure.structure_l SetTheory.Definitional.Project.FirstOrderSemantics.reduct

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
      ((PowerlessHereditaryBounded.formula_l (hBase := hBase) (φ := φ)
        (PowerlessRelativeClassFiniteSequences.sequence_delta_l _ _ _) η).trans
          (PowerlessRelativeClassFiniteSequences.sequence_formula_l
            (PowerlessHereditaryRelativization.env_l η) (.fvar (.there .here))
            (.fvar (.there (.there .here))) (.fvar .here)))

theorem exists_l {ω X : type_l hℳ B} (hω : omega_l (ℳ := structure_l hℳ B hBase) ω) :
    ∃ S : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω X S := by
  let ω' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨ω.val, PowerlessHereditaryClass.contained_l hℳ hBase ω.property⟩
  let X' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨X.val, PowerlessHereditaryClass.contained_l hℳ hBase X.property⟩
  have hω' := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mpr
    ((PowerlessHereditaryOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω)
  have hX' := (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) X').mp X.property
  obtain ⟨S, hS, hSEnv⟩ := PowerlessHereditaryFiniteSequences.exists_l (hBase := hBase) (X := X') hω' hX'
  let S' : type_l hℳ B := ⟨S.val,
    (PowerlessHereditaryClassInternals.correspondence_l (hBase := hBase) S).mpr hSEnv⟩
  refine ⟨S', fun f => ?_⟩
  let f' : PowerlessRelativeClassStructure.type_l hℳ B :=
    ⟨f.val, PowerlessHereditaryClass.contained_l hℳ hBase f.property⟩
  exact (hS f').trans ((PowerlessRelativeClassFiniteSequencesDerives.sequence_absolute_l
    (hBase := hBase) ω' X' f').trans (sequence_absolute_l (hBase := hBase) ω X f).symm)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    PowerlessFiniteSequencesSyntax.sentence_m.TrueIn (structure_l hℳ B hBase) :=
  PowerlessRelativeClassFiniteSequencesDerives.sentence_l.mpr (fun _ hω _ => exists_l (hBase := hBase) hω)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessHereditaryRelativization.guarded_m PowerlessFiniteSequencesSyntax.sentence_m)) :=
  PowerlessHereditaryRelativization.derives_m _ (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

#print axioms sequence_absolute_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFiniteSequencesAxiom
