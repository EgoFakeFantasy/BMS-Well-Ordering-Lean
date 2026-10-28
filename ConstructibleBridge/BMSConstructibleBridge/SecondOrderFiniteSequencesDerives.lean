import BMSConstructibleBridge.PowerlessFiniteSequencesSyntax
import BMSConstructibleBridge.SecondOrderFiniteSubsetsDerives
import BMSConstructibleBridge.SecondOrderFunctionEnumeration
import BMSConstructibleBridge.SecondOrderOmegaTransitive

/-!
# 任意母集的内部有限序列集合：原 Z₂ 对象推导

每个有限序列函数图是 ω×X 的内部有限子集。先形成该乘积的有限子集集合，
再按实际序列公式分离；所有内部长度及实际函数都双向覆盖，不使用 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteSequencesDerives

open Logic FirstOrder SecondOrderQuotient PowerlessFiniteSequencesSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    (ω : type_l hℳ) (hω : SecondOrderOmega.omega_l hℳ ω) (x : type_l hℳ) :
    ∃ s, spec_l (ℳ := structure_l hℳ) ω x s := by
  obtain ⟨p, hp⟩ := SecondOrderDefinableRelationImage.exists_l hℳ
    (Δ := []) (.equal (.fvar .here) (.fvar .here)) Env.empty ω x
  have hProduct q : mem_l hℳ q p ↔ ∃ a b, mem_l hℳ a ω ∧ mem_l hℳ b x ∧
      SecondOrderPairObjects.ordered_l hℳ a b q := by
    simpa only [Formula.satisfies, Term.eval, true_and] using hp q
  obtain ⟨q, hq⟩ := SecondOrderFiniteSubsetsDerives.exists_l hℳ ω hω p
  have hBound f (hf : sequence_l (ℳ := structure_l hℳ) ω x f) : mem_l hℳ f q := by
    obtain ⟨k, hk, hf⟩ := hf
    change SecondOrderFunctionObjects.map_l hℳ f k x at hf
    refine (hq f).mpr ⟨SecondOrderFunctionEnumeration.finite_l hℳ hk hf, ?_⟩
    intro r hr
    obtain ⟨a, b, ha, hb, hab⟩ := hf.1 r hr
    exact (hProduct r).mpr ⟨a, b, SecondOrderOmegaTransitive.member_l hℳ hω hk ha, hb, hab⟩
  let φ : Formula ℒ [] [.set, .set, .set] :=
    sequence_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)
  let η : Env (structure_l hℳ) [] [.set, .set] := (Env.empty.pushFree ω).pushFree x
  have hφ f : φ.satisfies (η.pushFree f) ↔ sequence_l (ℳ := structure_l hℳ) ω x f :=
    sequence_formula_l _ _ _ _
  obtain ⟨s, hs⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) q
  refine ⟨s, fun f => (hs f).trans ((and_congr Iff.rfl (hφ f)).trans ?_)⟩
  exact ⟨fun h => h.2, fun h => ⟨hBound f h, h⟩⟩

theorem sentence_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (structure_l hℳ) ↔
      ∀ ω : type_l hℳ, SecondOrderOmega.omega_l hℳ ω →
        ∀ x, ∃ s, spec_l (ℳ := structure_l hℳ) ω x s := by
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    SecondOrderOmegaSyntax.omega_l, spec_formula_l, Term.eval]
  rfl

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (structure_l hℳ) :=
  (sentence_formula_l hℳ).mpr (exists_l hℳ)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteSequencesDerives
