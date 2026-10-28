import BMSConstructibleBridge.PowerlessRelativeClassEnumerationUnionDerives
import BMSConstructibleBridge.PowerlessHereditaryExtension

/-! # 两个可数传递包络的配对扩张

先把两个包络的类内枚举交错，再用已证单点扩张把配对对象加入并包络。
这样配对对象本身有类内可数传递包络，不只证明它属于相对类。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryPairEnvelope

open Logic FirstOrder ThirdOrderSemantics PowerlessHereditaryClassInternals
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {X Y P : type_l hℳ B}
    (hX : envelope_l (𝒩 := structure_l hℳ B hBase) X)
    (hY : envelope_l (𝒩 := structure_l hℳ B hBase) Y)
    (hP : ∀ z : type_l hℳ B, mem_l hℳ z.val P.val ↔ z = X ∨ z = Y) :
    envelope_l (𝒩 := structure_l hℳ B hBase) P := by
  obtain ⟨U, G, ω, hXU, hUTrans, hω, hG, hGOnto⟩ := hX
  obtain ⟨V, H, ω', hYV, hVTrans, hω', hH, hHOnto⟩ := hY
  have hEq : ω' = ω := Subtype.ext (SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω').mp hω')
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω))
  subst ω'
  have hPair := PowerlessRelativeClassStructure.pairing_l hℳ B hBase
  change ∀ a b : type_l hℳ B, ∃ p : type_l hℳ B, ∀ z : type_l hℳ B,
    mem_l hℳ z.val p.val ↔ z = a ∨ z = b at hPair
  obtain ⟨T, hT⟩ := hPair U V
  have hUnion := PowerlessRelativeClassBasicAxioms.union_l hℳ B hBase
  change ∀ a : type_l hℳ B, ∃ w : type_l hℳ B, ∀ z : type_l hℳ B,
    mem_l hℳ z.val w.val ↔ ∃ y : type_l hℳ B, mem_l hℳ y.val a.val ∧ mem_l hℳ z.val y.val at hUnion
  obtain ⟨W, hW'⟩ := hUnion T
  have hW (z : type_l hℳ B) : mem_l hℳ z.val W.val ↔ mem_l hℳ z.val U.val ∨ mem_l hℳ z.val V.val := by
    refine (hW' z).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy, hzy⟩
      exact ((hT y).mp hy).elim (fun h => Or.inl (h ▸ hzy)) (fun h => Or.inr (h ▸ hzy))
    · rintro (hz | hz)
      · exact ⟨U, (hT U).mpr (Or.inl rfl), hz⟩
      · exact ⟨V, (hT V).mpr (Or.inr rfl), hz⟩
  obtain ⟨F, hF, hOnto⟩ := PowerlessRelativeClassEnumerationUnion.exists_l hω hG hH hGOnto hHOnto hW
  apply PowerlessHereditaryExtension.exists_l ω P W F hω ?_ ?_ hF hOnto
  · intro x hx y hy
    exact (hW y).mpr (((hW x).mp hx).elim
      (fun hxU => Or.inl (hUTrans x hxU y hy)) (fun hxV => Or.inr (hVTrans x hxV y hy)))
  · intro z hz
    exact (hW z).mpr (((hP z).mp hz).elim
      (fun h => Or.inl (h.symm ▸ hXU)) (fun h => Or.inr (h.symm ▸ hYV)))

def schema_m : Formula ℒ [] [.set, .set, .set] :=
  .imp (envelope_m (.fvar .here)) <| .imp (envelope_m (.fvar (.there .here))) <|
    .imp (SecondOrderObjectSyntax.pair_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here))))
      (envelope_m (.fvar (.there (.there .here))))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l hℳ)
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B) :
    sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, envelope_formula_l, pair_formula_l]
  exact exists_l

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m sentence_m (fun _ h𝒩 B hBase => models_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryPairEnvelope
