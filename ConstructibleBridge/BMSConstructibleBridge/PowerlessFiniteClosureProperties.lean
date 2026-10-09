import BMSConstructibleBridge.PowerlessFiniteClosureMinimum

/-!
# 最小有限子集闭包的唯一性与传递性

传递性的证明仅分离出闭包中自身包含于闭包的元素。若母集传递，这个分离
子集仍是有限子集闭合超集，最小性迫使它等于原闭包。无需额外迭代或收集。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteClosureProperties

open Logic FirstOrder ThirdOrderSemantics PowerlessFiniteClosureSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def transitive_l (x : carrier_l ℳ) : Prop :=
  ∀ a, member_l ℳ a x → subset_l a x

theorem unique_l (hℳ : Theory.Models ℳ SecondOrderWeakSetTheory.theory_m)
    {ω x c d : carrier_l ℳ} (hc : closure_l ω x c) (hd : closure_l ω x d) : c = d := by
  have hExt := hℳ _ SecondOrderWeakSetTheory.axiom_m.extensionality
  change ∀ a b : carrier_l ℳ, (∀ z, member_l ℳ z a ↔ member_l ℳ z b) → a = b at hExt
  exact hExt c d (fun z => ⟨hc.2.2 d hd.1 hd.2.1 z, hd.2.2 c hc.1 hc.2.1 z⟩)

theorem transitive_of_l (hℳ : Theory.Models ℳ SecondOrderWeakSetTheory.theory_m)
    {ω x c : carrier_l ℳ} (hx : transitive_l x) (hc : closure_l ω x c) :
    transitive_l c := by
  let φ : Formula ℒ [] [.set, .set] := subset_m (.fvar .here) (.fvar (.there .here))
  let η : Env ℳ [] [.set] := (Env.empty (M := ℳ)).pushFree c
  have hφ z : φ.satisfies (η.pushFree z) ↔ subset_l z c :=
    PowerlessFiniteClosureSyntax.subset_formula_l _ _ _
  have hSep := hℳ _ (SecondOrderWeakSetTheory.axiom_m.separation φ)
  have hSep' := (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mp hSep η
  obtain ⟨d, hd⟩ := (PowerlessWeakSeparationSyntax.schema_formula_l φ η).mp hSep' c
  have hmem z : member_l ℳ z d ↔ member_l ℳ z c ∧ subset_l z c :=
    (hd z).trans (and_congr Iff.rfl (hφ z))
  have hdc : subset_l d c := fun z hz => ((hmem z).mp hz).1
  have hxd : subset_l x d := fun z hz =>
    (hmem z).mpr ⟨hc.1 z hz, fun a ha => hc.1 a (hx z hz a ha)⟩
  have hClosed : closed_l ω d := fun a ha had =>
    (hmem a).mpr ⟨hc.2.1 a ha (fun z hz => hdc z (had z hz)),
      fun z hz => hdc z (had z hz)⟩
  exact fun z hz => ((hmem z).mp (hc.2.2 d hxd hClosed z hz)).2

#print axioms unique_l
#print axioms transitive_of_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteClosureProperties
