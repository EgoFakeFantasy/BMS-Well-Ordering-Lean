import BMSConstructibleBridge.PowerlessKleeneBrouwerPathBranch

/-! # 同一 raw 子集的实际分支纤维

纯隶属 ℒ，原 Z₂。原分离产生 V={f∈U:f(n)=b} 的精确成员方程；
追加前缀的扩展资格与路径资格保留，V 的最小元回传为 U 的分支最小元。
不假定 U/V 属于 Class，也不预供任意集合的最小元。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathFiber

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l)
open PowerlessKleeneBrouwerPrefix (extension_l)
open PowerlessKleeneBrouwerSyntax (compare_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def reading_l (n b U V : Raw) : Prop :=
  ∀ f, mem_l hℳ f V ↔ mem_l hℳ f U ∧ value_l (ℳ := 𝒱) f n b

theorem exists_l (n b U : Raw) : ∃ V, reading_l n b U V := by
  let φ : Formula ℒ [] [.set, .set, .set] :=
    PowerlessValueBounded.formula_m (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))
  let η : Env 𝒱 [] [.set, .set] := ((Env.empty).pushFree b).pushFree n
  have hφRead f : φ.satisfies (η.pushFree f) ↔ value_l (ℳ := 𝒱) f n b := by
    simp only [φ, η, PowerlessValueBounded.formula_l, Term.eval]
    rfl
  obtain ⟨V, hV⟩ := (SecondOrderSeparationAxiom.schema_l hℳ φ η).mp
    (SecondOrderSeparationAxiom.models_l hℳ φ η) U
  exact ⟨V, fun f => (hV f).trans (and_congr Iff.rfl (hφRead f))⟩

theorem nonempty_l {n b U V : Raw} (hV : reading_l n b U V)
    (hBranch : ∃ f, mem_l hℳ f U ∧ value_l (ℳ := 𝒱) f n b) : ∃ f, mem_l hℳ f V := by
  obtain ⟨f, hf⟩ := hBranch
  exact ⟨f, (hV f).mpr hf⟩

theorem paths_l {ω I A z r n b U V : Raw} (hV : reading_l n b U V)
    (hU : ∀ f, mem_l hℳ f U → path_l (𝒩 := 𝒱) ω I A z r f) :
    ∀ f, mem_l hℳ f V → path_l (𝒩 := 𝒱) ω I A z r f :=
  fun f hf => hU f ((hV f).mp hf).1

theorem extensions_l {ω I p n q s b U V : Raw} (hV : reading_l n b U V)
    (hp : map_l (ℳ := 𝒱) p n I) (hb : mem_l hℳ b I)
    (hSucc : PowerlessNatural.successor_l (ℳ := 𝒱) n s)
    (hRead : ∀ i a, value_l (ℳ := 𝒱) q i a ↔ value_l (ℳ := 𝒱) p i a ∨ i = n ∧ a = b)
    (hU : ∀ f, mem_l hℳ f U → extension_l (𝒩 := 𝒱) ω I p n f) :
    ∀ f, mem_l hℳ f V → extension_l (𝒩 := 𝒱) ω I q s f := by
  intro f hf
  obtain ⟨hfU, hfb⟩ := (hV f).mp hf
  exact (PowerlessKleeneBrouwerPathBranch.extension_iff_l hp hb hSucc hRead).mpr ⟨hU f hfU, hfb⟩

theorem minimum_transfer_l {ω I n b U V : Raw} (hV : reading_l n b U V)
    (hMin : ∃ f, mem_l hℳ f V ∧ ∀ g, mem_l hℳ g V → ¬compare_l (𝒩 := 𝒱) ω I g f) :
    ∃ f, mem_l hℳ f U ∧ value_l (ℳ := 𝒱) f n b ∧
      ∀ g, mem_l hℳ g U → value_l (ℳ := 𝒱) g n b → ¬compare_l (𝒩 := 𝒱) ω I g f := by
  obtain ⟨f, hf, hLeast⟩ := hMin
  obtain ⟨hfU, hfb⟩ := (hV f).mp hf
  exact ⟨f, hfU, hfb, fun g hg hgb => hLeast g ((hV g).mpr ⟨hg, hgb⟩)⟩

def reading_m {Γ Δ : SortContext ℒ} (n b U V : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up V)) <|
    .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up U))
      (PowerlessValueBounded.formula_m (.bvar .here) (up n) (up b))

theorem reading_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (n b U V : Term ℒ Γ Δ .set) :
    (reading_m n b U V).satisfies η ↔ reading_l (n.eval η) (b.eval η) (U.eval η) (V.eval η) := by
  simp only [reading_m, reading_l, Formula.satisfies, SecondOrderObjectSyntax.member_m,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def schema_m {Δ : SortContext ℒ} (n b U : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .existsE .set (reading_m (up n) (up b) (up U) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (n b U : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m n b U)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (n b U : Term ℒ [] Δ .set) : (sentence_m n b U).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, reading_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ) _ _ _

theorem derives_m {Δ : SortContext ℒ} (n b U : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m n b U)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ n b U)

#print axioms exists_l
#print axioms extensions_l
#print axioms minimum_transfer_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathFiber
