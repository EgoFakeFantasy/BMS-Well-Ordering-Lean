import BMSConstructibleBridge.PowerlessKleeneBrouwerEndpointPrefix
import BMSConstructibleBridge.PowerlessKleeneBrouwerReachable

/-! # 路径的全部实际值落入可达域

纯隶属 ℒ，原 Z₂。每个 f(k) 由真实终止前缀见证可达，故原路径图
同一对象 f 可改读为 n→D；无须替换图或选择新列。反向扩大陪域
单独保留真实值唯一性，用于受限关系上的路径对应。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathCodomain

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem map_shrink_l {f n I D : Raw} (hf : map_l (ℳ := 𝒱) f n I)
    (hSub : ∀ a, mem_l hℳ a D → mem_l hℳ a I)
    (hValues : ∀ k a, value_l (ℳ := 𝒱) f k a → mem_l hℳ a D) :
    map_l (ℳ := 𝒱) f n D := by
  constructor
  · intro p hp
    obtain ⟨k, a, hk, _ha, hPair⟩ := hf.1 p hp
    exact ⟨k, a, hk, hValues k a ⟨p, hp, hPair⟩, hPair⟩
  · intro k hk
    obtain ⟨a, ha, hUnique⟩ := hf.2 k hk
    exact ⟨a, ⟨hValues k a ha.2, ha.2⟩, fun b hb => hUnique b ⟨hSub b hb.1, hb.2⟩⟩

theorem map_enlarge_l {f n I D : Raw} (hf : map_l (ℳ := 𝒱) f n D)
    (hSub : ∀ a, mem_l hℳ a D → mem_l hℳ a I) : map_l (ℳ := 𝒱) f n I := by
  constructor
  · intro p hp
    obtain ⟨k, a, hk, ha, hPair⟩ := hf.1 p hp
    exact ⟨k, a, hk, hSub a ha, hPair⟩
  · intro k hk
    obtain ⟨a, ha, hUnique⟩ := hf.2 k hk
    exact ⟨a, ⟨hSub a ha.1, ha.2⟩, fun b hb =>
      hUnique b ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hf hb.2).2, hb.2⟩⟩

theorem values_l {ω I A z r S D f : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l ω I S D)
    (hPath : path_l (𝒩 := 𝒱) ω I A z r f) :
    ∀ k a, value_l (ℳ := 𝒱) f k a → mem_l hℳ a D := by
  intro k a hfa
  obtain ⟨p, hPathP, hEndP⟩ := PowerlessKleeneBrouwerEndpointPrefix.prefix_l hω hZero hPath hfa
  obtain ⟨_n, _hn, hf, _, _⟩ := hPath
  exact (hD a).mpr ⟨(SecondOrderFunctionProperties.value_mem_l hℳ hf hfa).2, p,
    (hS p).mpr hPathP, hEndP⟩

theorem map_l {ω I A z r S D f n : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l ω I S D)
    (hPath : path_l (𝒩 := 𝒱) ω I A z r f) (hf : ThirdOrderSemantics.map_l (ℳ := 𝒱) f n I) :
    ThirdOrderSemantics.map_l (ℳ := 𝒱) f n D :=
  map_shrink_l hf (fun a ha => ((hD a).mp ha).1) (values_l hω hZero hS hD hPath)

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def schema_m {Δ : SortContext ℒ} (ω I A z r S D f n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up z)))) <|
      .imp (PowerlessKleeneBrouwerPathClass.reading_m ω I A z r S) <|
        .imp (PowerlessKleeneBrouwerReachable.reading_m ω I S D) <|
          .imp (path_m ω I A z r f) <| .imp (PowerlessMapBounded.formula_m f n I)
            (PowerlessMapBounded.formula_m f n D)

def sentence_m {Δ : SortContext ℒ} (ω I A z r S D f n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I A z r S D f n)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I A z r S D f n : Term ℒ [] Δ .set) : (sentence_m ω I A z r S D f n).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l, SecondOrderObjectSyntax.member_m,
    PowerlessKleeneBrouwerPathClass.reading_formula_l, PowerlessKleeneBrouwerReachable.reading_formula_l,
    path_formula_l, PowerlessMapBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact map_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (ω I A z r S D f n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I A z r S D f n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I A z r S D f n)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathCodomain
