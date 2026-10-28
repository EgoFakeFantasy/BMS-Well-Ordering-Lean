import BMSConstructibleBridge.PowerlessKleeneBrouwerEndpoint
import BMSConstructibleBridge.SecondOrderFunctionRestriction

/-! # 路径上每个实际值的终止前缀

纯隶属 ℒ，原 Z₂。根坐标为原零时，任意内部坐标 k 的后继初段包含根。
原限制构造真实前缀 p，p 仍是同根路径且其末节点等于给定 f(k)。
不把可达域只含末节点误当作已含路径中间节点。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerEndpointPrefix

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)
open PowerlessKleeneBrouwerEndpoint (endpoint_l endpoint_m endpoint_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem prefix_l {ω I A z r f k a : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z)
    (hPath : path_l (𝒩 := 𝒱) ω I A z r f) (hValue : value_l (ℳ := 𝒱) f k a) :
    ∃ p, path_l (𝒩 := 𝒱) ω I A z r p ∧ endpoint_l ω I p a := by
  obtain ⟨n, hn, hf, hRoot, hEdges⟩ := hPath
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hω
  have hkn := (SecondOrderFunctionProperties.value_mem_l hℳ hf hValue).1
  have hzn := (SecondOrderFunctionProperties.value_mem_l hℳ hf hRoot).1
  have hkω := hOrd.transitive n hn k hkn
  have hzω := hOrd.transitive n hn z hzn
  obtain ⟨s, hs, hSucc⟩ := hω.1.2 k hkω
  have hks := (hSucc k).mpr (Or.inr rfl)
  have hzs : mem_l hℳ z s := by
    rcases hOrd.wellOrder.linear.compare z hzω k hkω with hEq | hzk | hkz
    · exact (hSucc z).mpr (Or.inr (SecondOrderQuotient.ext_l hℳ z k hEq))
    · exact (hSucc z).mpr (Or.inl hzk)
    · exact (hZero k hkz).elim
  have hnOrd : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱) n :=
    SetTheory.Structure.IsOrdinal.mem hOrd hn
  have hInclude (i : Raw) (hi : mem_l hℳ i s) : mem_l hℳ i n := by
    rcases (hSucc i).mp hi with hik | hEq
    · exact hnOrd.transitive k hkn i hik
    · exact hEq.symm ▸ hkn
  obtain ⟨p, hp, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hf hInclude
  have hPrefix : PowerlessRelativeClassSequenceSplit.prefix_l (ℳ₀ := 𝒱) s I f p := by
    intro i hi b _hb
    exact ⟨fun h => ((hRead i b).mp h).2, fun h => (hRead i b).mpr ⟨hi, h⟩⟩
  have hPathP : path_l (𝒩 := 𝒱) ω I A z r p :=
    PowerlessKleeneBrouwerPath.restrict_l (hℳ := hℳ) (p := p) ⟨n, hn, hf, hRoot, hEdges⟩ hs hp hzs hPrefix
  have hEndP : endpoint_l ω I p a := ⟨s, hs, k, hks, hp, hSucc, (hRead k a).mpr ⟨hks, hValue⟩⟩
  exact ⟨p, hPathP, hEndP⟩

def schema_m {Δ : SortContext ℒ} (ω I A z r f k a : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up z)))) <|
      .imp (path_m ω I A z r f) <| .imp (PowerlessValueBounded.formula_m f k a) <|
        .existsE .set <| .conj
          (path_m (up ω) (up I) (up A) (up z) (up r) (.bvar .here))
          (endpoint_m (up ω) (up I) (.bvar .here) (up a))

def sentence_m {Δ : SortContext ℒ} (ω I A z r f k a : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I A z r f k a)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I A z r f k a : Term ℒ [] Δ .set) : (sentence_m ω I A z r f k a).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l, SecondOrderObjectSyntax.member_m,
    path_formula_l, PowerlessValueBounded.formula_l, endpoint_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  exact prefix_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (ω I A z r f k a : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I A z r f k a)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I A z r f k a)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerEndpointPrefix
