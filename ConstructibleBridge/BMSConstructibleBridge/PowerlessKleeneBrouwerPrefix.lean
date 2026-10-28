import BMSConstructibleBridge.PowerlessKleeneBrouwerComparison
import BMSConstructibleBridge.PowerlessSuccessorBounded

/-! # 固定前缀及下一分支的 KB 比较

纯隶属 ℒ，原 Z₂。前缀扩展条件使用内部长度界与显式定义域包含，
可作 Δ₀ 分离。下一分支的值足以决定不同分支之间的 KB 方向；
同一分支可改用追加后的前缀，不需要构造尾序列。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPrefix

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassSequenceSplit (prefix_l)
open PowerlessKleeneBrouwerSyntax (compare_l compare_m compare_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def extension_m {Γ Δ : SortContext ℒ} (ω I p n f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <|
    .conj (PowerlessMapBounded.formula_m (up f) (.bvar .here) (up I)) <|
      .conj (membershipLevyBound.boundedForall (up n)
        (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))
        (PowerlessRelativeClassSequenceSplitDerives.prefix_m (up n) (up I) (up f) (up p))

theorem extension_delta_l {Γ Δ : SortContext ℒ} (ω I p n f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (extension_m ω I p n f) :=
  .bounded_exists _ (.conj (PowerlessMapBounded.delta_l _ _ _) <|
    .conj (.bounded_forall _ (.rel _ _))
      (PowerlessRelativeClassSequenceSplitDerives.prefix_delta_l _ _ _ _))

def extension_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω I p n f : carrier_l 𝒩) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ map_l f m I ∧
    (∀ i, member_l 𝒩 i n → member_l 𝒩 i m) ∧ prefix_l n I f p

theorem extension_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω I p n f : Term ℒ Γ Δ .set) :
    (extension_m ω I p n f).satisfies η ↔
      extension_l (ω.eval η) (I.eval η) (p.eval η) (n.eval η) (f.eval η) := by
  simp only [extension_m, extension_l, Formula.LevyBound.boundedExists,
    Formula.LevyBound.boundedForall, Formula.LevyBound.membership, membershipLevyBound,
    Formula.satisfies, PowerlessMapBounded.formula_l,
    PowerlessRelativeClassSequenceSplitDerives.prefix_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem not_self_l (x : Raw) : ¬mem_l hℳ x x := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact SecondOrderFoundation.irrefl_l hℳ X

theorem reflexive_l {ω I p n : Raw} (hn : mem_l hℳ n ω)
    (hp : map_l (ℳ := 𝒱) p n I) : extension_l (𝒩 := 𝒱) ω I p n p :=
  ⟨n, hn, hp, fun _ h => h, fun _ _ _ _ => Iff.rfl⟩

theorem length_cases_l {ω I p n f : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hn : mem_l hℳ n ω) (hp : map_l (ℳ := 𝒱) p n I)
    (hExt : extension_l (𝒩 := 𝒱) ω I p n f) :
    f = p ∨ compare_l (𝒩 := 𝒱) ω I f p := by
  obtain ⟨m, hm, hf, hInclude, hPrefix⟩ := hExt
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ hω
  rcases hOrd.wellOrder.linear.compare n hn m hm with hEq | hnm | hmn
  · have hSame : n = m := SecondOrderQuotient.ext_l hℳ n m hEq
    subst m
    exact Or.inl (PowerlessKleeneBrouwerComparison.prefix_ext_l hf hp hPrefix)
  · exact Or.inr (PowerlessKleeneBrouwerSyntax.extension_l
      (𝒩 := 𝒱) (n := m) (m := n) (f := f) (g := p) hm hn hf hp hnm hPrefix)
  · exact (not_self_l m (hInclude m hmn)).elim

theorem branch_compare_l {ω I p n f g a b : Raw}
    (hF : extension_l (𝒩 := 𝒱) ω I p n f) (hG : extension_l (𝒩 := 𝒱) ω I p n g)
    (hfa : value_l (ℳ := 𝒱) f n a) (hgb : value_l (ℳ := 𝒱) g n b)
    (hab : mem_l hℳ a b) : compare_l (𝒩 := 𝒱) ω I f g := by
  obtain ⟨m, hm, hf, _hNm, hPrefixF⟩ := hF
  obtain ⟨k, hk, hg, _hNk, hPrefixG⟩ := hG
  exact PowerlessKleeneBrouwerDecisive.to_compare_l hm hk hf hg
    ⟨fun i hi c hc => (hPrefixG i hi c hc).symm.trans (hPrefixF i hi c hc),
      a, (SecondOrderFunctionProperties.value_mem_l hℳ hf hfa).2, hfa, Or.inr
        ⟨b, (SecondOrderFunctionProperties.value_mem_l hℳ hg hgb).2, hgb, hab⟩⟩

theorem branch_refine_l {ω I p n q s f b : Raw}
    (hp : map_l (ℳ := 𝒱) p n I)
    (hSucc : PowerlessNatural.successor_l (ℳ := 𝒱) n s)
    (hRead : ∀ i a, value_l (ℳ := 𝒱) q i a ↔
      value_l (ℳ := 𝒱) p i a ∨ i = n ∧ a = b)
    (hF : extension_l (𝒩 := 𝒱) ω I p n f) (hfb : value_l (ℳ := 𝒱) f n b) :
    extension_l (𝒩 := 𝒱) ω I q s f := by
  obtain ⟨m, hm, hf, hInclude, hPrefix⟩ := hF
  refine ⟨m, hm, hf, ?_, ?_⟩
  · intro i hi
    rcases (hSucc i).mp hi with hi | hEq
    · exact hInclude i hi
    · subst i
      exact (SecondOrderFunctionProperties.value_mem_l hℳ hf hfb).1
  · intro i hi a ha
    rcases (hSucc i).mp hi with hi | hEq
    · have hNe : i ≠ n := fun h => not_self_l n (h ▸ hi)
      have hOld : value_l (ℳ := 𝒱) q i a ↔ value_l (ℳ := 𝒱) p i a :=
        (hRead i a).trans ⟨fun h => h.elim id (fun h => (hNe h.1).elim), Or.inl⟩
      exact hOld.trans (hPrefix i hi a ha)
    · subst i
      constructor
      · intro hqa
        rcases (hRead n a).mp hqa with hpa | ⟨_, rfl⟩
        · exact (not_self_l n (SecondOrderFunctionProperties.value_mem_l hℳ hp hpa).1).elim
        · exact hfb
      · intro hfa
        have hEq := SecondOrderFunctionProperties.value_unique_l hℳ hf hfa hfb
        exact (hRead n a).mpr (Or.inr ⟨rfl, hEq⟩)

def schema_m {Δ : SortContext ℒ} (ω I p n f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (SecondOrderObjectSyntax.member_m n ω) <|
    .imp (PowerlessMapBounded.formula_m p n I) <| .imp (extension_m ω I p n f)
      (.disj (.equal f p) (compare_m ω I f p))

def sentence_m {Δ : SortContext ℒ} (ω I p n f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I p n f)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I p n f : Term ℒ [] Δ .set) : (sentence_m ω I p n f).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    SecondOrderObjectSyntax.member_m, PowerlessMapBounded.formula_l,
    extension_formula_l, compare_formula_l, Arguments.eval]
  exact fun hω hn hp hf => length_cases_l (hℳ := hℳ) hω hn hp hf

theorem derives_m {Δ : SortContext ℒ} (ω I p n f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I p n f)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I p n f)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPrefix
