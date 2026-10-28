import BMSConstructibleBridge.PowerlessKleeneBrouwerPathAppend

/-! # 实际下一分支与追加前缀纤维的对应

纯隶属 ℒ，原 Z₂。同根下降路径中出现的下一值确是旧末节点的 A 前驱；
追加前缀的扩展集精确等于旧前缀扩展中固定该下一值的纤维。
同一 raw 图保持不变，不对纤维增加 Class 资格假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathBranch

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassSequenceSplit (prefix_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)
open PowerlessKleeneBrouwerPrefix (extension_l extension_m extension_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

private theorem not_self_l (x : Raw) : ¬mem_l hℳ x x := by
  obtain ⟨X, rfl⟩ := SecondOrderQuotient.surj_l hℳ x
  exact SecondOrderFoundation.irrefl_l hℳ X

theorem edge_l {ω I A z r p n k a b f : Raw}
    (hPath : path_l (𝒩 := 𝒱) ω I A z r f) (hp : map_l (ℳ := 𝒱) p n I)
    (hk : mem_l hℳ k n) (hLast : PowerlessNatural.successor_l (ℳ := 𝒱) k n)
    (hpa : value_l (ℳ := 𝒱) p k a) (hExt : extension_l (𝒩 := 𝒱) ω I p n f)
    (hfb : value_l (ℳ := 𝒱) f n b) : value_l (ℳ := 𝒱) A b a := by
  obtain ⟨m, _hm, hf, _hRoot, hEdges⟩ := hPath
  obtain ⟨l, _hl, hF, hInclude, hPrefix⟩ := hExt
  have hSame : m = l := PowerlessKleeneBrouwerDecisive.domain_unique_l hf hF
  subst l
  have haI := (SecondOrderFunctionProperties.value_mem_l hℳ hp hpa).2
  obtain ⟨hnm, hbI⟩ := SecondOrderFunctionProperties.value_mem_l hℳ hf hfb
  exact hEdges k (hInclude k hk) n hnm hLast a haI b hbI ((hPrefix k hk a haI).mp hpa) hfb

theorem extension_iff_l {ω I p n q s b f : Raw}
    (hp : map_l (ℳ := 𝒱) p n I) (hb : mem_l hℳ b I)
    (hSucc : PowerlessNatural.successor_l (ℳ := 𝒱) n s)
    (hRead : ∀ i a, value_l (ℳ := 𝒱) q i a ↔ value_l (ℳ := 𝒱) p i a ∨ i = n ∧ a = b) :
    extension_l (𝒩 := 𝒱) ω I q s f ↔
      extension_l (𝒩 := 𝒱) ω I p n f ∧ value_l (ℳ := 𝒱) f n b := by
  constructor
  · rintro ⟨m, hm, hf, hInclude, hPrefix⟩
    have hOld i (hi : mem_l hℳ i n) a :
        value_l (ℳ := 𝒱) q i a ↔ value_l (ℳ := 𝒱) p i a :=
      (hRead i a).trans ⟨fun h => h.elim id
        (fun h => (not_self_l n (h.1 ▸ hi)).elim), Or.inl⟩
    refine ⟨⟨m, hm, hf, fun i hi => hInclude i ((hSucc i).mpr (Or.inl hi)), ?_⟩, ?_⟩
    · intro i hi a ha
      exact (hOld i hi a).symm.trans (hPrefix i ((hSucc i).mpr (Or.inl hi)) a ha)
    · exact (hPrefix n ((hSucc n).mpr (Or.inr rfl)) b hb).mp
        ((hRead n b).mpr (Or.inr ⟨rfl, rfl⟩))
  · rintro ⟨hExt, hfb⟩
    exact PowerlessKleeneBrouwerPrefix.branch_refine_l hp hSucc hRead hExt hfb

def schema_m {Δ : SortContext ℒ} (ω I p n q s b f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessMapBounded.formula_m p n I) <| .imp (SecondOrderObjectSyntax.member_m b I) <|
    .imp (PowerlessSuccessorBounded.formula_m n s) <|
      .imp (SecondOrderFunctionAppendDerives.reading_m p n b q) <|
        .iff (extension_m ω I q s f)
          (.conj (extension_m ω I p n f) (PowerlessValueBounded.formula_m f n b))

def sentence_m {Δ : SortContext ℒ} (ω I p n q s b f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I p n q s b f)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I p n q s b f : Term ℒ [] Δ .set) : (sentence_m ω I p n q s b f).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessMapBounded.formula_l,
    SecondOrderObjectSyntax.member_m, PowerlessSuccessorBounded.formula_l,
    SecondOrderFunctionAppendDerives.reading_m, ThirdOrderSemantics.value_formula_l,
    extension_formula_l, PowerlessValueBounded.formula_l,
    Arguments.eval, Term.eval_weakenBound, Term.eval]
  exact fun hp hb hSucc hRead => extension_iff_l (hℳ := hℳ) hp hb hSucc hRead

theorem derives_m {Δ : SortContext ℒ} (ω I p n q s b f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I p n q s b f)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I p n q s b f)

def edge_schema_m {Δ : SortContext ℒ} (ω I A z r p n k a b f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (path_m ω I A z r f) <| .imp (PowerlessMapBounded.formula_m p n I) <|
    .imp (SecondOrderObjectSyntax.member_m k n) <| .imp (PowerlessSuccessorBounded.formula_m k n) <|
      .imp (PowerlessValueBounded.formula_m p k a) <| .imp (extension_m ω I p n f) <|
        .imp (PowerlessValueBounded.formula_m f n b) (PowerlessValueBounded.formula_m A b a)

def edge_sentence_m {Δ : SortContext ℒ} (ω I A z r p n k a b f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (edge_schema_m ω I A z r p n k a b f)

theorem edge_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I A z r p n k a b f : Term ℒ [] Δ .set) :
    (edge_sentence_m ω I A z r p n k a b f).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [edge_schema_m, Formula.satisfies, path_formula_l, PowerlessMapBounded.formula_l,
    SecondOrderObjectSyntax.member_m, PowerlessSuccessorBounded.formula_l,
    PowerlessValueBounded.formula_l, extension_formula_l, Arguments.eval]
  exact fun hPath hp hk hLast hpa hExt hfb => edge_l (hℳ := hℳ) hPath hp hk hLast hpa hExt hfb

theorem edge_derives_m {Δ : SortContext ℒ} (ω I A z r p n k a b f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (edge_sentence_m ω I A z r p n k a b f)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => edge_models_l hℳ ω I A z r p n k a b f)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathBranch
