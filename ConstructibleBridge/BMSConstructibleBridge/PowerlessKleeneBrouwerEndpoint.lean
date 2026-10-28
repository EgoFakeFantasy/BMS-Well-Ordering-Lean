import BMSConstructibleBridge.PowerlessKleeneBrouwerPathInduction
import BMSConstructibleBridge.SecondOrderNaturalCases
import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor

/-! # 有效下降路径的唯一末节点及前驱追加

纯隶属 ℒ，原 Z₂。路径长度包含根坐标，故内部自然数分情况排除零，
取得实际末坐标与唯一末节点。追加 A 前驱给出更小 KB 路径及其新末节点。
不以宿主有限列表或模型 ω 外部标准性取得末坐标。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerEndpoint

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def endpoint_m {Γ Δ : SortContext ℒ} (ω I f a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (.bvar .here) <|
    .conj (PowerlessMapBounded.formula_m (up (up f)) (.bvar (.there .here)) (up (up I))) <|
      .conj (PowerlessSuccessorBounded.formula_m (.bvar .here) (.bvar (.there .here)))
        (PowerlessValueBounded.formula_m (up (up f)) (.bvar .here) (up (up a)))

theorem endpoint_delta_l {Γ Δ : SortContext ℒ} (ω I f a : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (endpoint_m ω I f a) :=
  .bounded_exists _ (.bounded_exists _ (.conj (PowerlessMapBounded.delta_l _ _ _)
    (.conj (PowerlessSuccessorBounded.delta_l _ _) (PowerlessValueBounded.delta_l _ _ _))))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def endpoint_l (ω I f a : Raw) : Prop :=
  ∃ n, mem_l hℳ n ω ∧ ∃ k, mem_l hℳ k n ∧ map_l (ℳ := 𝒱) f n I ∧
    PowerlessNatural.successor_l (ℳ := 𝒱) k n ∧ value_l (ℳ := 𝒱) f k a

theorem endpoint_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ) (ω I f a : Term ℒ Γ Δ .set) :
    (endpoint_m ω I f a).satisfies η ↔ endpoint_l (ω.eval η) (I.eval η) (f.eval η) (a.eval η) := by
  simp only [endpoint_m, endpoint_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l,
    PowerlessSuccessorBounded.formula_l, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_l {ω I A z r f : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hPath : path_l (𝒩 := 𝒱) ω I A z r f) : ∃ a, mem_l hℳ a I ∧ endpoint_l ω I f a := by
  obtain ⟨n, hn, hf, hRoot, _⟩ := hPath
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hSame := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  have hnK : mem_l hℳ n K.omega := hSame ▸ hn
  rcases SecondOrderNaturalCases.cases_l K hnK with hZero | ⟨k, _hkω, hLast⟩
  · have hzn := (SecondOrderFunctionProperties.value_mem_l hℳ hf hRoot).1
    exact (PowerlessBMSQuotientSuccessor.zero_l K z (hZero ▸ hzn)).elim
  · have hkn := (hLast k).mpr (Or.inr rfl)
    obtain ⟨a, ha, _⟩ := hf.2 k hkn
    exact ⟨a, ha.1, n, hn, k, hkn, hf, hLast, ha.2⟩

theorem unique_l {ω I f a b : Raw} (ha : endpoint_l ω I f a) (hb : endpoint_l ω I f b) : a = b := by
  obtain ⟨n, _hn, k, _hk, hf, hLast, hfa⟩ := ha
  obtain ⟨m, _hm, l, _hl, hf', hLast', hfb⟩ := hb
  have hSame := PowerlessKleeneBrouwerDecisive.domain_unique_l hf hf'
  subst m
  have hSameLast := SecondOrderNaturalCases.successor_injective_l hℳ hLast hLast'
  subst l
  exact SecondOrderFunctionProperties.value_unique_l hℳ hf hfa hfb

theorem append_l {ω I A z r f a b : Raw} (hω : SecondOrderOmega.omega_l hℳ ω)
    (hPath : path_l (𝒩 := 𝒱) ω I A z r f) (hEnd : endpoint_l ω I f a)
    (hb : mem_l hℳ b I) (hEdge : value_l (ℳ := 𝒱) A b a) :
    ∃ q, path_l (𝒩 := 𝒱) ω I A z r q ∧ endpoint_l ω I q b ∧
      PowerlessKleeneBrouwerSyntax.compare_l (𝒩 := 𝒱) ω I q f := by
  obtain ⟨n, hn, k, hk, hf, hLast, hfa⟩ := hEnd
  obtain ⟨s, q, hs, hSucc, hq, hPathQ, hRead⟩ :=
    PowerlessKleeneBrouwerPathAppend.exists_l hω hPath hn hf hk hLast hfa hb hEdge
  have hqb := (hRead n b).mpr (Or.inr ⟨rfl, rfl⟩)
  have hns := (hSucc n).mpr (Or.inr rfl)
  have hExt := ((PowerlessKleeneBrouwerPathBranch.extension_iff_l hf hb hSucc hRead).mp
    (PowerlessKleeneBrouwerPrefix.reflexive_l hs hq)).1
  have hNe : q ≠ f := by
    intro hEq
    have hnn := (SecondOrderFunctionProperties.value_mem_l hℳ hf (hEq ▸ hqb)).1
    obtain ⟨N, rfl⟩ := SecondOrderQuotient.surj_l hℳ n
    exact SecondOrderFoundation.irrefl_l hℳ N hnn
  have hEndQ : endpoint_l ω I q b := ⟨s, hs, n, hns, hq, hSucc, hqb⟩
  exact ⟨q, hPathQ, hEndQ,
    (PowerlessKleeneBrouwerPrefix.length_cases_l hω hn hf hExt).resolve_left hNe⟩

def schema_m {Δ : SortContext ℒ} (ω I A z r f : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (path_m ω I A z r f) <|
    membershipLevyBound.boundedExists I <|
      .conj (endpoint_m (up ω) (up I) (up f) (.bvar .here)) <|
        membershipLevyBound.boundedForall (up I) <|
          .imp (endpoint_m (up (up ω)) (up (up I)) (up (up f)) (.bvar .here))
            (.equal (.bvar .here) (.bvar (.there .here)))

def sentence_m {Δ : SortContext ℒ} (ω I A z r f : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I A z r f)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I A z r f : Term ℒ [] Δ .set) : (sentence_m ω I A z r f).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l, path_formula_l,
    Formula.LevyBound.boundedExists, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, endpoint_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  intro hω hPath
  obtain ⟨a, ha, hEnd⟩ := exists_l (hℳ := hℳ) hω hPath
  exact ⟨a, ha, hEnd, fun b _hb hEndB => unique_l hEndB hEnd⟩

theorem derives_m {Δ : SortContext ℒ} (ω I A z r f : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I A z r f)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I A z r f)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerEndpoint
