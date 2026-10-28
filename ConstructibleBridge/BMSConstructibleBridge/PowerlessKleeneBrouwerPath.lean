import BMSConstructibleBridge.PowerlessKleeneBrouwerAppend

/-! # 有界下降路径及其真实前缀

纯隶属 ℒ，原 Z₂。固定根坐标 z 与根节点 r；内部相邻坐标上的
后一个值是前一个值的 A 前驱。实际路径 AST 为 Δ₀，保留原 ω/I/A。
包含根坐标的真实前缀仍是同根下降路径。良基性与 Class 存在另证。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPath

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassSequenceSplit (prefix_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def edges_m {Γ Δ : SortContext ℒ} (n I A f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall n <| membershipLevyBound.boundedForall (up n) <|
    .imp (PowerlessSuccessorBounded.formula_m (.bvar (.there .here)) (.bvar .here)) <|
      membershipLevyBound.boundedForall (up (up I)) <|
        membershipLevyBound.boundedForall (up (up (up I))) <|
          let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
          let i : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there .here)))
          let j : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
          let a : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
          let b : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
          .imp (PowerlessValueBounded.formula_m (w f) i a) <|
            .imp (PowerlessValueBounded.formula_m (w f) j b) (PowerlessValueBounded.formula_m (w A) b a)

theorem edges_delta_l {Γ Δ : SortContext ℒ} (n I A f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (edges_m n I A f) :=
  .bounded_forall _ (.bounded_forall _ (.imp (PowerlessSuccessorBounded.delta_l _ _) <|
    .bounded_forall _ (.bounded_forall _ (.imp (PowerlessValueBounded.delta_l _ _ _)
      (.imp (PowerlessValueBounded.delta_l _ _ _) (PowerlessValueBounded.delta_l _ _ _))))))

def edges_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (n I A f : carrier_l 𝒩) : Prop :=
  ∀ i, member_l 𝒩 i n → ∀ j, member_l 𝒩 j n → PowerlessNatural.successor_l (ℳ := 𝒩) i j →
    ∀ a, member_l 𝒩 a I → ∀ b, member_l 𝒩 b I → value_l f i a → value_l f j b → value_l A b a

theorem edges_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (n I A f : Term ℒ Γ Δ .set) :
    (edges_m n I A f).satisfies η ↔ edges_l (n.eval η) (I.eval η) (A.eval η) (f.eval η) := by
  simp only [edges_m, edges_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessSuccessorBounded.formula_l,
    PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def path_m {Γ Δ : SortContext ℒ} (ω I A z r f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <|
    .conj (PowerlessMapBounded.formula_m (up f) (.bvar .here) (up I)) <|
      .conj (PowerlessValueBounded.formula_m (up f) (up z) (up r))
        (edges_m (.bvar .here) (up I) (up A) (up f))

theorem path_delta_l {Γ Δ : SortContext ℒ} (ω I A z r f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (path_m ω I A z r f) :=
  .bounded_exists _ (.conj (PowerlessMapBounded.delta_l _ _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (edges_delta_l _ _ _ _)))

def path_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω I A z r f : carrier_l 𝒩) : Prop :=
  ∃ n, member_l 𝒩 n ω ∧ map_l f n I ∧ value_l f z r ∧ edges_l n I A f

theorem path_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω I A z r f : Term ℒ Γ Δ .set) :
    (path_m ω I A z r f).satisfies η ↔
      path_l (ω.eval η) (I.eval η) (A.eval η) (z.eval η) (r.eval η) (f.eval η) := by
  simp only [path_m, path_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l,
    PowerlessValueBounded.formula_l, edges_formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem restrict_l {ω I A z r f p n : Raw} (hPath : path_l (𝒩 := 𝒱) ω I A z r f)
    (hn : mem_l hℳ n ω) (hp : map_l (ℳ := 𝒱) p n I) (hz : mem_l hℳ z n)
    (hPrefix : prefix_l (ℳ₀ := 𝒱) n I f p) : path_l (𝒩 := 𝒱) ω I A z r p := by
  obtain ⟨m, _hm, hf, hRoot, hEdges⟩ := hPath
  have hInclude i (hi : mem_l hℳ i n) : mem_l hℳ i m := by
    obtain ⟨a, ha, _⟩ := hp.2 i hi
    exact (SecondOrderFunctionProperties.value_mem_l hℳ hf ((hPrefix i hi a ha.1).mp ha.2)).1
  exact ⟨n, hn, hp, (hPrefix z hz r (SecondOrderFunctionProperties.value_mem_l hℳ hf hRoot).2).mpr hRoot,
    fun i hi j hj hSucc a ha b hb hpa hpb =>
      hEdges i (hInclude i hi) j (hInclude j hj) hSucc a ha b hb
        ((hPrefix i hi a ha).mp hpa) ((hPrefix j hj b hb).mp hpb)⟩

def schema_m {Δ : SortContext ℒ} (ω I A z r f p n : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (path_m ω I A z r f) <| .imp (SecondOrderObjectSyntax.member_m n ω) <|
    .imp (PowerlessMapBounded.formula_m p n I) <| .imp (SecondOrderObjectSyntax.member_m z n) <|
      .imp (PowerlessRelativeClassSequenceSplitDerives.prefix_m n I f p) (path_m ω I A z r p)

def sentence_m {Δ : SortContext ℒ} (ω I A z r f p n : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I A z r f p n)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I A z r f p n : Term ℒ [] Δ .set) : (sentence_m ω I A z r f p n).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, path_formula_l,
    SecondOrderObjectSyntax.member_m, PowerlessMapBounded.formula_l,
    PowerlessRelativeClassSequenceSplitDerives.prefix_formula_l, Arguments.eval]
  exact fun hPath hn hp hz hPrefix => restrict_l (hℳ := hℳ) hPath hn hp hz hPrefix

theorem derives_m {Δ : SortContext ℒ} (ω I A z r f p n : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I A z r f p n)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I A z r f p n)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPath
