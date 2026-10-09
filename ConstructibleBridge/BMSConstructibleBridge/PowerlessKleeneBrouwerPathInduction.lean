import BMSConstructibleBridge.PowerlessKleeneBrouwerPathFiber
import BMSConstructibleBridge.PowerlessWeakSetInduction
import BMSConstructibleBridge.SecondOrderCollapseSyntax

/-! # 原坍缩输出上的内部路径最小元归纳

纯隶属 ℒ，原 Z₂。归纳点量化全部同根有效前缀和 raw 子集，
子节点的实际 H 值属于当前 H 值，故原集合归纳提供该分支最小元。
H/T 只作 raw 归纳参数，不作 Class 分离参数；没有外部良基归纳。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathInduction

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)
open PowerlessKleeneBrouwerPrefix (extension_l extension_m extension_formula_l)
open PowerlessKleeneBrouwerSyntax (compare_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def node_m {Γ Δ : SortContext ℒ} (ω I A z r p n k a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (path_m ω I A z r p) <| .conj (PowerlessMapBounded.formula_m p n I) <|
    .conj (PowerlessSuccessorBounded.formula_m k n) (PowerlessValueBounded.formula_m p k a)

def cone_m {Γ Δ : SortContext ℒ} (ω I A z r p n U : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall U <|
    .conj (path_m (up ω) (up I) (up A) (up z) (up r) (.bvar .here))
      (extension_m (up ω) (up I) (up p) (up n) (.bvar .here))

def good_m {Γ Δ : SortContext ℒ} (ω I A z r p n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <|
    .imp (cone_m (up ω) (up I) (up A) (up z) (up r) (up p) (up n) (.bvar .here)) <|
      .imp (.existsE .set (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))
        (PowerlessKleeneBrouwerMinimumStep.minimum_m (up ω) (up I) (.bvar .here))

def point_m {Γ Δ : SortContext ℒ} (ω I A z r H X : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall I <|
    .imp (PowerlessValueBounded.formula_m (up H) (.bvar .here) (up X)) <|
      .forallE .set <| membershipLevyBound.boundedForall (up (up ω)) <|
        membershipLevyBound.boundedForall (.bvar .here) <|
          let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
          let a : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set :=
            .bvar (.there (.there (.there .here)))
          let p : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
          let n : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
          let k : Term ℒ (.set :: .set :: .set :: .set :: Γ) Δ .set := .bvar .here
          .imp (node_m (w ω) (w I) (w A) (w z) (w r) p n k a)
            (good_m (w ω) (w I) (w A) (w z) (w r) p n)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

def node_l (ω I A z r p n k a : Raw) : Prop :=
  path_l (𝒩 := 𝒱) ω I A z r p ∧ map_l (ℳ := 𝒱) p n I ∧
    PowerlessNatural.successor_l (ℳ := 𝒱) k n ∧ value_l (ℳ := 𝒱) p k a

def cone_l (ω I A z r p n U : Raw) : Prop :=
  ∀ f, mem_l hℳ f U → path_l (𝒩 := 𝒱) ω I A z r f ∧ extension_l (𝒩 := 𝒱) ω I p n f

def good_l (ω I A z r p n : Raw) : Prop :=
  ∀ U, cone_l ω I A z r p n U → (∃ f, mem_l hℳ f U) →
    ∃ f, mem_l hℳ f U ∧ ∀ g, mem_l hℳ g U → ¬compare_l (𝒩 := 𝒱) ω I g f

def point_l (ω I A z r H X : Raw) : Prop :=
  ∀ a, mem_l hℳ a I → value_l (ℳ := 𝒱) H a X → ∀ p n, mem_l hℳ n ω →
    ∀ k, mem_l hℳ k n → node_l ω I A z r p n k a → good_l ω I A z r p n

theorem node_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω I A z r p n k a : Term ℒ Γ Δ .set) :
    (node_m ω I A z r p n k a).satisfies η ↔
      node_l (ω.eval η) (I.eval η) (A.eval η) (z.eval η) (r.eval η)
        (p.eval η) (n.eval η) (k.eval η) (a.eval η) := by
  simp only [node_m, node_l, Formula.satisfies, path_formula_l,
    PowerlessMapBounded.formula_l, PowerlessSuccessorBounded.formula_l, PowerlessValueBounded.formula_l]

theorem cone_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω I A z r p n U : Term ℒ Γ Δ .set) :
    (cone_m ω I A z r p n U).satisfies η ↔
      cone_l (ω.eval η) (I.eval η) (A.eval η) (z.eval η) (r.eval η) (p.eval η) (n.eval η) (U.eval η) := by
  simp only [cone_m, cone_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, path_formula_l, extension_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem good_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω I A z r p n : Term ℒ Γ Δ .set) :
    (good_m ω I A z r p n).satisfies η ↔
      good_l (ω.eval η) (I.eval η) (A.eval η) (z.eval η) (r.eval η) (p.eval η) (n.eval η) := by
  simp only [good_m, good_l, Formula.satisfies, cone_formula_l,
    SecondOrderObjectSyntax.member_m, PowerlessKleeneBrouwerMinimumStep.minimum_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem point_formula_l {Γ Δ : SortContext ℒ} (η : Env 𝒱 Γ Δ)
    (ω I A z r H X : Term ℒ Γ Δ .set) :
    (point_m ω I A z r H X).satisfies η ↔
      point_l (ω.eval η) (I.eval η) (A.eval η) (z.eval η) (r.eval η) (H.eval η) (X.eval η) := by
  simp only [point_m, point_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, node_formula_l, good_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 所有归纳见证均为原模型对象；分支子输出由原 H 方程落入 X。 -/
theorem step_l {ω I A z r T H X : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ b, mem_l hℳ b I → mem_l hℳ b ω)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (ih : ∀ Y, mem_l hℳ Y X → point_l ω I A z r H Y) :
    point_l ω I A z r H X := by
  intro a ha hHa p n hn k hk hNode U hCone hNonempty
  obtain ⟨hPathP, hp, hLast, hpa⟩ := hNode
  apply PowerlessKleeneBrouwerMinimumStep.step_l hω hSub hn hp
    (fun f hf => (hCone f hf).2) hNonempty
  intro b hb hBranch
  obtain ⟨f, hfU, hfb⟩ := hBranch
  have hEdge := PowerlessKleeneBrouwerPathBranch.edge_l
    (hCone f hfU).1 hp hk hLast hpa (hCone f hfU).2 hfb
  obtain ⟨Y, hY, _⟩ := hH.2.1.2 b hb
  have hYX : mem_l hℳ Y X :=
    (hH.2.2.2 a X ha hHa Y).mpr ⟨b, hb, hEdge, hY.2⟩
  obtain ⟨s, q, hs, hSucc, hq, hPathQ, hRead⟩ :=
    PowerlessKleeneBrouwerPathAppend.exists_l hω hPathP hn hp hk hLast hpa hb hEdge
  obtain ⟨V, hV⟩ := PowerlessKleeneBrouwerPathFiber.exists_l n b U
  have hNonV := PowerlessKleeneBrouwerPathFiber.nonempty_l hV ⟨f, hfU, hfb⟩
  have hPathsV := PowerlessKleeneBrouwerPathFiber.paths_l hV (fun f hf => (hCone f hf).1)
  have hExtV := PowerlessKleeneBrouwerPathFiber.extensions_l hV hp hb hSucc hRead
    (fun f hf => (hCone f hf).2)
  have hQnb := (hRead n b).mpr (Or.inr ⟨rfl, rfl⟩)
  have hNS := (hSucc n).mpr (Or.inr rfl)
  have hMinV := ih Y hYX b hb hY.2 q s hs n hNS
    ⟨hPathQ, hq, hSucc, hQnb⟩ V (fun f hf => ⟨hPathsV f hf, hExtV f hf⟩) hNonV
  exact PowerlessKleeneBrouwerPathFiber.minimum_transfer_l hV hMinV

/-- 对具体 point 公式调用原集合归纳，不将 raw H 提升为 Class 参数。 -/
theorem all_l {ω I A z r T H : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ b, mem_l hℳ b I → mem_l hℳ b ω)
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H) :
    ∀ X, point_l ω I A z r H X := by
  let η : Env 𝒱 [] [.set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree H |>.pushFree r |>.pushFree z |>.pushFree A |>.pushFree I |>.pushFree ω
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] := point_m
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there (.there (.there .here)))))
    (.fvar (.there (.there (.there (.there (.there .here))))))
    (.fvar (.there (.there (.there (.there (.there (.there .here))))))) (.fvar .here)
  have hFormula (X : Raw) : φ.satisfies (η.pushFree X) ↔ point_l ω I A z r H X :=
    point_formula_l (η.pushFree X) _ _ _ _ _ _ _
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) φ η
    (fun X ih => (hFormula X).mpr (step_l hω hSub hH
      (fun Y hY => (hFormula Y).mp (ih Y hY))))
  exact fun X => (hFormula X).mp (hAll X)

def schema_m {Δ : SortContext ℒ} (ω I A z r T H : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (ThirdOrderTheory.subset_m I ω) <|
      .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
        .forallE .set (point_m (up ω) (up I) (up A) (up z) (up r) (up H) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (ω I A z r T H : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m ω I A z r T H)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (ω I A z r T H : Term ℒ [] Δ .set) : (sentence_m ω I A z r T H).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, SecondOrderOmegaSyntax.omega_l,
    ThirdOrderSemantics.subset_formula_l, subset_l, SecondOrderCollapseSyntax.formula_l,
    point_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact all_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (ω I A z r T H : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m ω I A z r T H)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ ω I A z r T H)

#print axioms step_l
#print axioms all_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPathInduction
