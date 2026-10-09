import BMSConstructibleBridge.PowerlessThreeDefBudgetExists
import BMSConstructibleBridge.PowerlessCanonicalOrderPrefixEquations
import BMSConstructibleBridge.PowerlessCanonicalOrderPrefixSuccessor
import BMSConstructibleBridge.PowerlessCanonicalOrderLastOutput
import BMSConstructibleBridge.PowerlessCanonicalOrderLightHistoryLimitPrefix

/-! # 原规范比较图的内部集合归纳预算核

对象语言为纯隶属 ℒ，背景为原 Z₂ 图商。point 对全部 raw 比较前缀、实际
预算值和实际层断言成员界；原弱集合归纳实例覆盖非标准模型的内部序数。
预算只包含五个实际 Class 参数和三次 Def，不预设前缀覆盖、Class 比较图、
统一枚举或 Collection。这里仍消费原比较方程及父序，其来源须在终端接入。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderBudgetInduction

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def point_m {Γ Δ : SortContext ℒ} (B G q Q a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    let w (t : Term ℒ Γ Δ .set) := up (up (up t))
    let δ : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there (.there .here))
    let C : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar (.there .here)
    let p : Term ℒ (.set :: .set :: .set :: Γ) Δ .set := .bvar .here
    .imp (PowerlessValueBounded.formula_m (w Q) (w a) δ) <|
      .imp (PowerlessRelativeHierarchySyntax.level_m (w B) δ C) <|
        .imp (PowerlessCanonicalOrderRawPrefix.formula_m (w G) (w q) (w a) p)
          (SecondOrderObjectSyntax.member_m p C)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "Ordinal" => SetTheory.Structure.IsOrdinal
  (SetTheory.Definitional.Project.FirstOrderSemantics.reduct 𝒱)

def point_l (B G q Q a : Raw) : Prop :=
  ∀ δ C p, value_l (ℳ := 𝒱) Q a δ →
    PowerlessRelativeHierarchySemantics.level_l hℳ B δ C →
      PowerlessCanonicalOrderRawPrefix.holds_l (𝒩 := 𝒱) G q a p → mem_l hℳ p C

theorem point_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env 𝒱 Γ Δ) (B G q Q a : Term ℒ Γ Δ .set) :
    (point_m B G q Q a).satisfies η ↔
      point_l (B.eval η) (G.eval η) (q.eval η) (Q.eval η) (a.eval η) := by
  simp only [point_m, point_l, Formula.satisfies, PowerlessValueBounded.formula_l,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessCanonicalOrderRawPrefix.formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def parameters_l (W ω F G P₀ : Raw) : Env 𝒱 [] [.set, .set, .set, .set, .set] :=
  Env.empty |>.pushFree P₀ |>.pushFree G |>.pushFree F |>.pushFree ω |>.pushFree W

variable (hBase)

private theorem checker_l (K : source_coding_l hℳ)
    {ξ C W δ F H q P₀ α p : Raw}
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ ξ)
    (hC : PowerlessRelativeHierarchySemantics.level_l hℳ B ξ C)
    (hWC : mem_l hℳ W C) (hωC : mem_l hℳ ω.val C)
    (hδ : Ordinal δ) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F W)
    (hH : map_l (ℳ := 𝒱) H δ q)
    (hEquations : PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      t₁.val t₂.val t₃.val Pair.val Valid.val B P₀ F H)
    (hOrder : ∀ a X P, value_l (ℳ := 𝒱) F a X → value_l (ℳ := 𝒱) H a P →
      wellOrder_l (ℳ := 𝒱) X P)
    (hα : Ordinal α) (hp : PowerlessCanonicalOrderRawPrefix.holds_l (𝒩 := 𝒱) H q α p)
    (hpC : map_l (ℳ := 𝒱) p α C) :
    PowerlessCanonicalOrderLightHistory.holds_l (𝒩 := 𝒱) C W ω.val F G.val P₀ α p := by
  have hFMap : map_l (ℳ := 𝒱) F δ W := hF.1
  obtain ⟨f, hf, hReadF, hEq, hOrd⟩ :=
    PowerlessCanonicalOrderPrefixEquations.exists_l K hFMap hH hEquations hOrder hα hp
  exact PowerlessCanonicalOrderLightHistoryOriginal.from_equations_l hBase K
    ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hLimit hC hωC
    (fun x hx => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC W hWC x hx)
    hδ hF hf (fun a X hX => ((hReadF a X).mp hX).2) hpC hEq hOrd

theorem step_l (K : source_coding_l hℳ)
    {W δ F H q P₀ A Q a : Raw}
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hδ : Ordinal δ) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F W)
    (hH : map_l (ℳ := 𝒱) H δ q)
    (hEquations : PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      t₁.val t₂.val t₃.val Pair.val Valid.val B P₀ F H)
    (hOrder : ∀ i X P, value_l (ℳ := 𝒱) F i X → value_l (ℳ := 𝒱) H i P →
      wellOrder_l (ℳ := 𝒱) X P)
    (hBudget : PowerlessThreeDefBudget.spec_l hℳ (parameters_l W ω.val F G.val P₀) B A Q)
    (hPast : ∀ b, mem_l hℳ b a → point_l B H q Q b) : point_l B H q Q a := by
  intro θ C f hQa hC hf
  have haA := hBudget.source a θ hQa
  have ha : Ordinal a := SetTheory.Structure.IsOrdinal.mem hBudget.domain_ordinal haA
  obtain ⟨ξ, C₀, C₁, C₂, hLimit, hC₀, hDef₀₁, hDef₁₂, hDef₂C, hParams, haC₀, hEarlier⟩ :=
    hBudget.layers a θ C hQa hC
  have hWC₀ : mem_l hℳ W C₀ := hParams .set .here
  have hωC₀ : mem_l hℳ ω.val C₀ := hParams .set (.there .here)
  have hFC₀ : mem_l hℳ F C₀ := hParams .set (.there (.there .here))
  have hGC₀ : mem_l hℳ G.val C₀ := hParams .set (.there (.there (.there .here)))
  have hP₀C₀ : mem_l hℳ P₀ C₀ := hParams .set (.there (.there (.there (.there .here))))
  have hTrans₀ := PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC₀
  have hTrans₀' := fun x y hx hy => hTrans₀ x hx y hy
  have hTrans₁ := SecondOrderMemberDefProperties.transitive_l hℳ hDef₀₁ hTrans₀'
  have hTrans₂ := SecondOrderMemberDefProperties.transitive_l hℳ hDef₁₂ hTrans₁
  have hSub₀₁ := SecondOrderMemberDefProperties.contains_l hℳ hDef₀₁ hTrans₀'
  have hSub₁₂ := SecondOrderMemberDefProperties.contains_l hℳ hDef₁₂ hTrans₁
  have hSub₂C := SecondOrderMemberDefProperties.contains_l hℳ hDef₂C hTrans₂
  have hIntoC x (hx : mem_l hℳ x C₀) : mem_l hℳ x C :=
    hSub₂C x (hSub₁₂ x (hSub₀₁ x hx))
  have hCover (b : Raw) (hb : mem_l hℳ b a) :
      ∃ p, mem_l hℳ p C₀ ∧ PowerlessCanonicalOrderRawPrefix.holds_l (𝒩 := 𝒱) H q b p := by
    have hbA := hBudget.domain_ordinal.transitive a haA b hb
    obtain ⟨ν, hQb⟩ := hBudget.total b hbA
    obtain ⟨E, hE⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hBase
      (hBudget.output_ordinal b ν hQb)
    obtain ⟨p, hp⟩ := PowerlessCanonicalOrderRawPrefix.exists_l hℳ hH
      (fun i hi => PowerlessCanonicalOrderRawPrefix.subset_l hℳ hH hf i (ha.transitive b hb i hi))
    have hpE := hPast b hb ν E p hQb hE hp
    exact ⟨p, hTrans₀ E (hEarlier b hb ν E hQb hE) p hpE, hp⟩
  rcases PowerlessHierarchyLightHistoryBudgetInduction.cases_l hℳ ha with hZero | ⟨b, hSucc⟩ | hLimitA
  · have hfa : f = a := by
      apply SecondOrderQuotient.ext_l hℳ
      intro x
      constructor
      · intro hx
        obtain ⟨i, _P, hi, _hP, _hPair⟩ := hf.1.1 x hx
        exact False.elim (hZero i hi)
      · intro hx
        exact False.elim (hZero x hx)
    exact hIntoC f (hfa.symm ▸ haC₀)
  · have hb : mem_l hℳ b a := (hSucc b).mpr (Or.inr rfl)
    obtain ⟨p, hpC₀, hp⟩ := hCover b hb
    have hbC₀ := hTrans₀ a haC₀ b hb
    have hbδ := PowerlessCanonicalOrderRawPrefix.subset_l hℳ hH hf b hb
    obtain ⟨X, hX, _⟩ := hF.1.2 b hbδ
    obtain ⟨E, hE, _⟩ := hf.1.2 b hb
    have hEGlobal := ((hf.2 b E).mp hE.2).2
    have hEC₀ := PowerlessCanonicalOrderLastOutput.member_l hBase K
      ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hLimit hC₀ hωC₀
      (fun x hx => hTrans₀ W hWC₀ x hx) hP₀C₀ hbC₀ hpC₀ hδ hF hp.1 hp.2
      hEquations hOrder hX.2 hEGlobal
    have hRead i P : value_l (ℳ := 𝒱) p i P ↔
        mem_l hℳ i b ∧ value_l (ℳ := 𝒱) f i P := by
      constructor
      · intro hP
        obtain ⟨hi, hHP⟩ := (hp.2 i P).mp hP
        exact ⟨hi, (hf.2 i P).mpr ⟨ha.transitive b hb i hi, hHP⟩⟩
      · rintro ⟨hi, hP⟩
        exact (hp.2 i P).mpr ⟨hi, ((hf.2 i P).mp hP).2⟩
    exact hIntoC f (PowerlessCanonicalOrderPrefixSuccessor.member_l hBase hLimit hC₀
      ha hSucc hbC₀ hpC₀ hEC₀ hf.1 hp.1 hRead hE.2)
  · have hfC₀ := PowerlessCanonicalOrderRawPrefix.limit_codomain_l hℳ
      hBase hLimit hC₀ hLimitA haC₀ hf hCover
    have hChecker := checker_l hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G
      hCode hLimit hC₀ hWC₀ hωC₀ hδ hF hH hEquations hOrder ha hf hfC₀
    have hCoverLight (b : Raw) (hb : mem_l hℳ b a) :
        ∃ p, mem_l hℳ p C₀ ∧
          PowerlessCanonicalOrderLightHistory.holds_l (𝒩 := 𝒱) C₀ W ω.val F G.val P₀ b p := by
      obtain ⟨p, hpC₀, hp⟩ := hCover b hb
      have hbC₀ := hTrans₀ a haC₀ b hb
      have hpMap := PowerlessCanonicalOrderRawPrefix.codomain_l hℳ hp.1
        (fun i P hP => PowerlessRelativeLimitFunctionRange.value_member_l
          hBase hLimit hC₀ hbC₀ hpC₀ hp.1 hP)
      have hbOrd : Ordinal b := SetTheory.Structure.IsOrdinal.mem ha hb
      exact ⟨p, hpC₀, checker_l hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G
        hCode hLimit hC₀ hWC₀ hωC₀ hδ hF hH hEquations hOrder hbOrd hp hpMap⟩
    have hCoverage X (hX : mem_l hℳ X W) s
        (hs : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω.val X s) : mem_l hℳ s C₀ := by
      obtain ⟨n, hn, hMap⟩ := hs
      exact PowerlessRelativeLimitFiniteMaps.member_l hℳ hBase hLimit hC₀ K
        (hCode.omega_eq ▸ hωC₀) (hTrans₀ W hWC₀ X hX) (hCode.omega_eq ▸ hn) hMap
    have hFMap : map_l (ℳ := 𝒱) F δ W := hF.1
    obtain ⟨_H, _hHC₂, _hExact, _hUnion, hfC⟩ :=
      PowerlessCanonicalOrderLightHistoryLimitPrefix.exists_l hℳ hFMap hCode.sat_map
        hCoverage ha hLimitA hChecker hTrans₀ hDef₀₁ hDef₁₂ hDef₂C
        ⟨SecondOrderMemberDefProperties.mother_member_l hℳ hDef₀₁,
          hSub₀₁ W hWC₀, hSub₀₁ ω.val hωC₀, hSub₀₁ F hFC₀,
          hSub₀₁ G.val hGC₀, hSub₀₁ P₀ hP₀C₀, hSub₀₁ a haC₀⟩ hCoverLight
    exact hfC

theorem bounded_l (K : source_coding_l hℳ)
    {W δ F H q P₀ A Q : Raw}
    (ω e t₁ t₂ t₃ Pair N Valid Translation G : type_l hℳ B)
    {L : SecondOrderModel.set_l ℳ}
    (hCode : PowerlessRelativeCofinalDefCoding.spec_l (W := W)
      hBase K ω e t₁ t₂ t₃ Pair N Valid Translation G L)
    (hδ : Ordinal δ) (hF : PowerlessRelativeHierarchySemantics.history_l hℳ B δ F W)
    (hH : map_l (ℳ := 𝒱) H δ q)
    (hEquations : PowerlessCanonicalOrderOrdinalRestriction.equations_l K
      t₁.val t₂.val t₃.val Pair.val Valid.val B P₀ F H)
    (hOrder : ∀ i X P, value_l (ℳ := 𝒱) F i X → value_l (ℳ := 𝒱) H i P →
      wellOrder_l (ℳ := 𝒱) X P)
    (hBudget : PowerlessThreeDefBudget.spec_l hℳ (parameters_l W ω.val F G.val P₀) B A Q) :
    ∀ a, point_l B H q Q a := by
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    Env.empty |>.pushFree B |>.pushFree H |>.pushFree q |>.pushFree Q
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    point_m (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here)
  have hFormula a : φ.satisfies (η.pushFree a) ↔ point_l B H q Q a :=
    point_formula_l K (η.pushFree a) _ _ _ _ _
  have hAll := PowerlessWeakSetInduction.induction_l (SecondOrderWeakSetTheory.models_l hℳ) φ η
    (fun a ih => (hFormula a).mpr (step_l hBase K
      ω e t₁ t₂ t₃ Pair N Valid Translation G hCode hδ hF hH hEquations hOrder hBudget
      (fun b hb => (hFormula b).mp (ih b hb))))
  exact fun a => (hFormula a).mp (hAll a)

#print axioms point_formula_l
#print axioms step_l
#print axioms bounded_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderBudgetInduction
