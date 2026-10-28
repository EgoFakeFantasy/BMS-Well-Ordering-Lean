import BMSConstructibleBridge.PowerlessKleeneBrouwerPathCodomain
import BMSConstructibleBridge.PowerlessKleeneBrouwerNumericIndex
import BMSConstructibleBridge.PowerlessRelativeClassCleanRelation

/-! # 可达域上的同一全部路径与实际覆盖

纯隶属 ℒ，原 Z₂。限制 A 到真实可达域 D，保留同一个路径集 S 及每张原图 f。
每个路径值的实际终止前缀给出 D 资格；正反读数均证明，不以删边后路径减少
代替等价。覆盖由 D 的实际成员定义推出，不作为输入，也不假设原坍缩 H。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerRestrictedPaths

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessKleeneBrouwerPath (path_l path_m path_formula_l)
open PowerlessKleeneBrouwerEndpoint (endpoint_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem path_iff_l {ω I A z r S D E f : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l ω I S D)
    (hE : PowerlessRelativeClassCleanRelation.reading_l D A E) :
    path_l (𝒩 := 𝒱) ω I A z r f ↔ path_l (𝒩 := 𝒱) ω D E z r f := by
  have hSub (a : Raw) (ha : mem_l hℳ a D) := ((hD a).mp ha).1
  constructor
  · intro hPath
    have hValues := PowerlessKleeneBrouwerPathCodomain.values_l hω hZero hS hD hPath
    obtain ⟨n, hn, hf, hRoot, hEdges⟩ := hPath
    exact ⟨n, hn, PowerlessKleeneBrouwerPathCodomain.map_shrink_l hf hSub hValues, hRoot,
      fun i hi j hj hNext a ha b hb hfa hfb =>
        (hE b a).mpr ⟨hb, ha, hEdges i hi j hj hNext a (hSub a ha) b (hSub b hb) hfa hfb⟩⟩
  · rintro ⟨n, hn, hf, hRoot, hEdges⟩
    refine ⟨n, hn, PowerlessKleeneBrouwerPathCodomain.map_enlarge_l hf hSub, hRoot, ?_⟩
    intro i hi j hj hNext a _ha b _hb hfa hfb
    have haD := (SecondOrderFunctionProperties.value_mem_l hℳ hf hfa).2
    have hbD := (SecondOrderFunctionProperties.value_mem_l hℳ hf hfb).2
    exact ((hE b a).mp (hEdges i hi j hj hNext a haD b hbD hfa hfb)).2.2

theorem endpoint_l {ω I A z r S D f a : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l ω I S D)
    (hPath : path_l (𝒩 := 𝒱) ω I A z r f)
    (hEnd : PowerlessKleeneBrouwerEndpoint.endpoint_l ω I f a) :
    PowerlessKleeneBrouwerEndpoint.endpoint_l ω D f a := by
  obtain ⟨n, hn, k, hk, hf, hNext, hfa⟩ := hEnd
  exact ⟨n, hn, k, hk, PowerlessKleeneBrouwerPathCodomain.map_l hω hZero hS hD hPath hf, hNext, hfa⟩

theorem cover_l {ω I A z r S D E : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l ω I S D)
    (hE : PowerlessRelativeClassCleanRelation.reading_l D A E) :
    PowerlessKleeneBrouwerNumericIndex.cover_l ω D E z r := by
  intro a ha
  obtain ⟨_haI, f, hf, hEnd⟩ := (hD a).mp ha
  have hPath := (hS f).mp hf
  exact ⟨f, (path_iff_l hω hZero hS hD hE).mp hPath, endpoint_l hω hZero hS hD hPath hEnd⟩

theorem root_l {ω I A z r S D : Raw}
    (hω : SecondOrderOmega.omega_l hℳ ω) (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z)
    (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l ω I S D) : mem_l hℳ r D := by
  obtain ⟨n, p, hn, hzN, hNode, _⟩ := PowerlessKleeneBrouwerPathMinimum.root_l (hℳ := hℳ) (A := A) hω hZero hz hr
  exact (hD r).mpr ⟨hr, p, (hS p).mpr hNode.1, n, hn, z, hzN, hNode.2.1, hNode.2.2.1, hNode.2.2.2⟩

theorem exists_l {B ω I A z r S D : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hZero : PowerlessNatural.zero_l (ℳ := 𝒱) z)
    (hz : mem_l hℳ z ω) (hr : mem_l hℳ r I)
    (hDClass : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hAClass : PowerlessRelativeClassCorrespondence.member_l hℳ B A)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l ω I S D) :
    ∃ E, PowerlessRelativeClassCorrespondence.member_l hℳ B E ∧
      SecondOrderRegularRelation.relation_l hℳ E D ∧
        PowerlessRelativeClassCleanRelation.reading_l D A E ∧
          PowerlessKleeneBrouwerPathClass.reading_l ω D E z r S ∧
            PowerlessKleeneBrouwerNumericIndex.cover_l ω D E z r ∧ mem_l hℳ r D := by
  obtain ⟨E, hEClass, hClean, hE⟩ := PowerlessRelativeClassCleanRelation.exists_l hBase hDClass hAClass
  exact ⟨E, hEClass, hClean, hE, fun f => (hS f).trans (path_iff_l hω hZero hS hD hE),
    cover_l hω hZero hS hD hE, root_l hω hZero hz hr hS hD⟩

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def result_m {Γ Δ : SortContext ℒ} (B ω A z r S D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
    .conj (SecondOrderRelationSyntax.relation_m (.bvar .here) (up D)) <|
      .conj (PowerlessRelativeClassCleanRelation.reading_m (up D) (up A) (.bvar .here)) <|
        .conj (PowerlessKleeneBrouwerPathClass.reading_m (up ω) (up D) (.bvar .here) (up z) (up r) (up S)) <|
          .conj (PowerlessKleeneBrouwerNumericIndex.cover_m (up ω) (up D) (.bvar .here) (up z) (up r))
            (SecondOrderObjectSyntax.member_m (up r) (up D))

def schema_m {Δ : SortContext ℒ} (B ω I A z r S D : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (.forallE .set (.neg (SecondOrderObjectSyntax.member_m (.bvar .here) (up z)))) <|
      .imp (SecondOrderObjectSyntax.member_m z ω) <| .imp (SecondOrderObjectSyntax.member_m r I) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B D) <| .imp (PowerlessRelativeHierarchySyntax.class_m B A) <|
          .imp (PowerlessKleeneBrouwerPathClass.reading_m ω I A z r S) <|
            .imp (PowerlessKleeneBrouwerReachable.reading_m ω I S D) (result_m B ω A z r S D)

def sentence_m {Δ : SortContext ℒ} (B ω I A z r S D : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I A z r S D)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I A z r S D : Term ℒ [] Δ .set) : (sentence_m B ω I A z r S D).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, result_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, SecondOrderObjectSyntax.member_m,
    PowerlessRelativeHierarchySemantics.class_formula_l K,
    PowerlessKleeneBrouwerPathClass.reading_formula_l, PowerlessKleeneBrouwerReachable.reading_formula_l,
    SecondOrderRelationSyntax.relation_l, PowerlessRelativeClassCleanRelation.reading_formula_l,
    PowerlessKleeneBrouwerNumericIndex.cover_formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (B ω I A z r S D : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I A z r S D)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I A z r S D)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerRestrictedPaths
