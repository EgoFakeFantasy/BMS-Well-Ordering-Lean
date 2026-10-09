import BMSConstructibleBridge.PowerlessKleeneBrouwerEndpointMap
import BMSConstructibleBridge.PowerlessKleeneBrouwerPathWellOrder
import BMSConstructibleBridge.PowerlessRelativeClassCleanWellOrder
import BMSConstructibleBridge.PowerlessRelativeClassWellOrderSection
import BMSConstructibleBridge.PowerlessRelativeClassWellOrderPullbackAmbient
import BMSConstructibleBridge.PowerlessRelationalCollapseOrderedCut

/-! # 可达节点的实际前驱优先类内良序

纯隶属 ℒ，原 Z₂。末节点满射的 KB 最小代表组成实际 Class 逆图；
沿此单射拉回环境良序，并规范成无垃圾关系。A 前驱的追加路径严格更小，
最小代表比较因此保证 A 的每条域内边都被新良序保留。
所有集合图实际构造；原路径良序及末节点图仍是明确输入，不预供目标 J。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPredecessorOrder

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessKleeneBrouwerSyntax (compare_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {B ω I A z r S D F R : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hSub : ∀ b, mem_l hℳ b I → mem_l hℳ b ω)
    (hSClass : PowerlessRelativeClassCorrespondence.member_l hℳ B S)
    (hDClass : PowerlessRelativeClassCorrespondence.member_l hℳ B D)
    (hFClass : PowerlessRelativeClassCorrespondence.member_l hℳ B F)
    (hRClass : PowerlessRelativeClassCorrespondence.member_l hℳ B R)
    (hS : PowerlessKleeneBrouwerPathClass.reading_l ω I A z r S)
    (hD : PowerlessKleeneBrouwerReachable.reading_l ω I S D)
    (hMapF : map_l (ℳ := 𝒱) F S D)
    (hOntoF : PowerlessKleeneBrouwerEndpointMap.onto_l S D F)
    (hReadF : PowerlessKleeneBrouwerEndpointMap.reading_l ω I S D F)
    (hR : wellOrder_l (ℳ := 𝒱) S R)
    (hReadR : PowerlessKleeneBrouwerGraph.reading_l ω I S R) :
    ∃ J, PowerlessRelativeClassCorrespondence.member_l hℳ B J ∧
      SecondOrderRegularRelation.relation_l hℳ J D ∧ wellOrder_l (ℳ := 𝒱) D J ∧
        PowerlessRelationalCollapseOrderedCut.extends_l D A J := by
  let S₀ : type_l hℳ B := ⟨S, hSClass⟩
  let D₀ : type_l hℳ B := ⟨D, hDClass⟩
  let F₀ : type_l hℳ B := ⟨F, hFClass⟩
  let R₀ : type_l hℳ B := ⟨R, hRClass⟩
  have hF := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) F₀ S₀ D₀).mpr hMapF
  have hOnto := (PowerlessRelativeClassFunctionAbsolute.onto_l (hBase := hBase) F₀ S₀ D₀).mpr hOntoF
  obtain ⟨G, hG, hInject, hGRead⟩ := PowerlessRelativeClassWellOrderSection.exists_l hF
    (PowerlessRelativeClassAmbientWellOrder.restrict_l (hBase := hBase) (A := S₀) (R := R₀) hR) hOnto
  have hGRaw := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) G D₀ S₀).mp hG
  obtain ⟨L, hL, hLRead⟩ :=
    PowerlessRelativeClassWellOrderPullbackAmbient.exists_l (hBase := hBase) (R := R₀) hG hInject hR
  obtain ⟨J, hJClass, hClean, hReadJ, hJ⟩ :=
    PowerlessRelativeClassCleanWellOrder.exists_l hBase hDClass L.property hL
  have hMin {a p : Raw} (ha : mem_l hℳ a D) (hp : mem_l hℳ p S)
      (hGap : value_l (ℳ := 𝒱) G.val a p) :
      value_l (ℳ := 𝒱) F p a ∧
        ∀ t, mem_l hℳ t S → value_l (ℳ := 𝒱) F t a → ¬compare_l (𝒩 := 𝒱) ω I t p := by
    let a₀ : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hDClass ha⟩
    let p₀ : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hSClass hp⟩
    have hMinimal := ((hGRead a₀ p₀).mp
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G a₀ p₀).mpr hGap)).2.2
    refine ⟨(PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F₀ p₀ a₀).mp hMinimal.1, ?_⟩
    intro t ht hFta htp
    let t₀ : type_l hℳ B := ⟨t, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hSClass ht⟩
    exact hMinimal.2 t₀ ht
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) F₀ t₀ a₀).mpr hFta)
      ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R₀ t₀ p₀).mpr
        ((hReadR t p).mpr ⟨ht, hp, htp⟩))
  have hSeq (p : Raw) (hp : mem_l hℳ p S) :
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒱) ω I p := by
    obtain ⟨n, hn, hf, _, _⟩ := (hS p).mp hp
    exact ⟨n, hn, hf⟩
  refine ⟨J, hJClass, hClean, hJ, ?_⟩
  intro b hb a ha hEdge
  obtain ⟨p, hp, _⟩ := hGRaw.2 a ha
  obtain ⟨q, hq, _⟩ := hGRaw.2 b hb
  have hPMin := hMin ha hp.1 hp.2
  have hQMin := hMin hb hq.1 hq.2
  have hEndP := ((hReadF p a).mp hPMin.1).2.2
  obtain ⟨t, hPathT, hEndT, hTP⟩ :=
    PowerlessKleeneBrouwerEndpoint.append_l hω ((hS p).mp hp.1) hEndP ((hD b).mp hb).1 hEdge
  have htS := (hS t).mpr hPathT
  have hFtb := (hReadF t b).mpr ⟨htS, hb, hEndT⟩
  have hQP : compare_l (𝒩 := 𝒱) ω I q p := by
    rcases PowerlessKleeneBrouwerComparison.comparison_l hω hSub (hSeq q hq.1) (hSeq t htS) with
      hQT | hEq | hTQ
    · exact PowerlessKleeneBrouwerTransitivity.transitive_l hω hSub
        (hSeq q hq.1) (hSeq t htS) (hSeq p hp.1) hQT hTP
    · exact hEq.symm ▸ hTP
    · exact (hQMin.2 t htS hFtb hTQ).elim
  let a₀ : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hDClass ha⟩
  let b₀ : type_l hℳ B := ⟨b, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hDClass hb⟩
  let p₀ : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hSClass hp.1⟩
  let q₀ : type_l hℳ B := ⟨q, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hSClass hq.1⟩
  have hLba := (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) L b₀ a₀).mp
    ((hLRead b₀ a₀).mpr ⟨hb, ha, q₀, p₀, hq.1, hp.1,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G b₀ q₀).mpr hq.2,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) G a₀ p₀).mpr hp.2,
      (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) R₀ q₀ p₀).mpr
        ((hReadR q p).mpr ⟨hq.1, hp.1, hQP⟩)⟩)
  exact (hReadJ b a).mpr ⟨hb, ha, hLba⟩

def result_m {Γ Δ : SortContext ℒ} (B D A : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
    .conj (SecondOrderRelationSyntax.relation_m (.bvar .here) (up D)) <|
      .conj (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m (up D) (.bvar .here))
        (PowerlessRelationalCollapseOrderedCut.extends_m (up D) (up A) (.bvar .here))

def schema_m {Δ : SortContext ℒ} (B ω I A z r S D F R : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <| .imp (SecondOrderOmegaSyntax.omega_m ω) <|
    .imp (ThirdOrderTheory.subset_m I ω) <| .imp (PowerlessRelativeHierarchySyntax.class_m B S) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B D) <| .imp (PowerlessRelativeHierarchySyntax.class_m B F) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B R) <|
          .imp (PowerlessKleeneBrouwerPathClass.reading_m ω I A z r S) <|
            .imp (PowerlessKleeneBrouwerReachable.reading_m ω I S D) <|
              .imp (PowerlessMapBounded.formula_m F S D) <|
                .imp (PowerlessKleeneBrouwerEndpointMap.onto_m S D F) <|
                  .imp (PowerlessKleeneBrouwerEndpointMap.reading_m ω I S D F) <|
                    .imp (PowerlessRelativeClassEnumerationWellOrder.wellOrder_m S R) <|
                      .imp (PowerlessKleeneBrouwerGraph.reading_m ω I S R) (result_m B D A)

def sentence_m {Δ : SortContext ℒ} (B ω I A z r S D F R : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I A z r S D F R)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I A z r S D F R : Term ℒ [] Δ .set) : (sentence_m B ω I A z r S D F R).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, result_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    SecondOrderOmegaSyntax.omega_l, ThirdOrderSemantics.subset_formula_l, subset_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, PowerlessKleeneBrouwerPathClass.reading_formula_l,
    PowerlessKleeneBrouwerReachable.reading_formula_l, PowerlessMapBounded.formula_l,
    PowerlessKleeneBrouwerEndpointMap.onto_formula_l, PowerlessKleeneBrouwerEndpointMap.reading_formula_l,
    PowerlessRelativeClassEnumerationWellOrder.wellOrder_formula_l, PowerlessKleeneBrouwerGraph.reading_formula_l,
    SecondOrderRelationSyntax.relation_l, PowerlessRelationalCollapseOrderedCut.extends_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (B ω I A z r S D F R : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m B ω I A z r S D F R)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I A z r S D F R)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerPredecessorOrder
