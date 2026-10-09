import BMSConstructibleBridge.PowerlessKleeneBrouwerGraph
import BMSConstructibleBridge.SecondOrderRelationSyntax

/-! # 同一 KB 比较的无垃圾类内关系图

纯隶属 ℒ，原 Z₂。从实际 Class 积上的 Δ₀ 关系分离保留整张成员规格，
再读取所有 raw 坐标。结果同时保证关系资格及精确 KB 求值，不能从读数
单独推出无垃圾。没有把未知原坍缩 H 或其值域传给 Class 分离。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerCleanGraph

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessKleeneBrouwerSyntax (compare_l compare_m compare_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem exists_l {B ω I S : Raw}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hω : PowerlessRelativeClassCorrespondence.member_l hℳ B ω)
    (hI : PowerlessRelativeClassCorrespondence.member_l hℳ B I)
    (hS : PowerlessRelativeClassCorrespondence.member_l hℳ B S) :
    ∃ J, PowerlessRelativeClassCorrespondence.member_l hℳ B J ∧
      SecondOrderRegularRelation.relation_l hℳ J S ∧ PowerlessKleeneBrouwerGraph.reading_l ω I S J := by
  let O : type_l hℳ B := ⟨ω, hω⟩
  let I₀ : type_l hℳ B := ⟨I, hI⟩
  let S₀ : type_l hℳ B := ⟨S, hS⟩
  let φ : Formula ℒ [] [.set, .set, .set, .set] := compare_m
    (.fvar (.there (.there (.there .here)))) (.fvar (.there (.there .here)))
    (.fvar .here) (.fvar (.there .here))
  let η : Env (structure_l hℳ B hBase) [] [.set, .set] :=
    Env.empty |>.pushFree O |>.pushFree I₀
  have hδ : Formula.IsDelta0 membershipLevyBound φ := PowerlessKleeneBrouwerSyntax.compare_delta_l _ _ _ _
  obtain ⟨J, hJ⟩ := PowerlessRelativeClassRelation.exists_l hδ η S₀ S₀
  have hφ (x y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree x) ↔
      compare_l (𝒩 := 𝒱) ω I x.val y.val :=
    (PowerlessRelativeClassBounded.formula_l hδ ((η.pushFree y).pushFree x)).trans
      (compare_formula_l (PowerlessRelativeClassRelativization.env_l ((η.pushFree y).pushFree x)) _ _ _ _)
  have hRaw (p : Raw) : mem_l hℳ p J.val ↔ ∃ x y,
      mem_l hℳ x S ∧ mem_l hℳ y S ∧
        SecondOrderPairObjects.ordered_l hℳ x y p ∧ compare_l (𝒩 := 𝒱) ω I x y := by
    constructor
    · intro hp
      let p₀ : type_l hℳ B := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase J.property hp⟩
      obtain ⟨x, y, hx, hy, hPair, hCompare⟩ := (hJ p₀).mp hp
      exact ⟨x.val, y.val, hx, hy,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x y p₀).mp hPair,
        (hφ x y).mp hCompare⟩
    · rintro ⟨x, y, hx, hy, hPair, hCompare⟩
      let x₀ : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hS hx⟩
      let y₀ : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase hS hy⟩
      let p₀ : type_l hℳ B := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase x₀.property y₀.property hPair⟩
      exact (hJ p₀).mpr ⟨x₀, y₀, hx, hy,
        (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) x₀ y₀ p₀).mpr hPair,
        (hφ x₀ y₀).mpr hCompare⟩
  refine ⟨J.val, J.property, ?_, ?_⟩
  · intro p hp
    obtain ⟨x, y, hx, hy, hPair, _⟩ := (hRaw p).mp hp
    exact ⟨x, y, hx, hy, hPair⟩
  · intro f g
    constructor
    · rintro ⟨p, hp, hPair⟩
      obtain ⟨x, y, hx, hy, hPair', hCompare⟩ := (hRaw p).mp hp
      obtain ⟨hxf, hyg⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hPair' hPair).mp rfl
      simpa only [hxf, hyg] using And.intro hx (And.intro hy hCompare)
    · rintro ⟨hf, hg, hCompare⟩
      obtain ⟨p, hPair⟩ := SecondOrderPairObjects.ordered_exists_l hℳ f g
      exact ⟨p, (hRaw p).mpr ⟨f, g, hf, hg, hPair, hCompare⟩, hPair⟩

def schema_m {Δ : SortContext ℒ} (B ω I S : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B ω) <|
      .imp (PowerlessRelativeHierarchySyntax.class_m B I) <|
        .imp (PowerlessRelativeHierarchySyntax.class_m B S) <|
          .existsE .set <| .conj (PowerlessRelativeHierarchySyntax.class_m (up B) (.bvar .here)) <|
            .conj (SecondOrderRelationSyntax.relation_m (.bvar .here) (up S))
              (PowerlessKleeneBrouwerGraph.reading_m (up ω) (up I) (up S) (.bvar .here))

def sentence_m {Δ : SortContext ℒ} (B ω I S : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m B ω I S)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (B ω I S : Term ℒ [] Δ .set) : (sentence_m B ω I S).TrueIn 𝒱 := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderRelationSyntax.relation_l,
    PowerlessKleeneBrouwerGraph.reading_formula_l, up, Term.eval_weakenBound, Term.eval]
  exact exists_l (hℳ := hℳ)

theorem derives_m {Δ : SortContext ℒ} (B ω I S : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m B ω I S)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ B ω I S)

#print axioms exists_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessKleeneBrouwerCleanGraph
