import BMSConstructibleBridge.PowerlessRelationalCollapsePartial
import BMSConstructibleBridge.PowerlessRelativeLimitFunctionRange

/-! # 同一关系局部坍缩的陪域迁移与图认同

纯隶属 ℒ，原 Z₂。传递旧陪域把有界递归提升为全原坐标规格，
因而同一局部图可迁移到任何实际新陪域。图与源属于指定极限层时，
其全部输出坐标也属于该层，迁移不预设原 T 的类身份。
同一 H 的两个合格限制图由有序对唯一性取得集合相等，不仅值读数相同。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseTransport

open Logic FirstOrder
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "Raw" => type_l hℳ
local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

theorem recodomain_l {A I E C D G : Raw}
    (hC : ∀ a, mem_l hℳ a C → ∀ b, mem_l hℳ b a → mem_l hℳ b C)
    (hG : PowerlessRelationalCollapsePartial.partial_l A I E C G)
    (hMap : SecondOrderFunctionObjects.map_l hℳ G E D) :
    PowerlessRelationalCollapsePartial.partial_l A I E D G := by
  refine ⟨hG.1, hG.2.1, hMap, ?_⟩
  intro a ha b _hb hab z _hz
  exact PowerlessRelationalCollapsePartial.recursive_l hG hC a ha b hab z

theorem limit_l {B β L A I E C G : Raw}
    (hBase : ∀ a, mem_l hℳ a B → ∀ b, mem_l hℳ b a → mem_l hℳ b B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hL : PowerlessRelativeHierarchySemantics.level_l hℳ B β L)
    (hEL : mem_l hℳ E L) (hGL : mem_l hℳ G L)
    (hC : ∀ a, mem_l hℳ a C → ∀ b, mem_l hℳ b a → mem_l hℳ b C)
    (hG : PowerlessRelationalCollapsePartial.partial_l A I E C G) :
    PowerlessRelationalCollapsePartial.partial_l A I E L G := by
  have hValue (a b : Raw) (hab : SecondOrderFunctionObjects.value_l hℳ G a b) : mem_l hℳ b L :=
    PowerlessRelativeLimitFunctionRange.value_member_l hBase hLimit hL
      hEL hGL (q := C) (by exact hG.2.2.1) (by exact hab)
  apply recodomain_l hC hG
  constructor
  · intro p hp
    obtain ⟨a, b, ha, _, hab⟩ := hG.2.2.1.1 p hp
    exact ⟨a, b, ha, hValue a b ⟨p, hp, hab⟩, hab⟩
  · intro a ha
    obtain ⟨b, hb, _⟩ := hG.2.2.1.2 a ha
    exact ⟨b, ⟨hValue a b hb.2, hb.2⟩,
      fun z hz => SecondOrderFunctionProperties.value_unique_l hℳ hG.2.2.1 hz.2 hb.2⟩

theorem graph_eq_l {A I E T H C D F G : Raw}
    (hH : SecondOrderCollapseFunction.spec_l hℳ A I T H)
    (hC : ∀ a, mem_l hℳ a C → ∀ b, mem_l hℳ b a → mem_l hℳ b C)
    (hD : ∀ a, mem_l hℳ a D → ∀ b, mem_l hℳ b a → mem_l hℳ b D)
    (hF : PowerlessRelationalCollapsePartial.partial_l A I E C F)
    (hG : PowerlessRelationalCollapsePartial.partial_l A I E D G) : F = G := by
  apply SecondOrderQuotient.ext_l hℳ
  intro p
  constructor
  · intro hp
    obtain ⟨a, b, ha, _, hPair⟩ := hF.2.2.1.1 p hp
    have hHab := (PowerlessRelationalCollapsePartial.value_l hH hC hF ha).mp ⟨p, hp, hPair⟩
    obtain ⟨q, hq, hPair'⟩ := (PowerlessRelationalCollapsePartial.value_l hH hD hG ha).mpr hHab
    exact SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair ▸ hq
  · intro hp
    obtain ⟨a, b, ha, _, hPair⟩ := hG.2.2.1.1 p hp
    have hHab := (PowerlessRelationalCollapsePartial.value_l hH hD hG ha).mp ⟨p, hp, hPair⟩
    obtain ⟨q, hq, hPair'⟩ := (PowerlessRelationalCollapsePartial.value_l hH hC hF ha).mpr hHab
    exact SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair ▸ hq

def schema_m {Δ : SortContext ℒ} (A I E C D G : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (PowerlessRelativeHierarchyDerives.transitive_m C) <|
    .imp (PowerlessRelationalCollapsePartial.partial_m A I E C G) <|
      .imp (SecondOrderObjectSyntax.map_m G E D) (PowerlessRelationalCollapsePartial.partial_m A I E D G)

def sentence_m {Δ : SortContext ℒ} (A I E C D G : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m A I E C D G)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (A I E C D G : Term ℒ [] Δ .set) : (sentence_m A I E C D G).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessRelativeHierarchyDerives.transitive_formula_l,
    PowerlessRelationalCollapsePartial.formula_l, SecondOrderObjectSyntax.map_l]
  exact fun hC hG hMap => recodomain_l (hℳ := hℳ) hC hG hMap

theorem derives_m {Δ : SortContext ℒ} (A I E C D G : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (sentence_m A I E C D G)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ A I E C D G)

def equality_schema_m {Δ : SortContext ℒ} (A I E T H C D F G : Term ℒ [] Δ .set) : Formula ℒ [] Δ :=
  .imp (SecondOrderCollapseSyntax.formula_m A I T H) <|
    .imp (PowerlessRelativeHierarchyDerives.transitive_m C) <|
      .imp (PowerlessRelativeHierarchyDerives.transitive_m D) <|
        .imp (PowerlessRelationalCollapsePartial.partial_m A I E C F) <|
          .imp (PowerlessRelationalCollapsePartial.partial_m A I E D G) (.equal F G)

def equality_sentence_m {Δ : SortContext ℒ} (A I E T H C D F G : Term ℒ [] Δ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (equality_schema_m A I E T H C D F G)

theorem equality_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {Δ : SortContext ℒ}
    (A I E T H C D F G : Term ℒ [] Δ .set) : (equality_sentence_m A I E T H C D F G).TrueIn 𝒱 := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [equality_schema_m, Formula.satisfies, SecondOrderCollapseSyntax.formula_l,
    PowerlessRelativeHierarchyDerives.transitive_formula_l, PowerlessRelationalCollapsePartial.formula_l]
  exact fun hH hC hD hF hG => graph_eq_l (hℳ := hℳ) hH hC hD hF hG

theorem equality_derives_m {Δ : SortContext ℒ} (A I E T H C D F G : Term ℒ [] Δ .set) :
    Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (equality_sentence_m A I E T H C D F G)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => equality_models_l hℳ A I E T H C D F G)

#print axioms recodomain_l
#print axioms limit_l
#print axioms graph_eq_l
#print axioms derives_m
#print axioms equality_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelationalCollapseTransport
