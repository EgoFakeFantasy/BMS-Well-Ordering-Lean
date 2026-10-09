import BMSConstructibleBridge.PowerlessOrdinalRecursion
import BMSConstructibleBridge.PowerlessRelativeLimitFiniteRangeDerives
import BMSConstructibleBridge.SecondOrderFunctionRestriction

/-! # 原 Z₂ 图商中的精确有限前史

限制图不仅逐值相同，其集合成员也精确为原图在给定初始段上的有序对。
内部有限前史留在同一非零极限层，即使原总图尚未属于该层或相对类。
不要求 C∈C，不调用完整源理论模型；闭句回传原 Z₂ 推导核。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitHistory

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (H F n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up H)) <|
    .existsE .set <| .existsE .set <| .conj
      (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.bvar (.there (.there .here)))) <|
      .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w n))
        (SecondOrderObjectSyntax.value_m (w F) (.bvar (.there .here)) (.bvar .here))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (H F n : Term ℒ Γ Δ .set) : (formula_m H F n).satisfies η ↔
      PowerlessOrdinalRecursion.history_l (ℳ := 𝒩) (H.eval η) (F.eval η) (n.eval η) := by
  simp only [formula_m, PowerlessOrdinalRecursion.history_l, Formula.satisfies, ordered_formula_l,
    value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem congr_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {H F G n : carrier_l 𝒩}
    (h : ∀ x, member_l 𝒩 x n → ∀ y, value_l (ℳ := 𝒩) F x y ↔ value_l (ℳ := 𝒩) G x y) :
    PowerlessOrdinalRecursion.history_l (ℳ := 𝒩) H F n ↔
      PowerlessOrdinalRecursion.history_l (ℳ := 𝒩) H G n := by
  apply forall_congr'
  intro p
  apply iff_congr Iff.rfl
  apply exists_congr
  intro x
  apply exists_congr
  intro y
  apply and_congr_right
  intro _
  exact and_congr_right (fun hx => h x hx y)

theorem self_l {F n C : type_l hℳ}
    (hF : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F n C) :
    PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) F F n := by
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, hx, _, hPair⟩ := hF.1 p hp
    exact ⟨x, y, hPair, hx, p, hp, hPair⟩
  · rintro ⟨_, _, hPair, _, q, hq, hPair'⟩
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq

theorem value_l {H F n x y : type_l hℳ}
    (hH : PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) H F n) :
    value_l (ℳ := SecondOrderQuotient.structure_l hℳ) H x y ↔
      mem_l hℳ x n ∧ value_l (ℳ := SecondOrderQuotient.structure_l hℳ) F x y := by
  constructor
  · rintro ⟨p, hp, hPair⟩
    obtain ⟨a, b, hPair', ha, hValue⟩ := (hH p).mp hp
    obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hℳ hPair hPair').mp rfl
    exact ⟨ha, hValue⟩
  · rintro ⟨hx, ⟨p, hp, hPair⟩⟩
    exact ⟨p, (hH p).mpr ⟨x, y, hPair, hx, p, hp, hPair⟩, hPair⟩

theorem query_l {H F n k f : type_l hℳ}
    (hH : PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) H F n)
    (hk : mem_l hℳ k n) :
    PowerlessEvaluationClause.query_l (ℳ := SecondOrderQuotient.structure_l hℳ) H k f ↔
      PowerlessEvaluationClause.query_l (ℳ := SecondOrderQuotient.structure_l hℳ) F k f := by
  apply exists_congr
  intro Y
  exact and_congr ((value_l hH).trans (and_iff_right hk)) Iff.rfl

theorem restrict_l {F A D n : type_l hℳ}
    (hF : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F A D)
    (hn : ∀ x, mem_l hℳ x n → mem_l hℳ x A) :
    ∃ H, map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H n D ∧
      PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) H F n := by
  obtain ⟨H, hH, hRead⟩ := SecondOrderFunctionRestriction.exists_l hℳ hF hn
  refine ⟨H, hH, fun p => ?_⟩
  constructor
  · intro hp
    obtain ⟨x, y, hx, _, hPair⟩ := hH.1 p hp
    exact ⟨x, y, hPair, hx, ((hRead x y).mp ⟨p, hp, hPair⟩).2⟩
  · rintro ⟨x, y, hPair, hx, hValue⟩
    obtain ⟨q, hq, hPair'⟩ := (hRead x y).mpr ⟨hx, hValue⟩
    exact (SecondOrderPairObjects.ordered_unique_l hℳ hPair' hPair) ▸ hq

theorem exists_l (K : source_coding_l hℳ) {B β C F A n : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C) (hωC : mem_l hℳ K.omega C)
    (hn : mem_l hℳ n K.omega) (hF : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) F A C)
    (hSubset : ∀ x, mem_l hℳ x n → mem_l hℳ x A) :
    ∃ H, mem_l hℳ H C ∧ map_l (ℳ := SecondOrderQuotient.structure_l hℳ) H n C ∧
      PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) H F n := by
  obtain ⟨H, hH, hHistory⟩ := restrict_l hF hSubset
  exact ⟨H, PowerlessRelativeLimitFiniteMaps.subset_member_l hℳ hBase hLimit hC K hωC
    (fun _ hx => hx) hn hH, hH, hHistory⟩

theorem unique_l {H G F n : type_l hℳ}
    (hH : PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) H F n)
    (hG : PowerlessOrdinalRecursion.history_l (ℳ := SecondOrderQuotient.structure_l hℳ) G F n) : H = G :=
  SecondOrderQuotient.ext_l hℳ H G (fun p => (hH p).trans (hG p).symm)

private abbrev context_m : SortContext ℒ := [.set, .set, .set, .set, .set, .set, .set]

def schema_m : Formula ℒ [] context_m :=
  let B : Term ℒ [] context_m .set := .fvar .here
  let β : Term ℒ [] context_m .set := .fvar (.there .here)
  let C : Term ℒ [] context_m .set := .fvar (.there (.there .here))
  let ω : Term ℒ [] context_m .set := .fvar (.there (.there (.there .here)))
  let F : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there .here))))
  let A : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let n : Term ℒ [] context_m .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  .imp (PowerlessRelativeHierarchyDerives.transitive_m B) <|
    .imp (PowerlessRelativeHierarchySyntax.level_m B β C) <|
      .imp (PowerlessRelativeHierarchySyntax.limit_m β) <|
        .imp (SecondOrderOmegaSyntax.omega_m ω) <| .imp (SecondOrderObjectSyntax.member_m ω C) <|
          .imp (SecondOrderObjectSyntax.member_m n ω) <| .imp (SecondOrderObjectSyntax.map_m F A C) <|
            .imp (PowerlessRelativeLimitFiniteRangeDerives.subset_m n A) <|
              .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up C)) <|
                .conj (SecondOrderObjectSyntax.map_m (.bvar .here) (up n) (up C))
                  (formula_m (.bvar .here) (up F) (up n))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hBase hC hLimit hω hωC hn hF hSubset
  have hBase' := (PowerlessRelativeHierarchyDerives.transitive_formula_l hℳ η (.fvar .here)).mp hBase
  have hC' := (PowerlessRelativeHierarchySemantics.level_formula_l K η
    (.fvar .here) (.fvar (.there .here)) (.fvar (.there (.there .here)))).mp hC
  have hLimit' := (PowerlessRelativeHierarchySemantics.limit_formula_l
    (hℳ := hℳ) η (.fvar (.there .here))).mp hLimit
  have hω' := (omega_formula_l η (.fvar (.there (.there (.there .here))))).mp hω
  have hωEq := SecondOrderOmega.unique_l hℳ hω' K.omega_spec
  have hF' := (map_formula_l η _ _ _).mp hF
  have hSubset' : ∀ x, mem_l hℳ x (η.2 (.there (.there (.there (.there (.there (.there .here))))))) →
      mem_l hℳ x (η.2 (.there (.there (.there (.there (.there .here)))))) := hSubset
  obtain ⟨H, hHC, hH, hHistory⟩ := exists_l K hBase' hLimit' hC'
    (hωEq ▸ hωC) (hωEq ▸ hn) hF' hSubset'
  refine ⟨H, hHC, (map_formula_l _ _ _ _).mpr hH, ?_⟩
  exact (formula_l _ _ _ _).mpr hHistory

#print axioms exists_l
#print axioms value_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitHistory
