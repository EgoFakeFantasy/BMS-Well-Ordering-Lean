import BMSConstructibleBridge.PowerlessCanonicalOrderClassHistory
import BMSConstructibleBridge.PowerlessRelativeCutoffClassHistory

/-! # 首不可数截断的实际 Class 相容良序历史及原 Z₂ 推导

给定实际 Class 初始良序图及原完整基底守卫，在证明内取得实际层历史、
同一静态/Sat 编码包、原 raw 比较历史和预算。输出两张 Class 函数图，
每一阶段满足环境良序，较早阶段为较晚阶段的真正初段。

对象句明确保留初始良序图的 Class 身份，不能默认为任意 raw 基底序都在
Class 中；层和比较图的 Class 身份均非前提。不声称图属于 W、统一枚举
族已经存在、完整 cutoff Collection 已证或最终固定高度 BMS 已完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffClassOrderHistory

open Logic FirstOrder ThirdOrderSemantics PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

private abbrev up₆ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  up (up (up (up (up (up t)))))

def coherent_m {Γ Δ : SortContext ℒ} (I F H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .forallE .set <| .forallE .set <|
    .forallE .set <| .forallE .set <| .forallE .set <|
      let a := .bvar (.there (.there (.there (.there (.there .here)))))
      let b := .bvar (.there (.there (.there (.there .here))))
      let X := .bvar (.there (.there (.there .here)))
      let P := .bvar (.there (.there .here))
      let Y := .bvar (.there .here)
      let Q := .bvar .here
      .imp (SecondOrderWellOrderCoherentUnion.stage_m (up₆ I) (up₆ F) (up₆ H) a X P) <|
        .imp (SecondOrderWellOrderCoherentUnion.stage_m (up₆ I) (up₆ F) (up₆ H) b Y Q) <|
          .imp (SecondOrderObjectSyntax.member_m a b)
            (SecondOrderWellOrderCoherentUnionDerives.extension_m X P Y Q)

def coherent_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (I F H : carrier_l 𝒩) : Prop :=
  ∀ a b X P Y Q, SecondOrderWellOrderCoherentUnion.stage_l I F H a X P →
    SecondOrderWellOrderCoherentUnion.stage_l I F H b Y Q → member_l 𝒩 a b →
      SecondOrderWellOrderCoherentUnion.extension_l X P Y Q

theorem coherent_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (I F H : Term ℒ Γ Δ .set) :
    (coherent_m I F H).satisfies η ↔ coherent_l (I.eval η) (F.eval η) (H.eval η) := by
  simp only [coherent_m, coherent_l, Formula.satisfies,
    SecondOrderWellOrderCoherentUnion.stage_formula_l,
    SecondOrderWellOrderCoherentUnionDerives.extension_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up₆, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

/-- 共尾非零极限层的实际比较历史；不要求首不可数截断。 -/
theorem exists_cofinal_l (K : source_coding_l hℳ) {B β W : Raw}
    (P₀ : type_l hℳ B) (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀.val)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W)
    (hCofinal : PowerlessRelativeCofinalLimitBounds.cofinal_l β)
    (hωW : mem_l hℳ K.omega W) :
    ∃ F H : type_l hℳ B, ∃ q : Raw,
      PowerlessRelativeHierarchySemantics.history_l hℳ B β F.val W ∧
      map_l (ℳ := 𝒱) H.val β q ∧
      (∀ a X P, SecondOrderWellOrderCoherentUnion.stage_l β F.val H.val a X P →
        wellOrder_l (ℳ := 𝒱) X P) ∧ coherent_l (𝒩 := 𝒱) β F.val H.val := by
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx y hy => hSeed.2.1 x y hx hy
  let ω' : type_l hℳ B := ⟨K.omega, ⟨β, W, hW, hωW⟩⟩
  let W' : type_l hℳ B := ⟨W, PowerlessRelativeLevelClosure.class_l hℳ hBase hW⟩
  obtain ⟨e, t₁, t₂, t₃, Pair, N, Valid, Translation, G, L, hCode⟩ :=
    PowerlessRelativeCofinalDefCoding.exists_l hBase K hLimit hW hCofinal ω' hωW rfl
  have hOrd := PowerlessRelativeLevelClosure.ordinal_l hℳ hW
  obtain ⟨D, _hD, hRead⟩ :=
    PowerlessRelativeCofinalDefFunction.exists_l hBase K hLimit hW hCofinal hωW
  obtain ⟨F, hF⟩ := PowerlessRelativeCutoffClassHistory.class_exists_l
    hℳ K hBase D hRead hOrd hW (fun _ hx => hx)
  obtain ⟨H, q, hMap, _hEq, hLevel⟩ := PowerlessCanonicalOrderClassHistory.exists_l hBase K
    W' F P₀ ω' e t₁ t₂ t₃ Pair N Valid Translation G hCode hOrd hF
    hSeed.1 hSeed.2.2.1 hSeed.2.2.2
  obtain ⟨_he, ht₁, ht₂, ht₃, _hN, hPairMap, hPair, hValid⟩ :=
    PowerlessRelativeClassStaticCodingReading.reading_l K hCode.omega_eq hCode.static
  obtain ⟨V, hV, _hUnique⟩ := SecondOrderTriangularFormulaSyntax.exists_l hℳ
  have hCoding : SecondOrderComparisonStageTotal.coding_l K t₁.val t₂.val t₃.val Pair.val Valid.val :=
    ⟨ht₁, ht₂, ht₃, hPairMap, hPair, V, hV, hValid V hV⟩
  refine ⟨F, H, q, hF, hMap, ?_, ?_⟩
  · rintro a X P ⟨_ha, hX, hP⟩
    exact SecondOrderCanonicalLevel.order_l ((hLevel a X P hX).mp hP)
  · rintro a b X P Y Q ⟨_ha, hX, hP⟩ ⟨_hb, hY, hQ⟩ hab
    exact SecondOrderCanonicalLevel.extension_l K hCoding hab
      ((hLevel a X P hX).mp hP) ((hLevel b Y Q hY).mp hQ)

theorem exists_l (K : source_coding_l hℳ) {B ω Ω W : Raw}
    (P₀ : type_l hℳ B) (hSeed : SecondOrderCanonicalLevelDerives.guard_l B P₀.val)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hΩ : PowerlessRelativeOrdinalCutoff.first_l B ω Ω)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B Ω W) :
    ∃ F H : type_l hℳ B, ∃ q : Raw,
      PowerlessRelativeHierarchySemantics.history_l hℳ B Ω F.val W ∧
      map_l (ℳ := 𝒱) H.val Ω q ∧
      (∀ a X P, SecondOrderWellOrderCoherentUnion.stage_l Ω F.val H.val a X P →
        wellOrder_l (ℳ := 𝒱) X P) ∧ coherent_l (𝒩 := 𝒱) Ω F.val H.val := by
  have hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B :=
    fun x hx y hy => hSeed.2.1 x y hx hy
  have hωW := PowerlessRelativeOrdinalCoverage.covered_l hℳ K hBase Ω W hW ω
    (PowerlessRelativeCutoffBelow.omega_below_l (hBase := hBase) K hω hΩ)
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  exact exists_cofinal_l K P₀ hSeed (PowerlessRelativeCutoffLimit.limit_l K hBase hω hΩ)
    hW (PowerlessRelativeCutoffInnerLimits.cofinal_l K hBase hω hΩ) (hωEq ▸ hωW)

/-- 自由槽依次为 W、Ω、ω、P₀、B；初始序图 Class 守卫不可省略。 -/
def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  let W : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar .here
  let Ω := .fvar (.there .here)
  let ω := .fvar (.there (.there .here))
  let P₀ := .fvar (.there (.there (.there .here)))
  let B := .fvar (.there (.there (.there (.there .here))))
  .imp (SecondOrderCanonicalLevelDerives.guard_m B P₀) <|
    .imp (PowerlessRelativeHierarchySyntax.class_m B P₀) <|
      .imp (SecondOrderOmegaSyntax.omega_m ω) <|
        .imp (PowerlessRelativeOrdinalCutoff.first_m B ω Ω) <|
          .imp (PowerlessRelativeHierarchySyntax.level_m B Ω W) <|
            .existsE .set <| .existsE .set <| .existsE .set <|
              let w (t : Term ℒ [] [.set, .set, .set, .set, .set] .set) := up (up (up t))
              let F := .bvar (.there (.there .here))
              let H := .bvar (.there .here)
              let q := .bvar .here
              .conj (PowerlessRelativeHierarchySyntax.class_m (w B) F) <|
                .conj (PowerlessRelativeHierarchySyntax.class_m (w B) H) <|
                  .conj (PowerlessRelativeHierarchySyntax.history_m (w B) (w Ω) F (w W)) <|
                    .conj (SecondOrderObjectSyntax.map_m H (w Ω) q) <|
                      .conj (SecondOrderWellOrderCoherentUnionDerives.stages_m (w Ω) F H)
                        (coherent_m (w Ω) F H)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (h𝒩 : Theory.Models ℳ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l h𝒩) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  simp only [schema_m, Formula.satisfies, SecondOrderCanonicalLevelDerives.guard_formula_l,
    PowerlessRelativeHierarchySemantics.class_formula_l K, SecondOrderOmegaSyntax.omega_l,
    PowerlessRelativeOrdinalCutoff.first_formula_l K,
    PowerlessRelativeHierarchySemantics.level_formula_l K,
    PowerlessRelativeHierarchySemantics.history_formula_l K, map_formula_l,
    SecondOrderWellOrderCoherentUnionDerives.stages_formula_l, coherent_formula_l,
    up, Term.eval_weakenBound, Term.eval]
  intro η hSeed hP₀ hω hΩ hW
  obtain ⟨F, H, q, hF, hH, hOrder, hCoherent⟩ := exists_l K ⟨_, hP₀⟩ hSeed hω hΩ hW
  exact ⟨F.val, H.val, q, F.property, H.property, hF, hH, hOrder, hCoherent⟩

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m _ (fun _ h𝒩 => models_l h𝒩)

#print axioms coherent_formula_l
#print axioms exists_cofinal_l
#print axioms exists_l
#print axioms models_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCutoffClassOrderHistory
