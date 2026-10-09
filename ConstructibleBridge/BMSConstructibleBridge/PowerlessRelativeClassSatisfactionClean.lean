import BMSConstructibleBridge.PowerlessSatisfactionGraphClean
import BMSConstructibleBridge.PowerlessRelativeLimitDeltaSeparation
import BMSConstructibleBridge.PowerlessRelativeClassStructure

/-! # 指定非零极限层内的 Sat 图规范化

对已经属于实际层的图 R 作纯 Δ₀ 分离，只保留指定 ω 与 Seq 坐标的
Kuratowski 有序对。输出仍属于同一个层；全部原商坐标上的读值由显式
域限制保持。Class 身份来自实际层成员性，不从母集子集性质推断。

这里只处理图对象的清理及读值保持，不构造 Sat 规格、统一 Sat 族或历史，
也没有把语义辅助接口当作对象推导或 BMS 终局证明。全部见证留在 Prop。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionClean

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 单个成员具有指定坐标范围的有界证书。 -/
def filter_m {Γ Δ : SortContext ℒ} (ω S p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <|
    membershipLevyBound.boundedExists (up S) <|
      PowerlessPairBounded.ordered_m (.bvar (.there .here)) (.bvar .here) (up (up p))

theorem filter_delta_l {Γ Δ : SortContext ℒ} (ω S p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (filter_m ω S p) :=
  .bounded_exists _ (.bounded_exists _ (PowerlessPairBounded.ordered_delta_l _ _ _))

theorem filter_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω S p : Term ℒ Γ Δ .set) :
    (filter_m ω S p).satisfies η ↔ ∃ c f,
      member_l 𝒩 c (ω.eval η) ∧ member_l 𝒩 f (S.eval η) ∧
        ordered_l c f (p.eval η) := by
  simp only [filter_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessPairBounded.ordered_formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  constructor
  · rintro ⟨c, hc, f, hf, hPair⟩
    exact ⟨c, f, hc, hf, hPair⟩
  · rintro ⟨c, f, hc, hf, hPair⟩
    exact ⟨c, hc, f, hf, hPair⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {B β C : SecondOrderQuotient.type_l hℳ}

local notation "RawModel" => SecondOrderQuotient.structure_l hℳ

/-- 只在已有实际层成员 R 上分离；读值等价量化全部原商对象。 -/
theorem exists_l
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (ω S R : type_l hℳ B)
    (hω : mem_l hℳ ω.val C) (hS : mem_l hℳ S.val C) (hR : mem_l hℳ R.val C)
    (hDomain : ∀ c f, value_l (ℳ := RawModel) R.val c f →
      mem_l hℳ c ω.val ∧ mem_l hℳ f S.val) :
    ∃ Q : type_l hℳ B, mem_l hℳ Q.val C ∧
      (∀ c f, value_l (ℳ := RawModel) Q.val c f ↔
        value_l (ℳ := RawModel) R.val c f) ∧
      PowerlessSatisfactionGraphClean.holds_l (𝒩 := RawModel) ω.val S.val Q.val := by
  let η := (Env.empty (M := RawModel)).pushFree
    (sort := SetTheory.SetSort.set) S.val |>.pushFree (sort := SetTheory.SetSort.set) ω.val
  let φ : Formula ℒ [] [.set, .set, .set] :=
    filter_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  have hφ : Formula.IsDelta0 membershipLevyBound φ := filter_delta_l _ _ _
  have hParams : ∀ (s : SetTheory.SetSort)
      (v : Variable [SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (η.freeVal v) C := by
    intro s v
    cases s
    cases v with
    | here => exact hω
    | there v => cases v with
      | here => exact hS
      | there v => nomatch v
  have hFilter (p : SecondOrderQuotient.type_l hℳ) :
      φ.satisfies (η.pushFree p) ↔ ∃ c f,
        mem_l hℳ c ω.val ∧ mem_l hℳ f S.val ∧ ordered_l (ℳ := RawModel) c f p :=
    filter_formula_l (η.pushFree (sort := SetTheory.SetSort.set) p)
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  obtain ⟨q, hq, hSlice⟩ := PowerlessRelativeLimitDeltaSeparation.exists_l
    hBase hLimit hC hφ η hR hParams
  have hClass := PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase
    (PowerlessRelativeLevelClosure.class_l hℳ hBase hC) hq
  refine ⟨⟨q, hClass⟩, hq, ?_, ?_⟩
  · intro c f
    constructor
    · rintro ⟨p, hp, hPair⟩
      exact ⟨p, ((hSlice p).mp hp).1, hPair⟩
    · intro hValue
      obtain ⟨hc, hf⟩ := hDomain c f hValue
      obtain ⟨p, hp, hPair⟩ := hValue
      exact ⟨p, (hSlice p).mpr ⟨hp, (hFilter p).mpr ⟨c, f, hc, hf, hPair⟩⟩, hPair⟩
  · intro p hp
    exact (hFilter p).mp ((hSlice p).mp hp).2

#print axioms filter_delta_l
#print axioms filter_formula_l
#print axioms exists_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSatisfactionClean
