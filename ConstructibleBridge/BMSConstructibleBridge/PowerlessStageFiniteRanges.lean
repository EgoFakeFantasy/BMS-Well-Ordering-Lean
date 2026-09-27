import BMSConstructibleBridge.PowerlessStageFiniteGraphs
import BMSConstructibleBridge.PowerlessCoordinates

/-!
# 内部有限值域的任意子集落级

对实际内部长度作纯公式归纳。有限枚举可有重复值，待收集的集合也无须
在小层内可定义：只要它在背景模型中存在且被该枚举覆盖，就属于同一极限层。
这供有限关系图参数的成员性证明使用，不断言无限子集封闭或有限图反射。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteRanges

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 集合的每个元素都是给定图的一个值；不要求枚举无重复。 -/
def covered_l (f D : carrier_l ℳ) : Prop :=
  ∀ x, member_l ℳ x D → ∃ i, value_l f i x

def covered_m {Γ Δ : SortContext ℒ} (f D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp
    (SecondOrderObjectSyntax.member_m (.bvar .here) (D.weakenBound SetTheory.SetSort.set))
    (.existsE .set (SecondOrderObjectSyntax.value_m
      ((f.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)
      (.bvar .here) (.bvar (.there .here)))))

theorem covered_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (f D : Term ℒ Γ Δ .set) :
    (covered_m f D).satisfies η ↔ covered_l (f.eval η) (D.eval η) := by
  simp only [covered_m, covered_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

/-- 任意内部有限枚举所覆盖的内部集合属于同一非零极限层。 -/
theorem finite_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) :
    ∀ n, member_l ℳ n ω → ∀ f D, map_l f n A → covered_l f D → member_l ℳ D A := by
  classical
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => A, free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set] := .forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.map_m (.bvar (.there .here)) (.fvar .here) (.fvar (.there .here)))
    (.imp (covered_m (.bvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there .here))))))
  have h (n : carrier_l ℳ) : φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∀ f D, map_l f n A → covered_l f D → member_l ℳ D A := by
    simp only [φ, Formula.satisfies, map_formula_l, covered_formula_l,
      SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun z hz => (h z).mpr (by
      intro f D hf hD
      apply PowerlessStageClosure.empty_l hℳ hω hA hα ht hT
      intro x hx
      obtain ⟨i, hi⟩ := hD x hx
      exact hz i (PowerlessFunction.value_mem_l hℳ hf hi).1))
    (fun n m _ hm h₁ => (h m).mpr (by
      intro g D hg hD
      obtain ⟨f, a, hf, ha, hg⟩ := PowerlessAppendGraph.decompose_l hℳ hg hm
      let ζ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
        { bound := fun _ => f, free := fun _ => D }
      let ψ : Formula ℒ [] [.set, .set] := .existsE .set
        (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.bvar .here) (.fvar .here))
      obtain ⟨K, hK₀⟩ := PowerlessComprehension.separation_l hℳ ψ ζ D
      have hK : ∀ x, member_l ℳ x K ↔ member_l ℳ x D ∧ ∃ i, value_l f i x := by
        intro x
        refine (hK₀ x).trans (and_congr Iff.rfl ?_)
        simp only [ψ, Formula.satisfies, value_formula_l]
        rfl
      have hKA := (h n).mp h₁ f K hf (fun x hx => ((hK x).mp hx).2)
      have h₂ : ∀ x, member_l ℳ x D → member_l ℳ x K ∨ x = a := by
        intro x hx
        obtain ⟨i, hi⟩ := hD x hx
        rcases (PowerlessAppendGraph.value_l hℳ hg).mp hi with hi | ⟨_, hx₀⟩
        · exact Or.inl ((hK x).mpr ⟨hx, i, hi⟩)
        · exact Or.inr hx₀
      by_cases haD : member_l ℳ a D
      · apply PowerlessStageGraphClosure.adjoin_l hℳ hω ht hT hA hα hKA ha
        intro x
        exact ⟨h₂ x, fun hx => hx.elim (fun hx => ((hK x).mp hx).1) (fun hx => hx ▸ haD)⟩
      · have hDK : D = K := (PowerlessTheory.ext_l hℳ).eq_of_same_members D K (fun x => by
          constructor
          · intro hx
            exact (h₂ x hx).elim id (fun hx₀ => (haD (hx₀ ▸ hx)).elim)
          · intro hx
            exact ((hK x).mp hx).1)
        exact hDK.symm ▸ hKA))
  exact fun n hn => (h n).mp (h₀ n hn)

/-- 用背景模型的任意原公式筛选有限值域，所得关系图仍是小层的元素。
公式的参数可以在小层之外；结论不要求小层满足该分离实例。 -/
theorem separation_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ α A n f : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃)
    (hT : PowerlessTriangular.triangular_l ω e T)
    (hA : PowerlessHierarchyStage.stage_l ω e T t₁ t₂ t₃ α A)
    (hα : PowerlessStagePair.limit_l α) (hn : member_l ℳ n ω) (hf : map_l f n A)
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Γ))
    (η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) Γ.length) :
    ∃ D, member_l ℳ D A ∧ ∀ x, member_l ℳ x D ↔
      (∃ i, value_l f i x) ∧ φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) := by
  obtain ⟨B, hB⟩ := PowerlessCoordinates.range_exists_l hℳ f
  obtain ⟨D, hD⟩ := PowerlessComprehension.separation_l hℳ φ η B
  have h₀ : ∀ x, member_l ℳ x D ↔
      (∃ i, value_l f i x) ∧ φ.satisfies ((PowerlessComprehension.env_l η).pushFree x) :=
    fun x => (hD x).trans (and_congr (hB x) Iff.rfl)
  exact ⟨D, finite_l hℳ hω ht hT hA hα n hn f D hf (fun x hx => ((h₀ x).mp hx).1), h₀⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessStageFiniteRanges
