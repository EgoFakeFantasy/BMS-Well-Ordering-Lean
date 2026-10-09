import BMSConstructibleBridge.PowerlessAssignmentUpdateBounded
import BMSConstructibleBridge.PowerlessEvaluationQueryBounded
import BMSConstructibleBridge.PowerlessFiniteSequencesSyntax

/-! # 集合大小赋值域上存在量词求值的纯 Δ₀ 检查

更新图的见证限制到实际全体内部有限 A 值序列集 S。长度、取值与历史
查询均有显式界。与原无界写法的等价只要求 S 的精确序列规格，不使用
Collection、幂集或模型自然数外部标准性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationExistentialBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω A S H f i b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up (up t))
  membershipLevyBound.boundedExists ω <|
    .conj (PowerlessMapBounded.formula_m (up f) (.bvar .here) (up A)) <|
      .conj (SecondOrderObjectSyntax.member_m (up i) (.bvar .here)) <|
        membershipLevyBound.boundedExists (up A) <|
          membershipLevyBound.boundedExists (up (up S)) <|
            .conj (PowerlessMapBounded.formula_m (.bvar .here) (.bvar (.there (.there .here))) (w A)) <|
              .conj (PowerlessAssignmentUpdateBounded.formula_m (.bvar (.there (.there .here)))
                (w A) (w f) (w i) (.bvar (.there .here)) (.bvar .here))
                (PowerlessEvaluationQueryBounded.formula_m (w H) (w b) (.bvar .here))

theorem delta_l {Γ Δ : SortContext ℒ} (ω A S H f i b : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω A S H f i b) :=
  .bounded_exists ω (.conj (PowerlessMapBounded.delta_l _ _ _) (.conj (.rel _ _)
    (.bounded_exists (up A) (.bounded_exists (up (up S))
      (.conj (PowerlessMapBounded.delta_l _ _ _)
        (.conj (PowerlessAssignmentUpdateBounded.delta_l _ _ _ _ _ _)
          (PowerlessEvaluationQueryBounded.delta_l _ _ _)))))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω A S H f i b : carrier_l 𝒩) : Prop :=
  ∃ n, member_l 𝒩 n ω ∧ map_l (ℳ := 𝒩) f n A ∧ member_l 𝒩 i n ∧
    ∃ a, member_l 𝒩 a A ∧ ∃ g, member_l 𝒩 g S ∧ map_l (ℳ := 𝒩) g n A ∧
      PowerlessAssignmentUpdateBounded.holds_l (𝒩 := 𝒩) n A f i a g ∧
      PowerlessEvaluationClause.query_l (ℳ := 𝒩) H b g

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω A S H f i b : Term ℒ Γ Δ .set) :
    (formula_m ω A S H f i b).satisfies η ↔
      holds_l (ω.eval η) (A.eval η) (S.eval η) (H.eval η) (f.eval η) (i.eval η) (b.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l,
    PowerlessAssignmentUpdateBounded.formula_l, PowerlessEvaluationQueryBounded.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem exists_iff_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
    (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {ω A S H f i b : type_l hℳ}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω A S) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) ω A S H f i b ↔
      PowerlessEvaluationClause.exists_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω A H f i b := by
  constructor
  · rintro ⟨n, hn, hf, hi, a, ha, g, _, hg, hUpdate, hQuery⟩
    exact ⟨n, hn, hf, hi, a, ha, g, hg,
      (PowerlessAssignmentUpdateBounded.update_iff_l hℳ hf hg hi ha).mp hUpdate, hQuery⟩
  · rintro ⟨n, hn, hf, hi, a, ha, g, hg, hUpdate, hQuery⟩
    exact ⟨n, hn, hf, hi, a, ha, g, (hS g).mpr ⟨n, hn, hg⟩, hg,
      (PowerlessAssignmentUpdateBounded.update_iff_l hℳ hf hg hi ha).mpr hUpdate, hQuery⟩

def schema_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
  let ω : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar .here
  let A : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there .here)
  let S : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let H : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let f : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let i : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let b : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  .imp (PowerlessFiniteSequencesSyntax.spec_m ω A S) <|
    .iff (formula_m ω A S H f i b) (PowerlessEvaluationClause.exists_m ω A H f i b)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem derives_m : Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m sentence_m) := by
  apply SecondOrderAxioms.interpretation_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hS
  have hS' := (PowerlessFiniteSequencesSyntax.spec_formula_l η _ _ _).mp hS
  exact (formula_l η _ _ _ _ _ _ _).trans
    ((exists_iff_l hℳ hS').trans (PowerlessEvaluationClause.exists_formula_l η _ _ _ _ _ _).symm)

#print axioms delta_l
#print axioms exists_iff_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationExistentialBounded
