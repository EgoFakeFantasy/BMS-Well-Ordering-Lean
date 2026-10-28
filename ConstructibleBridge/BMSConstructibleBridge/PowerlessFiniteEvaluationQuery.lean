import BMSConstructibleBridge.PowerlessEvaluationFiniteHistoryBounded
import BMSConstructibleBridge.PowerlessEvaluationHistoryRestriction
import BMSConstructibleBridge.PowerlessEvaluationQueryBounded

/-! # 有界有限历史定义的稳定求值查询

用实际全体 C 值有限序列集 Q 界定候选图，只存在量化内部有限长度。
任一包含查询索引的原历史都给出相同结果；该结论覆盖非标准内部长度。
这里尚未把查询识别为良构公式的真值，也不宣称完整 Sat 图已经构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationQuery

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q k f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedExists ω <|
    membershipLevyBound.boundedExists (up Q) <| .conj
      (SecondOrderObjectSyntax.member_m (w k) (.bvar (.there .here))) <| .conj
        (PowerlessEvaluationFiniteHistoryBounded.formula_m (w C) (w ω) (w e) (w N) (w T) (w A) (w S)
          (w t₁) (w t₂) (w t₃) (.bvar .here) (.bvar (.there .here)))
        (PowerlessEvaluationQueryBounded.formula_m (.bvar .here) (w k) (w f))

theorem delta_l {Γ Δ : SortContext ℒ} (C ω e N T A S t₁ t₂ t₃ Q k f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m C ω e N T A S t₁ t₂ t₃ Q k f) :=
  .bounded_exists ω (.bounded_exists (up Q) (.conj (.rel _ _)
    (.conj (PowerlessEvaluationFiniteHistoryBounded.delta_l _ _ _ _ _ _ _ _ _ _ _ _)
      (PowerlessEvaluationQueryBounded.delta_l _ _ _))))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (C ω e N T A S t₁ t₂ t₃ Q k f : carrier_l 𝒩) : Prop :=
  ∃ m, member_l 𝒩 m ω ∧ ∃ F, member_l 𝒩 F Q ∧ member_l 𝒩 k m ∧
    PowerlessEvaluationFiniteHistoryBounded.holds_l C ω e N T A S t₁ t₂ t₃ F m ∧
    PowerlessEvaluationClause.query_l F k f

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (C ω e N T A S t₁ t₂ t₃ Q k f : Term ℒ Γ Δ .set) :
    (formula_m C ω e N T A S t₁ t₂ t₃ Q k f).satisfies η ↔
      holds_l (C.eval η) (ω.eval η) (e.eval η) (N.eval η) (T.eval η) (A.eval η) (S.eval η)
        (t₁.eval η) (t₂.eval η) (t₃.eval η) (Q.eval η) (k.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessEvaluationFiniteHistoryBounded.formula_l,
    PowerlessEvaluationQueryBounded.formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

theorem stable_l (K : source_coding_l hℳ) {B β C e N T A S t₁ t₂ t₃ Q F r k f : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C) (hωC : mem_l hℳ K.omega C)
    (he : PowerlessNatural.zero_l (ℳ := SecondOrderQuotient.structure_l hℳ) e)
    (hN : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega K.omega N)
    (hT : map_l (ℳ := SecondOrderQuotient.structure_l hℳ) T K.omega K.omega)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega A S)
    (hQ : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) K.omega C Q)
    (hr : mem_l hℳ r K.omega)
    (hF : PowerlessEvaluationFiniteHistory.trace_l (𝒩 := SecondOrderQuotient.structure_l hℳ)
      C K.omega e T A t₁ t₂ t₃ S F r) (hk : mem_l hℳ k r) :
    holds_l (𝒩 := SecondOrderQuotient.structure_l hℳ) C K.omega e N T A S t₁ t₂ t₃ Q k f ↔
      PowerlessEvaluationClause.query_l (ℳ := SecondOrderQuotient.structure_l hℳ) F k f := by
  have hωOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ K.omega_spec
  have hrOrd : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) r := by
    apply hωOrd.mem
    exact hr
  constructor
  · rintro ⟨m, hm, G, _, hkm, hG, hQuery⟩
    have hG' := (PowerlessEvaluationFiniteHistoryBounded.trace_iff_l K hBase hLimit hC hωC
      he hN hT hS hm).mp hG
    have hmOrd : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct (SecondOrderQuotient.structure_l hℳ)) m := by
      apply hωOrd.mem
      exact hm
    have hCompare : (∀ x, mem_l hℳ x m → mem_l hℳ x r) ∨
        (∀ x, mem_l hℳ x r → mem_l hℳ x m) := by
      rcases hωOrd.wellOrder.linear.compare m hm r hr with hSame | hmr | hrm
      · exact Or.inl (fun x hx => (hSame x).mp hx)
      · exact Or.inl (fun x hx => hrOrd.transitive m hmr x hx)
      · exact Or.inr (fun x hx => hmOrd.transitive r hrm x hx)
    rcases hCompare with hSubset | hSubset
    · exact (PowerlessEvaluationHistoryRestriction.query_l hmOrd.transitive hG' hF hSubset hkm).mp hQuery
    · exact (PowerlessEvaluationHistoryRestriction.query_l hrOrd.transitive hF hG' hSubset hk).mpr hQuery
  · intro hQuery
    exact ⟨r, hr, F, (hQ F).mpr ⟨r, hr, hF.1⟩, hk,
      (PowerlessEvaluationFiniteHistoryBounded.trace_iff_l K hBase hLimit hC hωC he hN hT hS hr).mpr hF,
      hQuery⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteEvaluationQuery
