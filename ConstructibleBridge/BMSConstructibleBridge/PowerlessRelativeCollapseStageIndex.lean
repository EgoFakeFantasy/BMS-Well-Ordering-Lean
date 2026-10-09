import BMSConstructibleBridge.PowerlessRelativeCodedHistoryCollapseDerives
import BMSConstructibleBridge.PowerlessBMSQuotientAxioms
import BMSConstructibleBridge.PowerlessRelativeOrdinalCoverage
import BMSConstructibleBridge.SecondOrderOrdinalBounded

/-! # 实际坍缩目标中的相对阶段集

对象语言为纯隶属 ℒ，背景为原 num/set Z₂。阶段集由原完整分离取得，
只保留同时在 T 中的阶段 a 和实际层对象 c。一般传递基集 B 可含较大
序数，因此这里不把 T 的全部序数成员误当作相对构造高度。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCollapseStageIndex

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def point_m {Γ Δ : SortContext ℒ} (B T a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set <| .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up T))
    (PowerlessRelativeHierarchySyntax.level_m (up B) (up a) (.bvar .here))

def spec_m {Γ Δ : SortContext ℒ} (B T J : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set <| .iff (SecondOrderObjectSyntax.member_m (.bvar .here) (up J))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up T))
      (point_m (up B) (up T) (.bvar .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

def point_l (B T a : type_l hℳ) : Prop :=
  ∃ c, mem_l hℳ c T ∧ level_l hℳ B a c

def spec_l (B T J : type_l hℳ) : Prop :=
  ∀ a, mem_l hℳ a J ↔ mem_l hℳ a T ∧ point_l B T a

theorem point_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B T a : Term ℒ Γ Δ .set) :
    (point_m B T a).satisfies η ↔ point_l (B.eval η) (T.eval η) (a.eval η) := by
  simp only [point_m, point_l, Formula.satisfies,
    PowerlessRelativeHierarchySemantics.level_formula_l K, SecondOrderObjectSyntax.member_m,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem spec_formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ) (B T J : Term ℒ Γ Δ .set) :
    (spec_m B T J).satisfies η ↔ spec_l (B.eval η) (T.eval η) (J.eval η) := by
  simp only [spec_m, spec_l, Formula.satisfies, point_formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 分离使用原层公式本身，不借用 T 的源模型资格或 Collection。 -/
theorem exists_l (K : source_coding_l hℳ) (B T : type_l hℳ) :
    ∃ J, spec_l B T J := by
  let φ : Formula ℒ [.set, .set, .set] [] :=
    point_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)
  let η : Env (SecondOrderQuotient.structure_l hℳ) [.set, .set] [] :=
    Env.empty |>.pushBound B |>.pushBound T
  obtain ⟨J, hJ⟩ := PowerlessBMSQuotientAxioms.separation_l hℳ φ η T
  refine ⟨J, fun a => (hJ a).trans (and_congr Iff.rfl ?_)⟩
  exact point_formula_l K (η.pushBound a) _ _ _

/-- 阶段向下封闭来自实际层成员性，而非假定 T 是层。 -/
theorem ordinal_l {B T J : type_l hℳ}
    (hB : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hT : ∀ x, mem_l hℳ x T → ∀ y, mem_l hℳ y x → mem_l hℳ y T)
    (hJ : spec_l B T J) : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) J := by
  have ha (a : type_l hℳ) (h : mem_l hℳ a J) : SetTheory.Structure.IsOrdinal
      (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
        (SecondOrderQuotient.structure_l hℳ)) a := by
    obtain ⟨_, c, _, hc⟩ := (hJ a).mp h
    exact PowerlessRelativeLevelClosure.ordinal_l hℳ hc
  apply SecondOrderOrdinalBounded.of_transitive_l hℳ
  · intro a haJ b hba
    obtain ⟨haT, c, hcT, hc⟩ := (hJ a).mp haJ
    have hb : SetTheory.Structure.IsOrdinal
        (SetTheory.Definitional.Project.FirstOrderSemantics.reduct
          (SecondOrderQuotient.structure_l hℳ)) b := by
      apply SetTheory.Structure.IsOrdinal.mem (ha a haJ)
      exact hba
    obtain ⟨d, hd⟩ := PowerlessRelativeOrdinalCoverage.level_exists_l hℳ hB hb
    exact (hJ b).mpr ⟨hT a haT b hba, d,
      hT c hcT d (PowerlessRelativeLevelClosure.members_l hℳ hB hba hd hc), hd⟩
  · intro a haJ b hba c hcb
    exact (ha a haJ).transitive b hba c hcb
  · intro a b haJ hbJ
    rcases SecondOrderOrdinalComparison.compare_l hℳ (ha a haJ) (ha b hbJ) with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

#print axioms point_formula_l
#print axioms spec_formula_l
#print axioms exists_l
#print axioms ordinal_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeCollapseStageIndex
