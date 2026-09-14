import BMSConstructibleBridge.PowerlessAssignmentsAbsolute
import BMSConstructibleBridge.PowerlessOperatorClosure

/-!
# 整个有限赋值集合的定义子集成员性

逐个候选图的成员条件只需传递性；全部图已经在域内的事实另作输入。
原源覆盖于是把整个 S 放入 D 输出，不要求 S 预先是输入域的元素。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentsCut

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def cut_l (ω A f : carrier_l ℳ) : Prop := ∃ n, member_l ℳ n ω ∧ map_l f n A

def cut_m {Γ Δ : SortContext ℒ} (ω A f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
    (SecondOrderObjectSyntax.map_m (w f) (.bvar .here) (w A)))

theorem cut_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A f : Term ℒ Γ Δ .set) :
    (cut_m ω A f).satisfies η ↔ cut_l (ω.eval η) (A.eval η) (f.eval η) := by
  simp only [cut_m, cut_l, Formula.satisfies, map_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem absolute_l {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B}
    (hBT : PowerlessNaturalOrder.transitive_l B) {ω A f : type_l B} :
    cut_l (ℳ := structure_l B hB) ω A f ↔ cut_l ω.val A.val f.val := by
  constructor
  · rintro ⟨n, hn, hf⟩
    exact ⟨n.val, hn, (PowerlessSourceGraphAbsolute.map_l hBT).mp hf⟩
  · rintro ⟨n, hn, hf⟩
    exact ⟨⟨n, hBT ω.val n ω.property hn⟩, hn, (PowerlessSourceGraphAbsolute.map_l hBT).mpr hf⟩

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ B D A S : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ B D)
    (hBT : PowerlessNaturalOrder.transitive_l B) (hωB : member_l ℳ ω B) (hA : member_l ℳ A B)
    (hS : PowerlessEvaluationOperator.assignments_l ω A S) (hSB : subset_l S B) : member_l ℳ S D := by
  let hB : ∃ x, member_l ℳ x B := ⟨ω, hωB⟩
  let η : Env (structure_l B hB) [.set, .set] [] :=
    ((Env.empty (σ := ℒ) (M := structure_l B hB)).pushBound
      (sort := SetTheory.SetSort.set) ⟨A, hA⟩).pushBound ⟨ω, hωB⟩
  let φ : Formula ℒ [.set, .set, .set] [] :=
    cut_m (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here)
  apply PowerlessOperatorClosure.specified_l hℳ hω ht hT hD φ η
  intro f
  have h₀ (hf : member_l ℳ f B) : φ.satisfies (η.pushBound ⟨f, hf⟩) ↔ member_l ℳ f S := by
    rw [cut_formula_l]
    exact (absolute_l hBT).trans (hS f).symm
  constructor
  · intro hf
    exact ⟨hSB f hf, (h₀ (hSB f hf)).mpr hf⟩
  · rintro ⟨hf, h⟩
    exact (h₀ hf).mp h

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentsCut
