import BMSConstructibleBridge.PowerlessAdditionIteration
import BMSConstructibleBridge.PowerlessAdditionFiniteAbsolute
import BMSConstructibleBridge.PowerlessOperatorClosure

/-!
# 以有限值公式定义整条原加法迭代图

固定自然数初值 a，原迭代图 F 的每个值由有限加法计算识别。
逐点核验成员公式后，源覆盖给 F∈D(A)，不将 F∈A 放入前提。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionIterationCut

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def cut_l (ω e a p : carrier_l ℳ) : Prop :=
  ∃ n t, member_l ℳ n ω ∧ member_l ℳ t ω ∧ ordered_l n t p ∧ PowerlessAdditionFinite.addition_l ω e a n t

def cut_m {Γ Δ : SortContext ℒ} (ω e a p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w ω))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
      (.conj (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (w p))
        (PowerlessAdditionFiniteSyntax.addition_m (w ω) (w e) (w a) (.bvar (.there .here)) (.bvar .here))))))

theorem cut_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e a p : Term ℒ Γ Δ .set) :
    (cut_m ω e a p).satisfies η ↔ cut_l (ω.eval η) (e.eval η) (a.eval η) (p.eval η) := by
  simp only [cut_m, cut_l, Formula.satisfies, ordered_formula_l, PowerlessAdditionFiniteSyntax.addition_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem absolute_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A} (hAT : PowerlessNaturalOrder.transitive_l A)
    {ω e a p : type_l A} {F : carrier_l ℳ} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
    (ha : member_l ℳ a.val ω.val) (hF : PowerlessAddition.iteration_l ω.val e.val a.val F)
    (hG : ∀ m, member_l ℳ m ω.val → ∀ g, map_l g m ω.val → member_l ℳ g A) :
    cut_l (ℳ := structure_l A hA) ω e a p ↔ member_l ℳ p.val F := by
  constructor
  · rintro ⟨n, t, hn, _, hp, ht⟩
    have h := (PowerlessAdditionFiniteAbsolute.addition_l hℳ hAT hω he ha hn hG).mp ht
    obtain ⟨q, hq, h₀⟩ := (PowerlessAdditionIteration.value_l hℳ hω he hF).mpr h
    have h₁ := PowerlessBasic.ordered_unique_l hℳ ((PowerlessSourceGraphAbsolute.ordered_l hAT).mp hp) h₀
    exact h₁.symm ▸ hq
  · intro hp
    obtain ⟨n, t, hn, ht, h₀⟩ := (PowerlessAdditionIteration.map_l hℳ hω he ha hF).1 p.val hp
    have hnA := hAT ω.val n ω.property hn
    have htA := hAT ω.val t ω.property ht
    refine ⟨⟨n, hnA⟩, ⟨t, htA⟩, hn, ht, (PowerlessSourceGraphAbsolute.ordered_l hAT).mpr h₀, ?_⟩
    exact (PowerlessAdditionFiniteAbsolute.addition_l hℳ hAT hω he ha hn hG).mpr
      ((PowerlessAdditionIteration.value_l hℳ hω he hF).mp ⟨p.val, hp, h₀⟩)

theorem source_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A : carrier_l ℳ} {hA : ∃ x, member_l ℳ x A} (hAT : PowerlessNaturalOrder.transitive_l A)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ) (ω e a p : Term ℒ Γ Δ .set)
    {F : carrier_l ℳ} (hω : omega_l (ω.eval η).val) (he : PowerlessNatural.zero_l (e.eval η).val)
    (ha : member_l ℳ (a.eval η).val (ω.eval η).val)
    (hF : PowerlessAddition.iteration_l (ω.eval η).val (e.eval η).val (a.eval η).val F)
    (hG : ∀ m, member_l ℳ m (ω.eval η).val → ∀ g, map_l g m (ω.eval η).val → member_l ℳ g A) :
    (cut_m ω e a p).satisfies η ↔ member_l ℳ (p.eval η).val F :=
  (cut_formula_l η ω e a p).trans (absolute_l hℳ hAT hω he ha hF hG)

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A D a F : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D)
    (hAT : PowerlessNaturalOrder.transitive_l A) (hωA : member_l ℳ ω A) (ha : member_l ℳ a ω)
    (hF : PowerlessAddition.iteration_l ω e a F)
    (hG : ∀ m, member_l ℳ m ω → ∀ g, map_l g m ω → member_l ℳ g A) (hFA : subset_l F A) : member_l ℳ F D := by
  let hA : ∃ x, member_l ℳ x A := ⟨ω, hωA⟩
  have heA := hAT ω e hωA (PowerlessNatural.zero_mem_l hℳ hω ht.1)
  have haA := hAT ω a hωA ha
  let η₀ : Env (structure_l A hA) [.set] [] := Env.empty.pushBound ⟨a, haA⟩
  let η₁ : Env (structure_l A hA) [.set, .set] [] := η₀.pushBound ⟨e, heA⟩
  let η : Env (structure_l A hA) [.set, .set, .set] [] := η₁.pushBound ⟨ω, hωA⟩
  let φ : Formula ℒ [.set, .set, .set, .set] [] :=
    cut_m (.bvar (.there .here)) (.bvar (.there (.there .here)))
      (.bvar (.there (.there (.there .here)))) (.bvar .here)
  apply PowerlessOperatorClosure.specified_l hℳ hω ht hT hD φ η
  intro p
  constructor
  · intro hp
    refine ⟨hFA p hp, ?_⟩
    exact (source_l hℳ hAT (η.pushBound ⟨p, hFA p hp⟩)
      (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar (.there (.there (.there .here))))
      (.bvar .here) hω ht.1 ha hF hG).mpr hp
  · rintro ⟨hpA, hp⟩
    exact (source_l hℳ hAT (η.pushBound ⟨p, hpA⟩)
      (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar (.there (.there (.there .here))))
      (.bvar .here) hω ht.1 ha hF hG).mp hp

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAdditionIterationCut
