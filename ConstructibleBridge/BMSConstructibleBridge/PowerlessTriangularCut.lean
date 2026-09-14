import BMSConstructibleBridge.PowerlessTriangularFiniteAbsolute
import BMSConstructibleBridge.PowerlessOperatorClosure

/-!
# 用有限三角数公式将实际 T 放入 D 输出

先逐点核验成员域中的公式确实定义外部实际 T。输入仅要求 T 的
各个有序对属于域，不要求整个 T 属于域；后者是算子输出的结论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularCut

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def cut_l (ω e p : carrier_l ℳ) : Prop :=
  ∃ n t, member_l ℳ n ω ∧ member_l ℳ t ω ∧ ordered_l n t p ∧ PowerlessTriangularFinite.value_l ω e n t

def cut_m {Γ Δ : SortContext ℒ} (ω e p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w ω))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
      (.conj (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (w p))
        (PowerlessTriangularFiniteSyntax.value_m (w ω) (w e) (.bvar (.there .here)) (.bvar .here))))))

theorem cut_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e p : Term ℒ Γ Δ .set) :
    (cut_m ω e p).satisfies η ↔ cut_l (ω.eval η) (e.eval η) (p.eval η) := by
  simp only [cut_m, cut_l, Formula.satisfies, ordered_formula_l, PowerlessTriangularFiniteSyntax.value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem absolute_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A} (hAT : PowerlessNaturalOrder.transitive_l A)
    {ω e p : type_l A} {T : carrier_l ℳ} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
    (hT : PowerlessTriangular.triangular_l ω.val e.val T)
    (hF : ∀ m, member_l ℳ m ω.val → ∀ f, map_l f m ω.val → member_l ℳ f A) :
    cut_l (ℳ := structure_l A hA) ω e p ↔ member_l ℳ p.val T := by
  constructor
  · rintro ⟨n, t, hn, _, hp, ht⟩
    obtain ⟨q, hq, h₀⟩ := (PowerlessTriangularFiniteAbsolute.value_l hℳ hAT hω he hT hn hF).mp ht
    have h := PowerlessBasic.ordered_unique_l hℳ ((PowerlessSourceGraphAbsolute.ordered_l hAT).mp hp) h₀
    exact h.symm ▸ hq
  · intro hp
    obtain ⟨n, t, hn, ht, h₀⟩ := hT.1.1 p.val hp
    have hnA := hAT ω.val n ω.property hn
    have htA := hAT ω.val t ω.property ht
    exact ⟨⟨n, hnA⟩, ⟨t, htA⟩, hn, ht, (PowerlessSourceGraphAbsolute.ordered_l hAT).mpr h₀,
      (PowerlessTriangularFiniteAbsolute.value_l hℳ hAT hω he hT hn hF).mpr ⟨p.val, hp, h₀⟩⟩

theorem source_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A : carrier_l ℳ} {hA : ∃ a, member_l ℳ a A} (hAT : PowerlessNaturalOrder.transitive_l A)
    {Γ Δ : SortContext ℒ} (η : Env (structure_l A hA) Γ Δ) (ω e p : Term ℒ Γ Δ .set)
    {T : carrier_l ℳ} (hω : omega_l (ω.eval η).val) (he : PowerlessNatural.zero_l (e.eval η).val)
    (hT : PowerlessTriangular.triangular_l (ω.eval η).val (e.eval η).val T)
    (hF : ∀ m, member_l ℳ m (ω.eval η).val → ∀ f, map_l f m (ω.eval η).val → member_l ℳ f A) :
    (cut_m ω e p).satisfies η ↔ member_l ℳ (p.eval η).val T :=
  (cut_formula_l η ω e p).trans (absolute_l hℳ hAT hω he hT hF)

theorem operator_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t₁ t₂ t₃ A D : carrier_l ℳ} (hω : omega_l ω)
    (ht : PowerlessEvaluationTags.tags_l e t₁ t₂ t₃) (hT : PowerlessTriangular.triangular_l ω e T)
    (hD : PowerlessEvaluationOperator.operator_l ω e T t₁ t₂ t₃ A D)
    (hAT : PowerlessNaturalOrder.transitive_l A) (hωA : member_l ℳ ω A) (heA : member_l ℳ e A)
    (hF : ∀ m, member_l ℳ m ω → ∀ f, map_l f m ω → member_l ℳ f A) (hTA : subset_l T A) : member_l ℳ T D := by
  let hA : ∃ a, member_l ℳ a A := ⟨ω, hωA⟩
  let η : Env (structure_l A hA) [.set, .set] [] :=
    ((Env.empty (σ := ℒ) (M := structure_l A hA)).pushBound
      (sort := SetTheory.SetSort.set) ⟨e, heA⟩).pushBound ⟨ω, hωA⟩
  let φ : Formula ℒ [.set, .set, .set] [] :=
    cut_m (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here)
  apply PowerlessOperatorClosure.specified_l hℳ hω ht hT hD φ η
  intro p
  constructor
  · intro hp
    refine ⟨hTA p hp, ?_⟩
    exact (source_l hℳ hAT (η.pushBound ⟨p, hTA p hp⟩)
      (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here) hω ht.1 hT hF).mpr hp
  · rintro ⟨hpA, hp⟩
    exact (source_l hℳ hAT (η.pushBound ⟨p, hpA⟩)
      (.bvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here) hω ht.1 hT hF).mp hp

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessTriangularCut
