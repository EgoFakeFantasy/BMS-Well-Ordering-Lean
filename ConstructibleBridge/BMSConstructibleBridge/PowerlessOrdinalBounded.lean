import BMSConstructibleBridge.PowerlessSourceAmbient
import BMSConstructibleBridge.PowerlessOrdinal

/-!
# 序数判定的原源有界公式与传递子域绝对性

使用原 Formula 的有界量词，不增加源语法类型。判定与原内部
Structure.IsOrdinal 等价；绝对性只要求外部核心模型和子域传递性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalBounded

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure StabilityFrame

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def transitive_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedForall a
    (membershipLevyBound.boundedForall (.bvar .here)
      (SecondOrderObjectSyntax.member_m (.bvar .here)
        ((a.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set)))

theorem transitive_delta_l {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (transitive_m a) :=
  .bounded_forall a (.bounded_forall (.bvar .here) (.rel _ _))

theorem transitive_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (transitive_m a) ↔ PowerlessNaturalOrder.transitive_l (a.eval η) := by
  simp only [transitive_m, Formula.LevyBound.boundedForall, Formula.satisfies,
    Formula.LevyBound.membership, membershipLevyBound, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound]
  exact ⟨fun h x y hx hy => h x hx y hy, fun h x hx y hy => h x y hx hy⟩

def ordinal_m {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (transitive_m a)
    (.conj (membershipLevyBound.boundedForall a (transitive_m (.bvar .here)))
      (membershipLevyBound.boundedForall a
        (membershipLevyBound.boundedForall (a.weakenBound SetTheory.SetSort.set)
          (.disj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here))
            (.disj (.equal (.bvar (.there .here)) (.bvar .here))
              (SecondOrderObjectSyntax.member_m (.bvar .here) (.bvar (.there .here))))))))

theorem ordinal_delta_l {Γ Δ : SortContext ℒ} (a : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (ordinal_m a) :=
  .conj (transitive_delta_l a) (.conj
    (.bounded_forall a (transitive_delta_l (.bvar .here)))
    (.bounded_forall a (.bounded_forall (a.weakenBound SetTheory.SetSort.set)
      (.disj (.rel _ _) (.disj (.equal _ _) (.rel _ _))))))

theorem ordinal_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (ordinal_m a) ↔ PowerlessOrdinal.ordinal_l (a.eval η) := by
  have h : Formula.satisfies η (ordinal_m a) ↔
      PowerlessNaturalOrder.transitive_l (a.eval η) ∧
        (∀ x, member_l ℳ x (a.eval η) → PowerlessNaturalOrder.transitive_l x) ∧
        (∀ x, member_l ℳ x (a.eval η) → ∀ y, member_l ℳ y (a.eval η) →
          member_l ℳ x y ∨ x = y ∨ member_l ℳ y x) := by
    simp only [ordinal_m, Formula.LevyBound.boundedForall, Formula.satisfies,
      transitive_formula_l, Formula.LevyBound.membership, membershipLevyBound,
      SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
    rfl
  rw [h]
  exact ⟨fun ⟨hA, h₀, h₁⟩ => PowerlessOrdinal.of_transitive_l hℳ hA h₀
    (fun x y hx hy => h₁ x hx y hy),
    fun hA => ⟨PowerlessOrdinal.transitive_l hA,
      fun _ hx => PowerlessOrdinal.transitive_l (PowerlessOrdinal.mem_l hA hx),
      fun _ hx _ hy => PowerlessOrdinal.compare_l hℳ hA hx hy⟩⟩

-- 原有纯公式只交换了 guard 与无关量词的位置，语义对应也须显式核验。
theorem equiv_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (ordinal_m a) ↔ Formula.satisfies η (PowerlessOrdinal.ordinal_m a) := by
  simp only [ordinal_m, PowerlessOrdinal.ordinal_m, Formula.LevyBound.boundedForall,
    Formula.satisfies, transitive_formula_l, PowerlessNaturalOrder.transitive_formula_l,
    Formula.LevyBound.membership, membershipLevyBound, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    ⟨fun h x y hx hy => h x hx y hy, fun h x hx y hy => h x y hx hy⟩)

theorem member_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A : carrier_l ℳ} {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    (hAT : PowerlessNaturalOrder.transitive_l A) {Γ Δ : SortContext ℒ}
    (η : Env (structure_l A hA) Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (ordinal_m a) ↔ PowerlessOrdinal.ordinal_l (a.eval η).val := by
  rw [PowerlessSourceAmbient.formula_l hAT (ordinal_delta_l a) η,
    ordinal_formula_l hℳ, PowerlessSourceAmbient.term_l]

theorem source_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {A : carrier_l ℳ} {hA : ∃ a, ThirdOrderSemantics.member_l ℳ a A}
    (hAT : PowerlessNaturalOrder.transitive_l A) {Γ Δ : SortContext ℒ}
    (η : Env (structure_l A hA) Γ Δ) (a : Term ℒ Γ Δ .set) :
    Formula.satisfies η (PowerlessOrdinal.ordinal_m a) ↔ PowerlessOrdinal.ordinal_l (a.eval η).val :=
  (equiv_l η a).symm.trans (member_l hℳ hAT η a)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessOrdinalBounded
