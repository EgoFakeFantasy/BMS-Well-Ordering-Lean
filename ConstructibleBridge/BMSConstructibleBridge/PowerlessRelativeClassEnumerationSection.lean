import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassOmegaAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassDeltaSeparation
import BMSConstructibleBridge.SecondOrderOmegaOrdinal
import BMSConstructibleBridge.PowerlessValueBounded

/-! # 类内枚举的最小编号逆图

每个纤维是类内 Δ₀ 子集，其最小内部自然数由原商正则性取得。
唯一性来自实际 ω 的隶属线序；所得逆图是类内集合，而不是 Type 选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationSection

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

def minimal_l (G x i : type_l hℳ B) : Prop :=
  value_l (ℳ := structure_l hℳ B hBase) G i x ∧ ∀ j : type_l hℳ B,
    mem_l hℳ j.val i.val → ¬value_l (ℳ := structure_l hℳ B hBase) G j x

def formula_m : Formula ℒ [] [.set, .set, .set] := .conj
  (PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here))
  (membershipLevyBound.boundedForall (.fvar (.there .here)) <| .neg
    (PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.bvar .here) (.fvar .here)))

theorem delta_l : Formula.IsDelta0 membershipLevyBound formula_m :=
  .conj (PowerlessValueBounded.delta_l _ _ _) (.bounded_forall _ (.neg (PowerlessValueBounded.delta_l _ _ _)))

theorem formula_l (G x i : type_l hℳ B) : formula_m.satisfies
    ((((Env.empty (M := structure_l hℳ B hBase)).pushFree G).pushFree i).pushFree x) ↔
      minimal_l (hBase := hBase) G x i := by
  simp only [formula_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l, Arguments.eval, Term.eval]
  rfl

theorem minimum_l {ω G X x : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val X.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i y)
    (hx : mem_l hℳ x.val X.val) :
    ∃ i : type_l hℳ B, mem_l hℳ i.val ω.val ∧ minimal_l (hBase := hBase) G x i := by
  let φ : Formula ℒ [] [.set, .set, .set] := PowerlessValueBounded.formula_m
    (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here))
  let η : Env (structure_l hℳ B hBase) [] [.set, .set] := ((Env.empty).pushFree G).pushFree x
  obtain ⟨S, hS⟩ := PowerlessRelativeClassDeltaSeparation.exists_l (hBase := hBase)
    (φ := φ) (PowerlessValueBounded.delta_l _ _ _) η ω
  have hRead (i : type_l hℳ B) : mem_l hℳ i.val S.val ↔ mem_l hℳ i.val ω.val ∧
      value_l (ℳ := structure_l hℳ B hBase) G i x :=
    (hS i).trans (and_congr Iff.rfl (PowerlessValueBounded.formula_l (η.pushFree i) _ _ _))
  obtain ⟨a, haω, ha⟩ := hOnto x hx
  have hFoundation := SecondOrderFoundation.models_l hℳ
  change ∀ S : SecondOrderQuotient.type_l hℳ, (∃ i, mem_l hℳ i S) →
    ∃ i, mem_l hℳ i S ∧ ∀ j, mem_l hℳ j i → ¬mem_l hℳ j S at hFoundation
  obtain ⟨i, hiS, hMin⟩ := hFoundation S.val ⟨a.val, (hRead a).mpr ⟨haω, ha⟩⟩
  let i' : type_l hℳ B := ⟨i, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase S.property hiS⟩
  have hi := (hRead i').mp hiS
  have hω' := (PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω
  exact ⟨i', hi.1, hi.2, fun j hji hj => hMin j.val hji ((hRead j).mpr
    ⟨SecondOrderOmegaTransitive.member_l hℳ hω' hi.1 hji, hj⟩)⟩

theorem unique_l {ω G x i j : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hiω : mem_l hℳ i.val ω.val) (hjω : mem_l hℳ j.val ω.val)
    (hi : minimal_l (hBase := hBase) G x i) (hj : minimal_l (hBase := hBase) G x j) : i = j := by
  have hOrd := SecondOrderOmegaOrdinal.ordinal_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l (hBase := hBase) ω).mp hω)
  rcases hOrd.wellOrder.linear.compare i.val hiω j.val hjω with h | h | h
  · exact Subtype.ext (SecondOrderQuotient.ext_l hℳ i.val j.val h)
  · exact (hj.2 i h hi.1).elim
  · exact (hi.2 j h hj.1).elim

theorem exists_l {ω G X : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val X.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i y) :
    ∃ R : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) R X ω ∧
      ∀ x i : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) R x i ↔
        mem_l hℳ x.val X.val ∧ mem_l hℳ i.val ω.val ∧ minimal_l (hBase := hBase) G x i := by
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l (hBase := hBase) delta_l
    ((Env.empty (M := structure_l hℳ B hBase)).pushFree G) X ω (by
      intro x hx
      obtain ⟨i, hiω, hi⟩ := minimum_l hω hOnto hx
      exact ⟨i, ⟨hiω, (formula_l G x i).mpr hi⟩, fun j hj =>
        unique_l hω hj.1 hiω ((formula_l G x j).mp hj.2) hi⟩)
  exact ⟨R, hR, fun x i => (hRead x i).trans
    (and_congr Iff.rfl (and_congr Iff.rfl (formula_l G x i)))⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassEnumerationSection
