import BMSConstructibleBridge.PowerlessRelativeLimitFiniteMapsDerives
import BMSConstructibleBridge.SecondOrderFiniteSequencesDerives
import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.SecondOrderMemberDefBoundedSlice

/-! # 内部有限序列集合属于相对可构造类

先对全部原商序列取得共同极限层界，再由纯 Δ₀ 检查式切片。
这里只证明序列集合的类成员关系；未证明其类内可数性或遗传性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteSequences

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def sequence_m {Γ Δ : SortContext ℒ} (ω X f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω (PowerlessMapBounded.formula_m (up f) (.bvar .here) (up X))

theorem sequence_delta_l {Γ Δ : SortContext ℒ} (ω X f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (sequence_m ω X f) :=
  .bounded_exists ω (PowerlessMapBounded.delta_l _ _ _)

theorem sequence_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω X f : Term ℒ Γ Δ .set) : (sequence_m ω X f).satisfies η ↔
      PowerlessFiniteSequencesSyntax.sequence_l (ω.eval η) (X.eval η) (f.eval η) := by
  simp only [sequence_m, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessMapBounded.formula_l, up,
    Arguments.eval, Term.eval_weakenBound, Term.eval]
  rfl

theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C ω X S : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hωC : mem_l hℳ ω C) (hXC : mem_l hℳ X C)
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω X S) :
    PowerlessRelativeClassCorrespondence.member_l hℳ B S := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨γ, D, _, hD, hDef⟩ := PowerlessRelativeLevelClosure.successor_exists_l hℳ hBase hC
  let φ : Formula ℒ [] [.set, .set, .set] := sequence_m
    (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] := ((Env.empty).pushFree X).pushFree ω
  have hParams : ∀ s (v : Variable [SetTheory.SetSort.set, SetTheory.SetSort.set] s), mem_l hℳ (η.freeVal v) C := by
    intro s v
    cases v with
    | here => exact hωC
    | there v => cases v with
      | here => exact hXC
      | there v => nomatch v
  have hSC : mem_l hℳ S D := SecondOrderMemberDefBoundedSlice.member_l hℳ (φ := φ) hDef
    (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hC)
    (sequence_delta_l _ _ _) η hParams (by
      intro f
      have hS' : mem_l hℳ f S ↔ PowerlessFiniteSequencesSyntax.sequence_l
          (ℳ := SecondOrderQuotient.structure_l hℳ) ω X f := hS f
      rw [hS']
      have hφ := sequence_formula_l (η.pushFree f)
        (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
      constructor
      · intro hf
        obtain ⟨n, hn, hMap⟩ := hf
        exact ⟨PowerlessRelativeLimitFiniteMaps.member_l hℳ hBase hLimit hC K
          (hωEq ▸ hωC) hXC (hωEq ▸ hn) hMap, hφ.mpr ⟨n, hn, hMap⟩⟩
      · intro hf
        exact hφ.mp hf.2)
  exact ⟨γ, D, hD, hSC⟩

theorem exists_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m) {B β C ω X : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hLimit : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hω : SecondOrderOmega.omega_l hℳ ω) (hωC : mem_l hℳ ω C) (hXC : mem_l hℳ X C) :
    ∃ S, PowerlessRelativeClassCorrespondence.member_l hℳ B S ∧
      PowerlessFiniteSequencesSyntax.spec_l (ℳ := SecondOrderQuotient.structure_l hℳ) ω X S := by
  obtain ⟨S, hS⟩ := SecondOrderFiniteSequencesDerives.exists_l hℳ ω hω X
  exact ⟨S, member_l hℳ hBase hLimit hC hω hωC hXC hS, hS⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteSequences
