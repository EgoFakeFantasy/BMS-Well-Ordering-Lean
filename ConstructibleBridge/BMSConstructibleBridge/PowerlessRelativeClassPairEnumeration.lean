import BMSConstructibleBridge.PowerlessRelativeClassPairFamily
import BMSConstructibleBridge.PowerlessRelativeClassTwoEntrySequence
import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequenceEnumeration
import BMSConstructibleBridge.PowerlessBMSQuotientSuccessor

/-! # 可枚举类参数的全部无序对仍可类内枚举

用实际有限序列的前两项形成无序对；缺少两项时填一个固定对角无序对。
图关系是纯 Δ₀，全部存在见证在 Prop，没有全体子集的幂集假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPairEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def entry_m {Γ Δ : SortContext ℒ} (X e one f p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := up (up t)
  membershipLevyBound.boundedExists X <| membershipLevyBound.boundedExists (up X) <| .conj
    (PowerlessValueBounded.formula_m (w f) (w e) (.bvar (.there .here))) <| .conj
      (PowerlessValueBounded.formula_m (w f) (w one) (.bvar .here))
      (PowerlessPairBounded.pair_m (.bvar (.there .here)) (.bvar .here) (w p))

theorem entry_delta_l {Γ Δ : SortContext ℒ} (X e one f p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (entry_m X e one f p) :=
  .bounded_exists X (.bounded_exists (up X) (.conj (PowerlessValueBounded.delta_l _ _ _)
    (.conj (PowerlessValueBounded.delta_l _ _ _) (PowerlessPairBounded.pair_delta_l _ _ _))))

def entry_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (X e one f p : carrier_l 𝒩) : Prop :=
  ∃ a, member_l 𝒩 a X ∧ ∃ b, member_l 𝒩 b X ∧
    value_l (ℳ := 𝒩) f e a ∧ value_l (ℳ := 𝒩) f one b ∧ pair_l (ℳ := 𝒩) a b p

theorem entry_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (X e one f p : Term ℒ Γ Δ .set) : (entry_m X e one f p).satisfies η ↔
      entry_l (X.eval η) (e.eval η) (one.eval η) (f.eval η) (p.eval η) := by
  simp only [entry_m, entry_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    PowerlessPairBounded.pair_formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def formula_m {Γ Δ : SortContext ℒ} (X Q e one d f p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (entry_m X e one f p) <| .conj
    (membershipLevyBound.boundedForall Q <| .neg (entry_m (up X) (up e) (up one) (up f) (.bvar .here)))
    (.equal p d)

theorem delta_l {Γ Δ : SortContext ℒ} (X Q e one d f p : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m X Q e one d f p) :=
  .disj (entry_delta_l _ _ _ _ _)
    (.conj (.bounded_forall Q (.neg (entry_delta_l _ _ _ _ _))) (.equal _ _))

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (X Q e one d f p : Term ℒ Γ Δ .set) : (formula_m X Q e one d f p).satisfies η ↔
      entry_l (𝒩 := 𝒩) (X.eval η) (e.eval η) (one.eval η) (f.eval η) (p.eval η) ∨
        ((∀ q, member_l 𝒩 q (Q.eval η) →
          ¬entry_l (𝒩 := 𝒩) (X.eval η) (e.eval η) (one.eval η) (f.eval η) q) ∧ p.eval η = d.eval η) := by
  simp only [formula_m, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, entry_formula_l, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem entry_unique_l {A X e one f p q : type_l hℳ B}
    (hfMap : map_l (ℳ := structure_l hℳ B hBase) f A X)
    (hp : entry_l (𝒩 := structure_l hℳ B hBase) X e one f p)
    (hq : entry_l (𝒩 := structure_l hℳ B hBase) X e one f q) : p = q := by
  obtain ⟨a, _, b, _, hfa, hfb, hpPair⟩ := hp
  obtain ⟨a', _, b', _, hfa', hfb', hqPair⟩ := hq
  have haa := PowerlessRelativeClassFunctionComposition.value_unique_l hfMap hfa' hfa
  have hbb := PowerlessRelativeClassFunctionComposition.value_unique_l hfMap hfb' hfb
  subst a'
  subst b'
  exact PowerlessRelativeClassPairFamily.pair_unique_l hpPair hqPair

theorem decoder_l {ω X Q e one d S : type_l hℳ B}
    (hS : PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω X S)
    (hd : mem_l hℳ d.val Q.val) : ∃ R : type_l hℳ B,
      map_l (ℳ := structure_l hℳ B hBase) R S Q ∧ ∀ f p : type_l hℳ B,
        entry_l (𝒩 := structure_l hℳ B hBase) X e one f p →
          mem_l hℳ f.val S.val → mem_l hℳ p.val Q.val →
            value_l (ℳ := structure_l hℳ B hBase) R f p := by
  classical
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree d).pushFree one).pushFree e).pushFree Q).pushFree X
  let x : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let q : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let z : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let o : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let a : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    formula_m x q z o a (.fvar .here) (.fvar (.there .here))
  have hφ (f p : type_l hℳ B) : φ.satisfies ((η.pushFree p).pushFree f) ↔
      entry_l (𝒩 := structure_l hℳ B hBase) X e one f p ∨
        ((∀ q : type_l hℳ B, mem_l hℳ q.val Q.val →
          ¬entry_l (𝒩 := structure_l hℳ B hBase) X e one f q) ∧ p = d) :=
    formula_l ((η.pushFree p).pushFree f) x q z o a (.fvar .here) (.fvar (.there .here))
  have hTotal (f : type_l hℳ B) (hf : mem_l hℳ f.val S.val) : ∃! p : type_l hℳ B,
      mem_l hℳ p.val Q.val ∧ φ.satisfies ((η.pushFree p).pushFree f) := by
    by_cases h : ∃ p : type_l hℳ B, mem_l hℳ p.val Q.val ∧ entry_l (𝒩 := structure_l hℳ B hBase) X e one f p
    · obtain ⟨p, hp, hEntry⟩ := h
      refine ⟨p, ⟨hp, (hφ f p).mpr (Or.inl hEntry)⟩, ?_⟩
      rintro r ⟨_, hr⟩
      rcases (hφ f r).mp hr with hr | ⟨hNone, _⟩
      · obtain ⟨_, _, hfMap⟩ := (hS f).mp hf
        exact entry_unique_l (X := X) (e := e) (one := one) hfMap hr hEntry
      · exact False.elim (hNone p hp hEntry)
    · have hNone : ∀ p : type_l hℳ B, mem_l hℳ p.val Q.val →
          ¬entry_l (𝒩 := structure_l hℳ B hBase) X e one f p := fun p hp hEntry => h ⟨p, hp, hEntry⟩
      refine ⟨d, ⟨hd, (hφ f d).mpr (Or.inr ⟨hNone, rfl⟩)⟩, ?_⟩
      rintro r ⟨hr, hφr⟩
      rcases (hφ f r).mp hφr with hEntry | ⟨_, hrd⟩
      · exact False.elim (hNone r hr hEntry)
      · exact hrd
  obtain ⟨R, hR, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l (hBase := hBase)
    (φ := φ) (delta_l x q z o a (.fvar .here) (.fvar (.there .here))) η S Q hTotal
  exact ⟨R, hR, fun f p hEntry hf hp => (hRead f p).mpr ⟨hf, hp, (hφ f p).mpr (Or.inl hEntry)⟩⟩

#print axioms delta_l
#print axioms decoder_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassPairEnumeration
