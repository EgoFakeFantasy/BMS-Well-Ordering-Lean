import BMSConstructibleBridge.PowerlessRelativeClassSequenceComposition
import BMSConstructibleBridge.PowerlessRelativeClassFiniteNumericEnumeration

/-! # 可枚举类参数的全部内部有限序列仍可类内枚举

先枚举数值序列，再逐图复合给定 ω 满射。反向覆盖使用最小编号提升，
不把环境可数性当作类内枚举，也不增加可数选择假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteSequenceEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (ω X G F S i f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists S <| .conj
    (PowerlessValueBounded.formula_m (up F) (up i) (.bvar .here))
    (PowerlessFiniteSequenceComposition.formula_m (up ω) (up X) (up G) (.bvar .here) (up f))

theorem delta_l {Γ Δ : SortContext ℒ} (ω X G F S i f : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m ω X G F S i f) :=
  .bounded_exists S (.conj (PowerlessValueBounded.delta_l _ _ _)
    (PowerlessFiniteSequenceComposition.delta_l _ _ _ _ _))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω X G F S i f : carrier_l 𝒩) : Prop :=
  ∃ g, member_l 𝒩 g S ∧ value_l (ℳ := 𝒩) F i g ∧
    PowerlessFiniteSequenceComposition.holds_l (𝒩 := 𝒩) ω X G g f

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω X G F S i f : Term ℒ Γ Δ .set) : (formula_m ω X G F S i f).satisfies η ↔
      holds_l (ω.eval η) (X.eval η) (G.eval η) (F.eval η) (S.eval η) (i.eval η) (f.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    PowerlessFiniteSequenceComposition.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {ω X G : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hG : map_l (ℳ := structure_l hℳ B hBase) G ω X)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val X.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i y) :
    ∃ S : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω X S ∧
      ∃ T : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) T ω S ∧
        ∀ f : type_l hℳ B, mem_l hℳ f.val S.val → ∃ i : type_l hℳ B,
          mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) T i f := by
  obtain ⟨N, hN, F, hF, hFOnto⟩ := PowerlessRelativeClassFiniteNumericEnumeration.exists_l (hBase := hBase) hω
  obtain ⟨S, hS⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_l (hBase := hBase) (X := X) hω
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set, .set, .set] :=
    (((((Env.empty).pushFree N).pushFree F).pushFree G).pushFree X).pushFree ω
  let w : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let x : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let g : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let f : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there .here)))))
  let s : Term ℒ [] [.set, .set, .set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there (.there (.there .here))))))
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set] :=
    formula_m w x g f s (.fvar .here) (.fvar (.there .here))
  have hφ (i y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree i) ↔
      holds_l (𝒩 := structure_l hℳ B hBase) ω X G F N i y :=
    formula_l ((η.pushFree y).pushFree i) w x g f s (.fvar .here) (.fvar (.there .here))
  have hTotal (i : type_l hℳ B) (hi : mem_l hℳ i.val ω.val) : ∃! y : type_l hℳ B,
      mem_l hℳ y.val S.val ∧ φ.satisfies ((η.pushFree y).pushFree i) := by
    obtain ⟨a, ⟨ha, hia⟩, _⟩ := hF.2 i hi
    obtain ⟨y, hy⟩ := PowerlessRelativeClassSequenceComposition.exists_l hG ((hN a).mp ha)
    have hyS : mem_l hℳ y.val S.val := by
      obtain ⟨n, hn, _, hyMap, _⟩ := hy
      exact (hS y).mpr ⟨n, hn, hyMap⟩
    refine ⟨y, ⟨hyS, (hφ i y).mpr ⟨a, ha, hia, hy⟩⟩, ?_⟩
    rintro z ⟨_, hz⟩
    obtain ⟨a', _, hia', hzComp⟩ := (hφ i z).mp hz
    have haa := PowerlessRelativeClassFunctionComposition.value_unique_l hF hia' hia
    subst a'
    exact PowerlessRelativeClassSequenceComposition.unique_l hzComp hy
  obtain ⟨T, hT, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l (hBase := hBase)
    (φ := φ) (delta_l w x g f s (.fvar .here) (.fvar (.there .here))) η ω S hTotal
  refine ⟨S, hS, T, hT, ?_⟩
  intro y hy
  obtain ⟨a, haComp⟩ := PowerlessRelativeClassSequenceComposition.lift_l hω hG hOnto ((hS y).mp hy)
  have haN : mem_l hℳ a.val N.val := by
    obtain ⟨n, hn, haMap, _, _⟩ := haComp
    exact (hN a).mpr ⟨n, hn, haMap⟩
  obtain ⟨i, hi, hia⟩ := hFOnto a haN
  exact ⟨i, hi, (hRead i y).mpr ⟨hi, hy, (hφ i y).mpr ⟨a, haN, hia, haComp⟩⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFiniteSequenceEnumeration
