import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessValueBounded

/-! # 类内单射的带默认值逆枚举

给定 X 到 ω 的实际集合单射和 X 中一个默认对象，把未使用的编号填默认值。
构造只用有界关系图存在；分支判断和见证均在 Prop，不抽取 Type 选择函数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInjectionEnumeration

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def formula_m {Γ Δ : SortContext ℒ} (R X d i y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (PowerlessValueBounded.formula_m R y i) <| .conj
    (membershipLevyBound.boundedForall X <| .neg
      (PowerlessValueBounded.formula_m (up R) (.bvar .here) (up i))) (.equal y d)

theorem delta_l {Γ Δ : SortContext ℒ} (R X d i y : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (formula_m R X d i y) :=
  .disj (PowerlessValueBounded.delta_l _ _ _)
    (.conj (.bounded_forall X (.neg (PowerlessValueBounded.delta_l _ _ _))) (.equal _ _))

def holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (R X d i y : carrier_l 𝒩) : Prop :=
  value_l (ℳ := 𝒩) R y i ∨ ((∀ g, member_l 𝒩 g X → ¬value_l (ℳ := 𝒩) R g i) ∧ y = d)

theorem formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (R X d i y : Term ℒ Γ Δ .set) : (formula_m R X d i y).satisfies η ↔
      holds_l (R.eval η) (X.eval η) (d.eval η) (i.eval η) (y.eval η) := by
  simp only [formula_m, holds_l, Formula.LevyBound.boundedForall, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessValueBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem exists_l {ω X R d : type_l hℳ B}
    (hR : map_l (ℳ := structure_l hℳ B hBase) R X ω)
    (hInjective : ∀ x y i : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) R x i →
      value_l (ℳ := structure_l hℳ B hBase) R y i → x = y)
    (hd : mem_l hℳ d.val X.val) : ∃ F : type_l hℳ B,
      map_l (ℳ := structure_l hℳ B hBase) F ω X ∧
        (∀ y : type_l hℳ B, mem_l hℳ y.val X.val → ∃ i : type_l hℳ B,
          mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) F i y) ∧
        ∀ i y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) F i y ↔
          mem_l hℳ i.val ω.val ∧ mem_l hℳ y.val X.val ∧
            holds_l (𝒩 := structure_l hℳ B hBase) R X d i y := by
  classical
  let η : Env (structure_l hℳ B hBase) [] [.set, .set, .set] :=
    (((Env.empty).pushFree d).pushFree X).pushFree R
  let r : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let x : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let a : Term ℒ [] [.set, .set, .set, .set, .set] .set := .fvar (.there (.there (.there (.there .here))))
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] := formula_m r x a (.fvar .here) (.fvar (.there .here))
  have hφ (i y : type_l hℳ B) : φ.satisfies ((η.pushFree y).pushFree i) ↔
      holds_l (𝒩 := structure_l hℳ B hBase) R X d i y :=
    formula_l ((η.pushFree y).pushFree i) r x a (.fvar .here) (.fvar (.there .here))
  have hTotal (i : type_l hℳ B) (_ : mem_l hℳ i.val ω.val) : ∃! y : type_l hℳ B,
      mem_l hℳ y.val X.val ∧ φ.satisfies ((η.pushFree y).pushFree i) := by
    by_cases h : ∃ y : type_l hℳ B, mem_l hℳ y.val X.val ∧ value_l (ℳ := structure_l hℳ B hBase) R y i
    · obtain ⟨y, hy, hRy⟩ := h
      refine ⟨y, ⟨hy, (hφ i y).mpr (Or.inl hRy)⟩, ?_⟩
      rintro z ⟨_, hz⟩
      rcases (hφ i z).mp hz with hRz | ⟨hNone, _⟩
      · exact hInjective z y i hRz hRy
      · exact False.elim (hNone y hy hRy)
    · have hNone : ∀ y : type_l hℳ B, mem_l hℳ y.val X.val →
          ¬value_l (ℳ := structure_l hℳ B hBase) R y i := fun y hy hRy => h ⟨y, hy, hRy⟩
      refine ⟨d, ⟨hd, (hφ i d).mpr (Or.inr ⟨hNone, rfl⟩)⟩, ?_⟩
      rintro z ⟨hz, hφz⟩
      rcases (hφ i z).mp hφz with hRz | ⟨_, hzd⟩
      · exact False.elim (hNone z hz hRz)
      · exact hzd
  obtain ⟨F, hF, hRead⟩ := PowerlessRelativeClassFunctionRelation.exists_l (hBase := hBase)
    (φ := φ) (delta_l r x a (.fvar .here) (.fvar (.there .here))) η ω X hTotal
  have hValue (i y : type_l hℳ B) : value_l (ℳ := structure_l hℳ B hBase) F i y ↔
      mem_l hℳ i.val ω.val ∧ mem_l hℳ y.val X.val ∧ holds_l (𝒩 := structure_l hℳ B hBase) R X d i y :=
    (hRead i y).trans (and_congr Iff.rfl (and_congr Iff.rfl (hφ i y)))
  refine ⟨F, hF, ?_, hValue⟩
  intro y hy
  obtain ⟨i, ⟨hi, hRi⟩, _⟩ := hR.2 y hy
  exact ⟨i, hi, (hValue i y).mpr ⟨hi, hy, Or.inl hRi⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassInjectionEnumeration
