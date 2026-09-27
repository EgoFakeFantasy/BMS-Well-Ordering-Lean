import BMSConstructibleBridge.PowerlessArithmeticComprehension
import BMSConstructibleBridge.PowerlessProduct
import BMSConstructibleBridge.SecondOrderFunctions

/-!
# 原数码关系实数的实际 Kuratowski 图

原边查询继续使用原算术配对公式，而不是附加 pair 符号或另一种三角数编码。
在内部 ω×ω 上分离，得到同一模型中的有序对集合，逐坐标保持原边和全函数性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticRelation

open Logic FirstOrder ThirdOrderSemantics PowerlessArithmeticTerms

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

def edge_m {Γ Δ : SortContext ℒ} (ω e X a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let τ : assignment_m [.num, .num, .set] Γ Δ := fun v => match v with
    | .here => a
    | .there .here => b
    | .there (.there .here) => X
  PowerlessArithmeticTranslation.formula_m ω e
    (fun {s} (v : Variable ([] : SortContext SecondOrderSyntax.signature_m) s) => nomatch v) τ
    (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

theorem edge_formula_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (w z R s t : Term ℒ Γ Δ .set)
    (X : PowerlessArithmetic.set_l ω) (a b : PowerlessArithmetic.num_l ω)
    (hw : w.eval η = ω) (hz : z.eval η = e) (hR : R.eval η = X.val)
    (hs : s.eval η = a.val) (ht : t.eval η = b.val) :
    (edge_m w z R s t).satisfies η ↔ SecondOrderPairing.relation_l (ℳ := 𝒩) X a b := by
  let ξ : Env 𝒩 [] [.num, .num, .set] :=
    (((Env.empty (M := 𝒩)).pushFree (σ := SecondOrderSyntax.signature_m) (sort := .set) X).pushFree
      (σ := SecondOrderSyntax.signature_m) (sort := .num) b).pushFree
        (σ := SecondOrderSyntax.signature_m) (sort := .num) a
  unfold edge_m
  refine (PowerlessArithmeticTranslation.formula_l hℳ hω ξ η w z _ _ hw hz ?_ ?_ _).trans
    (SecondOrderPairing.edge_l ξ _ _ _)
  · intro q v
    nomatch v
  · intro q v
    match q, v with
    | .num, .here => exact hs
    | .num, .there .here => exact ht
    | .set, .there (.there .here) => exact hR

/-- 每一个集合成员都必须是原关系的实际数坐标对，没有额外垃圾成员。 -/
def graph_l (X : PowerlessArithmetic.set_l ω) (G : carrier_l ℳ) : Prop :=
  ∀ p, member_l ℳ p G ↔ ∃ a b : PowerlessArithmetic.num_l ω,
    ordered_l a.val b.val p ∧ SecondOrderPairing.relation_l (ℳ := 𝒩) X a b

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (X : PowerlessArithmetic.set_l ω) : ∃ G, graph_l (he := he) (h₀ := h₀) (F := F) X G := by
  obtain ⟨P, hP⟩ := PowerlessProduct.exists_l hℳ ω ω
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases ω (Fin.cases e (fun _ => X.val)), free := fun _ => ω }
  let w : Term ℒ [.set, .set] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let z : Term ℒ [.set, .set] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let R : Term ℒ [.set, .set] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let φ : Formula ℒ [] [.set, .set, .set, .set] := .existsE .set (.existsE .set
    (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) w)
      (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) w)
        (.conj (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
          (edge_m w z R (.bvar (.there .here)) (.bvar .here))))))
  have h (p : carrier_l ℳ) : φ.satisfies ((PowerlessComprehension.env_l η).pushFree p) ↔
      ∃ a b : PowerlessArithmetic.num_l ω, ordered_l a.val b.val p ∧
        SecondOrderPairing.relation_l (ℳ := 𝒩) X a b := by
    simp only [φ, Formula.satisfies, ordered_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    change (∃ a b : carrier_l ℳ, member_l ℳ a ω ∧ member_l ℳ b ω ∧ ordered_l a b p ∧
      (edge_m w z R (.bvar (.there .here)) (.bvar .here)).satisfies
        ((((PowerlessComprehension.env_l η).pushFree p).pushBound a).pushBound b)) ↔ _
    constructor
    · rintro ⟨a, b, ha, hb, hp, h₁⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hp,
        (edge_formula_l hℳ hω _ w z R _ _ X ⟨a, ha⟩ ⟨b, hb⟩ rfl rfl rfl rfl rfl).mp h₁⟩
    · rintro ⟨a, b, hp, h₁⟩
      exact ⟨a.val, b.val, a.property, b.property, hp,
        (edge_formula_l hℳ hω _ w z R _ _ X a b rfl rfl rfl rfl rfl).mpr h₁⟩
  obtain ⟨G, hG⟩ := PowerlessComprehension.separation_l hℳ φ η P
  refine ⟨G, fun p => (hG p).trans ?_⟩
  rw [h p]
  exact ⟨And.right, fun ⟨a, b, hp, h₁⟩ =>
    ⟨(hP p).mpr ⟨a.val, a.property, b.val, b.property, hp⟩, a, b, hp, h₁⟩⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {X : PowerlessArithmetic.set_l ω} {G H : carrier_l ℳ}
    (hG : graph_l (he := he) (h₀ := h₀) (F := F) X G) (hH : graph_l (he := he) (h₀ := h₀) (F := F) X H) : G = H :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members G H (fun p => (hG p).trans (hH p).symm)

theorem value_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {X : PowerlessArithmetic.set_l ω} {G : carrier_l ℳ}
    (hG : graph_l (he := he) (h₀ := h₀) (F := F) X G) (a b : PowerlessArithmetic.num_l ω) :
    ThirdOrderSemantics.value_l G a.val b.val ↔ SecondOrderPairing.relation_l (ℳ := 𝒩) X a b := by
  constructor
  · rintro ⟨p, hp, h₁⟩
    obtain ⟨c, d, h₂, h₃⟩ := (hG p).mp hp
    obtain ⟨h₄, h₅⟩ := (PowerlessBasic.ordered_eq_l hℳ h₁ h₂).mp rfl
    have h₄ : a = c := Subtype.ext h₄
    have h₅ : b = d := Subtype.ext h₅
    exact h₄.symm ▸ h₅.symm ▸ h₃
  · intro h
    obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ a.val b.val
    exact ⟨p, (hG p).mpr ⟨a, b, hp, h⟩, hp⟩

/-- 两侧全函数性质等价，坐标仍是同一个内部自然数。 -/
theorem function_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {X : PowerlessArithmetic.set_l ω} {G : carrier_l ℳ}
    (hG : graph_l (he := he) (h₀ := h₀) (F := F) X G) :
    SecondOrderFunctions.function_l (ℳ := 𝒩) X ↔ map_l G ω ω := by
  constructor
  · intro h
    constructor
    · intro p hp
      obtain ⟨a, b, h₁, _⟩ := (hG p).mp hp
      exact ⟨a.val, b.val, a.property, b.property, h₁⟩
    · intro a ha
      obtain ⟨b, hb, h₁⟩ := h ⟨a, ha⟩
      refine ⟨b.val, ⟨b.property, (value_l hℳ hG _ b).mpr hb⟩, ?_⟩
      intro c hc
      exact congrArg Subtype.val (h₁ ⟨c, hc.1⟩ ((value_l hℳ hG _ _).mp hc.2))
  · intro h a
    obtain ⟨b, hb, h₁⟩ := h.2 a.val a.property
    refine ⟨⟨b, hb.1⟩, (value_l hℳ hG a _).mp hb.2, ?_⟩
    intro c hc
    exact Subtype.ext (h₁ c.val ⟨c.property, (value_l hℳ hG a c).mpr hc⟩)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmeticRelation
