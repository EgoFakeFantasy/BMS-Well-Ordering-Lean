import BMSConstructibleBridge.PowerlessArithmeticRelation

/-!
# 序对容器替代内部 ω×ω 的算术关系图

`PowerlessArithmeticRelation.exists_l` 用 `PowerlessProduct.exists_l hℳ ω ω` 只做了两件事：
给分离提供母集，以及将 Kuratowski 序对的成员送回该母集。两者都由一条覆盖假设代替。
本模块按此形状给出容器版出口：不消费 Collection，也不内建笛卡尔积构造。
它不声称这样的序对容器在无幂集核心内总存在，也不替代原 `exists_l`。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairCoverGraph

open Logic FirstOrder ThirdOrderSemantics PowerlessArithmeticTerms

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessArithmetic.structure_l
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {ω e : carrier_l ℳ} {he : PowerlessNatural.zero_l e} {h₀ : member_l ℳ e ω}
  {F : PowerlessArithmetic.operations_l ω e}

local notation "𝒩" => PowerlessArithmetic.structure_l he h₀ F

/-- 给定容纳全部 ω 上 Kuratowski 序对的集合，原算术关系的图只需分离。 -/
theorem graph_of_cover_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (hω : omega_l ω)
    (X : PowerlessArithmetic.set_l ω) (D : carrier_l ℳ)
    (hD : ∀ a b p, member_l ℳ a ω → member_l ℳ b ω → ordered_l a b p → member_l ℳ p D) :
    ∃ G, PowerlessArithmeticRelation.graph_l (he := he) (h₀ := h₀) (F := F) X G := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases ω (Fin.cases e (fun _ => X.val)), free := fun _ => ω }
  let w : Term ℒ [.set, .set] [.set, .set, .set, .set] .set := .fvar (.there .here)
  let z : Term ℒ [.set, .set] [.set, .set, .set, .set] .set := .fvar (.there (.there .here))
  let R : Term ℒ [.set, .set] [.set, .set, .set, .set] .set := .fvar (.there (.there (.there .here)))
  let φ : Formula ℒ [] [.set, .set, .set, .set] := .existsE .set (.existsE .set
    (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) w)
      (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) w)
        (.conj (SecondOrderObjectSyntax.ordered_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
          (PowerlessArithmeticRelation.edge_m w z R (.bvar (.there .here)) (.bvar .here))))))
  have h (p : carrier_l ℳ) : φ.satisfies ((PowerlessComprehension.env_l η).pushFree p) ↔
      ∃ a b : PowerlessArithmetic.num_l ω, ordered_l a.val b.val p ∧
        SecondOrderPairing.relation_l (ℳ := 𝒩) X a b := by
    simp only [φ, Formula.satisfies, ordered_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    change (∃ a b : carrier_l ℳ, member_l ℳ a ω ∧ member_l ℳ b ω ∧ ordered_l a b p ∧
      (PowerlessArithmeticRelation.edge_m w z R (.bvar (.there .here)) (.bvar .here)).satisfies
        ((((PowerlessComprehension.env_l η).pushFree p).pushBound a).pushBound b)) ↔ _
    constructor
    · rintro ⟨a, b, ha, hb, hp, h₁⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hp,
        (PowerlessArithmeticRelation.edge_formula_l hℳ hω _ w z R _ _ X ⟨a, ha⟩ ⟨b, hb⟩
          rfl rfl rfl rfl rfl).mp h₁⟩
    · rintro ⟨a, b, hp, h₁⟩
      exact ⟨a.val, b.val, a.property, b.property, hp,
        (PowerlessArithmeticRelation.edge_formula_l hℳ hω _ w z R _ _ X a b rfl rfl rfl rfl rfl).mpr
          h₁⟩
  obtain ⟨G, hG⟩ := PowerlessComprehension.separation_l hℳ φ η D
  refine ⟨G, fun p => (hG p).trans ?_⟩
  rw [h p]
  exact ⟨And.right, fun ⟨a, b, hp, h₁⟩ =>
    ⟨hD a.val b.val p a.property b.property hp, a, b, hp, h₁⟩⟩

#print axioms graph_of_cover_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessPairCoverGraph
