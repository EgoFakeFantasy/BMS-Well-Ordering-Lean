import BMSConstructibleBridge.SecondOrderInitialAgreement
import BMSConstructibleBridge.SecondOrderSetIteration

/-!
# 只依赖较小编号的求值稳定性

实际公式归纳证明：第 n 阶段起，前 n 行不再变化。局部性明确只允许读取
较小编号的旧行；结论覆盖所有模型编号和阶段，不使用外部自然数递归。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedStability

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderInitialAgreement

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def local_l (P : set_l ℳ → set_l ℳ → Prop) : Prop :=
  ∀ X Y U V, P X U → P Y V → ∀ n, agree_l X Y n →
    ∀ a, relation_l U n a ↔ relation_l V n a

private def succ {Γ Δ : SortContext signature_m} (s : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons s .nil)

def formula_m : Formula signature_m [] [.num, .set] :=
  .forallE .num <| .forallE .num <| .forallE .set <| .forallE .set <|
    .imp (PrimitiveFormulas.lt_m (.fvar .here) (succ (.bvar (.there (.there (.there .here))))))
      (.imp (PrimitiveFormulas.lt_m (.fvar .here) (succ (.bvar (.there (.there .here)))))
        (.imp (SecondOrderSections.formula_m (.fvar (.there .here)) (.bvar (.there .here))
          (.bvar (.there (.there (.there .here)))))
          (.imp (SecondOrderSections.formula_m (.fvar (.there .here)) (.bvar .here)
            (.bvar (.there (.there .here))))
            (SecondOrderInitialAgreement.formula_m (.bvar (.there .here)) (.bvar .here) (.fvar .here)))))

theorem pure_m : language_m formula_m = true := rfl

theorem stages_l (hℳ : Theory.Models ℳ theory_m) (P : set_l ℳ → set_l ℳ → Prop)
    (G A : set_l ℳ) (hG : SecondOrderSetIteration.spec_l P G A) (hP : local_l P)
    (n : num_l ℳ) :
    letI := semiring_l hℳ
    letI := order_l hℳ
    ∀ r s X Y, n ≤ r → n ≤ s → SecondOrderSections.spec_l G r X →
      SecondOrderSections.spec_l G s Y → agree_l X Y n := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  have h₀ (i : num_l ℳ) : i < succ_l i := (SecondOrderNaturalGraph.lt_succ_l hℳ _ _).mpr le_rfl
  apply induct_l hℳ formula_m pure_m ((Env.empty (M := ℳ)).pushFree G)
    (fun n => ∀ r s X Y, n ≤ r → n ≤ s → SecondOrderSections.spec_l G r X →
      SecondOrderSections.spec_l G s Y → agree_l X Y n) ?_ ?_ ?_ n
  · intro n
    simp only [formula_m, Formula.satisfies, SecondOrderSections.formula_l,
      SecondOrderInitialAgreement.formula_l, SecondOrderOrder.formula_l]
    change (∀ r s X Y, n < succ_l r → n < succ_l s → SecondOrderSections.spec_l G r X →
      SecondOrderSections.spec_l G s Y → agree_l X Y n) ↔ _
    simp only [SecondOrderNaturalGraph.lt_succ_l hℳ]
  · intro r s X Y _ _ _ _ i hi
    exact False.elim ((not_lt_of_ge (zero_le_l hℳ i)) hi)
  · intro n hn r s X Y hr hs hX hY
    have h₁ (r : num_l ℳ) (h : succ_l n ≤ r) : r ≠ zero_l ℳ := by
      intro h₁
      exact (not_le_of_gt (SecondOrderOrder.zero_succ_l hℳ n)) (h₁ ▸ h)
    obtain ⟨r, rfl⟩ := (predecessor_l hℳ r).resolve_left (h₁ r hr)
    obtain ⟨s, rfl⟩ := (predecessor_l hℳ s).resolve_left (h₁ s hs)
    have h₂ (r : num_l ℳ) (h : succ_l n ≤ succ_l r) : n ≤ r := by
      change (n = r ∨ SecondOrderOrder.lt_l n r)
      change (succ_l n = succ_l r ∨ SecondOrderOrder.lt_l (succ_l n) (succ_l r)) at h
      exact h.imp (fun h => SecondOrderModel.injective_l hℳ h) ((SecondOrderOrder.succ_iff_l hℳ n r).mp)
    obtain ⟨U, hU⟩ := SecondOrderSections.exists_l hℳ G r
    obtain ⟨V, hV⟩ := SecondOrderSections.exists_l hℳ G s
    apply (SecondOrderInitialAgreement.successor_l hℳ X Y n).mpr
    refine ⟨hn (succ_l r) (succ_l s) X Y ((le_of_lt (h₀ n)).trans hr)
      ((le_of_lt (h₀ n)).trans hs) hX hY, ?_⟩
    exact hP U V X Y (hG.2 r U X hU hX) (hG.2 s V Y hV hY) n
      (hn r s U V (h₂ r hr) (h₂ s hs) hU hV)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRankedStability
