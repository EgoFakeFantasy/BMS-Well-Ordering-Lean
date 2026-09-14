import BMSConstructibleBridge.PowerlessPairingAbsolute
import BMSConstructibleBridge.PowerlessFormulaConstructor

/-!
# 原语法节点与构造子公式的传递子域绝对性

自然数 guard 已在原正文中，正向直接读取，反向由原配数输出界取回见证。
不改写原编码公式，不在公开出口重复增加正文保证的自然数假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaCodeAbsolute

open Logic FirstOrder ThirdOrderSemantics PowerlessMemberStructure

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
  {B : carrier_l ℳ} {hB : ∃ x, member_l ℳ x B} (hBT : PowerlessNaturalOrder.transitive_l B)
  {ω e T : type_l B} (hω : omega_l ω.val) (he : PowerlessNatural.zero_l e.val)
  (hT : PowerlessTriangular.triangular_l ω.val e.val T.val)
  (hI : ∀ x, member_l ℳ x ω.val → ∀ F,
    PowerlessAddition.iteration_l ω.val e.val x F → member_l ℳ F B)

include hℳ hBT hω he hT hI

theorem node_l {t p n : type_l B} :
    PowerlessFormulaNode.node_l (ℳ := structure_l B hB) ω e T t p n ↔
      PowerlessFormulaNode.node_l ω.val e.val T.val t.val p.val n.val := by
  constructor
  · rintro ⟨ht, hp, c, hc, hn⟩
    exact ⟨ht, hp, c.val, (PowerlessPairingAbsolute.code_l hℳ hBT hω he hT ht hI).mp hc,
      (PowerlessSourceNaturalAbsolute.successor_l hBT).mp hn⟩
  · rintro ⟨ht, hp, c, hc, hn⟩
    have hcB := hBT ω.val c ω.property (PowerlessPairingCode.output_l hℳ hω he hT hc)
    exact ⟨ht, hp, ⟨c, hcB⟩, (PowerlessPairingAbsolute.code_l hℳ hBT hω he hT ht hI).mpr hc,
      (PowerlessSourceNaturalAbsolute.successor_l hBT).mpr hn⟩

theorem constructor_l {t a b n : type_l B} :
    PowerlessFormulaConstructor.constructor_l (ℳ := structure_l B hB) ω e T t a b n ↔
      PowerlessFormulaConstructor.constructor_l ω.val e.val T.val t.val a.val b.val n.val := by
  constructor
  · rintro ⟨ha, hb, p, hp, hn⟩
    exact ⟨ha, hb, p.val, (PowerlessPairingAbsolute.code_l hℳ hBT hω he hT ha hI).mp hp,
      (node_l hℳ hBT hω he hT hI).mp hn⟩
  · rintro ⟨ha, hb, p, hp, hn⟩
    have hpB := hBT ω.val p ω.property (PowerlessPairingCode.output_l hℳ hω he hT hp)
    exact ⟨ha, hb, ⟨p, hpB⟩, (PowerlessPairingAbsolute.code_l hℳ hBT hω he hT ha hI).mpr hp,
      (node_l hℳ hBT hω he hT hI).mpr hn⟩

theorem node_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (w z U t p n : Term ℒ Γ Δ .set) (hw : w.eval η = ω) (hz : z.eval η = e) (hU : U.eval η = T) :
    Formula.satisfies η (PowerlessFormulaNode.node_m w z U t p n) ↔
      PowerlessFormulaNode.node_l ω.val e.val T.val (t.eval η).val (p.eval η).val (n.eval η).val := by
  rw [PowerlessFormulaNode.node_formula_l, hw, hz, hU]
  exact node_l hℳ hBT hω he hT hI

theorem constructor_source_l {Γ Δ : SortContext ℒ} (η : Env (structure_l B hB) Γ Δ)
    (w z U t a b n : Term ℒ Γ Δ .set) (hw : w.eval η = ω) (hz : z.eval η = e) (hU : U.eval η = T) :
    Formula.satisfies η (PowerlessFormulaConstructor.constructor_m w z U t a b n) ↔
      PowerlessFormulaConstructor.constructor_l ω.val e.val T.val
        (t.eval η).val (a.eval η).val (b.eval η).val (n.eval η).val := by
  rw [PowerlessFormulaConstructor.constructor_formula_l, hw, hz, hU]
  exact constructor_l hℳ hBT hω he hT hI

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaCodeAbsolute
