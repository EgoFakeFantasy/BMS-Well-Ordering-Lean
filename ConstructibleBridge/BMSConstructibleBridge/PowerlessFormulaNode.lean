import BMSConstructibleBridge.PowerlessPairingBounds

/-!
# 内部语法节点码及严格下降界

节点码取三角配对值的集合后继。这里验证节点代数，不宣称已构造
完整合法性或 Sat；旧二阶模块的平方配数不能未经对应直接用于此编码。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaNode

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural PowerlessTriangular

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def node_l (ω e T t p n : carrier_l ℳ) : Prop :=
  member_l ℳ t ω ∧ member_l ℳ p ω ∧ ∃ c, PowerlessPairingCode.code_l ω e T t p c ∧ successor_l c n

def node_m {Γ Δ : SortContext ℒ} (ω e T t p n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.member_m t ω) (.conj (SecondOrderObjectSyntax.member_m p ω)
    (.existsE .set (.conj (PowerlessPairingCode.code_m (w ω) (w e) (w T) (w t) (w p) (.bvar .here))
      (PowerlessNaturalStep.successor_m (.bvar .here) (w n)))))

theorem node_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t p n : Term ℒ Γ Δ .set) :
    (node_m ω e T t p n).satisfies η ↔ node_l (ω.eval η) (e.eval η) (T.eval η) (t.eval η) (p.eval η) (n.eval η) := by
  simp only [node_m, node_l, Formula.satisfies, PowerlessPairingCode.code_formula_l,
    PowerlessNaturalStep.successor_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t p : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (ht : member_l ℳ t ω) (hp : member_l ℳ p ω) : ∃ n, member_l ℳ n ω ∧ node_l ω e T t p n := by
  obtain ⟨c, hc, h₀⟩ := PowerlessPairingCode.exists_l hℳ hω he hT ht hp
  obtain ⟨n, hn⟩ := successor_exists_l hℳ c
  exact ⟨n, successor_mem_l hℳ hω hc hn, ht, hp, c, h₀, hn⟩

theorem natural_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t p n : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (h : node_l ω e T t p n) : member_l ℳ n ω := by
  obtain ⟨_, _, c, hc, hn⟩ := h
  exact successor_mem_l hℳ hω (PowerlessPairingCode.output_l hℳ hω he hT hc) hn

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t p n m : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (hn : node_l ω e T t p n) (hm : node_l ω e T t p m) : n = m := by
  obtain ⟨_, _, c, hc, hn⟩ := hn
  obtain ⟨_, _, d, hd, hm⟩ := hm
  have h := PowerlessPairingCode.unique_l hℳ hω he hT hc hd
  subst d
  exact successor_unique_l hℳ hn hm

theorem injective_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t p s q n : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (ht : node_l ω e T t p n) (hs : node_l ω e T s q n) : t = s ∧ p = q := by
  obtain ⟨ht, _, c, hc, hn⟩ := ht
  obtain ⟨hs, _, d, hd, hm⟩ := hs
  have h := successor_injective_l hℳ hn hm
  subst d
  exact PowerlessPairingCode.injective_l hℳ hω he hT ht hs hc hd

theorem bounds_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t p n : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (h : node_l ω e T t p n) : member_l ℳ t n ∧ member_l ℳ p n := by
  obtain ⟨ht, hp, c, hc, hn⟩ := h
  obtain ⟨h₀, h₁⟩ := PowerlessPairingBounds.coordinates_l hℳ hω he hT ht hp hc
  exact ⟨(hn t).mpr h₀, (hn p).mpr h₁⟩

theorem children_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t p n a b : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω)
    (hp : PowerlessPairingCode.code_l ω e T a b p) (hn : node_l ω e T t p n) :
    member_l ℳ a n ∧ member_l ℳ b n := by
  have h₀ := (bounds_l hℳ hω he hT hn).2
  have h₁ := PowerlessNaturalOrder.member_transitive_l hℳ hω n (natural_l hℳ hω he hT hn)
  obtain ⟨h₂, h₃⟩ := PowerlessPairingBounds.coordinates_l hℳ hω he hT ha hb hp
  exact ⟨h₂.elim (fun h => h₁ p a h₀ h) (fun h => h.symm ▸ h₀),
    h₃.elim (fun h => h₁ p b h₀ h) (fun h => h.symm ▸ h₀)⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaNode
