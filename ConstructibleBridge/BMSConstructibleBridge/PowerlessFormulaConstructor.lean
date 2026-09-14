import BMSConstructibleBridge.PowerlessFormulaNode

/-!
# 二元载荷的内部公式构造子

标签与两个内部自然数载荷由实际三角配数编码。量词载荷取变量索引
及子公式码；本模块不把局部构造子识别等同于完整语法合法性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaConstructor

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural PowerlessTriangular

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def constructor_l (ω e T t a b n : carrier_l ℳ) : Prop :=
  member_l ℳ a ω ∧ member_l ℳ b ω ∧ ∃ p,
    PowerlessPairingCode.code_l ω e T a b p ∧ PowerlessFormulaNode.node_l ω e T t p n

def constructor_m {Γ Δ : SortContext ℒ} (ω e T t a b n : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.member_m a ω) (.conj (SecondOrderObjectSyntax.member_m b ω)
    (.existsE .set (.conj (PowerlessPairingCode.code_m (w ω) (w e) (w T) (w a) (w b) (.bvar .here))
      (PowerlessFormulaNode.node_m (w ω) (w e) (w T) (w t) (.bvar .here) (w n)))))

theorem constructor_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e T t a b n : Term ℒ Γ Δ .set) :
    (constructor_m ω e T t a b n).satisfies η ↔
      constructor_l (ω.eval η) (e.eval η) (T.eval η) (t.eval η) (a.eval η) (b.eval η) (n.eval η) := by
  simp only [constructor_m, constructor_l, Formula.satisfies, PowerlessPairingCode.code_formula_l,
    PowerlessFormulaNode.node_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t a b : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (ht : member_l ℳ t ω) (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ n, member_l ℳ n ω ∧ constructor_l ω e T t a b n := by
  obtain ⟨p, hp, h₀⟩ := PowerlessPairingCode.exists_l hℳ hω he hT ha hb
  obtain ⟨n, hn, h₁⟩ := PowerlessFormulaNode.exists_l hℳ hω he hT ht hp
  exact ⟨n, hn, ha, hb, p, h₀, h₁⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t a b n m : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (hn : constructor_l ω e T t a b n) (hm : constructor_l ω e T t a b m) : n = m := by
  obtain ⟨_, _, p, hp, hn⟩ := hn
  obtain ⟨_, _, q, hq, hm⟩ := hm
  have h := PowerlessPairingCode.unique_l hℳ hω he hT hp hq
  subst q
  exact PowerlessFormulaNode.unique_l hℳ hω he hT hn hm

theorem injective_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t a b s c d n : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (hn : constructor_l ω e T t a b n) (hm : constructor_l ω e T s c d n) : t = s ∧ a = c ∧ b = d := by
  obtain ⟨ha, _, p, hp, hn⟩ := hn
  obtain ⟨hc, _, q, hq, hm⟩ := hm
  obtain ⟨h, h₀⟩ := PowerlessFormulaNode.injective_l hℳ hω he hT hn hm
  subst q
  exact ⟨h, PowerlessPairingCode.injective_l hℳ hω he hT ha hc hp hq⟩

theorem bounds_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t a b n : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (h : constructor_l ω e T t a b n) : member_l ℳ a n ∧ member_l ℳ b n := by
  obtain ⟨ha, hb, _, hp, hn⟩ := h
  exact PowerlessFormulaNode.children_l hℳ hω he hT ha hb hp hn

theorem natural_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t a b n : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (h : constructor_l ω e T t a b n) : member_l ℳ n ω := by
  obtain ⟨_, _, _, _, hn⟩ := h
  exact PowerlessFormulaNode.natural_l hℳ hω he hT hn

theorem fiber_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e T t a b n : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hT : triangular_l ω e T)
    (hn : constructor_l ω e T t a b n) (s : carrier_l ℳ) (P : carrier_l ℳ → carrier_l ℳ → Prop) :
    (∃ i j, constructor_l ω e T s i j n ∧ P i j) ↔ s = t ∧ P a b := by
  constructor
  · rintro ⟨i, j, h, hP⟩
    obtain ⟨h₀, h₁, h₂⟩ := injective_l hℳ hω he hT h hn
    subst i
    subst j
    exact ⟨h₀, hP⟩
  · rintro ⟨h, hP⟩
    subst s
    exact ⟨a, b, hn, hP⟩

theorem nonzero_l {ω e T t a b n z : carrier_l ℳ} (hz : zero_l z)
    (hn : constructor_l ω e T t a b n) : n ≠ z := by
  intro h
  subst n
  obtain ⟨_, _, _, _, _, _, c, _, hc⟩ := hn
  exact hz c ((hc c).mpr (Or.inr rfl))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFormulaConstructor
