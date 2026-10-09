import BMSConstructibleBridge.SecondOrderTriangularInjective

/-! # 原算术语言中的三角公式构造子

保留原载荷配数、标签配数与最后一次后继，不改用平方配数。关系式存在
见证而非 Type 层所选函数；严格子码界对全部内部自然数成立。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularConstructor

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) := t.weakenBound sort_m.num

def node_l (t p n : num_l ℳ) : Prop :=
  ∃ c, SecondOrderTriangularPairing.code_l t p c ∧ n = succ_l c

def node_m {Γ Δ : SortContext signature_m} (t p n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .conj (SecondOrderTriangularPairing.code_m (up t) (up p) (.bvar .here))
    (.equal (up n) (Term.app (σ := signature_m) .succ (.cons (.bvar .here) .nil)))

theorem node_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (t p n : Term signature_m Γ Δ .num) :
    (node_m t p n).satisfies η ↔ node_l (t.eval η) (p.eval η) (n.eval η) := by
  simp only [node_m, node_l, Formula.satisfies, SecondOrderTriangularPairing.formula_l,
    up, Term.eval_weakenBound, Term.eval, Arguments.eval]
  rfl

def constructor_l (t a b n : num_l ℳ) : Prop :=
  ∃ p, SecondOrderTriangularPairing.code_l a b p ∧ node_l t p n

def constructor_m {Γ Δ : SortContext signature_m} (t a b n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .conj (SecondOrderTriangularPairing.code_m (up a) (up b) (.bvar .here))
    (node_m (up t) (.bvar .here) (up n))

theorem formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (t a b n : Term signature_m Γ Δ .num) :
    (constructor_m t a b n).satisfies η ↔ constructor_l (t.eval η) (a.eval η) (b.eval η) (n.eval η) := by
  simp only [constructor_m, constructor_l, Formula.satisfies, SecondOrderTriangularPairing.formula_l,
    node_formula_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem node_exists_l (hℳ : Theory.Models ℳ theory_m) (t p : num_l ℳ) : ∃ n, node_l t p n := by
  obtain ⟨c, hc⟩ := SecondOrderTriangularPairing.exists_l hℳ t p
  exact ⟨succ_l c, c, hc, rfl⟩

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (t a b : num_l ℳ) : ∃ n, constructor_l t a b n := by
  obtain ⟨p, hp⟩ := SecondOrderTriangularPairing.exists_l hℳ a b
  obtain ⟨n, hn⟩ := node_exists_l hℳ t p
  exact ⟨n, p, hp, hn⟩

theorem node_bounds_l (hℳ : Theory.Models ℳ theory_m) {t p n : num_l ℳ} (hn : node_l t p n) :
    SecondOrderOrder.lt_l t n ∧ SecondOrderOrder.lt_l p n := by
  obtain ⟨c, hc, rfl⟩ := hn
  have hSucc : SecondOrderOrder.lt_l c (succ_l c) := by
    refine ⟨zero_l ℳ, ?_⟩
    rw [add_succ_l hℳ, add_zero_l hℳ]
  have hLift {x : num_l ℳ} (h : x = c ∨ SecondOrderOrder.lt_l x c) : SecondOrderOrder.lt_l x (succ_l c) :=
    h.elim (fun hEq => hEq.symm ▸ hSucc) (fun hLt => SecondOrderOrder.trans_l hℳ hLt hSucc)
  obtain ⟨ht, hp⟩ := SecondOrderTriangularPairing.coordinates_l hℳ hc
  exact ⟨hLift ht, hLift hp⟩

theorem bounds_l (hℳ : Theory.Models ℳ theory_m) {t a b n : num_l ℳ} (hn : constructor_l t a b n) :
    SecondOrderOrder.lt_l a n ∧ SecondOrderOrder.lt_l b n := by
  obtain ⟨p, hp, hn⟩ := hn
  have hpn := (node_bounds_l hℳ hn).2
  have hLift {x : num_l ℳ} (h : x = p ∨ SecondOrderOrder.lt_l x p) : SecondOrderOrder.lt_l x n :=
    h.elim (fun hEq => hEq.symm ▸ hpn) (fun hLt => SecondOrderOrder.trans_l hℳ hLt hpn)
  obtain ⟨ha, hb⟩ := SecondOrderTriangularPairing.coordinates_l hℳ hp
  exact ⟨hLift ha, hLift hb⟩

theorem nonzero_l (hℳ : Theory.Models ℳ theory_m) {t a b n : num_l ℳ} (hn : constructor_l t a b n) :
    n ≠ zero_l ℳ := by
  obtain ⟨_, _, c, _, rfl⟩ := hn
  exact SecondOrderModel.nonzero_l hℳ c

theorem node_unique_l (hℳ : Theory.Models ℳ theory_m) {t p n m : num_l ℳ}
    (hn : node_l t p n) (hm : node_l t p m) : n = m := by
  obtain ⟨c, hc, rfl⟩ := hn
  obtain ⟨d, hd, rfl⟩ := hm
  exact congrArg succ_l (SecondOrderTriangularPairing.unique_l hℳ hc hd)

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {t a b n m : num_l ℳ}
    (hn : constructor_l t a b n) (hm : constructor_l t a b m) : n = m := by
  obtain ⟨p, hp, hn⟩ := hn
  obtain ⟨q, hq, hm⟩ := hm
  exact node_unique_l hℳ hn (SecondOrderTriangularPairing.unique_l hℳ hq hp ▸ hm)

theorem node_injective_l (hℳ : Theory.Models ℳ theory_m) {t p s q n : num_l ℳ}
    (hn : node_l t p n) (hm : node_l s q n) : t = s ∧ p = q := by
  obtain ⟨c, hc, hcn⟩ := hn
  obtain ⟨d, hd, hdn⟩ := hm
  have hcd := (SecondOrderModel.injective_l hℳ) (hcn.symm.trans hdn)
  exact SecondOrderTriangularInjective.injective_l hℳ (hcd ▸ hc) hd

theorem injective_l (hℳ : Theory.Models ℳ theory_m) {t a b s d f n : num_l ℳ}
    (hn : constructor_l t a b n) (hm : constructor_l s d f n) : t = s ∧ a = d ∧ b = f := by
  obtain ⟨p, hp, hn⟩ := hn
  obtain ⟨q, hq, hm⟩ := hm
  obtain ⟨hts, hpq⟩ := node_injective_l hℳ hn hm
  exact ⟨hts, SecondOrderTriangularInjective.injective_l hℳ (hpq ▸ hp) hq⟩

#print axioms bounds_l
#print axioms injective_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderTriangularConstructor
