import BMSConstructibleBridge.SecondOrderLegacyFormulaTranslationDomain

/-! # 内部翻译码的统一赋值长度界

若原码 n、原长度 l 的翻译输出为 q，则所有内部长度 L ≥ l+n 都使目标
码 q 合法。旧量词的前插使 l 增加一，但严格子码 p<n 给出 succ l+p ≤ l+n。
证明对实际纯算术公式作内部强归纳，不按模型 ω 作外部递归。
本界不证明两求值器同值，也不把目标合法性当作 Def 双向等价。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyFormulaTranslationLength

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (relation_l)
open SecondOrderAlgebra
open SecondOrderLegacyFormulaTranslation (query_l query_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) := t.weakenBound sort_m.num

private def sum_m {Γ Δ : SortContext signature_m} (l n : Term signature_m Γ Δ .num) :=
  Term.app (σ := signature_m) .add (.cons l (.cons n .nil))

def bound_l (l n L : num_l ℳ) : Prop := add_l l n = L ∨ SecondOrderOrder.lt_l (add_l l n) L

def bound_m {Γ Δ : SortContext signature_m} (l n L : Term signature_m Γ Δ .num) :
    Formula signature_m Γ Δ :=
  .disj (.equal (sum_m l n) L) (PrimitiveFormulas.lt_m (sum_m l n) L)

theorem bound_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (l n L : Term signature_m Γ Δ .num) :
    (bound_m l n L).satisfies η ↔ bound_l (l.eval η) (n.eval η) (L.eval η) := by
  simp only [bound_m, bound_l, Formula.satisfies, SecondOrderOrder.formula_l, sum_m, Term.eval]
  rfl

def row_m {Γ Δ : SortContext signature_m} (C W : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .forallE .num <| .forallE .num <|
    .imp (query_m (up (up (up C))) (up (up (up n)))
      (.bvar (.there (.there .here))) (.bvar (.there .here))) <|
      .imp (bound_m (.bvar (.there (.there .here))) (up (up (up n))) (.bvar .here))
        (GraphSyntax.edge_m (up (up (up W))) (.bvar (.there .here)) (.bvar .here))

theorem row_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (C W : Term signature_m Γ Δ .set) (n : Term signature_m Γ Δ .num) :
    (row_m C W n).satisfies η ↔ ∀ l q L, query_l (C.eval η) (n.eval η) l q →
      bound_l l (n.eval η) L → relation_l (W.eval η) q L := by
  simp only [row_m, Formula.satisfies, SecondOrderLegacyFormulaTranslation.query_formula_l,
    bound_formula_l, SecondOrderPairing.edge_l, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem length_l (hℳ : Theory.Models ℳ theory_m) {C W : set_l ℳ}
    (hC : SecondOrderLegacyFormulaTranslation.spec_l C) (hW : SecondOrderTriangularFormulaSyntax.spec_l W) :
    ∀ n l q L, query_l C n l q → bound_l l n L → relation_l W q L := by
  letI := semiring_l hℳ
  letI := order_l hℳ
  letI := ordered_l hℳ
  let φ : Formula signature_m [] [.num, .set, .set] :=
    row_m (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  apply SecondOrderListInduction.strong_induct_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty.pushFree W).pushFree C)
    (fun n => ∀ l q L, query_l C n l q → bound_l l n L → relation_l W q L)
    (fun n => row_formula_l _ _ _ _) ?_
  intro n ih l q L hQuery hBound
  change l + n ≤ L at hBound
  have hlL : l ≤ L := (le_add_of_nonneg_right (zero_le_l hℳ n)).trans hBound
  rcases (SecondOrderLegacyFormulaTranslation.equation_l hℳ hC n l q).mp hQuery with
    ⟨_, rfl⟩ | ⟨t, p, hNode, hCases⟩
  · exact SecondOrderTriangularFormulaBranches.zero_l hW L
  · have hpLt := (SecondOrderFormulaCode.bounds_l hℳ t p).2
    rw [hNode] at hpLt
    have hChild {k : num_l ℳ} (hk : SecondOrderOrder.lt_l k n) : bound_l l k L := by
      change l + k ≤ L
      exact (add_le_add (show l ≤ l from le_rfl) (le_of_lt hk)).trans hBound
    rcases hCases with hAtom | ⟨_, hNeg⟩ | ⟨_, hConj⟩ | ⟨_, hExists⟩
    · obtain ⟨_, _, r, s, _, hr, hs, hTag⟩ := hAtom
      have hrL : SecondOrderOrder.lt_l r L :=
        lt_of_lt_of_le (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hr).2 hlL
      have hsL : SecondOrderOrder.lt_l s L :=
        lt_of_lt_of_le (SecondOrderLegacyAssignmentReversal.bounds_l hℳ hs).2 hlL
      rcases hTag with ⟨_, hConstructor⟩ | ⟨_, hConstructor⟩
      · exact (SecondOrderTriangularFormulaBranches.equality_l hℳ hW hConstructor L).mpr ⟨hrL, hsL⟩
      · exact (SecondOrderTriangularFormulaBranches.membership_l hℳ hW hConstructor L).mpr ⟨hrL, hsL⟩
    · obtain ⟨a, ha, hConstructor⟩ := hNeg
      have hValid := ih p hpLt l a L ha (hChild hpLt)
      exact (SecondOrderTriangularFormulaBranches.nand_l hℳ hW hConstructor L).mpr ⟨hValid, hValid⟩
    · obtain ⟨i, j, a, b, d, hPair, ha, hb, hd, hConstructor⟩ := hConj
      have hChildren := SecondOrderFormulaCode.children_l hℳ t i j
      rw [hPair, hNode] at hChildren
      have hValidA := ih i hChildren.1 l a L ha (hChild hChildren.1)
      have hValidB := ih j hChildren.2 l b L hb (hChild hChildren.2)
      have hValidD := (SecondOrderTriangularFormulaBranches.nand_l hℳ hW hd L).mpr ⟨hValidA, hValidB⟩
      exact (SecondOrderTriangularFormulaBranches.nand_l hℳ hW hConstructor L).mpr ⟨hValidD, hValidD⟩
    · obtain ⟨a, ha, hConstructor⟩ := hExists
      have hSuccP : succ_l p ≤ n := by
        rw [succ_eq_l hℳ]
        exact (lt_iff_add_one_le_l hℳ p n).mp hpLt
      have hNextBound : bound_l (succ_l l) p L := by
        change add_l (succ_l l) p ≤ L
        calc
          add_l (succ_l l) p = add_l l (succ_l p) := by
            rw [SecondOrderNumbers.succ_add_l hℳ, add_succ_l hℳ]
          _ ≤ add_l l n := add_le_add le_rfl hSuccP
          _ ≤ L := hBound
      have hPositive : SecondOrderOrder.lt_l (zero_l ℳ) n := by
        rw [← hNode]
        exact SecondOrderOrder.zero_succ_l hℳ _
      have hSlot : SecondOrderOrder.lt_l l L :=
        lt_of_lt_of_le (lt_add_of_pos_right l hPositive) hBound
      have hValid := ih p hpLt (succ_l l) a L ha hNextBound
      exact (SecondOrderTriangularFormulaBranches.existential_l hℳ hW hConstructor L).mpr ⟨hSlot, hValid⟩

def sentence_m : Sentence signature_m := .forallE .set <| .forallE .set <|
  .imp (SecondOrderLegacyFormulaTranslation.spec_m (.bvar (.there .here))) <|
    .imp (SecondOrderTriangularFormulaSyntax.spec_m (.bvar .here)) <|
      .forallE .num <| row_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here)

theorem derives_m : Derives theory_m [] sentence_m := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  simp only [sentence_m, Formula.TrueIn, Formula.satisfies,
    SecondOrderLegacyFormulaTranslation.spec_formula_l, SecondOrderTriangularFormulaSyntax.spec_formula_l,
    row_formula_l, Term.eval]
  exact fun _ _ hC hW => length_l hℳ hC hW

#print axioms length_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderLegacyFormulaTranslationLength
