import BMSConstructibleBridge.SecondOrderOrdinalDoubleTailGraph
import BMSConstructibleBridge.SecondOrderWellFoundedInduction

/-! # 序数指标与内部有限尾的预算图

在基础图 S 的根 r 所表示的集合之后，按另一良基图 R 的根序添加 ω 长块。
标签零保留 S；标签一的根 (n,m) 的前驱为 R 中 n 的前驱的全部有限尾，以及
同一根 n 的较短有限尾。基础部分只包含 r 的成员，不加入 r，故第零块的
第零根表示基础集合本身，而不是其后继。

良基性使用原二阶算术的公式良基归纳与内部数强归纳；不使用宿主层良基性、
Collection 或 Class 超限递归。本模块先给 raw 图及成员读数所需的基本接口，
不把它称为最终对象层 BMS 良序证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBudgetGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

open SecondOrderOrdinalDoubleTailGraph (root_l root_m root_formula_l root_injective_l)

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  .app (σ := signature_m) .zero .nil

/-- 原指标图的严格前驱，加上同块的有限前驱。 -/
def lex_l (R : set_l ℳ) (i j n m : num_l ℳ) : Prop :=
  relation_l R i n ∨ (i = n ∧ SecondOrderOrder.lt_l j m)

private def lex_m {Γ Δ : SortContext signature_m} (R : Term signature_m Γ Δ .set)
    (i j n m : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .disj (GraphSyntax.edge_m R i n)
    (.conj (.equal i n) (PrimitiveFormulas.lt_m j m))

def spec_l (S : set_l ℳ) (r : num_l ℳ) (R G : set_l ℳ) : Prop :=
  ∀ x y, relation_l G x y ↔
    (∃ a b, value_l (zero_l ℳ) a = x ∧ value_l (zero_l ℳ) b = y ∧ relation_l S a b) ∨
    (∃ n m, root_l n m = y ∧
      ((∃ a, value_l (zero_l ℳ) a = x ∧ relation_l S a r) ∨
        ∃ i j, root_l i j = x ∧ lex_l R i j n m))

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ) (r : num_l ℳ)
    (R : set_l ℳ) : ∃ G, spec_l S r R G := by
  let φ : Formula signature_m [] [.num, .num, .set, .num, .set] := .disj
    (.existsE .num (.existsE .num (.conj
      (PrimitiveFormulas.pair_m zero_m (.bvar (.there .here)) (.fvar .here))
      (.conj (PrimitiveFormulas.pair_m zero_m (.bvar .here) (.fvar (.there .here)))
        (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))))))
    (.existsE .num (.existsE .num (.conj
      (root_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there .here)))
      (.disj
        (.existsE .num (.conj (PrimitiveFormulas.pair_m zero_m (.bvar .here) (.fvar .here))
          (GraphSyntax.edge_m (.fvar (.there (.there .here))) (.bvar .here)
            (.fvar (.there (.there (.there .here)))))))
        (.existsE .num (.existsE .num (.conj
          (root_m (.bvar (.there .here)) (.bvar .here) (.fvar .here))
          (lex_m (.fvar (.there (.there (.there (.there .here)))))
            (.bvar (.there .here)) (.bvar .here)
            (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))))))))))
  obtain ⟨G, hG⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree R).pushFree r).pushFree S)
  refine ⟨G, fun x y => (hG x y).trans ?_⟩
  simp only [φ, lex_m, Formula.satisfies, root_formula_l, SecondOrderPairing.formula_l,
    SecondOrderPairing.edge_l, SecondOrderOrder.formula_l, zero_m, Term.eval]
  rfl

theorem fiber_l (hℳ : Theory.Models ℳ theory_m) {S R G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r R G) : SecondOrderTaggedGraph.fiber_l (zero_l ℳ) S G := by
  intro x b
  rw [hG]
  constructor
  · rintro (⟨a, d, ha, hd, h⟩ | ⟨n, m, hn, _⟩)
    · obtain rfl := (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hd).2
      exact ⟨a, ha.symm, h⟩
    · exact (nonzero_l hℳ (zero_l ℳ)
        (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hn).1).elim
  · rintro ⟨a, rfl, ha⟩
    exact Or.inl ⟨a, b, rfl, rfl, ha⟩

theorem tail_edge_l (hℳ : Theory.Models ℳ theory_m) {S R G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r R G) (x n m : num_l ℳ) :
    relation_l G x (root_l n m) ↔
      (∃ a, value_l (zero_l ℳ) a = x ∧ relation_l S a r) ∨
        ∃ i j, root_l i j = x ∧ lex_l R i j n m := by
  rw [hG]
  constructor
  · rintro (⟨a, b, _, hb, _⟩ | ⟨i, j, hi, h⟩)
    · exact (nonzero_l hℳ (zero_l ℳ)
        (SecondOrderPairingBounds.injective_l hℳ _ _ _ _ hb).1.symm).elim
    · obtain ⟨rfl, rfl⟩ := root_injective_l hℳ hi
      exact h
  · exact fun h => Or.inr ⟨n, m, rfl, h⟩

/-- 外层是原图良基公式归纳；内层是模型内部数强归纳。 -/
theorem tail_wf_l (hℳ : Theory.Models ℳ theory_m) {S R G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r R G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
    (n : num_l ℳ) (hn : SecondOrderDomain.wf_l R n) :
    ∀ m, SecondOrderDomain.wf_l G (root_l n m) := by
  have hBase (a : num_l ℳ) : SecondOrderDomain.wf_l G (value_l (zero_l ℳ) a) :=
    SecondOrderTaggedDomain.wf_l hℳ _ S G (fiber_l hℳ hG) a (hS a)
  let φ : Formula signature_m [] [.num, .set] := .forallE .num (.existsE .num (.conj
    (root_m (.fvar .here) (.bvar (.there .here)) (.bvar .here))
    (GraphTranslation.domain_m (.fvar (.there .here)) (.bvar .here))))
  have hPure : language_m φ = true := by
    change (true && _) = true
    exact GraphTranslation.domain_pure_m _ _ rfl rfl
  have hRead (a : num_l ℳ) : φ.satisfies
      (((Env.empty (M := ℳ)).pushFree G).pushFree a) ↔
        ∀ m, SecondOrderDomain.wf_l G (root_l a m) := by
    simp only [φ, Formula.satisfies, root_formula_l, SecondOrderInterpretation.domain_l, Term.eval]
    change (∀ m : num_l ℳ, ∃ z : num_l ℳ,
      root_l a m = z ∧ SecondOrderDomain.wf_l G z) ↔ _
    simp
  apply (hRead n).mp
  apply SecondOrderWellFoundedInduction.induction_l hℳ φ hPure
    ((Env.empty (M := ℳ)).pushFree G) R ?_ n hn
  intro a _ ihOuter
  apply (hRead a).mpr
  let ψ : Formula signature_m [] [.num, .num, .set] := .existsE .num (.conj
    (root_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
    (GraphTranslation.domain_m (.fvar (.there (.there .here))) (.bvar .here)))
  have hPureInner : language_m ψ = true := by
    change (true && _) = true
    exact GraphTranslation.domain_pure_m _ _ rfl rfl
  have hReadInner (m : num_l ℳ) : ψ.satisfies
      ((((Env.empty (M := ℳ)).pushFree G).pushFree a).pushFree m) ↔
        SecondOrderDomain.wf_l G (root_l a m) := by
    simp only [ψ, Formula.satisfies, root_formula_l, SecondOrderInterpretation.domain_l, Term.eval]
    change (∃ z : num_l ℳ, root_l a m = z ∧ SecondOrderDomain.wf_l G z) ↔ _
    simp
  apply SecondOrderListInduction.strong_induct_l hℳ ψ hPureInner
    (((Env.empty (M := ℳ)).pushFree G).pushFree a)
    (fun m => SecondOrderDomain.wf_l G (root_l a m)) hReadInner
  intro m ihInner
  apply SecondOrderDomainClosure.intro_l hℳ G _
  intro x hx
  rcases (tail_edge_l hℳ hG x a m).mp hx with ⟨b, hb, _⟩ | ⟨i, j, hij, hlex⟩
  · exact hb ▸ hBase b
  · rcases hlex with hi | ⟨rfl, hj⟩
    · exact hij ▸ (hRead i).mp (ihOuter i hi) j
    · exact hij ▸ ihInner j hj

theorem wf_l (hℳ : Theory.Models ℳ theory_m) {S R G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r R G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
    (hR : ∀ a, SecondOrderDomain.wf_l R a) : ∀ a, SecondOrderDomain.wf_l G a := by
  classical
  intro a
  by_cases hZero : ∃ b, value_l (zero_l ℳ) b = a
  · obtain ⟨b, rfl⟩ := hZero
    exact SecondOrderTaggedDomain.wf_l hℳ _ S G (fiber_l hℳ hG) b (hS b)
  by_cases hOne : ∃ n m, root_l n m = a
  · obtain ⟨n, m, rfl⟩ := hOne
    exact tail_wf_l hℳ hG hS n (hR n) m
  exact SecondOrderDomain.leaf_l G a (fun x hx => by
    rcases (hG x a).mp hx with ⟨_, b, _, hb, _⟩ | ⟨n, m, hn, _⟩
    · exact hZero ⟨b, hb⟩
    · exact hOne ⟨n, m, hn⟩)

noncomputable def code_l (hℳ : Theory.Models ℳ theory_m) {S R G : set_l ℳ} {r : num_l ℳ}
    (hG : spec_l S r R G) (hS : ∀ a, SecondOrderDomain.wf_l S a)
    (n : num_l ℳ) (hn : SecondOrderDomain.wf_l R n) (m : num_l ℳ) :
    SecondOrderGraph.code_l ℳ := ⟨G, root_l n m, tail_wf_l hℳ hG hS n hn m⟩

#print axioms exists_l
#print axioms tail_wf_l
#print axioms wf_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderOrdinalBudgetGraph
