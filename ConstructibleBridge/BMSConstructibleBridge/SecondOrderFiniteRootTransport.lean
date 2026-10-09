import BMSConstructibleBridge.SecondOrderListInduction
import BMSConstructibleBridge.SecondOrderInterpretation
import BMSConstructibleBridge.SecondOrderCompleteness
import YesMetaZFC.Automation.ModelClosure

/-! # 内部有限下降路径上的根良基传输

原二阶语言，背景为原 Z₂。给定实际内部有限数图及相邻下降边，由原根域证书
得到每个界内节点的同一根域证书。归纳正文明确包含原 domain 公式，使用
实际公式的内部强归纳，不假设模型自然数外部标准或外部良基。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteRootTransport

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem transport_l (hℳ : Theory.Models ℳ theory_m) (R X : set_l ℳ) (n r : num_l ℳ)
    (hRoot : SecondOrderDomain.wf_l R r)
    (hInitial : ∀ a, relation_l X (zero_l ℳ) a → a = r)
    (hTotal : ∀ i, SecondOrderOrder.lt_l i n → ∃ a, relation_l X i a)
    (hEdges : ∀ i, SecondOrderOrder.lt_l (succ_l i) n → ∀ a b,
      relation_l X i a → relation_l X (succ_l i) b → relation_l R b a) :
    ∀ i, SecondOrderOrder.lt_l i n → ∀ a, relation_l X i a → SecondOrderDomain.wf_l R a := by
  let φ : Formula signature_m [] [.num, .set, .set] :=
    .forallE .num <| .imp (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
      (GraphTranslation.domain_m (.fvar (.there (.there .here))) (.bvar .here))
  have hφ : language_m φ = true := by
    change (true && language_m
      (GraphTranslation.domain_m (.fvar (.there (.there .here))) (.bvar .here))) = true
    rw [GraphTranslation.domain_pure_m _ _ rfl rfl]
    rfl
  let η : Env ℳ [] [.set, .set] := (Env.empty.pushFree R).pushFree X
  have hP (i : num_l ℳ) : φ.satisfies (η.pushFree i) ↔
      ∀ a, relation_l X i a → SecondOrderDomain.wf_l R a := by
    simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l, SecondOrderInterpretation.domain_l]
    rfl
  apply SecondOrderListInduction.strong_induct_below_l hℳ φ hφ η _ hP n
  intro i hi ih a hXa
  rcases predecessor_l hℳ i with rfl | ⟨j, rfl⟩
  · exact (hInitial a hXa).symm ▸ hRoot
  · have hj : SecondOrderOrder.lt_l j (succ_l j) := ⟨zero_l ℳ, by rw [add_succ_l hℳ, add_zero_l hℳ]⟩
    obtain ⟨b, hXb⟩ := hTotal j (SecondOrderOrder.trans_l hℳ hj hi)
    exact SecondOrderDomain.child_l hℳ R b a (ih j hj b hXb) (hEdges j hi b a hXb hXa)

private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m}
    (t : Term signature_m Γ Δ s) (r : sort_m) := t.weakenBound r

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ_m {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons t .nil)

def initial_m {Γ Δ : SortContext signature_m} (X : Term signature_m Γ Δ .set)
    (r : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .imp (GraphSyntax.edge_m (up X .num) zero_m (.bvar .here))
    (.equal (.bvar .here) (up r .num))

def nodes_m {Γ Δ : SortContext signature_m} (X : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .imp (PrimitiveFormulas.lt_m (.bvar .here) (up n .num)) <|
    .existsE .num <| GraphSyntax.edge_m (up (up X .num) .num) (.bvar (.there .here)) (.bvar .here)

def edges_m {Γ Δ : SortContext signature_m} (R X : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .imp (PrimitiveFormulas.lt_m (succ_m (.bvar .here)) (up n .num)) <|
    .forallE .num <| .forallE .num <|
      let w (t : Term signature_m Γ Δ .set) := up (up (up t .num) .num) .num
      let i : Term signature_m (.num :: .num :: .num :: Γ) Δ .num := .bvar (.there (.there .here))
      let a : Term signature_m (.num :: .num :: .num :: Γ) Δ .num := .bvar (.there .here)
      let b : Term signature_m (.num :: .num :: .num :: Γ) Δ .num := .bvar .here
      .imp (GraphSyntax.edge_m (w X) i a) <| .imp (GraphSyntax.edge_m (w X) (succ_m i) b)
        (GraphSyntax.edge_m (w R) b a)

def values_m {Γ Δ : SortContext signature_m} (R X : Term signature_m Γ Δ .set)
    (n : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .forallE .num <| .imp (PrimitiveFormulas.lt_m (.bvar .here) (up n .num)) <|
    .forallE .num <| .imp (GraphSyntax.edge_m (up (up X .num) .num) (.bvar (.there .here)) (.bvar .here))
      (GraphTranslation.domain_m (up (up R .num) .num) (.bvar .here))

def schema_m {Δ : SortContext signature_m} (R X : Term signature_m [] Δ .set)
    (n r : Term signature_m [] Δ .num) : Formula signature_m [] Δ :=
  .imp (GraphTranslation.domain_m R r) <| .imp (initial_m X r) <| .imp (nodes_m X n) <|
    .imp (edges_m R X n) (values_m R X n)

def sentence_m {Δ : SortContext signature_m} (R X : Term signature_m [] Δ .set)
    (n r : Term signature_m [] Δ .num) : Sentence signature_m :=
  Metatheory.Formula.forall_close (schema_m R X n r)

theorem models_l (hℳ : Theory.Models ℳ theory_m) {Δ : SortContext signature_m}
    (η : Env ℳ [] Δ) (R X : Term signature_m [] Δ .set) (n r : Term signature_m [] Δ .num) :
    (schema_m R X n r).satisfies η := by
  simp only [schema_m, initial_m, nodes_m, edges_m, values_m, Formula.satisfies,
    SecondOrderPairing.edge_l, SecondOrderInterpretation.domain_l, SecondOrderOrder.formula_l,
    up, Term.eval_weakenBound, zero_m, succ_m, Term.eval, Arguments.eval]
  exact transport_l hℳ (R.eval η) (X.eval η) (n.eval η) (r.eval η)

theorem derives_m {Δ : SortContext signature_m} (R X : Term signature_m [] Δ .set)
    (n r : Term signature_m [] Δ .num) : Derives theory_m [] (sentence_m R X n r) := by
  apply SecondOrderCompleteness.derives_m
  intro ℳ hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  exact models_l hℳ η R X n r

#print axioms transport_l
#print axioms derives_m

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderFiniteRootTransport
