import BMSConstructibleBridge.SecondOrderRootNormalization
import BMSConstructibleBridge.SecondOrderSections
import BMSConstructibleBridge.SecondOrderPairingBounds

/-! # 一张带根码族实数的统一零根规范化

直接以原二阶理解读取每行第零标记的图和第一标记的根，再统一拼接。
不先抽取行实数或根的 Type 函数；精确规格覆盖全部内部自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootedRealFamilyNormalization

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing (value_l relation_l)

set_option autoImplicit false

universe u

private def zero_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num := Term.app (σ := signature_m) .zero .nil
private def one_m {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons zero_m .nil)
private def succ_m {Γ Δ : SortContext signature_m} (a : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons a .nil)
private abbrev up {Γ Δ : SortContext signature_m} {s : sort_m} (t : Term signature_m Γ Δ s) :=
  t.weakenBound sort_m.num

def root_m {Γ Δ : SortContext signature_m} (H : Term signature_m Γ Δ .set)
    (i r : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .conj (PrimitiveFormulas.pair_m one_m (up r) (.bvar .here))
    (GraphSyntax.edge_m (up H) (up i) (.bvar .here))

def graph_m {Γ Δ : SortContext signature_m} (H : Term signature_m Γ Δ .set)
    (i a b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .existsE .num <| .conj
    (PrimitiveFormulas.pair_m (up (up a)) (up (up b)) (.bvar (.there .here))) <|
    .conj (PrimitiveFormulas.pair_m zero_m (.bvar (.there .here)) (.bvar .here))
      (GraphSyntax.edge_m (up (up H)) (up (up i)) (.bvar .here))

def edge_m {Γ Δ : SortContext signature_m} (H : Term signature_m Γ Δ .set)
    (i a b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num <| .conj (root_m (up H) (up i) (.bvar .here)) <|
    .existsE .num <| .conj (.equal (up (up a)) (succ_m (.bvar .here))) <|
      .disj (.conj (.equal (up (up b)) zero_m)
        (graph_m (up (up H)) (up (up i)) (.bvar .here) (.bvar (.there .here))))
        (.existsE .num <| .conj (.equal (up (up (up b))) (succ_m (.bvar .here)))
          (graph_m (up (up (up H))) (up (up (up i))) (.bvar (.there .here)) (.bvar .here)))

def formula_m : Formula signature_m [] [.num, .num, .set] :=
  .existsE .num <| .existsE .num <| .conj
    (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here) (.fvar (.there .here)))
    (edge_m (.fvar (.there (.there .here))) (.fvar .here) (.bvar (.there .here)) (.bvar .here))

theorem pure_m : language_m formula_m = true := pure_language_m _ rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def root_l (H : set_l ℳ) (i r : num_l ℳ) : Prop := relation_l H i (value_l (succ_l (zero_l ℳ)) r)
def graph_l (H : set_l ℳ) (i a b : num_l ℳ) : Prop := relation_l H i (value_l (zero_l ℳ) (value_l a b))
def edge_l (H : set_l ℳ) (i a b : num_l ℳ) : Prop :=
  ∃ r, root_l H i r ∧ ∃ c, a = succ_l c ∧
    ((b = zero_l ℳ ∧ graph_l H i c r) ∨ ∃ d, b = succ_l d ∧ graph_l H i c d)

theorem root_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (H : Term signature_m Γ Δ .set) (i r : Term signature_m Γ Δ .num) :
    (root_m H i r).satisfies η ↔ root_l (H.eval η) (i.eval η) (r.eval η) := by
  simp only [root_m, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l,
    zero_m, one_m, up, Term.eval_weakenBound, Term.eval, Arguments.eval]
  change (∃ c, value_l (succ_l (zero_l ℳ)) (r.eval η) = c ∧ relation_l (H.eval η) (i.eval η) c) ↔ _
  exact ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

theorem graph_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (H : Term signature_m Γ Δ .set) (i a b : Term signature_m Γ Δ .num) :
    (graph_m H i a b).satisfies η ↔ graph_l (H.eval η) (i.eval η) (a.eval η) (b.eval η) := by
  simp only [graph_m, Formula.satisfies, SecondOrderPairing.formula_l, SecondOrderPairing.edge_l,
    zero_m, up, Term.eval_weakenBound, Term.eval, Arguments.eval]
  change (∃ c d, value_l (a.eval η) (b.eval η) = c ∧ value_l (zero_l ℳ) c = d ∧
    relation_l (H.eval η) (i.eval η) d) ↔ _
  exact ⟨fun ⟨_, _, rfl, rfl, h⟩ => h, fun h => ⟨_, _, rfl, rfl, h⟩⟩

theorem edge_formula_l {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
    (H : Term signature_m Γ Δ .set) (i a b : Term signature_m Γ Δ .num) :
    (edge_m H i a b).satisfies η ↔ edge_l (H.eval η) (i.eval η) (a.eval η) (b.eval η) := by
  simp only [edge_m, edge_l, Formula.satisfies, root_formula_l, graph_formula_l,
    zero_m, succ_m, up, Term.eval_weakenBound, Term.eval, Arguments.eval]
  rfl

def spec_l (H K : set_l ℳ) : Prop :=
  ∀ i c, relation_l K i c ↔ ∃ a b, value_l a b = c ∧ edge_l H i a b

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (H : set_l ℳ) : ∃ K, spec_l H K := by
  obtain ⟨K, hK⟩ := SecondOrderRelations.comprehension_l hℳ formula_m pure_m (Env.empty.pushFree H)
  refine ⟨K, fun i c => (hK i c).trans ?_⟩
  simp only [formula_m, Formula.satisfies, SecondOrderPairing.formula_l, edge_formula_l, Term.eval]
  rfl

theorem row_edge_l (hℳ : Theory.Models ℳ theory_m) {H K Y : set_l ℳ} {i : num_l ℳ}
    (hK : spec_l H K) (hY : SecondOrderSections.spec_l K i Y) (a b : num_l ℳ) :
    relation_l Y a b ↔ edge_l H i a b := by
  refine (hY (value_l a b)).trans ((hK i _).trans ?_)
  constructor
  · rintro ⟨c, d, hPair, hEdge⟩
    obtain ⟨rfl, rfl⟩ := SecondOrderPairingBounds.injective_l hℳ c d a b hPair
    exact hEdge
  · intro hEdge
    exact ⟨a, b, rfl, hEdge⟩

/-- 同一行的根唯一后，任意行实数满足旧根的新根拼接规格。 -/
theorem row_normal_l (hℳ : Theory.Models ℳ theory_m) {H K F R Y : set_l ℳ} {i r : num_l ℳ}
    (hK : spec_l H K) (hF : SecondOrderSections.spec_l H i F)
    (hR : SecondOrderSections.spec_l F (zero_l ℳ) R)
    (hRoot : ∀ m, relation_l F (succ_l (zero_l ℳ)) m ↔ m = r)
    (hY : SecondOrderSections.spec_l K i Y) :
    ∃ P, SecondOrderRootNormalization.spec_l R r P Y := by
  obtain ⟨P, W, hNormal⟩ := SecondOrderRootNormalization.exists_l hℳ R r
  have hRoots m : root_l H i m ↔ m = r := (hF (value_l (succ_l (zero_l ℳ)) m)).symm.trans (hRoot m)
  have hGraphs a b : graph_l H i a b ↔ relation_l R a b :=
    ((hF (value_l (zero_l ℳ) (value_l a b))).symm.trans (hR (value_l a b)).symm)
  have hRead a b : relation_l Y a b ↔ ∃ c, a = succ_l c ∧
      ((b = zero_l ℳ ∧ relation_l R c r) ∨ ∃ d, b = succ_l d ∧ relation_l R c d) := by
    refine (row_edge_l hℳ hK hY a b).trans ?_
    constructor
    · rintro ⟨m, hm, c, hc, hBody⟩
      have hmr := (hRoots m).mp hm
      subst m
      exact ⟨c, hc, (or_congr (and_congr Iff.rfl (hGraphs c r))
        (exists_congr (fun d => and_congr Iff.rfl (hGraphs c d)))).mp hBody⟩
    · rintro ⟨c, hc, hBody⟩
      exact ⟨r, (hRoots r).mpr rfl, c, hc,
        (or_congr (and_congr Iff.rfl (hGraphs c r))
          (exists_congr (fun d => and_congr Iff.rfl (hGraphs c d)))).mpr hBody⟩
  refine ⟨P, hNormal.selection, ?_, ?_, ?_⟩
  · intro b h
    obtain ⟨c, hc, _⟩ := (hRead (zero_l ℳ) b).mp h
    exact nonzero_l hℳ c hc.symm
  · intro a
    refine (hRead (succ_l a) (zero_l ℳ)).trans ?_
    constructor
    · rintro ⟨c, hc, hBody⟩
      have hac := injective_l hℳ hc
      subst c
      rcases hBody with ⟨_, hEdge⟩ | ⟨d, hd, _⟩
      · exact (hNormal.selection a).mpr hEdge
      · exact (nonzero_l hℳ d hd.symm).elim
    · intro ha
      exact ⟨a, rfl, Or.inl ⟨rfl, (hNormal.selection a).mp ha⟩⟩
  · intro a b
    refine (hRead (succ_l a) (succ_l b)).trans ?_
    constructor
    · rintro ⟨c, hc, hBody⟩
      have hac := injective_l hℳ hc
      subst c
      rcases hBody with ⟨hb, _⟩ | ⟨d, hd, hEdge⟩
      · exact (nonzero_l hℳ b hb).elim
      · have hbd := injective_l hℳ hd
        subst d
        exact hEdge
    · intro hEdge
      exact ⟨a, rfl, Or.inr ⟨b, rfl, hEdge⟩⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderRootedRealFamilyNormalization
