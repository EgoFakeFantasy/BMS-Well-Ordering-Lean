import BMSConstructibleBridge.PowerlessConcatenation

/-!
# 内部集合函数的平移限制

把原图在区间 [p,p+q) 的取值改用局部下标 j<q 保存。图由真实纯公式构造，
不把宿主函数当作模型内集合；全部参数和区间长度均允许是内部非标准自然数。
精确域外规格、指定偏移处的读回和递增性供标签块拆分复用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessShiftedRestriction

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def entry_m {Γ Δ : SortContext ℒ} (ω e p f j a : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) := s.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj
    (PowerlessAdditionSyntax.addition_m (w ω) (w e) (w p) (w j) (.bvar .here))
    (SecondOrderObjectSyntax.value_m (w f) (.bvar .here) (w a)))

theorem entry_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e p f j a : Term ℒ Γ Δ .set) :
    (entry_m ω e p f j a).satisfies η ↔
      ∃ i, PowerlessAddition.addition_l (ω.eval η) (e.eval η) (p.eval η) (j.eval η) i ∧
        value_l (f.eval η) i (a.eval η) := by
  simp only [entry_m, Formula.satisfies, PowerlessAdditionSyntax.addition_formula_l,
    value_formula_l, Term.eval_weakenBound]
  rfl

def graph_l (ω e p q f g : carrier_l ℳ) : Prop :=
  ∀ j a, value_l g j a ↔ member_l ℳ j q ∧
    ∃ i, PowerlessAddition.addition_l ω e p j i ∧ value_l f i a

/-- 任意包含该区间的实际原函数，都有同值域的精确平移限制。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e p q r D A f : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (hr : PowerlessAddition.addition_l ω e p q r) (hD : subset_l r D) (hf : map_l f D A) :
    ∃ g, map_l g q A ∧ graph_l ω e p q f g := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 4 :=
    { bound := Fin.cases ω (Fin.cases e (Fin.cases p (fun _ => f))), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    entry_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here)))))) (.fvar (.there .here)) (.fvar .here)
  have hs (j a : carrier_l ℳ) :
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree j).pushFree a) ↔
        ∃ i, PowerlessAddition.addition_l ω e p j i ∧ value_l f i a := by
    dsimp only [φ]
    rw [entry_formula_l]
    rfl
  have htotal : ∀ j, member_l ℳ j q → ∃ a,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree j).pushFree a) := by
    intro j hj
    obtain ⟨i, _, hi⟩ := PowerlessAddition.exists_l hℳ hω he hp
      (PowerlessNaturalOrder.omega_transitive_l hℳ hω q j hq hj)
    obtain ⟨a, ⟨_, ha⟩, _⟩ := hf.2 i
      (hD i (PowerlessAdditionOrder.monotone_l hℳ hω he hj hi hr))
    exact ⟨a, (hs j a).mpr ⟨i, hi, ha⟩⟩
  have hunique : ∀ j, member_l ℳ j q → ∀ a b,
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree j).pushFree a) →
      φ.satisfies (((PowerlessComprehension.env_l η).pushFree j).pushFree b) → a = b := by
    intro j _ a b ha hb
    obtain ⟨i, hi, ha⟩ := (hs j a).mp ha
    obtain ⟨i₁, hi₁, hb⟩ := (hs j b).mp hb
    obtain rfl := PowerlessAddition.unique_l hℳ hω he hi hi₁
    exact PowerlessFunction.value_unique_l hℳ hf ha hb
  obtain ⟨g, C, hg, _, hV⟩ := PowerlessMapping.exists_l hℳ φ η q htotal hunique
  have hgraph : graph_l ω e p q f g := by
    intro j a
    constructor
    · intro ha
      have hj := (PowerlessFunction.value_mem_l hℳ hg ha).1
      exact ⟨hj, (hs j a).mp ((hV j hj a).mp ha)⟩
    · rintro ⟨hj, ha⟩
      exact (hV j hj a).mpr ((hs j a).mpr ha)
  refine ⟨g, PowerlessFunction.range_l hℳ hg ?_, hgraph⟩
  intro j a ha
  obtain ⟨_, i, _, hi⟩ := (hgraph j a).mp ha
  exact (PowerlessFunction.value_mem_l hℳ hf hi).2

/-- 给定实际偏移和后，局部查询直接等于原图在该坐标的查询。 -/
theorem at_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e p q f g i j a : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hG : graph_l ω e p q f g) (hj : member_l ℳ j q)
    (hi : PowerlessAddition.addition_l ω e p j i) : value_l g j a ↔ value_l f i a := by
  constructor
  · intro ha
    obtain ⟨_, i₁, hi₁, ha⟩ := (hG j a).mp ha
    exact PowerlessAddition.unique_l hℳ hω he hi₁ hi ▸ ha
  · exact fun ha => (hG j a).mpr ⟨hj, i, hi, ha⟩

/-- 平移限制继承原图的严格递增性，不需要外部有限性。 -/
theorem order_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e p q f g : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hG : graph_l ω e p q f g) (hf : PowerlessConcatenation.increasing_l f) :
    PowerlessConcatenation.increasing_l g := by
  intro i j a b hij ha hb
  obtain ⟨_, i₁, hi₁, ha⟩ := (hG i a).mp ha
  obtain ⟨_, j₁, hj₁, hb⟩ := (hG j b).mp hb
  exact hf i₁ j₁ a b (PowerlessAdditionOrder.monotone_l hℳ hω he hij hi₁ hj₁) ha hb

#print axioms exists_l
#print axioms at_l
#print axioms order_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessShiftedRestriction
