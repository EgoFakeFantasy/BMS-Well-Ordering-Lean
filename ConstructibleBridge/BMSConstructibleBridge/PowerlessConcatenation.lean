import BMSConstructibleBridge.PowerlessFiniteProduct

/-!
# 内部标签图拼接的逐坐标语义

精确拼接保留旧下标和加法移位下标。严格序证明按两段分区，
右块的内部下标序由同一加法的严格单调性和内部可比性恢复。
所有图及长度都属于原模型；不使用宿主有限列表或外部良基性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessConcatenation

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 在任意下标上的精确取值；原图的映射条件另行给出。 -/
def graph_l (ω e p f g h : carrier_l ℳ) : Prop :=
  ∀ i a, value_l h i a ↔ value_l f i a ∨
    ∃ j, PowerlessAddition.addition_l ω e p j i ∧ value_l g j a

def graph_m {Γ Δ : SortContext ℒ} (ω e p f g h : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) :=
    (s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.forallE .set (.iff
    (SecondOrderObjectSyntax.value_m (w h) (.bvar (.there .here)) (.bvar .here))
    (.disj (SecondOrderObjectSyntax.value_m (w f) (.bvar (.there .here)) (.bvar .here))
      (.existsE .set (.conj
        (PowerlessAdditionSyntax.addition_m ((w ω).weakenBound SetTheory.SetSort.set)
          ((w e).weakenBound SetTheory.SetSort.set) ((w p).weakenBound SetTheory.SetSort.set)
          (.bvar .here) (.bvar (.there (.there .here))))
        (SecondOrderObjectSyntax.value_m ((w g).weakenBound SetTheory.SetSort.set)
          (.bvar .here) (.bvar (.there .here))))))))

theorem graph_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e p f g h : Term ℒ Γ Δ .set) :
    (graph_m ω e p f g h).satisfies η ↔
      graph_l (ω.eval η) (e.eval η) (p.eval η) (f.eval η) (g.eval η) (h.eval η) := by
  simp only [graph_m, graph_l, Formula.satisfies, value_formula_l,
    PowerlessAdditionSyntax.addition_formula_l, Term.eval_weakenBound]
  rfl

def increasing_l (f : carrier_l ℳ) : Prop :=
  ∀ i j a b, member_l ℳ i j → value_l f i a → value_l f j b → member_l ℳ a b

private theorem left_mem_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e p q r i : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hp : member_l ℳ p ω) (hr : PowerlessAddition.addition_l ω e p q r)
    (hi : member_l ℳ i p) : member_l ℳ i r := by
  rcases PowerlessAdditionBounds.lower_l hℳ hω he hp hr with hpr | rfl
  · exact PowerlessNaturalOrder.member_transitive_l hℳ hω r
      (PowerlessAdditionBounds.output_l hℳ hω he hp hr) p i hpr hi
  · exact hi

/-- 从实际拼接构造取得全下标规格，域外不会凭空增加取值。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e p q r f g A : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hp : member_l ℳ p ω) (hq : member_l ℳ q ω)
    (hr : PowerlessAddition.addition_l ω e p q r) (hf : map_l f p A) (hg : map_l g q A) :
    ∃ h, map_l h r A ∧ graph_l ω e p f g h := by
  obtain ⟨h, hh, hV⟩ := PowerlessFiniteProduct.concat_graph_l hℳ hω he hp hq hr hf hg
  refine ⟨h, hh, fun i a => ⟨?_, ?_⟩⟩
  · intro ha
    rcases (hV i (PowerlessFunction.value_mem_l hℳ hh ha).1 a).mp ha with
      ⟨_, ha⟩ | ⟨j, _, hj, ha⟩
    · exact Or.inl ha
    · exact Or.inr ⟨j, hj, ha⟩
  · rintro (ha | ⟨j, hj, ha⟩)
    · have hi := (PowerlessFunction.value_mem_l hℳ hf ha).1
      exact (hV i (left_mem_l hℳ hω he hp hr hi) a).mpr (Or.inl ⟨hi, ha⟩)
    · have hjq := (PowerlessFunction.value_mem_l hℳ hg ha).1
      exact (hV i (PowerlessAdditionOrder.monotone_l hℳ hω he hjq hj hr) a).mpr
        (Or.inr ⟨j, hjq, hj, ha⟩)

/-- 旧前缀坐标的取值完全不变。 -/
theorem prefix_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e p r f g h A B i a : carrier_l ℳ} (hf : map_l f p A) (hh : map_l h r B)
    (hG : graph_l ω e p f g h) (hi : member_l ℳ i p) : value_l h i a ↔ value_l f i a := by
  obtain ⟨b, ⟨_, hb⟩, _⟩ := hf.2 i hi
  have hb₀ := (hG i b).mpr (Or.inl hb)
  exact ⟨fun ha => (PowerlessFunction.value_unique_l hℳ hh ha hb₀).symm ▸ hb,
    fun ha => (hG i a).mpr (Or.inl ha)⟩

/-- 内部加法移位后的坐标，精确读取右图的同一局部下标。 -/
theorem shift_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e p q r f g h A B i j a : carrier_l ℳ} (hg : map_l g q A) (hh : map_l h r B)
    (hG : graph_l ω e p f g h) (hj : member_l ℳ j q)
    (hi : PowerlessAddition.addition_l ω e p j i) : value_l h i a ↔ value_l g j a := by
  obtain ⟨b, ⟨_, hb⟩, _⟩ := hg.2 j hj
  have hb₀ := (hG i b).mpr (Or.inr ⟨j, hi, hb⟩)
  exact ⟨fun ha => (PowerlessFunction.value_unique_l hℳ hh ha hb₀).symm ▸ hb,
    fun ha => (hG i a).mpr (Or.inr ⟨j, hi, ha⟩)⟩

/-- 拼接不增加新的标签值，因此逐标签性质由两段共同保持。 -/
theorem labels_l {ω e p f g h : carrier_l ℳ} (hG : graph_l ω e p f g h)
    {P : carrier_l ℳ → Prop} (hf : ∀ i a, value_l f i a → P a)
    (hg : ∀ i a, value_l g i a → P a) : ∀ i a, value_l h i a → P a := by
  intro i a ha
  rcases (hG i a).mp ha with ha | ⟨j, _, ha⟩
  · exact hf i a ha
  · exact hg j a ha

private theorem reflect_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e p i j a b : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : PowerlessAddition.addition_l ω e p i a)
    (hb : PowerlessAddition.addition_l ω e p j b) (hab : member_l ℳ a b) : member_l ℳ i j := by
  rcases PowerlessNaturalCompare.compare_l hℳ hω i (PowerlessAdditionBounds.input_l hℳ ha)
    j (PowerlessAdditionBounds.input_l hℳ hb) with hij | rfl | hji
  · exact hij
  · have h := PowerlessAddition.unique_l hℳ hω he ha hb
    subst b
    exact (PowerlessNatural.asymmetry_l hℳ hab hab).elim
  · exact (PowerlessNatural.asymmetry_l hℳ hab
      (PowerlessAdditionOrder.monotone_l hℳ hω he hji hb ha)).elim

/-- 两段内部严格递增且左段标签均小于右段标签时，拼接仍严格递增。 -/
theorem order_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e p f g h A : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hp : member_l ℳ p ω) (hf : map_l f p A) (hG : graph_l ω e p f g h)
    (hf₀ : increasing_l f) (hg₀ : increasing_l g)
    (hfg : ∀ i j a b, value_l f i a → value_l g j b → member_l ℳ a b) : increasing_l h := by
  intro i j a b hij ha hb
  rcases (hG i a).mp ha with ha | ⟨u, hu, ha⟩
  · rcases (hG j b).mp hb with hb | ⟨v, _, hb⟩
    · exact hf₀ i j a b hij ha hb
    · exact hfg i v a b ha hb
  · rcases (hG j b).mp hb with hb | ⟨v, hv, hb⟩
    · have hi := PowerlessNaturalOrder.member_transitive_l hℳ hω p hp j i
        (PowerlessFunction.value_mem_l hℳ hf hb).1 hij
      rcases PowerlessAdditionBounds.lower_l hℳ hω he hp hu with hpi | hpi
      · exact (PowerlessNatural.asymmetry_l hℳ hi hpi).elim
      · subst p
        exact (PowerlessNatural.asymmetry_l hℳ hi hi).elim
    · exact hg₀ u v a b (reflect_l hℳ hω he hu hv hij) ha hb

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessConcatenation
