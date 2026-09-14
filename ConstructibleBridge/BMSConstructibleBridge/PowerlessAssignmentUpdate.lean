import BMSConstructibleBridge.PowerlessFiniteAssignments

/-!
# 内部有限赋值的单变量更新

更新保持原定义域与值域。精确取值公式和实际函数图条件同时保留，
供后续量词满足关系使用；不靠外部有限函数更新。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentUpdate

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def update_l (f i a g : carrier_l ℳ) : Prop :=
  ∀ x y, value_l g x y ↔ (x = i ∧ y = a) ∨ (x ≠ i ∧ value_l f x y)

def update_m {Γ Δ : SortContext ℒ} (f i a g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .forallE .set (.forallE .set (.iff
    (SecondOrderObjectSyntax.value_m (w g) (.bvar (.there .here)) (.bvar .here))
    (.disj (.conj (.equal (.bvar (.there .here)) (w i)) (.equal (.bvar .here) (w a)))
      (.conj (.neg (.equal (.bvar (.there .here)) (w i)))
        (SecondOrderObjectSyntax.value_m (w f) (.bvar (.there .here)) (.bvar .here))))))

theorem update_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f i a g : Term ℒ Γ Δ .set) :
    (update_m f i a g).satisfies η ↔ update_l (f.eval η) (i.eval η) (a.eval η) (g.eval η) := by
  simp only [update_m, update_l, Formula.satisfies, value_formula_l, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f n A i a : carrier_l ℳ} (hf : map_l f n A) (hi : member_l ℳ i n) (ha : member_l ℳ a A) :
    ∃ g, map_l g n A ∧ update_l f i a g := by
  classical
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases f (Fin.cases i (fun _ => a)), free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    .disj (.conj (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there .here)))))
      (.equal (.fvar .here) (.fvar (.there (.there (.there (.there .here)))))))
      (.conj (.neg (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there .here))))))
        (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here))) (.fvar (.there .here)) (.fvar .here)))
  have h : ∀ x y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ↔
      (x = i ∧ y = a) ∨ (x ≠ i ∧ value_l f x y) := by
    intro x y
    simp only [φ, Formula.satisfies, value_formula_l]
    rfl
  obtain ⟨g, B, hg, _, h₀⟩ := PowerlessMapping.exists_l hℳ φ η n
    (fun x hx => by
      by_cases h₁ : x = i
      · exact ⟨a, (h x a).mpr (Or.inl ⟨h₁, rfl⟩)⟩
      · obtain ⟨y, hy, _⟩ := hf.2 x hx
        exact ⟨y, (h x y).mpr (Or.inr ⟨h₁, hy.2⟩)⟩)
    (fun x _ y z hy hz => by
      rcases (h x y).mp hy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rcases (h x z).mp hz with ⟨_, hz⟩ | ⟨hx₀, _⟩
        · exact hy.trans hz.symm
        · exact (hx₀ hx).elim
      · rcases (h x z).mp hz with ⟨hx₀, _⟩ | ⟨_, hz⟩
        · exact (hx hx₀).elim
        · exact PowerlessFunction.value_unique_l hℳ hf hy hz)
  have h₁ : update_l f i a g := by
    intro x y
    constructor
    · intro hy
      exact (h x y).mp ((h₀ x (PowerlessFunction.value_mem_l hℳ hg hy).1 y).mp hy)
    · intro hy
      have hx : member_l ℳ x n := by
        rcases hy with ⟨hx, _⟩ | ⟨_, hy⟩
        · exact hx.symm ▸ hi
        · exact (PowerlessFunction.value_mem_l hℳ hf hy).1
      exact (h₀ x hx y).mpr ((h x y).mpr hy)
  refine ⟨g, PowerlessFunction.range_l hℳ hg ?_, h₁⟩
  intro x y hy
  rcases (h₁ x y).mp hy with ⟨_, hy⟩ | ⟨_, hy⟩
  · exact hy.symm ▸ ha
  · exact (PowerlessFunction.value_mem_l hℳ hf hy).2

theorem range_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f g i a n m A B : carrier_l ℳ} (hf : map_l f n A) (hg : map_l g m B)
    (ha : member_l ℳ a A) (h : update_l f i a g) : map_l g m A := by
  apply PowerlessFunction.range_l hℳ hg
  intro x y hy
  rcases (h x y).mp hy with ⟨_, hy⟩ | ⟨_, hy⟩
  · exact hy.symm ▸ ha
  · exact (PowerlessFunction.value_mem_l hℳ hf hy).2

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f i a g h n A : carrier_l ℳ} (hg : map_l g n A) (hh : map_l h n A)
    (hG : update_l f i a g) (hH : update_l f i a h) : g = h :=
  PowerlessFunction.ext_l hℳ hg hh (fun x _ y => (hG x y).trans (hH x y).symm)

theorem at_l {f i a g : carrier_l ℳ} (h : update_l f i a g) : value_l g i a :=
  (h i a).mpr (Or.inl ⟨rfl, rfl⟩)

theorem away_l {f i a g x y : carrier_l ℳ} (h : update_l f i a g) (hx : x ≠ i) :
    value_l g x y ↔ value_l f x y := by
  rw [h x y]
  exact ⟨fun h => h.elim (fun h => (hx h.1).elim) And.right, fun hy => Or.inr ⟨hx, hy⟩⟩

theorem length_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f n m A B : carrier_l ℳ} (hf : map_l f n A) (hg : map_l f m B) : n = m := by
  apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := hf.2 x hx
    exact (PowerlessFunction.value_mem_l hℳ hg hy.2).1
  · intro hx
    obtain ⟨y, hy, _⟩ := hg.2 x hx
    exact (PowerlessFunction.value_mem_l hℳ hf hy.2).1

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAssignmentUpdate
