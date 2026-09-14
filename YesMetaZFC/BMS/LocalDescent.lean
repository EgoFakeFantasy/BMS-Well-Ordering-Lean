import YesMetaZFC.BMS.WellFoundedness

/-!
# 按初始数组局部化的表示下降

每个初始高度可以使用自己的标签框架。局部下降只要求已有表示的上界随
非平凡扩张严格下降，不要求同一框架同时表示所有高度的初始数组。
最终装配仅消费各初始数组的可达性，保留原有生成关系及严格良序结论。
-/

namespace YesMetaZFC.BMS.StabilityFrame.LocalDescent

universe u

/-- 局部表示下降条件，不包含任何初始数组存在性要求。 -/
def expands_l {A : Type u} (F : StabilityFrame A) : Prop :=
  ∀ {a : ValidArray} (n : Nat) {α : A} (p : StableRepresentation F a),
    p.BoundedBy α → a.expand n ≠ a →
      ∃ β, F.lt β α ∧
        ∃ q : StableRepresentation F (a.expand n), q.BoundedBy β

/-- 有界稳定表示与局部下降给出可达性；不需要数组已生成。 -/
theorem acc_l {A : Type u} {F : StabilityFrame A}
    (h : expands_l F) {a : ValidArray} {α : A}
    (p : StableRepresentation F a) (hα : p.BoundedBy α) : Acc Step a := by
  have h₀ := F.lt_wellFounded.apply α
  induction h₀ generalizing a with
  | intro α _ hᵢ =>
      apply Acc.intro a
      intro b h₁
      rcases h₁.1 with ⟨n, h₂⟩
      subst b
      rcases h n p hα h₁.2 with ⟨β, hβ, q, hq⟩
      exact hᵢ β hβ q hq

/-- 各初始数组分别可达，便足以保证整个生成关系良基。 -/
theorem wf_l (h : ∀ n, Acc Step (validSeed n)) :
    WellFounded GeneratedStep := by
  have h₀ : ∀ {a : ValidArray}, Generated a → Acc Step a := by
    intro a h₁
    induction h₁ with
    | seed n => exact h n
    | @expand a _ n hᵢ =>
        by_cases h₂ : a.expand n = a
        · simpa only [h₂] using hᵢ
        · exact hᵢ.inv ⟨⟨n, rfl⟩, h₂⟩
  exact ⟨fun a => InvImage.accessible Subtype.val (h₀ a.2)⟩

/-- 生成子类型上的良基性可沿扩张封闭性还原为原数组的可达性。 -/
theorem acc_generated_l (h : WellFounded GeneratedStep) (a : GeneratedArray) :
    Acc Step a.1 := by
  have h₀ := h.apply a
  induction h₀ with
  | intro a _ hᵢ =>
      apply Acc.intro a.1
      intro b h₁
      exact hᵢ ⟨b, generated_of_step a.2 h₁⟩ h₁

/-- 一步良基性与既有共同初始数组路径给出严格良序，不附加可比性假设。 -/
theorem wellOrder_of_wf_l (h : WellFounded GeneratedStep) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent := by
  refine ⟨h.transGen,
    RepresentationDescentSystem.generatedStrictDescent_transitive, ?_⟩
  intro a b
  rcases generated_iff_seed_path.mp a.2 with ⟨n, p⟩
  rcases generated_iff_seed_path.mp b.2 with ⟨m, q⟩
  have p₀ : ExpansionPath (validSeed (max n m)) (validSeed n) :=
    RepresentationDescentSystem.expansionPath_validSeed_of_le (Nat.le_max_left _ _)
  have q₀ : ExpansionPath (validSeed (max n m)) (validSeed m) :=
    RepresentationDescentSystem.expansionPath_validSeed_of_le (Nat.le_max_right _ _)
  have h₀ := acc_generated_l h ⟨validSeed (max n m), .seed (max n m)⟩
  rcases expansionPath_endpoints_comparable_of_accessible h₀
      (p₀.trans p) (q₀.trans q) with h₁ | h₁ | h₁
  · exact Or.inl (Subtype.ext h₁)
  · exact Or.inr (Or.inl
      (RepresentationDescentSystem.generatedStrictDescent_of_strictDescent b.2 h₁))
  · exact Or.inr (Or.inr
      (RepresentationDescentSystem.generatedStrictDescent_of_strictDescent a.2 h₁))

/-- 各高度的局部可达性共同给出原 BM4 严格良序结论。 -/
theorem wellOrder_l (h : ∀ n, Acc Step (validSeed n)) :
    StrictWellOrder GeneratedArray GeneratedStrictDescent :=
  wellOrder_of_wf_l (wf_l h)

/-- 一步良基性排除生成数组上的无限下降链。 -/
theorem no_descent_of_wf_l (h : WellFounded GeneratedStep) :
    ¬ ∃ f : Nat → GeneratedArray,
      ∀ n, GeneratedStep (f (n + 1)) (f n) := by
  have h₀ : ∀ {a : GeneratedArray}, Acc GeneratedStep a →
      ∀ f : Nat → GeneratedArray, f 0 = a →
        (∀ n, GeneratedStep (f (n + 1)) (f n)) → False := by
    intro a h₁
    induction h₁ with
    | intro a _ hᵢ =>
        intro f h₂ h₃
        have h₄ : GeneratedStep (f 1) a := by
          rw [← h₂]
          exact h₃ 0
        apply hᵢ (f 1) h₄ (fun n => f (n + 1)) rfl
        intro n
        simpa only [Nat.add_assoc] using h₃ (n + 1)
  rintro ⟨f, h₁⟩
  exact h₀ (h.apply (f 0)) f rfl h₁

/-- 按高度分别证明可达性后，所有 BM4 生成数组都没有无限下降链。 -/
theorem no_descent_l (h : ∀ n, Acc Step (validSeed n)) :
    ¬ ∃ f : Nat → GeneratedArray,
      ∀ n, GeneratedStep (f (n + 1)) (f n) :=
  no_descent_of_wf_l (wf_l h)

end YesMetaZFC.BMS.StabilityFrame.LocalDescent
