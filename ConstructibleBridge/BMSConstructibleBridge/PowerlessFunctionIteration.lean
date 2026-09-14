import BMSConstructibleBridge.PowerlessRecursionSyntax

/-!
# 实际自映射的内部自然数迭代

把 H:A→A 在域外以初值总化，以已有纯公式递归实际构造迭代图。
再用内部归纳证明全部值始终留在 A，因而真实轨迹从不使用缺省分支。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionIteration

open Logic FirstOrder ThirdOrderSemantics PowerlessNatural

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def step_m {Γ Δ : SortContext ℒ} (H A a x y : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .disj (.conj (SecondOrderObjectSyntax.member_m x A) (SecondOrderObjectSyntax.value_m H x y))
    (.conj (.neg (SecondOrderObjectSyntax.member_m x A)) (.equal y a))

theorem step_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (H A a x y : Term ℒ Γ Δ .set) :
    (step_m H A a x y).satisfies η ↔
      (member_l ℳ (x.eval η) (A.eval η) ∧ value_l (H.eval η) (x.eval η) (y.eval η)) ∨
      (¬member_l ℳ (x.eval η) (A.eval η) ∧ y.eval η = a.eval η) := by
  simp only [step_m, Formula.satisfies, SecondOrderObjectSyntax.member_m, Arguments.eval, value_formula_l]
  rfl

def iteration_l (ω e A H a f : carrier_l ℳ) : Prop :=
  map_l f ω A ∧ value_l f e a ∧ ∀ n m x y, member_l ℳ n ω → successor_l n m →
    value_l f n x → value_l f m y → value_l H x y

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e A H a : carrier_l ℳ} (hω : omega_l ω) (he : zero_l e) (hH : map_l H A A)
    (ha : member_l ℳ a A) : ∃ f, iteration_l ω e A H a f := by
  classical
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases H (Fin.cases A (fun _ => a)), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    step_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.fvar (.there .here)) (.fvar .here)
  have h : ∀ x y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ↔
      (member_l ℳ x A ∧ value_l H x y) ∨ (¬member_l ℳ x A ∧ y = a) :=
    fun x y => step_formula_l _ _ _ _ _ _
  obtain ⟨f, B, hf, hF, h₀⟩ := PowerlessOmegaRecursion.exists_l hℳ φ η
    (fun x => by
      by_cases hx : member_l ℳ x A
      · obtain ⟨y, hy, _⟩ := hH.2 x hx
        exact ⟨y, (h x y).mpr (Or.inl ⟨hx, hy.2⟩)⟩
      · exact ⟨a, (h x a).mpr (Or.inr ⟨hx, rfl⟩)⟩)
    (fun x y z hy hz => by
      rcases (h x y).mp hy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rcases (h x z).mp hz with ⟨_, hz⟩ | ⟨hz, _⟩
        · exact PowerlessFunction.value_unique_l hℳ hH hy hz
        · exact (hz hx).elim
      · rcases (h x z).mp hz with ⟨hz, _⟩ | ⟨_, hz⟩
        · exact (hx hz).elim
        · exact hy.trans hz.symm) hω he a
  let ξ : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases f (fun _ => A), free := fun _ => ω }
  let ψ : Formula ℒ [] [.set, .set, .set] :=
    .forallE .set (.imp (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (.fvar (.there (.there .here)))))
  have h₁ : ∀ n, ψ.satisfies ((PowerlessComprehension.env_l ξ).pushFree n) ↔
      ∀ x, value_l f n x → member_l ℳ x A := by
    intro n
    simp only [ψ, Formula.satisfies, value_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval]
    rfl
  have h₂ := PowerlessNatural.induction_l hℳ ψ ξ hω
    (fun z hz => (h₁ z).mpr (by
      have h₃ := zero_unique_l hℳ hz he
      subst z
      intro x hx
      exact (PowerlessFunction.value_unique_l hℳ hf hx hF).symm ▸ ha))
    (fun n m hn hm h₃ => (h₁ m).mpr (by
      intro y hy
      obtain ⟨x, hx, _⟩ := hf.2 n hn
      have h₄ := (h₁ n).mp h₃ x hx.2
      rcases (h x y).mp (h₀ n m x y hn hm hx.2 hy) with ⟨_, hy⟩ | ⟨hy, _⟩
      · exact (PowerlessFunction.value_mem_l hℳ hH hy).2
      · exact (hy h₄).elim))
  have h₃ : ∀ n x, value_l f n x → member_l ℳ x A :=
    fun n x hx => (h₁ n).mp (h₂ n (PowerlessFunction.value_mem_l hℳ hf hx).1) x hx
  refine ⟨f, PowerlessFunction.range_l hℳ hf h₃, hF, ?_⟩
  intro n m x y hn hm hx hy
  exact ((h x y).mp (h₀ n m x y hn hm hx hy)).elim And.right (fun h₄ => (h₄.1 (h₃ n x hx)).elim)

def iteration_m {Γ Δ : SortContext ℒ} (ω e A H a f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) :=
    (((t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.map_m f ω A) (.conj (SecondOrderObjectSyntax.value_m f e a)
    (.forallE .set (.forallE .set (.forallE .set (.forallE .set (.imp
      (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here)))) (w ω)) (.imp
        (PowerlessNaturalStep.successor_m (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))) (.imp
          (SecondOrderObjectSyntax.value_m (w f) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here))) (.imp
            (SecondOrderObjectSyntax.value_m (w f) (.bvar (.there (.there .here))) (.bvar .here))
            (SecondOrderObjectSyntax.value_m (w H) (.bvar (.there .here)) (.bvar .here)))))))))))

theorem iteration_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e A H a f : Term ℒ Γ Δ .set) :
    (iteration_m ω e A H a f).satisfies η ↔
      iteration_l (ω.eval η) (e.eval η) (A.eval η) (H.eval η) (a.eval η) (f.eval η) := by
  simp only [iteration_m, iteration_l, Formula.satisfies, map_formula_l, value_formula_l,
    PowerlessNaturalStep.successor_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFunctionIteration
