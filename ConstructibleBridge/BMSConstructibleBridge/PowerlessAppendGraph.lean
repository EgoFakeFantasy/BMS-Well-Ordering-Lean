import BMSConstructibleBridge.PowerlessRestriction
import BMSConstructibleBridge.PowerlessNaturalStep

/-! # 向内部函数图追加一个坐标 -/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessAppendGraph

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def append_l (f n a g : carrier_l ℳ) : Prop :=
  ∀ p, member_l ℳ p g ↔ member_l ℳ p f ∨ ordered_l n a p

def append_m {Γ Δ : SortContext ℒ} (f n a g : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (SecondOrderObjectSyntax.member_m (.bvar .here) (g.weakenBound SetTheory.SetSort.set))
    (.disj (SecondOrderObjectSyntax.member_m (.bvar .here) (f.weakenBound SetTheory.SetSort.set))
      (SecondOrderObjectSyntax.ordered_m (n.weakenBound SetTheory.SetSort.set)
        (a.weakenBound SetTheory.SetSort.set) (.bvar .here))))

theorem append_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f n a g : Term ℒ Γ Δ .set) :
    (append_m f n a g).satisfies η ↔ append_l (f.eval η) (n.eval η) (a.eval η) (g.eval η) := by
  simp only [append_m, append_l, Formula.satisfies, ordered_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (f n a : carrier_l ℳ) : ∃ g, append_l f n a g := by
  obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ n a
  obtain ⟨E, hE⟩ := PowerlessBasic.pairing_l hℳ p p
  obtain ⟨F, hF⟩ := PowerlessBasic.pairing_l hℳ f E
  obtain ⟨g, hg⟩ := PowerlessBasic.union_l hℳ F
  refine ⟨g, fun q => (hg q).trans ?_⟩
  constructor
  · rintro ⟨B, hB, hq⟩
    rcases (hF B).mp hB with hB | hB
    · subst B
      exact Or.inl hq
    · subst B
      have h₀ : q = p := (hE q).mp hq |>.elim id id
      exact Or.inr (h₀.symm ▸ hp)
  · rintro (hq | hq)
    · exact ⟨f, (hF f).mpr (Or.inl rfl), hq⟩
    · have h₀ := PowerlessBasic.ordered_unique_l hℳ hq hp
      exact ⟨E, (hF E).mpr (Or.inr rfl), (hE q).mpr (Or.inl h₀)⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f n a g h : carrier_l ℳ} (hg : append_l f n a g) (hh : append_l f n a h) : g = h :=
  (PowerlessTheory.ext_l hℳ).eq_of_same_members g h (fun p => (hg p).trans (hh p).symm)

theorem value_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f n a g x y : carrier_l ℳ} (hg : append_l f n a g) :
    ThirdOrderSemantics.value_l g x y ↔ ThirdOrderSemantics.value_l f x y ∨ x = n ∧ y = a := by
  constructor
  · rintro ⟨p, hp, h₀⟩
    rcases (hg p).mp hp with hp | hp
    · exact Or.inl ⟨p, hp, h₀⟩
    · exact Or.inr ((PowerlessBasic.ordered_eq_l hℳ h₀ hp).mp rfl)
  · rintro (⟨p, hp, h₀⟩ | ⟨hx, hy⟩)
    · exact ⟨p, (hg p).mpr (Or.inl hp), h₀⟩
    · subst x
      subst y
      obtain ⟨p, hp⟩ := PowerlessBasic.ordered_exists_l hℳ n a
      exact ⟨p, (hg p).mpr (Or.inr hp), hp⟩

theorem map_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f n a g m A : carrier_l ℳ} (hf : ThirdOrderSemantics.map_l f n A) (ha : member_l ℳ a A)
    (hm : PowerlessNatural.successor_l n m) (hg : append_l f n a g) : ThirdOrderSemantics.map_l g m A := by
  have h₀ : ¬member_l ℳ n n := fun h => PowerlessNatural.asymmetry_l hℳ h h
  constructor
  · intro p hp
    rcases (hg p).mp hp with hp | hp
    · obtain ⟨x, y, hx, hy, h₁⟩ := hf.1 p hp
      exact ⟨x, y, (hm x).mpr (Or.inl hx), hy, h₁⟩
    · exact ⟨n, a, (hm n).mpr (Or.inr rfl), ha, hp⟩
  · intro x hx
    have h₁ : ∀ y z, ThirdOrderSemantics.value_l g x y → ThirdOrderSemantics.value_l g x z → y = z := by
      intro y z hy hz
      rcases (value_l hℳ hg).mp hy with hy | ⟨hx₀, hy⟩
      · rcases (value_l hℳ hg).mp hz with hz | ⟨hx₀, _⟩
        · exact PowerlessFunction.value_unique_l hℳ hf hy hz
        · exact (h₀ (hx₀ ▸ (PowerlessFunction.value_mem_l hℳ hf hy).1)).elim
      · rcases (value_l hℳ hg).mp hz with hz | ⟨_, hz⟩
        · exact (h₀ (hx₀ ▸ (PowerlessFunction.value_mem_l hℳ hf hz).1)).elim
        · exact hy.trans hz.symm
    rcases (hm x).mp hx with hx | hx
    · obtain ⟨y, hy, _⟩ := hf.2 x hx
      have hy₀ := (value_l hℳ hg).mpr (Or.inl hy.2)
      exact ⟨y, ⟨hy.1, hy₀⟩, fun z hz => h₁ z y hz.2 hy₀⟩
    · have hy := (value_l hℳ hg).mpr (Or.inr ⟨hx, rfl⟩)
      exact ⟨a, ⟨ha, hy⟩, fun z hz => h₁ z a hz.2 hy⟩

theorem decompose_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {g n m A : carrier_l ℳ} (hg : ThirdOrderSemantics.map_l g m A) (hm : PowerlessNatural.successor_l n m) :
    ∃ f a, ThirdOrderSemantics.map_l f n A ∧ member_l ℳ a A ∧ append_l f n a g := by
  obtain ⟨f, hf, hF⟩ := PowerlessRestriction.exists_l hℳ hg (fun x hx => (hm x).mpr (Or.inl hx))
  obtain ⟨a, ha, _⟩ := hg.2 n ((hm n).mpr (Or.inr rfl))
  refine ⟨f, a, hf, ha.1, ?_⟩
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, hx, _, h₀⟩ := hg.1 p hp
    rcases (hm x).mp hx with hx | hx
    · obtain ⟨q, hq, h₁⟩ := (hF x y).mpr ⟨hx, p, hp, h₀⟩
      exact Or.inl ((PowerlessBasic.ordered_unique_l hℳ h₀ h₁).symm ▸ hq)
    · subst x
      have h₁ := PowerlessFunction.value_unique_l hℳ hg ⟨p, hp, h₀⟩ ha.2
      exact Or.inr (h₁ ▸ h₀)
  · rintro (hp | hp)
    · obtain ⟨x, y, _, _, h₀⟩ := hf.1 p hp
      obtain ⟨q, hq, h₁⟩ := ((hF x y).mp ⟨p, hp, h₀⟩).2
      exact (PowerlessBasic.ordered_unique_l hℳ h₀ h₁).symm ▸ hq
    · obtain ⟨q, hq, h₀⟩ := ha.2
      exact (PowerlessBasic.ordered_unique_l hℳ hp h₀).symm ▸ hq

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessAppendGraph
