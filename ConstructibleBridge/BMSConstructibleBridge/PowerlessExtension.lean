import BMSConstructibleBridge.PowerlessFunction

/-! # 内部函数图的一点延拓

旧定义域之外添一个输入及其指定值。所有输出仍是模型中的实际集合，
并给出全域的值关系，供有限递归轨迹保留旧方程使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessExtension

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {f A B S c d : carrier_l ℳ} (hf : map_l f A B) (hc : ¬member_l ℳ c A)
    (hS : ∀ x, member_l ℳ x S ↔ member_l ℳ x A ∨ x = c) :
    ∃ g D, map_l g S D ∧ ∀ x y, value_l g x y ↔ value_l f x y ∨ x = c ∧ y = d := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases f (Fin.cases c (fun _ => d)), free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    .disj (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here))
      (.conj (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there .here)))))
        (.equal (.fvar .here) (.fvar (.there (.there (.there (.there .here)))))))
  have h : ∀ x y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ↔
      value_l f x y ∨ x = c ∧ y = d := by
    intro x y
    simp only [φ, Formula.satisfies, value_formula_l]
    rfl
  obtain ⟨g, D, hg, _, hV⟩ := PowerlessMapping.exists_l hℳ φ η S
    (fun x hx => by
      rcases (hS x).mp hx with hx | hx
      · obtain ⟨y, hy, _⟩ := hf.2 x hx
        exact ⟨y, (h x y).mpr (Or.inl hy.2)⟩
      · exact ⟨d, (h x d).mpr (Or.inr ⟨hx, rfl⟩)⟩)
    (fun x _ y z hy hz => by
      rcases (h x y).mp hy with hy | ⟨hx, hy⟩
      · rcases (h x z).mp hz with hz | ⟨hx, _⟩
        · exact PowerlessFunction.value_unique_l hℳ hf hy hz
        · exact (hc (hx ▸ (PowerlessFunction.value_mem_l hℳ hf hy).1)).elim
      · rcases (h x z).mp hz with hz | ⟨_, hz⟩
        · exact (hc (hx ▸ (PowerlessFunction.value_mem_l hℳ hf hz).1)).elim
        · exact hy.trans hz.symm)
  refine ⟨g, D, hg, fun x y => ?_⟩
  constructor
  · intro hy
    exact (h x y).mp ((hV x (PowerlessFunction.value_mem_l hℳ hg hy).1 y).mp hy)
  · intro hy
    have hx : member_l ℳ x S := by
      apply (hS x).mpr
      rcases hy with hy | ⟨rfl, _⟩
      · exact Or.inl (PowerlessFunction.value_mem_l hℳ hf hy).1
      · exact Or.inr rfl
    exact (hV x hx y).mpr ((h x y).mpr hy)

theorem constant_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m) (A a : carrier_l ℳ) :
    ∃ f B, map_l f A B ∧ ∀ x y, value_l f x y ↔ member_l ℳ x A ∧ y = a := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 1 :=
    { bound := fun _ => a, free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .equal (.fvar .here) (.fvar (.there (.there .here)))
  have h : ∀ x y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ↔ y = a :=
    fun _ _ => Iff.rfl
  obtain ⟨f, B, hf, _, hV⟩ := PowerlessMapping.exists_l hℳ φ η A
    (fun x _ => ⟨a, (h x a).mpr rfl⟩)
    (fun x _ y z hy hz => ((h x y).mp hy).trans ((h x z).mp hz).symm)
  refine ⟨f, B, hf, fun x y => ?_⟩
  constructor
  · intro hy
    have hx := (PowerlessFunction.value_mem_l hℳ hf hy).1
    exact ⟨hx, (h x y).mp ((hV x hx y).mp hy)⟩
  · rintro ⟨hx, hy⟩
    exact (hV x hx y).mpr ((h x y).mpr hy)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessExtension
