import BMSConstructibleBridge.PowerlessAppendGraph

/-!
# 模型内部有限链的逐项延长

关系与载体均为实际集合。对纯公式“存在指定长度的链”作内部归纳，
每次只追加一个实际有序对；不要求自然数外部标准，也不收集无限选择序列。
延长条件须由调用者证明，本模块不将其当作背景公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteChain

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def chain_l (R A n f : carrier_l ℳ) : Prop :=
  map_l f n A ∧ ∀ i j x y, member_l ℳ i j →
    value_l f i x → value_l f j y → value_l R x y

def chain_m {Γ Δ : SortContext ℒ} (R A n f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (s : Term ℒ Γ Δ .set) :=
    (((s.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set).weakenBound
      SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.map_m f n A)
    (.forallE .set (.forallE .set (.forallE .set (.forallE .set (.imp
      (SecondOrderObjectSyntax.member_m (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))))
      (.imp (SecondOrderObjectSyntax.value_m (w f)
        (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
        (.imp (SecondOrderObjectSyntax.value_m (w f)
          (.bvar (.there (.there .here))) (.bvar .here))
          (SecondOrderObjectSyntax.value_m (w R) (.bvar (.there .here)) (.bvar .here)))))))))

theorem chain_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (R A n f : Term ℒ Γ Δ .set) :
    (chain_m R A n f).satisfies η ↔
      chain_l (R.eval η) (A.eval η) (n.eval η) (f.eval η) := by
  simp only [chain_m, chain_l, Formula.satisfies, map_formula_l, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    (R A : carrier_l ℳ) {e : carrier_l ℳ} (he : PowerlessNatural.zero_l e) :
    chain_l R A e e := by
  have hf : map_l e e A := ⟨fun p hp => (he p hp).elim, fun x hx => (he x hx).elim⟩
  exact ⟨hf, fun i _ x _ _ hx _ => (he i (PowerlessFunction.value_mem_l hℳ hf hx).1).elim⟩

theorem append_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {R A n m f a g : carrier_l ℳ} (hf : chain_l R A n f)
    (ha : member_l ℳ a A) (hm : PowerlessNatural.successor_l n m)
    (hg : PowerlessAppendGraph.append_l f n a g)
    (h : ∀ i x, value_l f i x → value_l R x a) : chain_l R A m g := by
  refine ⟨PowerlessAppendGraph.map_l hℳ hf.1 ha hm hg, ?_⟩
  intro i j x y hij hx hy
  rcases (PowerlessAppendGraph.value_l hℳ hg).mp hx with hx | ⟨rfl, rfl⟩
  · rcases (PowerlessAppendGraph.value_l hℳ hg).mp hy with hy | ⟨rfl, rfl⟩
    · exact hf.2 i j x y hij hx hy
    · exact h i x hx
  · rcases (PowerlessAppendGraph.value_l hℳ hg).mp hy with hy | ⟨rfl, rfl⟩
    · exact (PowerlessNatural.asymmetry_l hℳ hij
        (PowerlessFunction.value_mem_l hℳ hf.1 hy).1).elim
    · exact (PowerlessNatural.asymmetry_l hℳ hij hij).elim

/-- 任意内部长度的有限链存在；只要求每条已有有限链能延长。 -/
theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω R A : carrier_l ℳ} (hω : omega_l ω)
    (h : ∀ n f, member_l ℳ n ω → chain_l R A n f →
      ∃ a, member_l ℳ a A ∧ ∀ i x, value_l f i x → value_l R x a) :
    ∀ n, member_l ℳ n ω → ∃ f, chain_l R A n f := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 2 :=
    { bound := Fin.cases A (fun _ => R), free := fun _ => A }
  let φ : Formula ℒ [] [.set, .set, .set] :=
    .existsE .set (chain_m (.fvar (.there (.there .here)))
      (.fvar (.there .here)) (.fvar .here) (.bvar .here))
  have hφ : ∀ n, φ.satisfies ((PowerlessComprehension.env_l η).pushFree n) ↔
      ∃ f, chain_l R A n f := by
    intro n
    change (∃ f, (chain_m _ _ _ _).satisfies _) ↔ _
    simp only [chain_formula_l]
    rfl
  have h₀ := PowerlessNatural.induction_l hℳ φ η hω
    (fun e he => (hφ e).mpr ⟨e, zero_l hℳ R A he⟩)
    (fun n m hn hm hf => by
      obtain ⟨f, hf⟩ := (hφ n).mp hf
      obtain ⟨a, ha, h₁⟩ := h n f hn hf
      obtain ⟨g, hg⟩ := PowerlessAppendGraph.exists_l hℳ f n a
      exact (hφ m).mpr ⟨g, append_l hℳ hf ha hm hg h₁⟩)
  exact fun n hn => (hφ n).mp (h₀ n hn)

/-- 传递且处处可向上延长的非空关系，只需查看有限链的末项。 -/
theorem serial_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω R A : carrier_l ℳ} (hω : omega_l ω)
    (hA : ∃ a, member_l ℳ a A)
    (hR : ∀ x y z, value_l R x y → value_l R y z → value_l R x z)
    (h : ∀ x, member_l ℳ x A → ∃ y, member_l ℳ y A ∧ value_l R x y) :
    ∀ n, member_l ℳ n ω → ∃ f, chain_l R A n f := by
  obtain ⟨e, he⟩ := PowerlessBasic.empty_l hℳ
  apply exists_l hℳ hω
  intro n f hn hf
  rcases PowerlessNaturalStep.cases_l hℳ hω he n hn with rfl | ⟨m, _, hm⟩
  · obtain ⟨a, ha⟩ := hA
    exact ⟨a, ha, fun i x hx => (he i (PowerlessFunction.value_mem_l hℳ hf.1 hx).1).elim⟩
  · obtain ⟨x, ⟨hx, hfx⟩, _⟩ := hf.1.2 m ((hm m).mpr (Or.inr rfl))
    obtain ⟨y, hy, hxy⟩ := h x hx
    refine ⟨y, hy, ?_⟩
    intro i z hfz
    rcases (hm i).mp (PowerlessFunction.value_mem_l hℳ hf.1 hfz).1 with hi | rfl
    · exact hR z x y (hf.2 i m z x hi hfz hfx) hxy
    · have hz := PowerlessFunction.value_unique_l hℳ hf.1 hfz hfx
      exact hz ▸ hxy

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessFiniteChain
