import BMSConstructibleBridge.PowerlessFunctionIterationUnique
import BMSConstructibleBridge.PowerlessAdditionBounds

/-!
# 同一内部自然数域上的乘法图

先把 x ↦ x+a 构造成内部 ω 的实际自映射，再从内部零迭代。
所有因子及递归次数都允许是非标准自然数。乘法不是宿主 Nat 上的计算结果，
也不将一张尚未构造的递归图列为背景假设。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMultiplication

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 加上固定右项的实际函数图；域外没有额外图值。 -/
def operator_l (ω e a H : carrier_l ℳ) : Prop :=
  map_l H ω ω ∧ ∀ x y, value_l H x y ↔
    member_l ℳ x ω ∧ PowerlessAddition.addition_l ω e x a y

def operator_m {Γ Δ : SortContext ℒ} (ω e a H : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .conj (SecondOrderObjectSyntax.map_m H ω ω) (.forallE .set (.forallE .set (.iff
    (SecondOrderObjectSyntax.value_m (w H) (.bvar (.there .here)) (.bvar .here))
    (.conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (w ω))
      (PowerlessAdditionSyntax.addition_m (w ω) (w e) (.bvar (.there .here)) (w a) (.bvar .here))))))

theorem operator_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e a H : Term ℒ Γ Δ .set) :
    (operator_m ω e a H).satisfies η ↔ operator_l (ω.eval η) (e.eval η) (a.eval η) (H.eval η) := by
  simp only [operator_m, operator_l, Formula.satisfies, map_formula_l, value_formula_l,
    PowerlessAdditionSyntax.addition_formula_l, SecondOrderObjectSyntax.member_m,
    Arguments.eval, Term.eval_weakenBound]
  rfl

theorem operator_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) : ∃ H, operator_l ω e a H := by
  let η : SetTheory.Env (SetTheory.Definitional.Project.FirstOrderSemantics.reduct ℳ) 3 :=
    { bound := Fin.cases ω (Fin.cases e (fun _ => a)), free := fun _ => ω }
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    PowerlessAdditionSyntax.addition_m (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))
      (.fvar (.there (.there (.there (.there .here))))) (.fvar .here)
  have h : ∀ x y, φ.satisfies (((PowerlessComprehension.env_l η).pushFree x).pushFree y) ↔
      PowerlessAddition.addition_l ω e x a y := fun x y =>
    PowerlessAdditionSyntax.addition_formula_l _ _ _ _ _ _
  obtain ⟨H, B, hH, _, hV⟩ := PowerlessMapping.exists_l hℳ φ η ω
    (fun x hx => by
      obtain ⟨y, _, hy⟩ := PowerlessAddition.exists_l hℳ hω he hx ha
      exact ⟨y, (h x y).mpr hy⟩)
    (fun x _ y z hy hz => PowerlessAddition.unique_l hℳ hω he ((h x y).mp hy) ((h x z).mp hz))
  have hG : ∀ x y, value_l H x y ↔ member_l ℳ x ω ∧ PowerlessAddition.addition_l ω e x a y := by
    intro x y
    constructor
    · intro hy
      have hx := (PowerlessFunction.value_mem_l hℳ hH hy).1
      exact ⟨hx, (h x y).mp ((hV x hx y).mp hy)⟩
    · rintro ⟨hx, hy⟩
      exact (hV x hx y).mpr ((h x y).mpr hy)
  exact ⟨H, PowerlessFunction.range_l hℳ hH (fun x y hy =>
    PowerlessAdditionBounds.output_l hℳ hω he ((hG x y).mp hy).1 ((hG x y).mp hy).2), hG⟩

theorem operator_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a H K : carrier_l ℳ} (hH : operator_l ω e a H) (hK : operator_l ω e a K) : H = K :=
  PowerlessFunction.ext_l hℳ hH.1 hK.1 (fun x _ y => (hH.2 x y).trans (hK.2 x y).symm)

/-- 左因子 a、右因子 b 的乘积由同一加法自映射的第 b 次迭代给出。 -/
def multiplication_l (ω e a b c : carrier_l ℳ) : Prop :=
  ∃ H f, operator_l ω e a H ∧ PowerlessFunctionIteration.iteration_l ω e ω H e f ∧ value_l f b c

def multiplication_m {Γ Δ : SortContext ℒ} (ω e a b c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj (operator_m (w ω) (w e) (w a) (.bvar (.there .here)))
    (.conj (PowerlessFunctionIteration.iteration_m (w ω) (w e) (w ω) (.bvar (.there .here))
      (w e) (.bvar .here)) (SecondOrderObjectSyntax.value_m (.bvar .here) (w b) (w c)))))

theorem multiplication_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω e a b c : Term ℒ Γ Δ .set) :
    (multiplication_m ω e a b c).satisfies η ↔
      multiplication_l (ω.eval η) (e.eval η) (a.eval η) (b.eval η) (c.eval η) := by
  simp only [multiplication_m, multiplication_l, Formula.satisfies, operator_formula_l,
    PowerlessFunctionIteration.iteration_formula_l, value_formula_l, Term.eval_weakenBound]
  rfl

theorem exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (ha : member_l ℳ a ω) (hb : member_l ℳ b ω) :
    ∃ c, member_l ℳ c ω ∧ multiplication_l ω e a b c := by
  obtain ⟨H, hH⟩ := operator_exists_l hℳ hω he ha
  obtain ⟨f, hf⟩ := PowerlessFunctionIteration.exists_l hℳ hω he hH.1
    (PowerlessNatural.zero_mem_l hℳ hω he)
  obtain ⟨c, hc, _⟩ := hf.1.2 b hb
  exact ⟨c, hc.1, H, f, hH, hf, hc.2⟩

theorem unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c d : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hc : multiplication_l ω e a b c) (hd : multiplication_l ω e a b d) : c = d := by
  obtain ⟨H, f, hH, hf, hc⟩ := hc
  obtain ⟨K, g, hK, hg, hd⟩ := hd
  have h := operator_unique_l hℳ hH hK
  subst K
  have h := PowerlessFunctionIteration.unique_l hℳ hω he hH.1 hf hg
  subst g
  exact PowerlessFunction.value_unique_l hℳ hf.1 hc hd

theorem natural_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a b c : carrier_l ℳ} (h : multiplication_l ω e a b c) :
    member_l ℳ b ω ∧ member_l ℳ c ω := by
  obtain ⟨_, _, _, hf, hc⟩ := h
  exact PowerlessFunction.value_mem_l hℳ hf.1 hc

theorem zero_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a c : carrier_l ℳ} (h : multiplication_l ω e a e c) : c = e := by
  obtain ⟨_, _, _, hf, hc⟩ := h
  exact PowerlessFunction.value_unique_l hℳ hf.1 hc hf.2.1

theorem successor_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e a n m c d : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (hn : member_l ℳ n ω) (hm : PowerlessNatural.successor_l n m)
    (hc : multiplication_l ω e a n c) (hd : multiplication_l ω e a m d) :
    PowerlessAddition.addition_l ω e c a d := by
  obtain ⟨H, f, hH, hf, hc⟩ := hc
  obtain ⟨K, g, hK, hg, hd⟩ := hd
  have h := operator_unique_l hℳ hH hK
  subst K
  have h := PowerlessFunctionIteration.unique_l hℳ hω he hH.1 hf hg
  subst g
  exact ((hH.2 c d).mp (hf.2.2 n m c d hn hm hc hd)).2

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMultiplication
