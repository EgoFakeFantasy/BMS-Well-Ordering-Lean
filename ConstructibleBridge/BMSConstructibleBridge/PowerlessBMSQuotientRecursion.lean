import BMSConstructibleBridge.PowerlessBMSQuotientInduction
import BMSConstructibleBridge.PowerlessBMSQuotientArithmetic

/-!
# 图商上加法迭代的唯一性

在实际 Z₂ 图码翻译的归纳实例中比较两张递归图。图值唯一性只用商有序对的
坐标唯一性；归纳性质量化全部商对象，包括尚未证明属于 ω 的图值。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientRecursion

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SecondOrderQuotient.structure_l

universe u

variable {M : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hM : Theory.Models M SecondOrderArithmetic.theory_m}

private abbrev quotient_l := SecondOrderQuotient.structure_l hM

/-- 图的每个值都满足声明的定义域和值域；仅需有序对坐标唯一性。 -/
theorem value_mem_l {f A B x y : SecondOrderQuotient.type_l hM}
    (hf : map_l (ℳ := quotient_l) f A B) (h : value_l (ℳ := quotient_l) f x y) :
    member_l quotient_l x A ∧ member_l quotient_l y B := by
  obtain ⟨p, hp, hpair⟩ := h
  obtain ⟨z, w, hz, hw, hpair'⟩ := hf.1 p hp
  obtain ⟨rfl, rfl⟩ := (SecondOrderPairObjects.ordered_eq_l hM hpair hpair').mp rfl
  exact ⟨hz, hw⟩

/-- 任意商函数图的值唯一性，不要求完整集合论公理。 -/
theorem value_unique_l {f A B x y z : SecondOrderQuotient.type_l hM}
    (hf : map_l (ℳ := quotient_l) f A B)
    (hy : value_l (ℳ := quotient_l) f x y) (hz : value_l (ℳ := quotient_l) f x z) :
    y = z := by
  have hxy := value_mem_l hf hy
  have hxz := value_mem_l hf hz
  obtain ⟨w, _, hw⟩ := hf.2 x hxy.1
  exact (hw y ⟨hxy.2, hy⟩).trans (hw z ⟨hxz.2, hz⟩).symm

/-- 相同对象的两个集合后继外延相等。 -/
theorem successor_unique_l {a b c : SecondOrderQuotient.type_l hM}
    (hb : PowerlessNatural.successor_l (ℳ := quotient_l) a b)
    (hc : PowerlessNatural.successor_l (ℳ := quotient_l) a c) : b = c :=
  SecondOrderQuotient.ext_l hM b c fun x => (hb x).trans (hc x).symm

/-- 同域商函数图由逐点值关系决定，不使用 Collection。 -/
theorem map_ext_l {f g A B D : SecondOrderQuotient.type_l hM}
    (hf : map_l (ℳ := quotient_l) f A B) (hg : map_l (ℳ := quotient_l) g A D)
    (h : ∀ x y, value_l (ℳ := quotient_l) f x y ↔ value_l (ℳ := quotient_l) g x y) :
    f = g := by
  apply SecondOrderQuotient.ext_l hM
  intro p
  constructor
  · intro hp
    obtain ⟨x, y, _, _, hpair⟩ := hf.1 p hp
    obtain ⟨q, hq, hpair'⟩ := (h x y).mp ⟨p, hp, hpair⟩
    exact (SecondOrderPairObjects.ordered_unique_l hM hpair hpair').symm ▸ hq
  · intro hp
    obtain ⟨x, y, _, _, hpair⟩ := hg.1 p hp
    obtain ⟨q, hq, hpair'⟩ := (h x y).mpr ⟨p, hp, hpair⟩
    exact (SecondOrderPairObjects.ordered_unique_l hM hpair hpair').symm ▸ hq

/-- 两张图在指定输入处的全部值一致；自由参数依次为输入、第一图、第二图。 -/
def agreement_m : Formula ℒ [] [.set, .set, .set] :=
  .forallE .set (.forallE .set (.imp
    (SecondOrderObjectSyntax.value_m (.fvar (.there .here)) (.fvar .here)
      (.bvar (.there .here)))
    (.imp (SecondOrderObjectSyntax.value_m (.fvar (.there (.there .here)))
      (.fvar .here) (.bvar .here)) (.equal (.bvar (.there .here)) (.bvar .here)))))

/-- 每个比较公式的实际二阶翻译都有原推导核中的归纳证明。 -/
theorem agreement_induction_m :
    Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.induction_m (GraphTranslation.form_m agreement_m)) :=
  GraphTranslation.induction_m agreement_m

theorem agreement_formula_l (f g n : SecondOrderQuotient.type_l hM) :
    agreement_m.satisfies
      ((((Env.empty (M := quotient_l)).pushFree g).pushFree f).pushFree n) ↔
      ∀ x y, value_l (ℳ := quotient_l) f n x → value_l (ℳ := quotient_l) g n y → x = y := by
  simp only [agreement_m, Formula.satisfies, value_formula_l]
  rfl

/-- 任意加法迭代图逐点相容；证明范围是原模型的全部内部自然数。 -/
theorem addition_agreement_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    {a f g : SecondOrderQuotient.type_l hM}
    (hf : PowerlessAddition.iteration_l (ℳ := quotient_l) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val a f)
    (hg : PowerlessAddition.iteration_l (ℳ := quotient_l) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val a g)
    (n : SecondOrderModel.num_l M) (x y : SecondOrderQuotient.type_l hM)
    (hx : value_l (ℳ := quotient_l) f (PowerlessBMSQuotientCoding.numberCode_l C n).val x)
    (hy : value_l (ℳ := quotient_l) g (PowerlessBMSQuotientCoding.numberCode_l C n).val y) :
    x = y := by
  obtain ⟨B, hF, hf₀, hf₁⟩ := hf
  obtain ⟨D, hG, hg₀, hg₁⟩ := hg
  have h := PowerlessBMSQuotientInduction.induction_l C agreement_m
    (((Env.empty (M := quotient_l)).pushFree g).pushFree f) ?_ ?_ n
  · exact (agreement_formula_l f g _).mp h x y hx hy
  · apply (agreement_formula_l f g _).mpr
    intro x y hx hy
    exact (value_unique_l hF hx hf₀).trans (value_unique_l hG hy hg₀).symm
  · intro k hk
    apply (agreement_formula_l f g _).mpr
    intro x y hx hy
    obtain ⟨v, hv, _⟩ := hF.2 _ (PowerlessBMSQuotientCoding.numberCode_l C k).property
    obtain ⟨w, hw, _⟩ := hG.2 _ (PowerlessBMSQuotientCoding.numberCode_l C k).property
    have hvw := (agreement_formula_l f g _).mp hk v w hv.2 hw.2
    subst w
    exact successor_unique_l
      ((PowerlessAddition.step_formula_l C.omega v x).mp
        (hf₁ _ _ v x (PowerlessBMSQuotientCoding.numberCode_l C k).property
          (PowerlessBMSQuotientSuccessor.successor_l C k) hv.2 hx))
      ((PowerlessAddition.step_formula_l C.omega v y).mp
        (hg₁ _ _ v y (PowerlessBMSQuotientCoding.numberCode_l C k).property
          (PowerlessBMSQuotientSuccessor.successor_l C k) hw.2 hy))

/-- 纯集合加法关系没有额外输出；输出无需预先假定属于 ω。 -/
theorem addition_iff_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    (a b : SecondOrderModel.num_l M) (c : SecondOrderQuotient.type_l hM) :
    PowerlessAddition.addition_l (ℳ := quotient_l) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val
      (PowerlessBMSQuotientCoding.numberCode_l C a).val
      (PowerlessBMSQuotientCoding.numberCode_l C b).val c ↔
      c = (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.add_l a b)).val := by
  constructor
  · rintro ⟨f, hf, hc⟩
    obtain ⟨g, hg, hd⟩ := PowerlessBMSQuotientArithmetic.additionInstance_l C a b
    exact addition_agreement_l C hf hg b _ _ hc hd
  · rintro rfl
    exact PowerlessBMSQuotientArithmetic.additionInstance_l C a b

/-- 初值可为任意商对象；自然数输入处的两个加法输出相等。 -/
theorem addition_unique_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    {a b c d : SecondOrderQuotient.type_l hM} (hb : member_l quotient_l b C.omega)
    (hc : PowerlessAddition.addition_l (ℳ := quotient_l) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val a b c)
    (hd : PowerlessAddition.addition_l (ℳ := quotient_l) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val a b d) :
    c = d := by
  obtain ⟨n, hn⟩ := PowerlessBMSQuotientCoding.numberCode_surjective_l C ⟨b, hb⟩
  have hn' : (PowerlessBMSQuotientCoding.numberCode_l C n).val = b := congrArg Subtype.val hn
  obtain ⟨f, hf, hc⟩ := hc
  obtain ⟨g, hg, hd⟩ := hd
  rw [← hn'] at hc hd
  exact addition_agreement_l C hf hg n c d hc hd

/-- 同一自映射的两张迭代图在全部内部自然数处相容。 -/
theorem function_agreement_l (C : PowerlessBMSQuotientCoding.source_coding_l hM)
    {A H a f g : SecondOrderQuotient.type_l hM}
    (hH : map_l (ℳ := quotient_l) H A A)
    (hf : PowerlessFunctionIteration.iteration_l (ℳ := quotient_l) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val A H a f)
    (hg : PowerlessFunctionIteration.iteration_l (ℳ := quotient_l) C.omega
      (PowerlessBMSQuotientCoding.numberCode_l C (SecondOrderModel.zero_l M)).val A H a g)
    (n : SecondOrderModel.num_l M) (x y : SecondOrderQuotient.type_l hM)
    (hx : value_l (ℳ := quotient_l) f (PowerlessBMSQuotientCoding.numberCode_l C n).val x)
    (hy : value_l (ℳ := quotient_l) g (PowerlessBMSQuotientCoding.numberCode_l C n).val y) :
    x = y := by
  have h := PowerlessBMSQuotientInduction.induction_l C agreement_m
    (((Env.empty (M := quotient_l)).pushFree g).pushFree f) ?_ ?_ n
  · exact (agreement_formula_l f g _).mp h x y hx hy
  · apply (agreement_formula_l f g _).mpr
    intro x y hx hy
    exact (value_unique_l hf.1 hx hf.2.1).trans (value_unique_l hg.1 hy hg.2.1).symm
  · intro k hk
    apply (agreement_formula_l f g _).mpr
    intro x y hx hy
    obtain ⟨v, hv, _⟩ := hf.1.2 _ (PowerlessBMSQuotientCoding.numberCode_l C k).property
    obtain ⟨w, hw, _⟩ := hg.1.2 _ (PowerlessBMSQuotientCoding.numberCode_l C k).property
    have hvw := (agreement_formula_l f g _).mp hk v w hv.2 hw.2
    subst w
    exact value_unique_l hH
      (hf.2.2 _ _ v x (PowerlessBMSQuotientCoding.numberCode_l C k).property
        (PowerlessBMSQuotientSuccessor.successor_l C k) hv.2 hx)
      (hg.2.2 _ _ v y (PowerlessBMSQuotientCoding.numberCode_l C k).property
        (PowerlessBMSQuotientSuccessor.successor_l C k) hw.2 hy)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessBMSQuotientRecursion
