import BMSConstructibleBridge.PowerlessMultiplication
import BMSConstructibleBridge.SecondOrderArithmetic

/-!
# 纯集合模型上的双排序算术结构

数域是同一模型的内部 ω，集合域是模型中实际存在的 ω 子集，不是全部宿主谓词。
四种算术运算由已经构造的内部图给出，结构定义只消费显式运算证书。
本模块验证原九条基础公理；完整二阶理解还需逐公式翻译，不能由此直接调用
任意 Z₂ 模型中的 BMS 程序定理。未使用的 pair/start/step 槽作缺省解释，
不宣称它们已满足原算法；原具体目标已经消去这些附加符号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmetic

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

abbrev num_l (ω : carrier_l ℳ) := {a : carrier_l ℳ // member_l ℳ a ω}

abbrev set_l (ω : carrier_l ℳ) := {A : carrier_l ℳ // subset_l A ω}

/-- 运算与原内部图逐项对应；没有任意新算术函数或额外对象公理。 -/
structure operations_l (ω e : carrier_l ℳ) where
  succ_l : num_l ω → num_l ω
  add_l : num_l ω → num_l ω → num_l ω
  mul_l : num_l ω → num_l ω → num_l ω
  succ_graph_l : ∀ a, PowerlessNatural.successor_l a.val (succ_l a).val
  add_graph_l : ∀ a b, PowerlessAddition.addition_l ω e a.val b.val (add_l a b).val
  mul_graph_l : ∀ a b, PowerlessMultiplication.multiplication_l ω e a.val b.val (mul_l a b).val

/-- 存在性只在命题中打包；不通过选择固定一个全局模型或全局 ω。 -/
theorem operations_exists_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e) :
    Nonempty (operations_l ω e) := by
  have h₁ : ∀ a : num_l ω, ∃ b : num_l ω, PowerlessNatural.successor_l a.val b.val := by
    intro a
    obtain ⟨b, hb⟩ := PowerlessNatural.successor_exists_l hℳ a.val
    exact ⟨⟨b, PowerlessNatural.successor_mem_l hℳ hω a.property hb⟩, hb⟩
  have h₂ : ∀ a b : num_l ω, ∃ c : num_l ω,
      PowerlessAddition.addition_l ω e a.val b.val c.val := by
    intro a b
    obtain ⟨c, hc, h⟩ := PowerlessAddition.exists_l hℳ hω he a.property b.property
    exact ⟨⟨c, hc⟩, h⟩
  have h₃ : ∀ a b : num_l ω, ∃ c : num_l ω,
      PowerlessMultiplication.multiplication_l ω e a.val b.val c.val := by
    intro a b
    obtain ⟨c, hc, h⟩ := PowerlessMultiplication.exists_l hℳ hω he a.property b.property
    exact ⟨⟨c, hc⟩, h⟩
  choose S hS using h₁
  choose A hA using h₂
  choose M hM using h₃
  exact ⟨⟨S, A, M, hS, hA, hM⟩⟩

/-- 原图的唯一性保证全部证书给出同一组运算；存在性选取不改变算术解释。 -/
theorem operations_unique_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (F G : operations_l ω e) : F = G := by
  cases F with
  | mk S A M hS hA hM =>
    cases G with
    | mk S₁ A₁ M₁ hS₁ hA₁ hM₁ =>
      have h₁ : S = S₁ := funext fun a =>
        Subtype.ext (PowerlessNatural.successor_unique_l hℳ (hS a) (hS₁ a))
      have h₂ : A = A₁ := funext fun a => funext fun b =>
        Subtype.ext (PowerlessAddition.unique_l hℳ hω he (hA a b) (hA₁ a b))
      have h₃ : M = M₁ := funext fun a => funext fun b =>
        Subtype.ext (PowerlessMultiplication.unique_l hℳ hω he (hM a b) (hM₁ a b))
      cases h₁
      cases h₂
      cases h₃
      rfl

/-- 显式证书决定结构。实数排序没有把幂集存在性加回背景。 -/
def structure_l {ω e : carrier_l ℳ} (he : PowerlessNatural.zero_l e)
    (h₀ : member_l ℳ e ω) (F : operations_l ω e) :
    FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m where
  Carrier
    | .num => num_l ω
    | .set => set_l ω
  nonempty
    | .num => ⟨⟨e, h₀⟩⟩
    | .set => ⟨⟨e, fun x hx => (he x hx).elim⟩⟩
  funcInterp
    | .zero, .nil => ⟨e, h₀⟩
    | .succ, .cons a .nil => F.succ_l a
    | .add, .cons a (.cons b .nil) => F.add_l a b
    | .mul, .cons a (.cons b .nil) => F.mul_l a b
    | .pair, .cons _ (.cons _ .nil) => ⟨e, h₀⟩
  relInterp
    | .mem, .cons a (.cons A .nil) => member_l ℳ a.val A.val
    | .start, .cons _ (.cons _ .nil) => False
    | .step, .cons _ (.cons _ (.cons _ .nil)) => False

/-- 原九条算术／集合基础公理在同一内部域成立；本结论不含理解方案。 -/
theorem base_l (hℳ : Theory.Models ℳ PowerlessTheory.theory_m)
    {ω e : carrier_l ℳ} (hω : omega_l ω) (he : PowerlessNatural.zero_l e)
    (F : operations_l ω e) (k : SecondOrderArithmetic.base_m) :
    (SecondOrderArithmetic.sentence_m k).TrueIn
      (structure_l he (PowerlessNatural.zero_mem_l hℳ hω he) F) := by
  let z : num_l ω := ⟨e, PowerlessNatural.zero_mem_l hℳ hω he⟩
  cases k
  · change ∀ a : num_l ω, ¬F.succ_l a = z
    intro a h
    have h₀ : (F.succ_l a).val = e := congrArg Subtype.val h
    have h₁ : PowerlessNatural.successor_l a.val e := h₀ ▸ F.succ_graph_l a
    exact he a.val ((h₁ a.val).mpr (Or.inr rfl))
  · change ∀ a b : num_l ω, F.succ_l a = F.succ_l b → a = b
    intro a b h
    apply Subtype.ext
    exact PowerlessNatural.successor_injective_l hℳ (F.succ_graph_l a)
      ((congrArg Subtype.val h).symm ▸ F.succ_graph_l b)
  · change ∀ a : num_l ω, a = z ∨ ∃ b : num_l ω, a = F.succ_l b
    intro a
    rcases PowerlessNaturalStep.cases_l hℳ hω he a.val a.property with h | ⟨b, hb, h⟩
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr ⟨⟨b, hb⟩, Subtype.ext (PowerlessNatural.successor_unique_l hℳ h (F.succ_graph_l ⟨b, hb⟩))⟩
  · change ∀ a : num_l ω, F.add_l a z = a
    intro a
    exact Subtype.ext (PowerlessAddition.zero_l hℳ (F.add_graph_l a z))
  · change ∀ a b : num_l ω, F.add_l a (F.succ_l b) = F.succ_l (F.add_l a b)
    intro a b
    exact Subtype.ext (PowerlessNatural.successor_unique_l hℳ
      (PowerlessAddition.successor_l hℳ hω he b.property (F.succ_graph_l b)
        (F.add_graph_l a b) (F.add_graph_l a (F.succ_l b))) (F.succ_graph_l (F.add_l a b)))
  · change ∀ a : num_l ω, F.mul_l a z = z
    intro a
    exact Subtype.ext (PowerlessMultiplication.zero_l hℳ (F.mul_graph_l a z))
  · change ∀ a b : num_l ω, F.mul_l a (F.succ_l b) = F.add_l (F.mul_l a b) a
    intro a b
    exact Subtype.ext (PowerlessAddition.unique_l hℳ hω he
      (PowerlessMultiplication.successor_l hℳ hω he b.property (F.succ_graph_l b)
        (F.mul_graph_l a b) (F.mul_graph_l a (F.succ_l b))) (F.add_graph_l (F.mul_l a b) a))
  · change ∀ A B : set_l ω, (∀ a : num_l ω, member_l ℳ a.val A.val ↔ member_l ℳ a.val B.val) → A = B
    intro A B h
    apply Subtype.ext
    apply (PowerlessTheory.ext_l hℳ).eq_of_same_members
    intro x
    exact ⟨fun hx => (h ⟨x, A.property x hx⟩).mp hx,
      fun hx => (h ⟨x, B.property x hx⟩).mpr hx⟩
  · change ∀ A : set_l ω, (member_l ℳ e A.val ∧ ∀ a : num_l ω,
      member_l ℳ a.val A.val → member_l ℳ (F.succ_l a).val A.val) →
        ∀ a : num_l ω, member_l ℳ a.val A.val
    intro A h a
    apply hω.2 A.val _ a.val a.property
    apply (PowerlessNatural.inductive_iff_l A.val).mpr
    refine ⟨⟨e, he, h.1⟩, ?_⟩
    intro x hx
    let b : num_l ω := ⟨x, A.property x hx⟩
    exact ⟨(F.succ_l b).val, h.2 b hx, F.succ_graph_l b⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessArithmetic
