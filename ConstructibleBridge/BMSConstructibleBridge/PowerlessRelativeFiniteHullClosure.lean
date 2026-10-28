import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments
import BMSConstructibleBridge.PowerlessNaturalOrder
import BMSConstructibleBridge.PowerlessRelativeLimitClosure
import BMSConstructibleBridge.SecondOrderUnion

/-! # 从有限元素性取得实际基础操作闭包

对象语言为纯隶属 ℒ，背景和推导核均为原 Z₂。四条原公式同时保留
无序对、二元并的存在式和完整成员矩阵。存在式把见证回收到 I，矩阵
再由 I 反映到传递 W，因而取得环境中的真实规格；只有局部成员规格
不足以断言实际操作闭包。环境外延性最后识别任意同规格实际输出。

I 不须传递，也不要求 I∈W 或 W∈I。所得真实闭包可直接用于全部
内部有限赋值；这消去赋值工具的操作闭包守卫，不是完整源模型构造。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullClosure

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 绑定槽依次为实际输出、第二输入、第一输入。 -/
def pair_matrix_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set] Δ :=
  SecondOrderObjectSyntax.pair_m (.bvar (.there (.there .here)))
    (.bvar (.there .here)) (.bvar .here)

def pair_exists_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set] Δ :=
  .existsE .set (pair_matrix_m Δ)

def binary_matrix_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set] Δ :=
  PowerlessRelativeFiniteHullAssignments.binary_m (.bvar (.there (.there .here)))
    (.bvar (.there .here)) (.bvar .here)

def binary_exists_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set] Δ :=
  .existsE .set (binary_matrix_m Δ)

/-- 矩阵与存在式必须一起保留，不能仅反射存在见证。 -/
def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk ([.set, .set] : SortContext ℒ) (pair_exists_m Δ),
    Sigma.mk ([.set, .set, .set] : SortContext ℒ) (pair_matrix_m Δ),
    Sigma.mk ([.set, .set] : SortContext ℒ) (binary_exists_m Δ),
    Sigma.mk ([.set, .set, .set] : SortContext ℒ) (binary_matrix_m Δ)]

theorem family_length_m (Δ : SortContext ℒ) : (family_m Δ).length = 4 := rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def pair_at_l (U a b p : carrier_l ℳ) : Prop :=
  ∀ z, member_l ℳ z U → (member_l ℳ z p ↔ z = a ∨ z = b)

def binary_at_l (U a b c : carrier_l ℳ) : Prop :=
  ∀ z, member_l ℳ z U → (member_l ℳ z c ↔ member_l ℳ z a ∨ member_l ℳ z b)

def pair_reflection_l (I W : carrier_l ℳ) : Prop :=
  ∀ a, member_l ℳ a I → ∀ b, member_l ℳ b I →
    ((∃ p, member_l ℳ p W ∧ pair_at_l W a b p) ↔
      ∃ p, member_l ℳ p I ∧ pair_at_l I a b p)

def pair_matrix_reflection_l (I W : carrier_l ℳ) : Prop :=
  ∀ a, member_l ℳ a I → ∀ b, member_l ℳ b I → ∀ p, member_l ℳ p I →
    (pair_at_l W a b p ↔ pair_at_l I a b p)

def binary_reflection_l (I W : carrier_l ℳ) : Prop :=
  ∀ a, member_l ℳ a I → ∀ b, member_l ℳ b I →
    ((∃ c, member_l ℳ c W ∧ binary_at_l W a b c) ↔
      ∃ c, member_l ℳ c I ∧ binary_at_l I a b c)

def binary_matrix_reflection_l (I W : carrier_l ℳ) : Prop :=
  ∀ a, member_l ℳ a I → ∀ b, member_l ℳ b I → ∀ c, member_l ℳ c I →
    (binary_at_l W a b c ↔ binary_at_l I a b c)

def spec_l (I W : carrier_l ℳ) : Prop :=
  pair_reflection_l I W ∧ pair_matrix_reflection_l I W ∧
    binary_reflection_l I W ∧ binary_matrix_reflection_l I W

/-- 四条元素性实例读取同一原 I/W，不改变自由参数或绑定方向。 -/
theorem family_formula_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ ↔
      spec_l (I.eval ζ) (W.eval ζ) := by
  match I, W with
  | .bvar v, _ => nomatch v
  | .app f _, _ => nomatch f
  | _, .bvar v => nomatch v
  | _, .app f _ => nomatch f
  | .fvar v, .fvar w =>
    change (pair_reflection_l (ζ.freeVal v) (ζ.freeVal w) ∧
      pair_matrix_reflection_l (ζ.freeVal v) (ζ.freeVal w) ∧
      binary_reflection_l (ζ.freeVal v) (ζ.freeVal w) ∧
      binary_matrix_reflection_l (ζ.freeVal v) (ζ.freeVal w) ∧ True) ↔ _
    simp only [spec_l, and_true, Term.eval]

/-- 传递 W 中的局部无序对规格就是环境全域的真实规格。 -/
theorem pair_l {W a b p : carrier_l ℳ}
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := ℳ) W)
    (ha : member_l ℳ a W) (hb : member_l ℳ b W) (hp : member_l ℳ p W)
    (h : pair_at_l W a b p) : ThirdOrderSemantics.pair_l a b p := by
  intro z
  constructor
  · intro hz
    exact (h z (hW p z hp hz)).mp hz
  · intro hz
    exact (h z (hz.elim (fun hz => hz ▸ ha) (fun hz => hz ▸ hb))).mpr hz

/-- 二元并的反向成员也由输入的 W 成员性提升，不假设 I 传递。 -/
theorem binary_l {W a b c : carrier_l ℳ}
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := ℳ) W)
    (ha : member_l ℳ a W) (hb : member_l ℳ b W) (hc : member_l ℳ c W)
    (h : binary_at_l W a b c) :
    PowerlessRelativeFiniteHullAssignments.binary_l a b c := by
  intro z
  constructor
  · intro hz
    exact (h z (hW c z hc hz)).mp hz
  · intro hz
    have hzW : member_l ℳ z W := hz.elim (hW a z ha) (hW b z hb)
    exact (h z hzW).mpr hz

/-- 四式共同反射得到全部环境真实操作的闭包，而不预供 I 的闭包。 -/
theorem closure_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    {I₀ W₀ : carrier_l ℳ}
    (hPair : ∀ a b : carrier_l ℳ, ∃ p, ThirdOrderSemantics.pair_l a b p)
    (hBinary : ∀ a b : carrier_l ℳ, ∃ c,
      PowerlessRelativeFiniteHullAssignments.binary_l a b c)
    (hExt : ∀ a b : carrier_l ℳ,
      (∀ z, member_l ℳ z a ↔ member_l ℳ z b) → a = b)
    (hW : PowerlessNaturalOrder.transitive_l (ℳ := ℳ) W₀)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l W₀)
    (hIW : ThirdOrderSemantics.subset_l I₀ W₀)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    PowerlessRelativeFiniteHullAssignments.closed_l I₀ := by
  have hRead := (family_formula_l ζ I W τ).mp h
  rw [hI₀, hW₀] at hRead
  constructor
  · intro a b p ha hb hp
    obtain ⟨q, hq⟩ := hPair a b
    have hqW := hClosed.1 a b q (hIW a ha) (hIW b hb) hq
    obtain ⟨r, hrI, hr⟩ := (hRead.1 a ha b hb).mp ⟨q, hqW, fun z _ => hq z⟩
    have hrW := (hRead.2.1 a ha b hb r hrI).mpr hr
    have hr' := pair_l hW (hIW a ha) (hIW b hb) (hIW r hrI) hrW
    have hEq : p = r := hExt p r (fun z => (hp z).trans (hr' z).symm)
    exact hEq.symm ▸ hrI
  · intro a b c ha hb hc
    obtain ⟨q, hq⟩ := hBinary a b
    have hqW := hClosed.2 a b q (hIW a ha) (hIW b hb) hq
    obtain ⟨r, hrI, hr⟩ := (hRead.2.2.1 a ha b hb).mp ⟨q, hqW, fun z _ => hq z⟩
    have hrW := (hRead.2.2.2 a ha b hb r hrI).mpr hr
    have hr' := binary_l hW (hIW a ha) (hIW b hb) (hIW r hrI) hrW
    have hEq : c = r := hExt c r (fun z => (hc z).trans (hr' z).symm)
    exact hEq.symm ▸ hrI

section Quotient

variable {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 实际非零极限层已具备所需真实闭包，不预供完整源理论。 -/
theorem limit_closed_l (hℳ : Theory.Models ℳ₀ SecondOrderArithmetic.theory_m)
    {B β W : SecondOrderQuotient.type_l hℳ}
    (hB : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (hβ : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W) :
    PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) W := by
  constructor
  · intro a b p ha hb hp
    exact PowerlessRelativeLimitClosure.pair_l hℳ hB hβ hW ha hb hp
  · intro a b c ha hb hc
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ a b
    have hpW := PowerlessRelativeLimitClosure.pair_l hℳ hB hβ hW ha hb hp
    apply PowerlessRelativeLimitClosure.union_l hℳ hB hβ hW hpW
    intro z
    change ∀ z, SecondOrderQuotient.mem_l hℳ z c ↔
      SecondOrderQuotient.mem_l hℳ z a ∨ SecondOrderQuotient.mem_l hℳ z b at hc
    refine (hc z).trans ⟨?_, ?_⟩
    · rintro (hz | hz)
      · exact ⟨a, (hp a).mpr (Or.inl rfl), hz⟩
      · exact ⟨b, (hp b).mpr (Or.inr rfl), hz⟩
    · rintro ⟨y, hy, hz⟩
      rcases (hp y).mp hy with rfl | rfl
      · exact Or.inl hz
      · exact Or.inr hz

/-- 真实二元并由原环境配对、并集公理构造。 -/
theorem binary_exists_l (hℳ : Theory.Models ℳ₀ SecondOrderArithmetic.theory_m)
    (A B : SecondOrderQuotient.type_l hℳ) :
    ∃ C, PowerlessRelativeFiniteHullAssignments.binary_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) A B C := by
  obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ A B
  have hUnion := SecondOrderUnion.models_l hℳ
  change ∀ a : SecondOrderQuotient.type_l hℳ, ∃ c, ∀ z,
    SecondOrderQuotient.mem_l hℳ z c ↔ ∃ y,
      SecondOrderQuotient.mem_l hℳ y a ∧ SecondOrderQuotient.mem_l hℳ z y at hUnion
  obtain ⟨C, hC⟩ := hUnion p
  refine ⟨C, ?_⟩
  intro z
  change SecondOrderQuotient.mem_l hℳ z C ↔
    SecondOrderQuotient.mem_l hℳ z A ∨ SecondOrderQuotient.mem_l hℳ z B
  refine (hC z).trans ⟨?_, ?_⟩
  · rintro ⟨y, hy, hz⟩
    rcases (hp y).mp hy with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨A, (hp A).mpr (Or.inl rfl), hz⟩
    · exact ⟨B, (hp B).mpr (Or.inr rfl), hz⟩

/-- 同一四公式族直接给全部内部有限函数，不再索要 I 的操作闭包。 -/
theorem member_l (hℳ : Theory.Models ℳ₀ SecondOrderArithmetic.theory_m)
    (K : PowerlessBMSQuotientCoding.source_coding_l hℳ)
    {B β I₀ W₀ n A f : SecondOrderQuotient.type_l hℳ}
    (hB : ∀ x, SecondOrderQuotient.mem_l hℳ x B → ∀ y,
      SecondOrderQuotient.mem_l hℳ y x → SecondOrderQuotient.mem_l hℳ y B)
    (hβ : PowerlessRelativeHierarchySemantics.limit_l hℳ β)
    (hW : PowerlessRelativeHierarchySemantics.level_l hℳ B β W₀)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (hIW : ThirdOrderSemantics.subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hωI : ∀ x, SecondOrderQuotient.mem_l hℳ x K.omega → SecondOrderQuotient.mem_l hℳ x I₀)
    (hn : SecondOrderQuotient.mem_l hℳ n K.omega)
    (hf : ThirdOrderSemantics.map_l (ℳ := SecondOrderQuotient.structure_l hℳ) f n A)
    (hValues : PowerlessRelativeFiniteHullAssignments.values_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) I₀ f) : SecondOrderQuotient.mem_l hℳ f I₀ := by
  have hTrans : PowerlessNaturalOrder.transitive_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) W₀ :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hB hW x hx y hy
  have hClosed := closure_l ζ I W τ
    (fun a b => SecondOrderPairObjects.pair_exists_l hℳ a b) (binary_exists_l hℳ)
    (fun a b hz => SecondOrderQuotient.ext_l hℳ a b hz) hTrans
    (limit_closed_l hℳ hB hβ hW) hIW hI₀ hW₀ h
  exact PowerlessRelativeFiniteHullAssignments.member_l K hωI hClosed hn hf hValues

/-- I、W 两槽；W 的真实闭包与传递性仍显式保留，I 闭包在结论中取得。 -/
def schema_m : Formula ℒ [] [.set, .set] :=
  let I : Term ℒ [] [.set, .set] .set := .fvar .here
  let W := .fvar (.there .here)
  .imp (PowerlessNaturalOrder.transitive_m W) <|
    .imp (PowerlessRelativeFiniteHullAssignments.closed_m W) <|
      .imp (ThirdOrderTheory.subset_m I W) <|
        .imp (PowerlessRelativeFiniteElementarity.form_m (family_m []) I W
          (fun v => nomatch v)) (PowerlessRelativeFiniteHullAssignments.closed_m I)

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l (hℳ : Theory.Models ℳ₀ SecondOrderArithmetic.theory_m) :
    sentence_m.TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro ζ
  simp only [schema_m, Formula.satisfies, PowerlessNaturalOrder.transitive_formula_l,
    PowerlessRelativeFiniteHullAssignments.closed_formula_l,
    ThirdOrderSemantics.subset_formula_l]
  intro hW hClosed hIW h
  exact closure_l (Δ := []) ζ (.fvar .here) (.fvar (.there .here)) (fun v => nomatch v)
    (fun a b => SecondOrderPairObjects.pair_exists_l hℳ a b) (binary_exists_l hℳ)
    (fun a b hz => SecondOrderQuotient.ext_l hℳ a b hz) hW hClosed hIW rfl rfl h

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m sentence_m) :=
  SecondOrderAxioms.interpretation_m sentence_m (fun _ hℳ => models_l hℳ)

end Quotient

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullClosure
