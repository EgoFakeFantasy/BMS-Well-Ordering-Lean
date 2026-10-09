import BMSConstructibleBridge.PowerlessMemberStructure
import BMSConstructibleBridge.PowerlessMemberDefSyntax
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 实际成员塌缩的关系式原公式运输

纯隶属 ℒ 没有函数符号。两个结构间的关系只需双向全域、保持并反映
等式及隶属，即可在已给的相关环境间运输每个外部原 Formula 的真值。
量词分支逐次在 Prop 中取得相关见证，不从原集合图抽取 Type 同构。

原 Z₂ 模型中的实际 H:I→T 用 map、onto、injective 和成员双向保持
实例化上述关系。原 global_m 的全部量词在 MemberI 与 MemberT 内部
解释，包括其隐藏的 ω、空对象和全内部赋值，不将非传递 I 的内部 Def
替换成完整 ambient Def(I)。本模块是后续原对象推导装配的语义中间核，
不是内部统一真值、凝聚、Class 资格或 BMS 终局的对象证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberCollapseTransport

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SecondOrderQuotient.structure_l

universe u v

section Structures

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
  {𝒩 : FirstOrder.Structure.{0, 0, 0, v} ℒ}

/-- 只有 Prop 规格，没有携带载体映射或所选见证。 -/
structure correspondence_l (R : carrier_l ℳ → carrier_l 𝒩 → Prop) : Prop where
  left_total_l : ∀ x, ∃ y, R x y
  right_total_l : ∀ y, ∃ x, R x y
  equality_l : ∀ x y a b, R x a → R y b → (x = y ↔ a = b)
  membership_l : ∀ x y a b, R x a → R y b →
    (ThirdOrderSemantics.member_l ℳ x y ↔ ThirdOrderSemantics.member_l 𝒩 a b)

/-- 原绑定与自由槽逐点相关；不构造一个环境到另一个环境的函数。 -/
def environments_related_l {Γ Δ : SortContext ℒ}
    (R : carrier_l ℳ → carrier_l 𝒩 → Prop) (η : Env ℳ Γ Δ) (ξ : Env 𝒩 Γ Δ) : Prop :=
  (∀ w : Variable Γ .set, R (η.boundVal w) (ξ.boundVal w)) ∧
    ∀ w : Variable Δ .set, R (η.freeVal w) (ξ.freeVal w)

/-- 只递归外部有限槽表；全部像见证在 Prop 中逐个消去。 -/
private theorem assignment_exists_l {R : carrier_l ℳ → carrier_l 𝒩 → Prop}
    (hR : ∀ x, ∃ y, R x y) (Γ : SortContext ℒ) (η : Assignment ℳ Γ) :
    ∃ ξ : Assignment 𝒩 Γ, ∀ w : Variable Γ .set, R (η w) (ξ w) := by
  induction Γ with
  | nil =>
    exact ⟨Assignment.empty, fun w => nomatch w⟩
  | cons s Γ ih =>
    cases s
    obtain ⟨ξ, hξ⟩ := ih (fun w => η (.there w))
    obtain ⟨y, hy⟩ := hR (η .here)
    refine ⟨Assignment.push y ξ, ?_⟩
    intro w
    cases w with
    | here => exact hy
    | there w => exact hξ w

/-- 任意有限原环境具有相关像；不抽取一个 Type 层环境映射。 -/
theorem env_exists_l {Γ Δ : SortContext ℒ} {R : carrier_l ℳ → carrier_l 𝒩 → Prop}
    (hR : ∀ x, ∃ y, R x y) (η : Env ℳ Γ Δ) :
    ∃ ξ : Env 𝒩 Γ Δ, environments_related_l R η ξ := by
  obtain ⟨ξ₀, h₀⟩ := assignment_exists_l hR Γ η.boundVal
  obtain ⟨ξ₁, h₁⟩ := assignment_exists_l hR Δ η.freeVal
  exact ⟨⟨ξ₀, ξ₁⟩, h₀, h₁⟩

theorem term_l {Γ Δ : SortContext ℒ} {R : carrier_l ℳ → carrier_l 𝒩 → Prop}
    {η : Env ℳ Γ Δ} {ξ : Env 𝒩 Γ Δ} (h : environments_related_l R η ξ)
    (t : Term ℒ Γ Δ .set) : R (t.eval η) (t.eval ξ) := by
  match t with
  | .bvar w => exact h.1 w
  | .fvar w => exact h.2 w
  | .app f _ => nomatch f

theorem push_l {Γ Δ : SortContext ℒ} {R : carrier_l ℳ → carrier_l 𝒩 → Prop}
    {η : Env ℳ Γ Δ} {ξ : Env 𝒩 Γ Δ} (h : environments_related_l R η ξ)
    {x : carrier_l ℳ} {y : carrier_l 𝒩} (hxy : R x y) :
    environments_related_l R (η.pushBound (sort := SetTheory.SetSort.set) x)
      (ξ.pushBound (sort := SetTheory.SetSort.set) y) := by
  constructor
  · intro w
    cases w with
    | here => exact hxy
    | there w => exact h.1 w
  · exact h.2

/-- 自由参数的逐槽关系随同一实际参数扩展，仍不选择任何像函数。 -/
theorem push_free_l {Γ Δ : SortContext ℒ} {R : carrier_l ℳ → carrier_l 𝒩 → Prop}
    {η : Env ℳ Γ Δ} {ξ : Env 𝒩 Γ Δ} (h : environments_related_l R η ξ)
    {x : carrier_l ℳ} {y : carrier_l 𝒩} (hxy : R x y) :
    environments_related_l R (η.pushFree (sort := SetTheory.SetSort.set) x)
      (ξ.pushFree (sort := SetTheory.SetSort.set) y) := by
  constructor
  · exact h.1
  · intro w
    cases w with
    | here => exact hxy
    | there w => exact h.2 w

/-- 外部 Formula 结构递归只运输同一个原 AST，不假设模型自然数外部标准。 -/
theorem formula_l {R : carrier_l ℳ → carrier_l 𝒩 → Prop} (hR : correspondence_l R)
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env ℳ Γ Δ) (ξ : Env 𝒩 Γ Δ)
    (h : environments_related_l R η ξ) : φ.satisfies η ↔ φ.satisfies ξ := by
  match φ with
  | .falsum => exact Iff.rfl
  | .truth => exact Iff.rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
    exact hR.membership_l (s.eval η) (t.eval η) (s.eval ξ) (t.eval ξ) (term_l h s) (term_l h t)
  | .equal (sort := .set) s t =>
    exact hR.equality_l (s.eval η) (t.eval η) (s.eval ξ) (t.eval ξ) (term_l h s) (term_l h t)
  | .neg φ => exact not_congr (formula_l hR φ η ξ h)
  | .conj φ ψ => exact and_congr (formula_l hR φ η ξ h) (formula_l hR ψ η ξ h)
  | .disj φ ψ => exact or_congr (formula_l hR φ η ξ h) (formula_l hR ψ η ξ h)
  | .imp φ ψ => exact imp_congr (formula_l hR φ η ξ h) (formula_l hR ψ η ξ h)
  | .iff φ ψ => exact iff_congr (formula_l hR φ η ξ h) (formula_l hR ψ η ξ h)
  | .existsE .set φ =>
    change (∃ x, φ.satisfies (η.pushBound x)) ↔ ∃ y, φ.satisfies (ξ.pushBound y)
    constructor
    · rintro ⟨x, hφ⟩
      obtain ⟨y, hxy⟩ := hR.left_total_l x
      exact ⟨y, (formula_l hR φ (η.pushBound x) (ξ.pushBound y) (push_l h hxy)).mp hφ⟩
    · rintro ⟨y, hφ⟩
      obtain ⟨x, hxy⟩ := hR.right_total_l y
      exact ⟨x, (formula_l hR φ (η.pushBound x) (ξ.pushBound y) (push_l h hxy)).mpr hφ⟩
  | .forallE .set φ =>
    change (∀ x, φ.satisfies (η.pushBound x)) ↔ ∀ y, φ.satisfies (ξ.pushBound y)
    constructor
    · intro hφ y
      obtain ⟨x, hxy⟩ := hR.right_total_l y
      exact (formula_l hR φ (η.pushBound x) (ξ.pushBound y) (push_l h hxy)).mp (hφ x)
    · intro hφ x
      obtain ⟨y, hxy⟩ := hR.left_total_l x
      exact (formula_l hR φ (η.pushBound x) (ξ.pushBound y) (push_l h hxy)).mpr (hφ y)

end Structures

section Quotient

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ

variable {I T : SecondOrderQuotient.type_l hℳ} {hI : ∃ x, SecondOrderQuotient.mem_l hℳ x I}
  {hT : ∃ x, SecondOrderQuotient.mem_l hℳ x T}

local notation "ℳ₀" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) I hI
local notation "𝒩₀" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) T hT

/-- 关系本身只是同一 raw 集合图的值谓词，不选择图值为宿主函数。 -/
def relation_l (H : Raw) (x : PowerlessMemberStructure.type_l (ℳ := 𝒱) I)
    (y : PowerlessMemberStructure.type_l (ℳ := 𝒱) T) : Prop :=
  SecondOrderFunctionObjects.value_l hℳ H x.val y.val

theorem graph_l (H : Raw) (hH : SecondOrderFunctionObjects.map_l hℳ H I T)
    (hOnto : ∀ y, SecondOrderQuotient.mem_l hℳ y T →
      ∃ x, SecondOrderQuotient.mem_l hℳ x I ∧ SecondOrderFunctionObjects.value_l hℳ H x y)
    (hInjective : SecondOrderFunctionObjects.injective_l hℳ H)
    (hMember : ∀ x y a b, SecondOrderQuotient.mem_l hℳ x I →
      SecondOrderQuotient.mem_l hℳ y I → SecondOrderFunctionObjects.value_l hℳ H x a →
      SecondOrderFunctionObjects.value_l hℳ H y b →
      (SecondOrderQuotient.mem_l hℳ x y ↔ SecondOrderQuotient.mem_l hℳ a b)) :
    correspondence_l (ℳ := ℳ₀) (𝒩 := 𝒩₀) (relation_l H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, ⟨hy, hxy⟩, _⟩ := hH.2 x.val x.property
    exact ⟨⟨y, hy⟩, hxy⟩
  · intro y
    obtain ⟨x, hx, hxy⟩ := hOnto y.val y.property
    exact ⟨⟨x, hx⟩, hxy⟩
  · intro x y a b hxa hyb
    constructor
    · intro hxy
      have hxy' := congrArg Subtype.val hxy
      exact Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ hH (hxy' ▸ hxa) hyb)
    · intro hab
      have hab' := congrArg Subtype.val hab
      exact Subtype.ext (hInjective _ _ _ (hab' ▸ hxa) hyb)
  · intro x y a b hxa hyb
    exact hMember x.val y.val a.val b.val x.property y.property hxa hyb

/-- 实际 MemberI 与 MemberT 的全公式出口；I、H、T 均无需属于另一个载体。 -/
theorem member_l (H : Raw) (hH : SecondOrderFunctionObjects.map_l hℳ H I T)
    (hOnto : ∀ y, SecondOrderQuotient.mem_l hℳ y T →
      ∃ x, SecondOrderQuotient.mem_l hℳ x I ∧ SecondOrderFunctionObjects.value_l hℳ H x y)
    (hInjective : SecondOrderFunctionObjects.injective_l hℳ H)
    (hMember : ∀ x y a b, SecondOrderQuotient.mem_l hℳ x I →
      SecondOrderQuotient.mem_l hℳ y I → SecondOrderFunctionObjects.value_l hℳ H x a →
      SecondOrderFunctionObjects.value_l hℳ H y b →
      (SecondOrderQuotient.mem_l hℳ x y ↔ SecondOrderQuotient.mem_l hℳ a b))
    {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) (η : Env ℳ₀ Γ Δ) (ξ : Env 𝒩₀ Γ Δ)
    (h : environments_related_l (relation_l H) η ξ) : φ.satisfies η ↔ φ.satisfies ξ :=
  formula_l (ℳ := ℳ₀) (𝒩 := 𝒩₀)
    (graph_l (hI := hI) (hT := hT) H hH hOnto hInjective hMember) φ η ξ h

/-- 原 global_m 在两侧成员结构中解释，不偷换成 ambient 原 Def 规格。 -/
theorem global_l (H : Raw) (hH : SecondOrderFunctionObjects.map_l hℳ H I T)
    (hOnto : ∀ y, SecondOrderQuotient.mem_l hℳ y T →
      ∃ x, SecondOrderQuotient.mem_l hℳ x I ∧ SecondOrderFunctionObjects.value_l hℳ H x y)
    (hInjective : SecondOrderFunctionObjects.injective_l hℳ H)
    (hMember : ∀ x y a b, SecondOrderQuotient.mem_l hℳ x I →
      SecondOrderQuotient.mem_l hℳ y I → SecondOrderFunctionObjects.value_l hℳ H x a →
      SecondOrderFunctionObjects.value_l hℳ H y b →
      (SecondOrderQuotient.mem_l hℳ x y ↔ SecondOrderQuotient.mem_l hℳ a b))
    (X Y : PowerlessMemberStructure.type_l (ℳ := 𝒱) I)
    (A B : PowerlessMemberStructure.type_l (ℳ := 𝒱) T)
    (hXA : relation_l H X A) (hYB : relation_l H Y B) :
    (PowerlessMemberDefSyntax.global_m (Γ := []) (Δ := [.set, .set])
      (.fvar .here) (.fvar (.there .here))).satisfies
        ((Env.empty (M := ℳ₀)).pushFree Y |>.pushFree X) ↔
      (PowerlessMemberDefSyntax.global_m (Γ := []) (Δ := [.set, .set])
        (.fvar .here) (.fvar (.there .here))).satisfies
          ((Env.empty (M := 𝒩₀)).pushFree B |>.pushFree A) := by
  let η : Env ℳ₀ [] [.set, .set] := (Env.empty.pushFree Y).pushFree X
  let ξ : Env 𝒩₀ [] [.set, .set] := (Env.empty.pushFree B).pushFree A
  have h : environments_related_l (relation_l H) η ξ := by
    constructor
    · intro w
      nomatch w
    · intro w
      cases w with
      | here => exact hXA
      | there w => cases w with
        | here => exact hYB
        | there w => nomatch w
  exact member_l (hI := hI) (hT := hT) H hH hOnto hInjective hMember
    (PowerlessMemberDefSyntax.global_m (.fvar .here) (.fvar (.there .here))) η ξ h

end Quotient

#print axioms term_l
#print axioms env_exists_l
#print axioms relation_l
#print axioms push_l
#print axioms push_free_l
#print axioms formula_l
#print axioms graph_l
#print axioms member_l
#print axioms global_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberCollapseTransport
