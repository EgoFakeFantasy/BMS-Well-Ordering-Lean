import BMSConstructibleBridge.PowerlessSourceTuple
import BMSConstructibleBridge.PowerlessRelativeLimitSourceBasics

/-!
# 仅依赖配对的原有限元组编码

复用原 SourceTuple 的公式、值列、编码与环境，不另造语法。
编码存在性只消费显式有序对存在性，解码只消费同码坐标唯一性。
递归指标是原公式的外部固定元数，不对模型内部 ω 作外部归纳。
末端从实际极限层的配对基础取得同一接口，不要求层满足完整源理论。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceTuplePairing

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  PowerlessMemberStructure.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 两个实际无序对对象相等时，成员规格已经确定其坐标。 -/
theorem pair_coordinates_l {a b c d p q : carrier_l ℳ}
    (hp : ThirdOrderSemantics.pair_l a b p)
    (hq : ThirdOrderSemantics.pair_l c d q) (h : p = q) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  apply Set.pair_eq_pair_iff.mp
  ext x
  change (x = a ∨ x = b) ↔ (x = c ∨ x = d)
  exact (hp x).symm.trans (h ▸ hq x)

/-- 同一个 Kuratowski 码的坐标唯一性不需要整个背景理论。 -/
theorem ordered_coordinates_l {a b c d p : carrier_l ℳ}
    (hp : ordered_l a b p) (hq : ordered_l c d p) : a = c ∧ b = d := by
  obtain ⟨s, t, hs, ht, hp⟩ := hp
  obtain ⟨v, w, hv, hw, hq⟩ := hq
  rcases pair_coordinates_l hp hq rfl with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have h₃ : a = c := (pair_coordinates_l hs hv h₁).elim And.left And.left
    have h₄ := pair_coordinates_l ht hw h₂
    exact ⟨h₃, h₄.elim And.right (fun h₅ => h₅.2.trans (h₃.symm.trans h₅.1))⟩
  · have h₃ : a = c ∧ a = d := by
      rcases pair_coordinates_l hs hw h₁ with h | h
      · exact h
      · exact h.symm
    have h₄ : b = c := (pair_coordinates_l ht hv h₂).elim And.right And.right
    exact ⟨h₃.1, h₄.trans (h₃.1.symm.trans h₃.2)⟩

/-- 三次实际无序对存在性给出原 Kuratowski 有序对。 -/
theorem ordered_exists_l
    (hPair : ∀ a b : carrier_l ℳ, ∃ p, ThirdOrderSemantics.pair_l a b p)
    (a b : carrier_l ℳ) : ∃ p, ordered_l a b p := by
  obtain ⟨s, hs⟩ := hPair a a
  obtain ⟨t, ht⟩ := hPair a b
  obtain ⟨p, hp⟩ := hPair s t
  exact ⟨p, s, t, hs, ht, hp⟩

/-- 原两输入合并公式直接由实际 Kuratowski 坐标规格解码。 -/
theorem pair_l
    {Γ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: .set :: Γ))
    (η : Env ℳ [] Γ) {p x z : carrier_l ℳ} (hp : ordered_l x z p)
    (y : carrier_l ℳ) :
    (PowerlessSourcePack.pair_m φ).satisfies ((η.pushFree p).pushFree y) ↔
      φ.satisfies (((η.pushFree z).pushFree x).pushFree y) := by
  rw [PowerlessSourcePack.formula_l]
  constructor
  · rintro ⟨a, b, hab, hφ⟩
    obtain ⟨rfl, rfl⟩ := ordered_coordinates_l hab hp
    exact hφ
  · intro hφ
    exact ⟨x, z, hp, hφ⟩

/-- 对封闭集合中的有限值列有实际层内码，只需有序对存在性。 -/
theorem code_exists_l
    (hPair : ∀ a b : carrier_l ℳ, ∃ p, ordered_l a b p)
    (A e : carrier_l ℳ) (he : member_l ℳ e A)
    (hA : ∀ a b p, member_l ℳ a A → member_l ℳ b A →
      ordered_l a b p → member_l ℳ p A)
    (n : Nat) (v : Values ℳ.Carrier (List.replicate n .set))
    (hv : PowerlessSourceTuple.bounded_l A n v) :
    ∃ p, member_l ℳ p A ∧ PowerlessSourceTuple.code_l e n v p := by
  match n, v with
  | 0, .nil => exact ⟨e, he, rfl⟩
  | 1, .cons x .nil => exact ⟨x, hv.1, rfl⟩
  | n + 2, .cons x (.cons z v) =>
    obtain ⟨q, hq⟩ := hPair x z
    obtain ⟨p, hp, h⟩ := code_exists_l hPair A e he hA (n + 1) (.cons q v)
      ⟨hA x z q hv.1 hv.2.1 hq, hv.2.2⟩
    exact ⟨p, hp, q, hq, h⟩

/-- 原有限元组公式的忠实性不要求结构满足完整背景理论。 -/
theorem formula_l
    {Γ : SortContext ℒ} (η : Env ℳ [] Γ) (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (v : Values ℳ.Carrier (List.replicate n .set)) {e p : carrier_l ℳ}
    (hp : PowerlessSourceTuple.code_l e n v p) (y : carrier_l ℳ) :
    (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y) ↔
      φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y) := by
  match n, v with
  | 0, .nil => exact PowerlessSourceTuple.empty_formula_l φ η p y
  | 1, .cons x .nil =>
    change p = x at hp
    subst p
    rfl
  | n + 2, .cons x (.cons z v) =>
    obtain ⟨q, hq, hp⟩ := hp
    exact (formula_l η (n + 1) (PowerlessSourcePack.pair_m φ) (.cons q v) hp y).trans
      (pair_l φ (PowerlessSourceTuple.env_l η n v) hq y)

/-- 对同一个码的见证闭包恢复为原有限元数请求的见证闭包。 -/
theorem closure_l
    (hPair : ∀ a b : carrier_l ℳ, ∃ p, ordered_l a b p)
    {Γ : SortContext ℒ} (η : Env ℳ [] Γ) (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (P : carrier_l ℳ → Prop) (A e : carrier_l ℳ) (he : member_l ℳ e A)
    (hA : ∀ a b p, member_l ℳ a A → member_l ℳ b A →
      ordered_l a b p → member_l ℳ p A)
    (h : ∀ p, member_l ℳ p A →
      (∃ y, P y ∧ (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y)) →
        ∃ y, member_l ℳ y A ∧
          (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y)) :
    ∀ v, PowerlessSourceTuple.bounded_l A n v →
      (∃ y, P y ∧ φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)) →
        ∃ y, member_l ℳ y A ∧
          φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y) := by
  rintro v hv ⟨y, hy, hφ⟩
  obtain ⟨p, hp, hC⟩ := code_exists_l hPair A e he hA n v hv
  obtain ⟨z, hz, hψ⟩ := h p hp ⟨y, hy, (formula_l η n φ v hC y).mpr hφ⟩
  exact ⟨z, hz, (formula_l η n φ v hC z).mp hψ⟩

/-- 谓词限定的值列；用于层成员结构中尚不是层内对象的实际闭包像。 -/
def bounded_l (P : carrier_l ℳ → Prop) :
    (n : Nat) → Values ℳ.Carrier (List.replicate n .set) → Prop
  | 0, .nil => True
  | n + 1, .cons x v => P x ∧ bounded_l P n v

theorem bounded_member_l (A : carrier_l ℳ) (n : Nat)
    (v : Values ℳ.Carrier (List.replicate n .set)) :
    bounded_l (fun x => member_l ℳ x A) n v ↔ PowerlessSourceTuple.bounded_l A n v := by
  match n, v with
  | 0, .nil => rfl
  | n + 1, .cons x v => exact and_congr Iff.rfl (bounded_member_l A n v)

/-- 同一配对闭包谓词中的输入列有原编码，不要求该谓词在结构中有载体。 -/
theorem predicate_code_l
    (hPair : ∀ a b : carrier_l ℳ, ∃ p, ordered_l a b p)
    (P : carrier_l ℳ → Prop) (e : carrier_l ℳ) (he : P e)
    (hP : ∀ a b p, P a → P b → ordered_l a b p → P p)
    (n : Nat) (v : Values ℳ.Carrier (List.replicate n .set)) (hv : bounded_l P n v) :
    ∃ p, P p ∧ PowerlessSourceTuple.code_l e n v p := by
  match n, v with
  | 0, .nil => exact ⟨e, he, rfl⟩
  | 1, .cons x .nil => exact ⟨x, hv.1, rfl⟩
  | n + 2, .cons x (.cons z v) =>
    obtain ⟨q, hq⟩ := hPair x z
    obtain ⟨p, hp, h⟩ := predicate_code_l hPair P e he hP (n + 1) (.cons q v)
      ⟨hP x z q hv.1 hv.2.1 hq, hv.2.2⟩
    exact ⟨p, hp, q, hq, h⟩

/-- 编码闭包恢复原请求，允许 P(x) 为 ambient 中的 x.val∈I，而不假设 I∈W。 -/
theorem predicate_closure_l
    (hPair : ∀ a b : carrier_l ℳ, ∃ p, ordered_l a b p)
    {Γ : SortContext ℒ} (η : Env ℳ [] Γ) (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Γ)))
    (P Q : carrier_l ℳ → Prop) (e : carrier_l ℳ) (he : P e)
    (hP : ∀ a b p, P a → P b → ordered_l a b p → P p)
    (h : ∀ p, P p →
      (∃ y, Q y ∧ (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y)) →
        ∃ y, P y ∧ (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y)) :
    ∀ v, bounded_l P n v →
      (∃ y, Q y ∧ φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)) →
        ∃ y, P y ∧ φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y) := by
  rintro v hv ⟨y, hy, hφ⟩
  obtain ⟨p, hp, hC⟩ := predicate_code_l hPair P e he hP n v hv
  obtain ⟨z, hz, hψ⟩ := h p hp ⟨y, hy, (formula_l η n φ v hC y).mpr hφ⟩
  exact ⟨z, hz, (formula_l η n φ v hC z).mp hψ⟩

section Level

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {h𝒩 : Theory.Models 𝒩 SecondOrderArithmetic.theory_m}
  {B β W ω : SecondOrderQuotient.type_l h𝒩}

local notation "𝒱" => SecondOrderQuotient.structure_l h𝒩

/-- 实际极限层提供通用编码和解码所需的全部配对条件。 -/
theorem level_l
    (hBase : ∀ x, SecondOrderQuotient.mem_l h𝒩 x B →
      ∀ y, SecondOrderQuotient.mem_l h𝒩 y x → SecondOrderQuotient.mem_l h𝒩 y B)
    (hβ : PowerlessRelativeHierarchySemantics.limit_l h𝒩 β)
    (hW : PowerlessRelativeHierarchySemantics.level_l h𝒩 B β W)
    (hωW : SecondOrderQuotient.mem_l h𝒩 ω W) :
    let 𝒲 := PowerlessMemberStructure.structure_l (ℳ := 𝒱) W ⟨ω, hωW⟩
    (∀ a b : carrier_l 𝒲, ∃ p, ordered_l a b p) ∧
      (∀ a b c d p : carrier_l 𝒲,
        ordered_l a b p → ordered_l c d p → a = c ∧ b = d) := by
  let 𝒲 := PowerlessMemberStructure.structure_l (ℳ := 𝒱) W ⟨ω, hωW⟩
  have hPair := PowerlessRelativeLimitSourceBasics.pairing_l hBase hβ hW hωW
  change ∀ a b : carrier_l 𝒲, ∃ p, ThirdOrderSemantics.pair_l a b p at hPair
  exact ⟨ordered_exists_l hPair, fun _ _ _ _ _ hp hq => ordered_coordinates_l hp hq⟩

end Level

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceTuplePairing
