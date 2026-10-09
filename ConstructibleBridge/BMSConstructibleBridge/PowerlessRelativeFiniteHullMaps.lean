import BMSConstructibleBridge.PowerlessMemberBounded
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity
import BMSConstructibleBridge.PowerlessMapBounded
import BMSConstructibleBridge.PowerlessFiniteSequencesSyntax

/-! # 非传递有限闭包域的完整映射与有限赋值读取

完整 map 原规格已有纯 Δ₀ 表达；将它作为同一 I 的实际反射请求，
先经传递 W 核验，再读取 MemberI 原映射规格。没有假定 I 传递，
也不把 raw 有序对图与 MemberI 中任意图未经核验就等同。
全部内部自然数属于 I 时，原完整 Seq 规格可读回实际 MemberI。
这些语义中间桥由 SourceHistory 同域反射族提供资格，不能单独
替代最终源存在性、Collection 或固定高度的 Z₂ 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullMaps

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l

universe u

abbrev context_m : SortContext ℒ := [.set, .set, .set]

/-- 绑定槽为陪域 D、定义域 A、图 F，原自由参数不变。 -/
def matrix_m (Δ : SortContext ℒ) : Formula ℒ context_m Δ :=
  PowerlessMapBounded.formula_m (.bvar (.there (.there .here)))
    (.bvar (.there .here)) (.bvar .here)

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk context_m (matrix_m Δ)]

theorem matrix_delta_l (Δ : SortContext ℒ) :
    Formula.IsDelta0 membershipLevyBound (matrix_m Δ) :=
  PowerlessMapBounded.delta_l _ _ _

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 反射的是完整图规格，不仅是给定输入的求值存在性。 -/
theorem reflect_l {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩 [] Δ) (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    {I₀ W₀ : carrier_l 𝒩}
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hNonempty : ∃ x, member_l 𝒩 x W₀) (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (hFree : ∀ v : Variable Δ .set, member_l 𝒩 (ν.freeVal v) I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (η : Env 𝒩 context_m Δ) (hη : ∀ s (v : Variable Δ s), η.freeVal v = ν.freeVal v)
    (hBound : ∀ v : Variable context_m .set, member_l 𝒩 (η.boundVal v) I₀) :
    (matrix_m Δ).satisfies η ↔
      (PowerlessRelativization.formula_m (matrix_m Δ)).satisfies (η.pushFree I₀) := by
  change (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧ True at h
  have hReflect := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (matrix_m Δ) ζ I W τ ν hτ).mp h.1 η hη (fun v => hI₀.symm ▸ hBound v)
  rw [hI₀, hW₀] at hReflect
  have hAbsolute := PowerlessMemberBounded.relativized_l hW hNonempty (matrix_delta_l Δ) η
    (fun v => hIW _ (hBound v)) (fun v => by
      rw [hη _ v]
      exact hIW _ (hFree v))
  exact hAbsolute.symm.trans hReflect

/-- 所有图参数属于同一 I 时，两侧完整 map 原规格同值。 -/
theorem model_l {Δ Ε : SortContext ℒ} {I₀ W₀ : carrier_l 𝒩}
    (hI : ∃ x, member_l 𝒩 x I₀) (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (F A D : PowerlessMemberStructure.type_l (ℳ := 𝒩) I₀) :
    map_l (ℳ := 𝒩) F.val A.val D.val ↔
      map_l (ℳ := PowerlessMemberStructure.structure_l I₀ hI) F A D := by
  let η : Env (PowerlessMemberStructure.structure_l I₀ hI) context_m Δ :=
    ((ν.pushBound F).pushBound A).pushBound D
  have hNonempty : ∃ x, member_l 𝒩 x W₀ := by
    obtain ⟨x, hx⟩ := hI
    exact ⟨x, hIW x hx⟩
  have hReflect := (reflect_l ζ I W τ (PowerlessRelativization.env_l ν) hτ hI₀ hW₀
    hW hNonempty hIW (fun v => (ν.freeVal v).property) h
    (PowerlessRelativization.env_l η) (fun _ _ => rfl)
    (fun v => (η.boundVal v).property)).trans
      (PowerlessRelativization.formula_l (matrix_m Δ) η)
  have hRaw : (matrix_m Δ).satisfies (PowerlessRelativization.env_l η) ↔
      map_l (ℳ := 𝒩) F.val A.val D.val := by
    rw [matrix_m, PowerlessMapBounded.formula_l]
    rfl
  have hMember : (matrix_m Δ).satisfies η ↔
      map_l (ℳ := PowerlessMemberStructure.structure_l I₀ hI) F A D := by
    rw [matrix_m, PowerlessMapBounded.formula_l]
    rfl
  exact hRaw.symm.trans (hReflect.trans hMember)

/-- 内部 ω 的所有成员在 I 中时，原完整 Seq 可读回同一个 MemberI。 -/
theorem sequences_l {Δ Ε : SortContext ℒ} {I₀ W₀ : carrier_l 𝒩}
    (hI : ∃ x, member_l 𝒩 x I₀) (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (PowerlessMemberStructure.structure_l I₀ hI) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = (ν.freeVal v).val)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ x, member_l 𝒩 x W₀ → ∀ y, member_l 𝒩 y x → member_l 𝒩 y W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (ω A S : PowerlessMemberStructure.type_l (ℳ := 𝒩) I₀)
    (hω : ∀ n, member_l 𝒩 n ω.val → member_l 𝒩 n I₀)
    (hSeq : PowerlessFiniteSequencesSyntax.spec_l (ℳ := 𝒩) ω.val A.val S.val) :
    PowerlessFiniteSequencesSyntax.spec_l
      (ℳ := PowerlessMemberStructure.structure_l I₀ hI) ω A S := by
  intro f
  change member_l 𝒩 f.val S.val ↔
    ∃ n : PowerlessMemberStructure.type_l (ℳ := 𝒩) I₀,
      member_l 𝒩 n.val ω.val ∧
        map_l (ℳ := PowerlessMemberStructure.structure_l I₀ hI) f n A
  constructor
  · intro hf
    obtain ⟨n, hn, hMap⟩ := (hSeq f.val).mp hf
    let n₀ : PowerlessMemberStructure.type_l (ℳ := 𝒩) I₀ := ⟨n, hω n hn⟩
    exact ⟨n₀, hn, (model_l hI ζ I W τ ν hτ hI₀ hW₀ hW hIW h f n₀ A).mp hMap⟩
  · rintro ⟨n, hn, hMap⟩
    exact (hSeq f.val).mpr ⟨n.val, hn,
      (model_l hI ζ I W τ ν hτ hI₀ hW₀ hW hIW h f n A).mpr hMap⟩

#print axioms matrix_delta_l
#print axioms reflect_l
#print axioms model_l
#print axioms sequences_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullMaps
