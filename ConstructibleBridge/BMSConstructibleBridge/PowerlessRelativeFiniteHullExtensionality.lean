import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity
import BMSConstructibleBridge.PowerlessRelativeLimitSourceBasics
import BMSConstructibleBridge.PowerlessRelativeFiniteHullAssignments

/-! # 有限成员域的外延性与无孤立点

纯隶属语言 ℒ 中只增加两条原公式：区别成员的存在见证，以及上邻居
的存在见证。原自由参数上下文 Δ 保持不变；两式不读取参数槽。
同一个 MemberI→MemberW 的有限元素性将 W 中的真实见证回收到 I。
上邻居已足以覆盖成员关系的端点域，无需假设 I 传递或 I∈W。
实际极限层只消费已有外延性与配对，不要求完整源理论。
本模块是内部成员塌缩的中间依赖，不替代最终 BMS 对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullExtensionality

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature
  PowerlessMemberStructure.structure_l PowerlessMemberStructure.type_l
  SecondOrderQuotient.structure_l

universe u

/-- 绑定槽依次为区别见证 z、第二对象 y、第一对象 x。 -/
def distinguish_matrix_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set] Δ :=
  .neg (.iff
    (member_m (.bvar .here) (.bvar (.there (.there .here))))
    (member_m (.bvar .here) (.bvar (.there .here))))

def distinguish_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set] Δ :=
  .existsE .set (distinguish_matrix_m Δ)

/-- 绑定槽依次为上邻居 p、原对象 x。 -/
def upper_matrix_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set] Δ :=
  member_m (.bvar (.there .here)) (.bvar .here)

def upper_m (Δ : SortContext ℒ) : Formula ℒ [.set] Δ :=
  .existsE .set (upper_matrix_m Δ)

/-- 外部有限原族保留两个各自不同的绑定上下文。 -/
def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk ([.set, .set] : SortContext ℒ) (distinguish_m Δ),
    Sigma.mk ([.set] : SortContext ℒ) (upper_m Δ)]

theorem family_length_m (Δ : SortContext ℒ) : (family_m Δ).length = 2 := rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

theorem distinguish_matrix_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ)
    (x y z : carrier_l ℳ) :
    (distinguish_matrix_m Δ).satisfies (((η.pushBound x).pushBound y).pushBound z) ↔
      ¬(member_l ℳ z x ↔ member_l ℳ z y) := Iff.rfl

theorem distinguish_formula_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ)
    (x y : carrier_l ℳ) :
    (distinguish_m Δ).satisfies ((η.pushBound x).pushBound y) ↔
      ∃ z, ¬(member_l ℳ z x ↔ member_l ℳ z y) := Iff.rfl

theorem upper_matrix_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ) (x p : carrier_l ℳ) :
    (upper_matrix_m Δ).satisfies ((η.pushBound x).pushBound p) ↔
      member_l ℳ x p := Iff.rfl

theorem upper_formula_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ) (x : carrier_l ℳ) :
    (upper_m Δ).satisfies (η.pushBound x) ↔ ∃ p, member_l ℳ x p := Iff.rfl

/-- 直接读取原对象元素性实例；域项仍在装配上下文中。 -/
theorem distinguish_entry_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (PowerlessRelativeFiniteElementarity.entry_m (distinguish_m Δ) I W τ).satisfies ζ ↔
      ∀ x, member_l ℳ x (I.eval ζ) → ∀ y, member_l ℳ y (I.eval ζ) →
        ((∃ z, member_l ℳ z (W.eval ζ) ∧ ¬(member_l ℳ z x ↔ member_l ℳ z y)) ↔
          ∃ z, member_l ℳ z (I.eval ζ) ∧ ¬(member_l ℳ z x ↔ member_l ℳ z y)) := by
  match I, W with
  | .bvar v, _ => nomatch v
  | .app f _, _ => nomatch f
  | _, .bvar v => nomatch v
  | _, .app f _ => nomatch f
  | .fvar _, .fvar _ => exact Iff.rfl

theorem upper_entry_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (PowerlessRelativeFiniteElementarity.entry_m (upper_m Δ) I W τ).satisfies ζ ↔
      ∀ x, member_l ℳ x (I.eval ζ) →
        ((∃ p, member_l ℳ p (W.eval ζ) ∧ member_l ℳ x p) ↔
          ∃ p, member_l ℳ p (I.eval ζ) ∧ member_l ℳ x p) := by
  match I, W with
  | .bvar v, _ => nomatch v
  | .app f _, _ => nomatch f
  | _, .bvar v => nomatch v
  | _, .app f _ => nomatch f
  | .fvar _, .fvar _ => exact Iff.rfl

/-- 两条实例使用同一 I、W、原参数嵌入及装配环境。 -/
theorem family_formula_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set) :
    (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ ↔
      (∀ x, member_l ℳ x (I.eval ζ) → ∀ y, member_l ℳ y (I.eval ζ) →
        ((∃ z, member_l ℳ z (W.eval ζ) ∧ ¬(member_l ℳ z x ↔ member_l ℳ z y)) ↔
          ∃ z, member_l ℳ z (I.eval ζ) ∧ ¬(member_l ℳ z x ↔ member_l ℳ z y))) ∧
      (∀ x, member_l ℳ x (I.eval ζ) →
        ((∃ p, member_l ℳ p (W.eval ζ) ∧ member_l ℳ x p) ↔
          ∃ p, member_l ℳ p (I.eval ζ) ∧ member_l ℳ x p)) := by
  change ((PowerlessRelativeFiniteElementarity.entry_m (distinguish_m Δ) I W τ).satisfies ζ ∧
    ((PowerlessRelativeFiniteElementarity.entry_m (upper_m Δ) I W τ).satisfies ζ ∧ True)) ↔ _
  rw [and_true]
  exact and_congr (distinguish_entry_l ζ I W τ) (upper_entry_l ζ I W τ)

/-- 把本两式放在原族前面时，保留原族并取回所需两个实例。 -/
theorem append_l {Δ Ε : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (ζ : Env ℳ [] Ε) (I W : Term ℒ [] Ε .set)
    (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ ++ Φ) I W τ).satisfies ζ) :
    (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ :=
  ⟨h.1, h.2.1, trivial⟩

variable {I₀ W₀ : carrier_l ℳ} {hW : ∃ x, member_l ℳ x W₀}

local notation "𝒲" => PowerlessMemberStructure.structure_l (ℳ := ℳ) W₀ hW
local notation "WType" => PowerlessMemberStructure.type_l (ℳ := ℳ) W₀

/-- 区别见证足以保证实际 I 成员关系外延，不假定 I 传递。 -/
theorem extensionality_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (hIW : subset_l I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hExt : SecondOrderAxioms.extensionality_m.TrueIn 𝒲)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    ∀ x y, member_l ℳ x I₀ → member_l ℳ y I₀ →
      (∀ z, member_l ℳ z I₀ → (member_l ℳ z x ↔ member_l ℳ z y)) → x = y := by
  classical
  have hRead := (family_formula_l ζ I W τ).mp h
  rw [hI₀, hW₀] at hRead
  change ∀ a b : WType, (∀ z : WType,
    member_l ℳ z.val a.val ↔ member_l ℳ z.val b.val) → a = b at hExt
  intro x y hx hy hxy
  by_contra hEq
  let x₀ : WType := ⟨x, hIW x hx⟩
  let y₀ : WType := ⟨y, hIW y hy⟩
  have hSome : ∃ z, member_l ℳ z W₀ ∧ ¬(member_l ℳ z x ↔ member_l ℳ z y) := by
    by_contra hNone
    have hEq₀ : x₀ = y₀ := hExt x₀ y₀ (fun z => by
      by_contra hz
      exact hNone ⟨z.val, z.property, hz⟩)
    exact hEq (congrArg Subtype.val hEq₀)
  obtain ⟨z, hz, hNot⟩ := (hRead.1 x hx y hy).mp hSome
  exact hNot (hxy z hz)

/-- 上邻居见证使每个 I 内对象都是成员图的实际端点。 -/
theorem upper_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (hIW : subset_l I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hPair : SecondOrderPairSet.formula_m.TrueIn 𝒲)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    ∀ x, member_l ℳ x I₀ → ∃ p, member_l ℳ p I₀ ∧ member_l ℳ x p := by
  have hRead := (family_formula_l ζ I W τ).mp h
  rw [hI₀, hW₀] at hRead
  change ∀ a b : WType, ∃ p : WType, ∀ z : WType,
    member_l ℳ z.val p.val ↔ z = a ∨ z = b at hPair
  intro x hx
  let x₀ : WType := ⟨x, hIW x hx⟩
  obtain ⟨p, hp⟩ := hPair x₀ x₀
  exact (hRead.2 x hx).mp ⟨p.val, p.property, (hp x₀).mpr (Or.inl rfl)⟩

def upper_sentence_m : Sentence ℒ := .forallE .set (upper_m [])

/-- 原商中的两条背景公理；不包含完整 Separation 或 Collection。 -/
def background_m : Sentence ℒ :=
  .conj SecondOrderAxioms.extensionality_m SecondOrderPairSet.formula_m

/-- 结论仍是原纯 ℒ 相对化公式，而非增加新的内部谓词符号。 -/
def conclusion_m {Ε : SortContext ℒ} (I : Term ℒ [] Ε .set) : Formula ℒ [] Ε :=
  .conj (PowerlessRelativeParameters.instance_m SecondOrderAxioms.extensionality_m I
    (fun v => nomatch v))
    (PowerlessRelativeParameters.instance_m upper_sentence_m I (fun v => nomatch v))

theorem conclusion_formula_l {Ε : SortContext ℒ} (ζ : Env ℳ [] Ε) (I : Term ℒ [] Ε .set) :
    (conclusion_m I).satisfies ζ ↔
      (∀ x y, member_l ℳ x (I.eval ζ) → member_l ℳ y (I.eval ζ) →
        (∀ z, member_l ℳ z (I.eval ζ) → (member_l ℳ z x ↔ member_l ℳ z y)) → x = y) ∧
      (∀ x, member_l ℳ x (I.eval ζ) → ∃ p, member_l ℳ p (I.eval ζ) ∧ member_l ℳ x p) := by
  match I with
  | .bvar v => nomatch v
  | .app f _ => nomatch f
  | .fvar _ =>
    apply and_congr ?_ Iff.rfl
    exact ⟨fun h x y hx hy hxy => h x hx y hy hxy,
      fun h x hx y hy hxy => h x y hx hy hxy⟩

theorem formula_l {Δ Ε : SortContext ℒ} (ζ : Env ℳ [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (hIW : subset_l I₀ W₀) (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hExt : SecondOrderAxioms.extensionality_m.TrueIn 𝒲)
    (hPair : SecondOrderPairSet.formula_m.TrueIn 𝒲)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (conclusion_m I).satisfies ζ := by
  apply (conclusion_formula_l ζ I).mpr
  rw [hI₀]
  exact ⟨extensionality_l (ℳ := ℳ) (I₀ := I₀) (W₀ := W₀) (hW := hW)
      ζ I W τ hIW hI₀ hW₀ hExt h,
    upper_l (ℳ := ℳ) (I₀ := I₀) (W₀ := W₀) (hW := hW)
      ζ I W τ hIW hI₀ hW₀ hPair h⟩

section Level

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {h𝒩 : Theory.Models 𝒩 SecondOrderArithmetic.theory_m}
  {B β I₁ W₁ ω : SecondOrderQuotient.type_l h𝒩}

local notation "𝒱" => SecondOrderQuotient.structure_l h𝒩

/-- 实际层的基础公理与同一个有限元素性结论给出塌缩所需两项守卫。 -/
theorem level_l {Δ Ε : SortContext ℒ} (ζ : Env 𝒱 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (hBase : ∀ x, SecondOrderQuotient.mem_l h𝒩 x B → ∀ y,
      SecondOrderQuotient.mem_l h𝒩 y x → SecondOrderQuotient.mem_l h𝒩 y B)
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l h𝒩 β)
    (hLevel : PowerlessRelativeHierarchySemantics.level_l h𝒩 B β W₁)
    (hωW : SecondOrderQuotient.mem_l h𝒩 ω W₁)
    (hIW : ∀ x, SecondOrderQuotient.mem_l h𝒩 x I₁ → SecondOrderQuotient.mem_l h𝒩 x W₁)
    (hI₁ : I.eval ζ = I₁) (hW₁ : W.eval ζ = W₁)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (∀ x y, SecondOrderQuotient.mem_l h𝒩 x I₁ → SecondOrderQuotient.mem_l h𝒩 y I₁ →
      (∀ z, SecondOrderQuotient.mem_l h𝒩 z I₁ →
        (SecondOrderQuotient.mem_l h𝒩 z x ↔ SecondOrderQuotient.mem_l h𝒩 z y)) → x = y) ∧
      (∀ x, SecondOrderQuotient.mem_l h𝒩 x I₁ →
        ∃ p, SecondOrderQuotient.mem_l h𝒩 p I₁ ∧ SecondOrderQuotient.mem_l h𝒩 x p) := by
  have hExt := PowerlessRelativeLimitSourceBasics.extensionality_l hBase hLevel hωW
  have hPair := PowerlessRelativeLimitSourceBasics.pairing_l hBase hLimit hLevel hωW
  have hIW₀ : subset_l (ℳ := 𝒱) I₁ W₁ := by
    simpa only [ThirdOrderSemantics.member_l, ThirdOrderSemantics.subset_l,
      SecondOrderQuotient.structure_l] using hIW
  constructor
  · simpa only [ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using
      extensionality_l (ℳ := 𝒱) (I₀ := I₁) (W₀ := W₁) (hW := ⟨ω, hωW⟩)
        ζ I W τ hIW₀ hI₁ hW₁ hExt h
  · simpa only [ThirdOrderSemantics.member_l, SecondOrderQuotient.structure_l] using
      upper_l (ℳ := 𝒱) (I₀ := I₁) (W₀ := W₁) (hW := ⟨ω, hωW⟩)
        ζ I W τ hIW₀ hI₁ hW₁ hPair h

/-- 所消费的实际层背景在原 Z₂ 推导核中已有带全部守卫的证明。 -/
theorem background_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeLimitSourceBasics.guarded_m background_m)) :=
  PowerlessRelativeLimitSourceBasics.derives_m background_m
    (fun _ _ _ _ _ _ hBase hLevel hLimit _ hωW =>
      ⟨PowerlessRelativeLimitSourceBasics.extensionality_l hBase hLevel hωW,
        PowerlessRelativeLimitSourceBasics.pairing_l hBase hLimit hLevel hωW⟩)

end Level

section Quotient

variable {ℳ₀ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 真实传递母域的外延性和配对来自原商及基础闭包，不预供母域源理论。 -/
theorem closed_formula_l (hℳ : Theory.Models ℳ₀ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    {I₁ W₁ : SecondOrderQuotient.type_l hℳ}
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₁)
    (hClosed : PowerlessRelativeFiniteHullAssignments.closed_l
      (𝒩 := SecondOrderQuotient.structure_l hℳ) W₁)
    (hNonempty : ∃ x, member_l (SecondOrderQuotient.structure_l hℳ) x W₁)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₁ W₁)
    (hI₁ : I.eval ζ = I₁) (hW₁ : W.eval ζ = W₁)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ) :
    (conclusion_m I).satisfies ζ := by
  let 𝒩 := PowerlessMemberStructure.structure_l
    (ℳ := SecondOrderQuotient.structure_l hℳ) W₁ hNonempty
  let C := PowerlessMemberStructure.type_l (ℳ := SecondOrderQuotient.structure_l hℳ) W₁
  have hExt : SecondOrderAxioms.extensionality_m.TrueIn 𝒩 := by
    change ∀ a b : C, (∀ z : C,
      SecondOrderQuotient.mem_l hℳ z.val a.val ↔ SecondOrderQuotient.mem_l hℳ z.val b.val) → a = b
    intro a b hab
    apply Subtype.ext
    apply SecondOrderQuotient.ext_l hℳ
    intro z
    exact ⟨fun hz => (hab ⟨z, hTrans a.val z a.property hz⟩).mp hz,
      fun hz => (hab ⟨z, hTrans b.val z b.property hz⟩).mpr hz⟩
  have hPair : SecondOrderPairSet.formula_m.TrueIn 𝒩 := by
    change ∀ a b : C, ∃ p : C, ∀ z : C,
      SecondOrderQuotient.mem_l hℳ z.val p.val ↔ z = a ∨ z = b
    intro a b
    obtain ⟨p, hp⟩ := SecondOrderPairObjects.pair_exists_l hℳ a.val b.val
    refine ⟨⟨p, hClosed.1 a.val b.val p a.property b.property hp⟩, fun z => ?_⟩
    exact (hp z.val).trans (or_congr
      ⟨Subtype.ext, congrArg Subtype.val⟩ ⟨Subtype.ext, congrArg Subtype.val⟩)
  exact formula_l (ℳ := SecondOrderQuotient.structure_l hℳ)
    (I₀ := I₁) (W₀ := W₁) (hW := hNonempty) ζ I W τ hIW hI₁ hW₁ hExt hPair h

end Quotient

#print axioms family_length_m
#print axioms distinguish_formula_l
#print axioms upper_formula_l
#print axioms distinguish_entry_l
#print axioms upper_entry_l
#print axioms family_formula_l
#print axioms append_l
#print axioms extensionality_l
#print axioms upper_l
#print axioms conclusion_formula_l
#print axioms formula_l
#print axioms level_l
#print axioms background_derives_m
#print axioms closed_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullExtensionality
