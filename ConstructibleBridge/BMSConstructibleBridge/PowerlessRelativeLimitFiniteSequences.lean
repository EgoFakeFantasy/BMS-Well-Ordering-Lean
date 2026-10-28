import BMSConstructibleBridge.PowerlessRelativeClassFiniteSequences
import BMSConstructibleBridge.PowerlessRelativeLimitClosure

/-! # 严格先前非零极限层上的有限序列集属于指定外层

实际 ω 与陪域 X 均为内层 E 的成员。每条内部有限映射属于 E，序列集
因而是 E 上以 ω、X 为参数的 Δ₀ 切片，并进入 Def(E)。该后继仍严格
低于给定外层极限阶段，所以整个序列集属于预定外层 C。
陪域成员前提不可只改为 X ⊆ E；切片还需实际参数 X 属于母层。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteSequences

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (type_l mem_l)
open PowerlessRelativeHierarchySemantics (level_l limit_l)
open PowerlessRelativeClassFiniteSequences (sequence_m sequence_delta_l sequence_formula_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

/-- 序列集进入固定外层；所有内部长度和实际有限映射都由原规格覆盖。 -/
theorem member_l {B δ E β C ω X S : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hInner : limit_l hℳ δ) (hE : level_l hℳ B δ E)
    (hOuter : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hEarlier : mem_l hℳ δ β)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hωE : mem_l hℳ ω E) (hXE : mem_l hℳ X E)
    (hS : PowerlessFiniteSequencesSyntax.spec_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) ω X S) : mem_l hℳ S C := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ hω K.omega_spec
  obtain ⟨a, D, ha, hD, hDef⟩ :=
    PowerlessRelativeLimitClosure.def_bound_l hℳ hBase hOuter hC hEarlier hE
  let φ : Formula ℒ [] [.set, .set, .set] := sequence_m
    (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
  let η : Env (SecondOrderQuotient.structure_l hℳ) [] [.set, .set] :=
    ((Env.empty).pushFree X).pushFree ω
  have hParams : ∀ s (v : Variable [SetTheory.SetSort.set, SetTheory.SetSort.set] s),
      mem_l hℳ (η.freeVal v) E := by
    intro s v
    cases v with
    | here => exact hωE
    | there v => cases v with
      | here => exact hXE
      | there v => nomatch v
  have hSD : mem_l hℳ S D := SecondOrderMemberDefBoundedSlice.member_l hℳ (φ := φ)
    hDef (PowerlessRelativeLevelClosure.transitive_l hℳ hBase hE)
    (sequence_delta_l _ _ _) η hParams (by
      intro f
      have hS' : mem_l hℳ f S ↔ PowerlessFiniteSequencesSyntax.sequence_l
          (ℳ := SecondOrderQuotient.structure_l hℳ) ω X f := hS f
      rw [hS']
      have hφ := sequence_formula_l (η.pushFree f)
        (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar .here)
      constructor
      · rintro ⟨n, hn, hMap⟩
        exact ⟨PowerlessRelativeLimitFiniteMaps.member_l hℳ hBase hInner hE K
          (hωEq ▸ hωE) hXE (hωEq ▸ hn) hMap, hφ.mpr ⟨n, hn, hMap⟩⟩
      · intro hf
        exact hφ.mp hf.2)
  exact (PowerlessRelativeLimitClosure.value_l hℳ hBase hOuter hC S).mpr
    ⟨a, D, ha, hD, hSD⟩

/-- 从原二阶实际序列集存在性取得同一个满足固定外层界的集合。 -/
theorem exists_l {B δ E β C ω X : type_l hℳ}
    (hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B)
    (hInner : limit_l hℳ δ) (hE : level_l hℳ B δ E)
    (hOuter : limit_l hℳ β) (hC : level_l hℳ B β C)
    (hEarlier : mem_l hℳ δ β)
    (hω : SecondOrderOmega.omega_l hℳ ω)
    (hωE : mem_l hℳ ω E) (hXE : mem_l hℳ X E) :
    ∃ S, mem_l hℳ S C ∧ PowerlessFiniteSequencesSyntax.spec_l
      (ℳ := SecondOrderQuotient.structure_l hℳ) ω X S := by
  obtain ⟨S, hS⟩ := SecondOrderFiniteSequencesDerives.exists_l hℳ ω hω X
  exact ⟨S, member_l hBase hInner hE hOuter hC hEarlier hω hωE hXE hS, hS⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeLimitFiniteSequences
