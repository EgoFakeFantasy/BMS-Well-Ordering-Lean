import BMSConstructibleBridge.PowerlessFiniteSequenceComposition
import BMSConstructibleBridge.PowerlessRelativeClassSequenceLift
import BMSConstructibleBridge.PowerlessFiniteSequencesSyntax

/-! # 类内有限序列复合的存在、唯一性及提升

复合是类内实际函数图；验证只比较受定义域和值域约束的求值。所用数值
序列来自规范编号逆图，不要求内部可数选择或完整 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceComposition

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem value_mem_l {f A D x y : type_l hℳ B}
    (hf : map_l (ℳ := structure_l hℳ B hBase) f A D)
    (hxy : value_l (ℳ := structure_l hℳ B hBase) f x y) :
    mem_l hℳ x.val A.val ∧ mem_l hℳ y.val D.val :=
  SecondOrderFunctionProperties.value_mem_l hℳ
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f A D).mp hf)
    ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x y).mp hxy)

theorem domain_unique_l {g A D ω : type_l hℳ B}
    (hg : map_l (ℳ := structure_l hℳ B hBase) g A ω)
    (hg' : map_l (ℳ := structure_l hℳ B hBase) g D ω) : A = D := by
  apply (PowerlessRelativeClassStructure.ext_l hℳ B hBase).eq_of_same_members
  intro x
  constructor
  · intro hx
    obtain ⟨y, ⟨_, hxy⟩, _⟩ := hg.2 x hx
    exact (value_mem_l hg' hxy).1
  · intro hx
    obtain ⟨y, ⟨_, hxy⟩, _⟩ := hg'.2 x hx
    exact (value_mem_l hg hxy).1

theorem unique_l {ω X G g f f' : type_l hℳ B}
    (hf : PowerlessFiniteSequenceComposition.holds_l (𝒩 := structure_l hℳ B hBase) ω X G g f)
    (hf' : PowerlessFiniteSequenceComposition.holds_l (𝒩 := structure_l hℳ B hBase) ω X G g f') : f = f' := by
  obtain ⟨n, _, hg, hfMap, hRead⟩ := hf
  obtain ⟨m, _, hg', hfMap', hRead'⟩ := hf'
  have hnm := domain_unique_l hg hg'
  subst m
  apply Subtype.ext
  apply PowerlessBMSQuotientRecursion.map_ext_l (hM := hℳ)
    (f := f.val) (g := f'.val) (A := n.val) (B := X.val) (D := X.val)
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f n X).mp hfMap)
    ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f' n X).mp hfMap')
  intro x y
  constructor
  · intro hxy
    have hmem := SecondOrderFunctionProperties.value_mem_l hℳ
      ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f n X).mp hfMap) hxy
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase n.property hmem.1⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hmem.2⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f' x' y').mp
      ((hRead' x' hmem.1 y' hmem.2).mpr ((hRead x' hmem.1 y' hmem.2).mp
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x' y').mpr hxy)))
  · intro hxy
    have hmem := SecondOrderFunctionProperties.value_mem_l hℳ
      ((PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f' n X).mp hfMap') hxy
    let x' : type_l hℳ B := ⟨x, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase n.property hmem.1⟩
    let y' : type_l hℳ B := ⟨y, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase X.property hmem.2⟩
    exact (PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f x' y').mp
      ((hRead x' hmem.1 y' hmem.2).mpr ((hRead' x' hmem.1 y' hmem.2).mp
        ((PowerlessRelativeClassFunctionAbsolute.value_l (hBase := hBase) f' x' y').mpr hxy)))

theorem exists_l {ω X G g : type_l hℳ B}
    (hG : map_l (ℳ := structure_l hℳ B hBase) G ω X)
    (hg : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := structure_l hℳ B hBase) ω ω g) :
    ∃ f : type_l hℳ B,
      PowerlessFiniteSequenceComposition.holds_l (𝒩 := structure_l hℳ B hBase) ω X G g f := by
  obtain ⟨n, hn, hgMap⟩ := hg
  obtain ⟨f, hfMap, hRead⟩ := PowerlessRelativeClassFunctionComposition.exists_l hgMap hG
  refine ⟨f, n, hn, hgMap, hfMap, fun k hk y hy => ⟨?_, ?_⟩⟩
  · intro hky
    exact ((hRead k y).mp hky).2.2
  · intro hky
    exact (hRead k y).mpr ⟨hk, hy, hky⟩

theorem lift_l {ω X G f : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hG : map_l (ℳ := structure_l hℳ B hBase) G ω X)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val X.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i y)
    (hf : PowerlessFiniteSequencesSyntax.sequence_l (ℳ := structure_l hℳ B hBase) ω X f) :
    ∃ g : type_l hℳ B,
      PowerlessFiniteSequenceComposition.holds_l (𝒩 := structure_l hℳ B hBase) ω X G g f := by
  obtain ⟨n, hn, hfMap⟩ := hf
  obtain ⟨g, hgMap, hLift⟩ := PowerlessRelativeClassSequenceLift.exists_l hω hOnto hfMap
  refine ⟨g, n, hn, hgMap, hfMap, fun k hk y _ => ⟨?_, ?_⟩⟩
  · intro hky
    obtain ⟨j, ⟨hj, hkj⟩, _⟩ := hgMap.2 k hk
    exact ⟨j, hj, hkj, hLift k j y hkj hky⟩
  · rintro ⟨j, _, hkj, hjy⟩
    obtain ⟨z, ⟨_, hkz⟩, _⟩ := hfMap.2 k hk
    have hzy := PowerlessRelativeClassFunctionComposition.value_unique_l hG (hLift k j z hkj hkz) hjy
    exact hzy ▸ hkz

#print axioms unique_l
#print axioms exists_l
#print axioms lift_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassSequenceComposition
