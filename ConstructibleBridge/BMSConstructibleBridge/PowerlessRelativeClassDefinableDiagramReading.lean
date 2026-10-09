import BMSConstructibleBridge.PowerlessDefinableMembershipDiagram
import BMSConstructibleBridge.PowerlessRelativeClassFunctionAbsolute
import BMSConstructibleBridge.PowerlessRelativeClassPair

/-! # 单值数码求值的同一隶属图读数

纯隶属 ℒ，背景原 Z₂。给定完整求值同值及实际输出资格，原 raw
边同类内边双向一致；任何类内精确分离图必与原规范图相等。
这里只证明认同，不把输出资格当作分离存在性，也不改原图编号。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDefinableDiagramReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)
open PowerlessDefinableMembershipDiagram (edge_l spec_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ z, mem_l hℳ z B → ∀ t, mem_l hℳ t z → mem_l hℳ t B}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒩₀" => structure_l hℳ B hBase
local notation "M" => type_l hℳ B

theorem edge_reading_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hRead : ∀ n y : M, ψ.satisfies ((ξ.pushFree n.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree n).pushFree y))
    (hOutputs : ∀ (n : M) y, ψ.satisfies ((ξ.pushFree n.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y) (n m : M) :
    edge_l φ η n m ↔ edge_l ψ ξ n.val m.val := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    exact ⟨a.val, b.val, (hRead n a).mpr ha, (hRead m b).mpr hb, hab⟩
  · rintro ⟨a, b, ha, hb, hab⟩
    let a₀ : M := ⟨a, hOutputs n a ha⟩
    let b₀ : M := ⟨b, hOutputs m b hb⟩
    exact ⟨a₀, b₀, (hRead n a₀).mp ha, (hRead m b₀).mp hb, hab⟩

theorem same_l {Δ Θ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ψ : Formula ℒ [] (.set :: .set :: Θ))
    (η : Env 𝒩₀ [] Δ) (ξ : Env 𝒱 [] Θ)
    (hRead : ∀ n y : M, ψ.satisfies ((ξ.pushFree n.val).pushFree y.val) ↔
      φ.satisfies ((η.pushFree n).pushFree y))
    (hOutputs : ∀ (n : M) y, ψ.satisfies ((ξ.pushFree n.val).pushFree y) →
      PowerlessRelativeClassCorrespondence.member_l hℳ B y)
    (ω Z : M) (A : SecondOrderQuotient.type_l hℳ)
    (hA : spec_l ψ ξ ω.val A) (hZ : spec_l φ η ω Z) : A = Z.val := by
  apply SecondOrderQuotient.ext_l hℳ
  intro p
  constructor
  · intro hp
    obtain ⟨n, m, hn, hm, hEdge, hPair⟩ := (hA p).mp hp
    let n₀ : M := ⟨n, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hn⟩
    let m₀ : M := ⟨m, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property hm⟩
    let p₀ : M := ⟨p, PowerlessRelativeClassPair.ordered_l hℳ hBase n₀.property m₀.property hPair⟩
    exact (hZ p₀).mpr ⟨n₀, m₀, hn, hm,
      (edge_reading_l φ ψ η ξ hRead hOutputs n₀ m₀).mpr hEdge,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) n₀ m₀ p₀).mpr hPair⟩
  · intro hp
    let p₀ : M := ⟨p, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase Z.property hp⟩
    obtain ⟨n, m, hn, hm, hEdge, hPair⟩ := (hZ p₀).mp hp
    exact (hA p).mpr ⟨n.val, m.val, hn, hm,
      (edge_reading_l φ ψ η ξ hRead hOutputs n m).mp hEdge,
      (PowerlessRelativeClassFunctionAbsolute.ordered_l (hBase := hBase) n m p₀).mp hPair⟩

#print axioms edge_reading_l
#print axioms same_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassDefinableDiagramReading
