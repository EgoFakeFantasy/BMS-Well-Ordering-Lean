import BMSConstructibleBridge.PowerlessWholeCollapseTruth
import BMSConstructibleBridge.PowerlessRelativeFiniteHullClosure

/-! # 原虚拟全像的真实操作闭包传到同一坍缩值域

源域仍是原 image 谓词，不收集为集合。原全同构及目标的真实传递性
使任意目标成员都有原逆像；真实无序对和二元并的规格因而完整传输。
目标操作的任意 raw 候选由原商外延性认同，不假定 T 属于 Class。
这是后续原覆盖包读回的语义辅助接口，实际程序消去闭包前提另行装配。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessWholeCollapseClosure

open Logic FirstOrder ThirdOrderSemantics
open PowerlessDefinableMembershipIsomorphism (image_l project_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "Raw" => SecondOrderQuotient.type_l hℳ
local notation "ε" => SecondOrderQuotient.mem_l hℳ

def closed_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C : Raw) : Prop :=
  (∀ a b p, image_l φ η C a → image_l φ η C b →
    ThirdOrderSemantics.pair_l (ℳ := 𝒱) a b p → image_l φ η C p) ∧
  (∀ a b p, image_l φ η C a → image_l φ η C b →
    PowerlessRelativeFiniteHullAssignments.binary_l (𝒩 := 𝒱) a b p → image_l φ η C p)

theorem pair_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H : Raw)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T)
    {a b p x y q : Raw} (hax : project_l φ η C H a x)
    (hby : project_l φ η C H b y) (hpq : project_l φ η C H p q)
    (hqT : ε q T) (hp : ThirdOrderSemantics.pair_l (ℳ := 𝒱) a b p) :
    ThirdOrderSemantics.pair_l (ℳ := 𝒱) x y q := by
  intro z
  constructor
  · intro hzq
    obtain ⟨v, hvz⟩ := hIso.2.2.2.2 z (hTrans q z hqT hzq)
    have hvp := (hIso.2.2.2.1 v p z q hvz hpq).mpr hzq
    rcases (hp v).mp hvp with hva | hvb
    · rw [hva] at hvz
      exact Or.inl (hIso.2.2.1 a z x hvz hax)
    · rw [hvb] at hvz
      exact Or.inr (hIso.2.2.1 b z y hvz hby)
  · rintro (hzx | hzy)
    · rw [hzx]
      exact (hIso.2.2.2.1 a p x q hax hpq).mp ((hp a).mpr (Or.inl rfl))
    · rw [hzy]
      exact (hIso.2.2.2.1 b p y q hby hpq).mp ((hp b).mpr (Or.inr rfl))

theorem binary_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H : Raw)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T)
    {a b p x y q : Raw} (hax : project_l φ η C H a x)
    (hby : project_l φ η C H b y) (hpq : project_l φ η C H p q)
    (hxT : ε x T) (hyT : ε y T) (hqT : ε q T)
    (hp : PowerlessRelativeFiniteHullAssignments.binary_l (𝒩 := 𝒱) a b p) :
    PowerlessRelativeFiniteHullAssignments.binary_l (𝒩 := 𝒱) x y q := by
  intro z
  constructor
  · intro hzq
    obtain ⟨v, hvz⟩ := hIso.2.2.2.2 z (hTrans q z hqT hzq)
    rcases (hp v).mp ((hIso.2.2.2.1 v p z q hvz hpq).mpr hzq) with hva | hvb
    · exact Or.inl ((hIso.2.2.2.1 v a z x hvz hax).mp hva)
    · exact Or.inr ((hIso.2.2.2.1 v b z y hvz hby).mp hvb)
  · rintro (hzx | hzy)
    · obtain ⟨v, hvz⟩ := hIso.2.2.2.2 z (hTrans x z hxT hzx)
      have hva := (hIso.2.2.2.1 v a z x hvz hax).mpr hzx
      exact (hIso.2.2.2.1 v p z q hvz hpq).mp ((hp v).mpr (Or.inl hva))
    · obtain ⟨v, hvz⟩ := hIso.2.2.2.2 z (hTrans y z hyT hzy)
      have hvb := (hIso.2.2.2.1 v b z y hvz hby).mpr hzy
      exact (hIso.2.2.2.1 v p z q hvz hpq).mp ((hp v).mpr (Or.inr hvb))

theorem target_l {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: .set :: Δ))
    (η : Env 𝒱 [] Δ) (C T H : Raw)
    (hIso : PowerlessDefinableWholeCollapse.isomorphism_l φ η C T H)
    (hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) T)
    (hClosed : closed_l φ η C) :
    PowerlessRelativeFiniteHullAssignments.closed_l (𝒩 := 𝒱) T := by
  constructor
  · intro x y p hx hy hp
    obtain ⟨a, hax⟩ := hIso.2.2.2.2 x hx
    obtain ⟨b, hby⟩ := hIso.2.2.2.2 y hy
    have haI : image_l φ η C a := by
      obtain ⟨n, hn, hna, _⟩ := hax
      exact ⟨n, hn, hna⟩
    have hbI : image_l φ η C b := by
      obtain ⟨m, hm, hmb, _⟩ := hby
      exact ⟨m, hm, hmb⟩
    obtain ⟨c, hc⟩ := SecondOrderPairObjects.pair_exists_l hℳ a b
    obtain ⟨q, hqT, hcq⟩ := hIso.1 c (hClosed.1 a b c haI hbI hc)
    have hq := pair_l φ η C T H hIso hTrans hax hby hcq hqT hc
    have hEq : p = q := SecondOrderQuotient.ext_l hℳ p q (fun z => (hp z).trans (hq z).symm)
    exact hEq.symm ▸ hqT
  · intro x y p hx hy hp
    obtain ⟨a, hax⟩ := hIso.2.2.2.2 x hx
    obtain ⟨b, hby⟩ := hIso.2.2.2.2 y hy
    have haI : image_l φ η C a := by
      obtain ⟨n, hn, hna, _⟩ := hax
      exact ⟨n, hn, hna⟩
    have hbI : image_l φ η C b := by
      obtain ⟨m, hm, hmb, _⟩ := hby
      exact ⟨m, hm, hmb⟩
    obtain ⟨c, hc⟩ := PowerlessRelativeFiniteHullClosure.binary_exists_l hℳ a b
    obtain ⟨q, hqT, hcq⟩ := hIso.1 c (hClosed.2 a b c haI hbI hc)
    have hq := binary_l φ η C T H hIso hTrans hax hby hcq hx hy hqT hc
    have hEq : p = q := SecondOrderQuotient.ext_l hℳ p q (fun z => (hp z).trans (hq z).symm)
    exact hEq.symm ▸ hqT

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessWholeCollapseClosure
