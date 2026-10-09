import BMSConstructibleBridge.SecondOrderGraft

/-! # 新根拼接的实数唯一性

零与后继穷尽原模型数域，所以完整拼接规格决定整个模型实数。该证明不
要求原图良基；用于全域实数操作时，域保持性需另行核验。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalGraft

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem unique_l (hℳ : Theory.Models ℳ theory_m) {R P G H : set_l ℳ}
    (hG : SecondOrderGraft.spec_l R P G) (hH : SecondOrderGraft.spec_l R P H) : G = H := by
  apply SecondOrderRelations.ext_l hℳ
  intro c d
  rcases predecessor_l hℳ c with rfl | ⟨c, rfl⟩
  · exact iff_of_false (hG.zero d) (hH.zero d)
  · rcases predecessor_l hℳ d with rfl | ⟨d, rfl⟩
    · exact (hG.root c).trans (hH.root c).symm
    · exact (hG.shift c d).trans (hH.shift c d).symm

theorem exists_l (hℳ : Theory.Models ℳ theory_m) (R P : set_l ℳ) :
    ∃! G, SecondOrderGraft.spec_l R P G := by
  obtain ⟨G, hG⟩ := SecondOrderGraft.exists_l hℳ R P
  exact ⟨G, hG, fun H hH => unique_l hℳ hH hG⟩

#print axioms unique_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalGraft
