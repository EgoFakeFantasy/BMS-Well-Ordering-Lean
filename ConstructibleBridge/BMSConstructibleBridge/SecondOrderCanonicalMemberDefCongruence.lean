import BMSConstructibleBridge.SecondOrderCanonicalMemberDefSemantics

/-! # 唯一原图 Def 在换码下保持商相等

原始输出实数不必字面相等；商中的母对象相等足以由 Def 规格唯一性取得
输出对象相等。所有原图根证书和默认参数证书均由调用者的实际构造提供。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

theorem eq_l (hℳ : Theory.Models ℳ theory_m) (A B : SecondOrderGraph.code_l ℳ)
    (hAB : SecondOrderGraph.eq_l A B) {W W' : set_l ℳ}
    (hW : SecondOrderDomain.wf_l W (zero_l ℳ)) (hW' : SecondOrderDomain.wf_l W' (zero_l ℳ))
    (hA : SecondOrderCanonicalMemberDefGraph.canonical_l A.real A.root W)
    (hB : SecondOrderCanonicalMemberDefGraph.canonical_l B.real B.root W') :
    SecondOrderGraph.eq_l ⟨W, zero_l ℳ, hW⟩ ⟨W', zero_l ℳ, hW'⟩ := by
  obtain ⟨a, hDefault, V, E, D, Q, R, T, F, G, P, h⟩ := hA
  obtain ⟨b, hDefault', V', E', D', Q', R', T', F', G', P', h'⟩ := hB
  have hDef := SecondOrderCanonicalMemberDefSemantics.represents_l hℳ A hDefault h
  have hDef' := SecondOrderCanonicalMemberDefSemantics.represents_l hℳ B hDefault' h'
  have hInput := (SecondOrderQuotient.eq_iff_l hℳ A B).mpr hAB
  rw [hInput] at hDef
  exact (SecondOrderQuotient.eq_iff_l hℳ _ _).mp (SecondOrderMemberDef.unique_l hℳ hDef hDef')

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCanonicalMemberDefCongruence
