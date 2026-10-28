import BMSConstructibleBridge.SecondOrderProgramRectangular

/-!
# 当前高度规范化的内部数组集合

规范化要求共同列长等于同一数组的实际支撑高度，而不是种子高度或外部上界。
下述实际纯公式供原理解公理收集内部集合，再交给内部轨迹归纳使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramNormalized

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing
open SecondOrderProgramRectangular (rectangular_l rectangular_m rectangular_syntax_l)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 实际宽度与共同列高存在，而且该列高正是同一数组的当前支撑高度。 -/
def normalized_l (H L E : set_l ℳ) (x : num_l ℳ) : Prop :=
  ∃ n h, rectangular_l L E x n h ∧ relation_l H x h

/-- 自由槽[x,H,L,E]；绑定实际宽度n和同一实际高度h。 -/
def normalized_m : Formula signature_m [] [.num, .set, .set, .set] :=
  .existsE .num (.existsE .num (.conj
    (rectangular_m (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar .here) (.bvar (.there .here)) (.bvar .here))
    (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))))

/-- 公式与值语义保留同一数组、同一高度及原读取和长度关系。 -/
theorem normalized_syntax_l (H L E : set_l ℳ) (x : num_l ℳ) :
    Formula.satisfies (((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree H).pushFree x)
      normalized_m ↔ normalized_l H L E x := by
  simp only [normalized_m, normalized_l, Formula.satisfies, rectangular_syntax_l,
    SecondOrderPairing.edge_l]
  rfl

/-- 规范化数组码构成模型内部集合；后续不对任意外部谓词直接归纳。 -/
theorem normalized_set_l (hℳ : Theory.Models ℳ theory_m) (H L E : set_l ℳ) :
    ∃ S : set_l ℳ, ∀ x, mem_l x S ↔ normalized_l H L E x := by
  obtain ⟨S, hS⟩ := comprehension_l hℳ normalized_m (pure_language_m _ rfl)
    ((((Env.empty (M := ℳ)).pushFree E).pushFree L).pushFree H)
  exact ⟨S, fun x => (hS x).trans (normalized_syntax_l H L E x)⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramNormalized
