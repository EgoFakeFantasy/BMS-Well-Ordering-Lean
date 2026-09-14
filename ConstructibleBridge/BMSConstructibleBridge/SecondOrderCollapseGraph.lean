import BMSConstructibleBridge.SecondOrderMixedImage
import BMSConstructibleBridge.SecondOrderNaturalNumbers
import BMSConstructibleBridge.SecondOrderTransitiveSuperset

/-!
# 内部良基数图的坍缩值域及集合图

每个数根已经满足内部域时，以其图商对象为坍缩值。只对原关系的域域构造
传递值域和集合函数图，不要求原关系外延，也不调用宿主 Mostowski 坍缩。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCollapseGraph

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

def field_l (S : set_l ℳ) (a : num_l ℳ) : Prop := ∃ b, relation_l S a b ∨ relation_l S b a

def code_l (S : set_l ℳ) (hS : ∀ n, SecondOrderDomain.wf_l S n) (n : num_l ℳ) :
    SecondOrderGraph.code_l ℳ := ⟨S, n, hS n⟩

theorem field_exists_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ) :
    ∃ P : set_l ℳ, ∀ a, mem_l a P ↔ field_l S a := by
  let φ : Formula signature_m [] [.num, .set] :=
    .existsE .num (.disj (GraphSyntax.edge_m (.fvar (.there .here)) (.fvar .here) (.bvar .here))
      (GraphSyntax.edge_m (.fvar (.there .here)) (.bvar .here) (.fvar .here)))
  obtain ⟨P, hP⟩ := comprehension_l hℳ φ (pure_language_m _ rfl) ((Env.empty (M := ℳ)).pushFree S)
  refine ⟨P, fun a => (hP a).trans ?_⟩
  simp only [φ, Formula.satisfies, SecondOrderPairing.edge_l]
  rfl

theorem range_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) :
    ∃ U : SecondOrderGraph.code_l ℳ,
      (∀ X, SecondOrderGraph.mem_l X U ↔ ∃ n, field_l S n ∧ SecondOrderGraph.eq_l X (code_l S hS n)) ∧
      SecondOrderTransitiveSuperset.transitive_l U := by
  obtain ⟨P, hP⟩ := field_exists_l hℳ S
  obtain ⟨U, hU⟩ := SecondOrderGraftSemantics.exists_l hℳ S P (fun n _ => hS n)
  have h : ∀ X, SecondOrderGraph.mem_l X U ↔ ∃ n, field_l S n ∧ SecondOrderGraph.eq_l X (code_l S hS n) :=
    fun X => (hU X).trans (exists_congr (fun n => and_congr (hP n) Iff.rfl))
  refine ⟨U, h, ?_⟩
  intro B C hB hC
  obtain ⟨b, _, h₁⟩ := (h B).mp hB
  obtain ⟨c, hc, h₂⟩ := hC
  obtain ⟨d, hd, h₃⟩ := (SecondOrderBisimulation.match_l B.real S B.root b h₁).1 c hc
  exact (h C).mpr ⟨d, ⟨b, Or.inl hd⟩,
    SecondOrderBisimulation.trans_l hℳ C.real B.real S C.root c d h₂ h₃⟩

theorem identity_l (hℳ : Theory.Models ℳ theory_m) (S : set_l ℳ) :
    ∃ T : set_l ℳ, ∀ a b, relation_l T a b ↔ field_l S a ∧ a = b := by
  obtain ⟨P, hP⟩ := field_exists_l hℳ S
  let φ : Formula signature_m [] [.num, .num, .set] :=
    .conj (.rel .mem (.cons (.fvar .here) (.cons (.fvar (.there (.there .here))) .nil)))
      (.equal (.fvar .here) (.fvar (.there .here)))
  obtain ⟨T, hT⟩ := SecondOrderRelations.comprehension_l hℳ φ (pure_language_m _ rfl)
    ((Env.empty (M := ℳ)).pushFree P)
  refine ⟨T, fun a b => (hT a b).trans ?_⟩
  change (mem_l a P ∧ a = b) ↔ _
  rw [hP]

/-- 坍缩图本身是集合，完整成员由原域域中的有序对描述。 -/
theorem graph_l (hℳ : Theory.Models ℳ theory_m) (R S : set_l ℳ)
    (hR : ∀ a b, relation_l R a b ↔ SecondOrderOrder.lt_l a b)
    (hS : ∀ n, SecondOrderDomain.wf_l S n) :
    ∃ f : SecondOrderQuotient.type_l hℳ, ∀ p, SecondOrderQuotient.mem_l hℳ p f ↔
      ∃ n, field_l S n ∧ SecondOrderPairObjects.ordered_l hℳ
        (SecondOrderQuotient.mk_l hℳ (SecondOrderNaturalGraph.code_l hℳ R hR n))
        (SecondOrderQuotient.mk_l hℳ (code_l S hS n)) p := by
  obtain ⟨T, hT⟩ := identity_l hℳ S
  obtain ⟨f, hf⟩ := SecondOrderMixedImage.exists_l hℳ R S T
    (fun a b _ => ⟨SecondOrderNaturalGraph.wf_l hℳ R hR a, hS b⟩)
  refine ⟨f, fun p => (hf p).trans ?_⟩
  constructor
  · rintro ⟨a, b, h, hp⟩
    obtain ⟨h₁, rfl⟩ := (hT a b).mp h
    exact ⟨a, h₁, hp⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨n, n, (hT n n).mpr ⟨hn, rfl⟩, hp⟩

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderCollapseGraph
