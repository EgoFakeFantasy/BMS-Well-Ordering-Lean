import BMSConstructibleBridge.SecondOrderProgramAncestorBudget
import BMSConstructibleBridge.SecondOrderProgramAncestorStepCongruence

/-!
# 祖先迭代在不同参数上下文中的同步

父查询在两个上下文逐列一致时，两次原祖先迭代始终携带相同的当前列和累计表。
归纳不变量是原语言中的共同状态存在式，步数覆盖模型的全部内部自然数。
初始累计表不要求为空；后续链程序可以直接取零实例。两侧参数码与程序码均不必相等。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorIterationCongruence

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderPairing SecondOrderFunctions SecondOrderProgramSemantics
open SecondOrderProgramTotality SecondOrderProgramArithmetic SecondOrderProgramIteration
open SecondOrderProgramAncestorStep (step_m)
open SecondOrderProgramAncestorTransition (step_none_l step_some_l)
open SecondOrderProgramAncestorStepCongruence (step_congr_l)
open SecondOrderProgramAncestorBudget (state_m state_syntax_l)
open SecondOrderProgramListShift (output_m output_syntax_l)
open PrimitiveProgram (code_m graph_m)

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-- 两个实际迭代输出只在外层参数槽不同，列号与累计表完全相同。 -/
def coupled_l (R U : set_l ℳ) (s₁ s₂ x z n : num_l ℳ) : Prop := ∃ t v a b,
  value_l x (value_l t v) = a ∧ value_l z (value_l t v) = b ∧
    relation_l R (value_l s₁ n) a ∧ relation_l U (value_l s₂ n) b

/-- 自由槽为[n,s₁,s₂,x,z,R,U]，依次绑定共同列t、累计码v与两侧输出a、b。 -/
def coupled_m : Formula signature_m [] [.num, .num, .num, .num, .num, .set, .set] :=
  .existsE .num (.existsE .num (.existsE .num (.existsE .num (.conj
    (state_m (.fvar (.there (.there (.there .here))))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here)))
      (.bvar (.there .here)))
    (.conj (state_m (.fvar (.there (.there (.there (.there .here)))))
      (.bvar (.there (.there (.there .here)))) (.bvar (.there (.there .here))) (.bvar .here))
      (.conj (output_m (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there .here)) (.fvar .here) (.bvar (.there .here)))
        (output_m (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
          (.fvar (.there (.there .here))) (.fvar .here) (.bvar .here))))))))

/-- 同步存在式仅使用既有纯语言。 -/
theorem coupled_language_m : language_m coupled_m = true := pure_language_m _ rfl

/-- 实际归纳公式保留两个迭代图、两个初态及两个参数。 -/
theorem coupled_syntax_l (R U : set_l ℳ) (s₁ s₂ x z n : num_l ℳ) :
    Formula.satisfies ((((((((Env.empty (M := ℳ)).pushFree U).pushFree R).pushFree z).pushFree x).pushFree s₂).pushFree s₁).pushFree n)
      coupled_m ↔ coupled_l R U s₁ s₂ x z n := by
  simp only [coupled_m, coupled_l, Formula.satisfies, state_syntax_l, output_syntax_l]
  rfl

/-- 从相同列与累计器出发，任意内部步数后存在相同的列与累计器。 -/
theorem common_state_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m) {C D R U : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hU : graph_semantics_l (graph_m (repeat_m (step_m d))) U)
    (x z : num_l ℳ)
    (hparent : ∀ j q : num_l ℳ, relation_l C (value_l x j) q ↔ relation_l D (value_l z j) q)
    (k v n : num_l ℳ) : ∃ t w,
    relation_l R (value_l (value_l x (value_l k v)) n) (value_l x (value_l t w)) ∧
      relation_l U (value_l (value_l z (value_l k v)) n) (value_l z (value_l t w)) := by
  obtain ⟨S, _, hS⟩ := graph_total_l hℳ (step_m c)
  obtain ⟨T, _, hT⟩ := graph_total_l hℳ (step_m d)
  have hcoupled : coupled_l R U (value_l x (value_l k v)) (value_l z (value_l k v)) x z n := by
    apply induct_l hℳ coupled_m coupled_language_m
      (((((((Env.empty (M := ℳ)).pushFree U).pushFree R).pushFree z).pushFree x).pushFree
        (value_l z (value_l k v))).pushFree (value_l x (value_l k v)))
      (fun n => coupled_l R U (value_l x (value_l k v)) (value_l z (value_l k v)) x z n)
      (coupled_syntax_l R U (value_l x (value_l k v)) (value_l z (value_l k v)) x z) ?_ ?_ n
    · exact ⟨k, v, _, _, rfl, rfl,
        (repeat_zero_l hℳ (step_m c) hR _ _).mpr rfl,
        (repeat_zero_l hℳ (step_m d) hU _ _).mpr rfl⟩
    · rintro j ⟨t, w, a, b, ha, hb, hr, hu⟩
      subst a
      subst b
      obtain ⟨q, hq, _⟩ := function_of_semantics_l hℳ c hC (value_l x t)
      rcases predecessor_l hℳ q with rfl | ⟨p, rfl⟩
      · have hs := (step_none_l hℳ c hS hC hq w (value_l x (value_l t w))).mpr rfl
        have ht := (step_congr_l hℳ c d hC hD hS hT x z hparent t w t w).mp hs
        exact ⟨t, w, _, _, rfl, rfl,
          (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr ⟨_, hr, hs⟩,
          (repeat_succ_l hℳ (step_m d) hU hT _ j _).mpr ⟨_, hu, ht⟩⟩
      · have hs := (step_some_l hℳ c hS hC hq w
          (value_l x (value_l p (succ_l (value_l p w))))).mpr rfl
        have ht := (step_congr_l hℳ c d hC hD hS hT x z hparent t w p
          (succ_l (value_l p w))).mp hs
        exact ⟨p, succ_l (value_l p w), _, _, rfl, rfl,
          (repeat_succ_l hℳ (step_m c) hR hS _ j _).mpr ⟨_, hr, hs⟩,
          (repeat_succ_l hℳ (step_m d) hU hT _ j _).mpr ⟨_, hu, ht⟩⟩
  obtain ⟨t, w, a, b, ha, hb, hr, hu⟩ := hcoupled
  subst a
  subst b
  exact ⟨t, w, hr, hu⟩

/-- 函数性把共同存在升级为任意指定列与累计输出的双向对应。 -/
theorem repeat_congr_l (hℳ : Theory.Models ℳ theory_m) (c d : code_m) {C D R U : set_l ℳ}
    (hC : graph_semantics_l (graph_m c) C) (hD : graph_semantics_l (graph_m d) D)
    (hR : graph_semantics_l (graph_m (repeat_m (step_m c))) R)
    (hU : graph_semantics_l (graph_m (repeat_m (step_m d))) U)
    (x z : num_l ℳ)
    (hparent : ∀ j q : num_l ℳ, relation_l C (value_l x j) q ↔ relation_l D (value_l z j) q)
    (k v n t w : num_l ℳ) :
    relation_l R (value_l (value_l x (value_l k v)) n) (value_l x (value_l t w)) ↔
      relation_l U (value_l (value_l z (value_l k v)) n) (value_l z (value_l t w)) := by
  obtain ⟨a, b, hr, hu⟩ := common_state_l hℳ c d hC hD hR hU x z hparent k v n
  constructor
  · intro h
    have he := function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m c)) hR) hr h
    have hi := (SecondOrderPairingBounds.injective_l hℳ x (value_l a b) x (value_l t w) he).2
    exact (congrArg (value_l z) hi) ▸ hu
  · intro h
    have he := function_value_unique_l (function_of_semantics_l hℳ (repeat_m (step_m d)) hU) hu h
    have hi := (SecondOrderPairingBounds.injective_l hℳ z (value_l a b) z (value_l t w) he).2
    exact (congrArg (value_l x) hi) ▸ hr

#print axioms coupled_l
#print axioms coupled_m
#print axioms coupled_language_m
#print axioms coupled_syntax_l
#print axioms common_state_l
#print axioms repeat_congr_l

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramAncestorIterationCongruence
