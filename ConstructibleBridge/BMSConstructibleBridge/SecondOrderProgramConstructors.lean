import BMSConstructibleBridge.PrimitiveProgram
import BMSConstructibleBridge.SecondOrderBetaSequence
import BMSConstructibleBridge.SecondOrderUnpairing
import BMSConstructibleBridge.SecondOrderRelations
import BMSConstructibleBridge.SecondOrderFunctions
import BMSConstructibleBridge.SecondOrderPairing
import BMSConstructibleBridge.SecondOrderPairingBounds
import BMSConstructibleBridge.SecondOrderNumbers
import BMSConstructibleBridge.SecondOrderOrder
import BMSConstructibleBridge.SecondOrderProgramSemantics

/-!
# 任务24 整合模块 A：`code_m` 六个非递归构造的内部全函数图

按 Codex #1318 / #1334 的最小模块方案，把任务22 已验收的 §D 非递归部分（统一图理解助手
`graph_comprehension_l` 与原 zero/succ/left/right/comp/pair 六构造闭包）整理为正式模块。
这不是重写六构造，而是经审查允许的整合：证明体沿用任务22 的已核版本。

* 统一使用 WB `SecondOrderProgramSemantics.graph_semantics_l`（本文件 `open` 它），
  不再本地重定义，避免两套未接口的 `graph_semantics_l`。
* 只新增独立模块，不改聚合根 `BMSConstructibleBridge.lean`、163 冻结源、BMSTools、lakefile、工具链。
* 无 sorry / admit / 新公理；出口的公理足迹由 `SecondOrderProgramTotality` 末端统一审计。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramConstructors

open Logic FirstOrder SecondOrderSyntax SecondOrderArithmetic SecondOrderModel
open SecondOrderAlgebra SecondOrderPairing SecondOrderNumbers
open SecondOrderBetaSequence PrimitiveFormulas SecondOrderProgramSemantics

set_option autoImplicit false

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} signature_m}

/-! ## 求值助手与统一图理解助手 -/

/-- 自由首槽在 `pushFree` 环境中的求值。 -/
theorem eval_fvar_here_l {Δ : SortContext signature_m} (η : Env ℳ [] Δ) (a : num_l ℳ) :
    Term.eval (η.pushFree a) (.fvar .here : Term signature_m [] (.num :: Δ) .num) = a := by
  simp [Term.eval, Env.pushFree, Assignment.push]

/-- 自由次槽在两次 `pushFree` 环境中的求值。 -/
theorem eval_fvar_there_here_l {Δ : SortContext signature_m} (η : Env ℳ [] Δ) (a b : num_l ℳ) :
    Term.eval ((η.pushFree b).pushFree a)
      (.fvar (.there .here) : Term signature_m [] (.num :: .num :: Δ) .num) = b := by
  simp [Term.eval, Env.pushFree, Assignment.push]

/-- **§D 核心助手**：统一值语义 + 全域唯一 ⇒ 存在内部集合 `X`，`X` 是全函数图且逐点等于
`F.form` 的语义。对 `F.form` 的自由槽 0/1 实例调用 `SecondOrderRelations.comprehension_l`；
输入在首槽。必须保留任意模型语义前提 `hsem`：不能用 `F.sound`（只约束标准模型 `structure_l`）。 -/
theorem graph_comprehension_l (hℳ : Theory.Models ℳ theory_m) {f : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (R : num_l ℳ → num_l ℳ → Prop)
    (hsem : ∀ {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ)
        (s t : Term signature_m Γ Δ .num),
      Formula.satisfies η (F.form s t) ↔ R (s.eval η) (t.eval η))
    (huniq : ∀ a : num_l ℳ, ∃! b : num_l ℳ, R a b) :
    ∃ X : set_l ℳ, SecondOrderFunctions.function_l X ∧ graph_semantics_l F X := by
  have hlang : SecondOrderArithmetic.language_m
      (F.form (.fvar .here) (.fvar (.there .here)) :
        Formula signature_m [] [.num, .num]) = true :=
    SecondOrderArithmetic.pure_language_m _ (F.pure _ _ rfl rfl)
  obtain ⟨X, hX⟩ := SecondOrderRelations.comprehension_l hℳ
    (F.form (.fvar .here) (.fvar (.there .here))) hlang (Env.empty (M := ℳ))
  have hXR : ∀ m n : num_l ℳ, relation_l X m n ↔ R m n := by
    intro m n
    rw [hX m n]
    have e1 : Term.eval (((Env.empty (M := ℳ)).pushFree n).pushFree m)
        (.fvar .here : Term signature_m [] [.num, .num] .num) = m :=
      eval_fvar_here_l ((Env.empty (M := ℳ)).pushFree n) m
    have e2 : Term.eval (((Env.empty (M := ℳ)).pushFree n).pushFree m)
        (.fvar (.there .here) : Term signature_m [] [.num, .num] .num) = n :=
      eval_fvar_there_here_l (Env.empty (M := ℳ)) m n
    simpa [e1, e2] using hsem (((Env.empty (M := ℳ)).pushFree n).pushFree m)
      (.fvar .here) (.fvar (.there .here))
  refine ⟨X, ?_, ?_⟩
  · intro n
    obtain ⟨b, hb, hu⟩ := huniq n
    refine ⟨b, (hXR n b).mpr hb, ?_⟩
    intro m hm
    exact hu m ((hXR n m).mp hm)
  · intro Γ Δ η s t
    rw [hXR (s.eval η) (t.eval η)]
    exact hsem η s t

/-! ## 构造 1：zero（零函数） -/

theorem zero_semantics_l (_hℳ : Theory.Models ℳ theory_m)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (PrimitiveFormulas.zero_l.form s t) ↔ zero_l ℳ = t.eval η := by
  rfl

theorem zero_unique_l (_hℳ : Theory.Models ℳ theory_m) (_a : num_l ℳ) :
    ∃! b : num_l ℳ, zero_l ℳ = b :=
  ⟨zero_l ℳ, rfl, fun _ hb => hb.symm⟩

theorem zero_graph_l (hℳ : Theory.Models ℳ theory_m) :
    ∃ X : set_l ℳ, SecondOrderFunctions.function_l X ∧
      graph_semantics_l PrimitiveFormulas.zero_l X :=
  graph_comprehension_l hℳ PrimitiveFormulas.zero_l (fun _ b => zero_l ℳ = b)
    (zero_semantics_l hℳ) (zero_unique_l hℳ)

/-! ## 构造 2：succ（后继函数） -/

theorem succ_semantics_l (_hℳ : Theory.Models ℳ theory_m)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (PrimitiveFormulas.succ_l.form s t) ↔ succ_l (s.eval η) = t.eval η := by
  rfl

theorem succ_unique_l (_hℳ : Theory.Models ℳ theory_m) (a : num_l ℳ) :
    ∃! b : num_l ℳ, succ_l a = b :=
  ⟨succ_l a, rfl, fun _ hb => hb.symm⟩

theorem succ_graph_l (hℳ : Theory.Models ℳ theory_m) :
    ∃ X : set_l ℳ, SecondOrderFunctions.function_l X ∧
      graph_semantics_l PrimitiveFormulas.succ_l X :=
  graph_comprehension_l hℳ PrimitiveFormulas.succ_l (fun a b => succ_l a = b)
    (succ_semantics_l hℳ) (succ_unique_l hℳ)

/-! ## 构造 3 / 4：left / right（配对两投影） -/

theorem left_semantics_l (hℳ : Theory.Models ℳ theory_m)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (PrimitiveFormulas.left_l.form s t) ↔
      (SecondOrderUnpairing.value_l hℳ (s.eval η)).1 = t.eval η :=
  SecondOrderUnpairing.left_l hℳ η s t

theorem left_unique_l (hℳ : Theory.Models ℳ theory_m) (a : num_l ℳ) :
    ∃! b : num_l ℳ, (SecondOrderUnpairing.value_l hℳ a).1 = b :=
  ⟨(SecondOrderUnpairing.value_l hℳ a).1, rfl, fun _ hb => hb.symm⟩

theorem left_graph_l (hℳ : Theory.Models ℳ theory_m) :
    ∃ X : set_l ℳ, SecondOrderFunctions.function_l X ∧
      graph_semantics_l PrimitiveFormulas.left_l X :=
  graph_comprehension_l hℳ PrimitiveFormulas.left_l
    (fun a b => (SecondOrderUnpairing.value_l hℳ a).1 = b)
    (left_semantics_l hℳ) (left_unique_l hℳ)

theorem right_semantics_l (hℳ : Theory.Models ℳ theory_m)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (PrimitiveFormulas.right_l.form s t) ↔
      (SecondOrderUnpairing.value_l hℳ (s.eval η)).2 = t.eval η :=
  SecondOrderUnpairing.right_l hℳ η s t

theorem right_unique_l (hℳ : Theory.Models ℳ theory_m) (a : num_l ℳ) :
    ∃! b : num_l ℳ, (SecondOrderUnpairing.value_l hℳ a).2 = b :=
  ⟨(SecondOrderUnpairing.value_l hℳ a).2, rfl, fun _ hb => hb.symm⟩

theorem right_graph_l (hℳ : Theory.Models ℳ theory_m) :
    ∃ X : set_l ℳ, SecondOrderFunctions.function_l X ∧
      graph_semantics_l PrimitiveFormulas.right_l X :=
  graph_comprehension_l hℳ PrimitiveFormulas.right_l
    (fun a b => (SecondOrderUnpairing.value_l hℳ a).2 = b)
    (right_semantics_l hℳ) (right_unique_l hℳ)

/-! ## 构造 5：comp（复合，先 G 后 F） -/

theorem comp_semantics_l (_hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η ((F.comp_l G).form s t) ↔
      ∃ m : num_l ℳ, relation_l XG (s.eval η) m ∧ relation_l XF m (t.eval η) := by
  simp only [PrimitiveFormulas.graph_l.comp_l, Formula.satisfies]
  constructor
  · rintro ⟨m, hG', hF'⟩
    refine ⟨m, ?_, ?_⟩
    · have hg₁ : relation_l XG ((s.weakenBound sort_m.num).eval (Env.pushBound η m)) m := by
        simpa [Term.eval, Assignment.push, Env.pushBound] using
          (hG (Env.pushBound η m) (s.weakenBound sort_m.num) (.bvar .here)).mp hG'
      simpa [Term.eval_weakenBound] using hg₁
    · have hf₁ : relation_l XF m ((t.weakenBound sort_m.num).eval (Env.pushBound η m)) := by
        simpa [Term.eval, Assignment.push, Env.pushBound] using
          (hF (Env.pushBound η m) (.bvar .here) (t.weakenBound sort_m.num)).mp hF'
      simpa [Term.eval_weakenBound] using hf₁
  · rintro ⟨m, hG', hF'⟩
    refine ⟨m, ?_, ?_⟩
    · have hg₁ : relation_l XG ((s.weakenBound sort_m.num).eval (Env.pushBound η m)) m :=
        by simpa [Term.eval_weakenBound] using hG'
      simpa [Term.eval, Assignment.push, Env.pushBound] using
        (hG (Env.pushBound η m) (s.weakenBound sort_m.num) (.bvar .here)).mpr hg₁
    · have hf₁ : relation_l XF m ((t.weakenBound sort_m.num).eval (Env.pushBound η m)) :=
        by simpa [Term.eval_weakenBound] using hF'
      refine (hF (Env.pushBound η m) (.bvar .here) (t.weakenBound sort_m.num)).mpr ?_
      simpa [Term.eval, Assignment.push, Env.pushBound] using hf₁

theorem comp_unique_l (_hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (_F : PrimitiveFormulas.graph_l f) (_G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hXF : SecondOrderFunctions.function_l XF)
    (hXG : SecondOrderFunctions.function_l XG) (a : num_l ℳ) :
    ∃! b : num_l ℳ, ∃ m : num_l ℳ, relation_l XG a m ∧ relation_l XF m b := by
  obtain ⟨m, hm, hmu⟩ := hXG a
  obtain ⟨b, hb, hbu⟩ := hXF m
  refine ⟨b, ⟨m, hm, hb⟩, ?_⟩
  rintro b' ⟨m', hm', hb'⟩
  have hm_eq : m' = m := hmu m' hm'
  subst hm_eq
  exact hbu b' hb'

theorem comp_graph_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    (hXF : SecondOrderFunctions.function_l XF) (hXG : SecondOrderFunctions.function_l XG) :
    ∃ X : set_l ℳ, SecondOrderFunctions.function_l X ∧
      graph_semantics_l (F.comp_l G) X :=
  graph_comprehension_l hℳ (F.comp_l G)
    (fun a b => ∃ m : num_l ℳ, relation_l XG a m ∧ relation_l XF m b)
    (comp_semantics_l hℳ F G XF XG hF hG) (comp_unique_l hℳ F G XF XG hXF hXG)

/-! ## 构造 6：pair（两子图配对） -/

theorem pair_semantics_l (_hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    {Γ Δ : SortContext signature_m} (η : Env ℳ Γ Δ) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η ((F.pair_l G).form s t) ↔
      ∃ u v : num_l ℳ,
        relation_l XF (s.eval η) u ∧ relation_l XG (s.eval η) v ∧ value_l u v = t.eval η := by
  simp only [PrimitiveFormulas.graph_l.pair_l]
  change (∃ w₁ w₀ : num_l ℳ,
      Formula.satisfies (Env.pushBound (Env.pushBound η w₁) w₀)
        (F.form ((s.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here))) ∧
      Formula.satisfies (Env.pushBound (Env.pushBound η w₁) w₀)
        (G.form ((s.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here)) ∧
      Formula.satisfies (Env.pushBound (Env.pushBound η w₁) w₀)
        (PrimitiveFormulas.pair_m (.bvar (.there .here)) (.bvar .here)
          ((t.weakenBound sort_m.num).weakenBound sort_m.num))) ↔ _
  constructor
  · rintro ⟨w₁, w₀, hF', hG', hp⟩
    refine ⟨w₁, w₀, ?_, ?_, ?_⟩
    · have hf₁ : relation_l XF
          (((s.weakenBound sort_m.num).weakenBound sort_m.num).eval
            (Env.pushBound (Env.pushBound η w₁) w₀)) w₁ := by
        simpa [Term.eval, Assignment.push, Env.pushBound] using
          (hF (Env.pushBound (Env.pushBound η w₁) w₀)
            ((s.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here))).mp hF'
      simpa [Term.eval_weakenBound] using hf₁
    · have hg₁ : relation_l XG
          (((s.weakenBound sort_m.num).weakenBound sort_m.num).eval
            (Env.pushBound (Env.pushBound η w₁) w₀)) w₀ := by
        simpa [Term.eval, Assignment.push, Env.pushBound] using
          (hG (Env.pushBound (Env.pushBound η w₁) w₀)
            ((s.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here)).mp hG'
      simpa [Term.eval_weakenBound] using hg₁
    · have hp₁ : value_l w₁ w₀ =
          ((t.weakenBound sort_m.num).weakenBound sort_m.num).eval
            (Env.pushBound (Env.pushBound η w₁) w₀) := by
        simpa [Term.eval, Assignment.push, Env.pushBound] using
          (SecondOrderPairing.formula_l (Env.pushBound (Env.pushBound η w₁) w₀)
            (.bvar (.there .here)) (.bvar .here)
            ((t.weakenBound sort_m.num).weakenBound sort_m.num)).mp hp
      simpa [Term.eval_weakenBound] using hp₁
  · rintro ⟨u, v, hF', hG', hp⟩
    refine ⟨u, v, ?_, ?_, ?_⟩
    · have hf₁ : relation_l XF
          (((s.weakenBound sort_m.num).weakenBound sort_m.num).eval
            (Env.pushBound (Env.pushBound η u) v)) u := by
        simpa [Term.eval_weakenBound] using hF'
      simpa [Term.eval, Assignment.push, Env.pushBound] using
        (hF (Env.pushBound (Env.pushBound η u) v)
          ((s.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar (.there .here))).mpr hf₁
    · have hg₁ : relation_l XG
          (((s.weakenBound sort_m.num).weakenBound sort_m.num).eval
            (Env.pushBound (Env.pushBound η u) v)) v := by
        simpa [Term.eval_weakenBound] using hG'
      simpa [Term.eval, Assignment.push, Env.pushBound] using
        (hG (Env.pushBound (Env.pushBound η u) v)
          ((s.weakenBound sort_m.num).weakenBound sort_m.num) (.bvar .here)).mpr hg₁
    · have hp₁ : value_l u v =
          ((t.weakenBound sort_m.num).weakenBound sort_m.num).eval
            (Env.pushBound (Env.pushBound η u) v) := by
        simpa [Term.eval_weakenBound] using hp
      refine (SecondOrderPairing.formula_l (Env.pushBound (Env.pushBound η u) v)
        (.bvar (.there .here)) (.bvar .here)
        ((t.weakenBound sort_m.num).weakenBound sort_m.num)).mpr ?_
      simpa [Term.eval, Assignment.push, Env.pushBound] using hp₁

theorem pair_unique_l (_hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (_F : PrimitiveFormulas.graph_l f) (_G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hXF : SecondOrderFunctions.function_l XF)
    (hXG : SecondOrderFunctions.function_l XG) (a : num_l ℳ) :
    ∃! b : num_l ℳ, ∃ u v : num_l ℳ,
      relation_l XF a u ∧ relation_l XG a v ∧ value_l u v = b := by
  obtain ⟨u, hu, hu'⟩ := hXF a
  obtain ⟨v, hv, hv'⟩ := hXG a
  refine ⟨value_l u v, ⟨u, v, hu, hv, rfl⟩, ?_⟩
  rintro b ⟨u', v', hu'', hv'', hb⟩
  have : u' = u := hu' u' hu''
  subst this
  have : v' = v := hv' v' hv''
  subst this
  exact hb.symm

theorem pair_graph_l (hℳ : Theory.Models ℳ theory_m) {f g : Nat → Nat}
    (F : PrimitiveFormulas.graph_l f) (G : PrimitiveFormulas.graph_l g)
    (XF XG : set_l ℳ) (hF : graph_semantics_l F XF) (hG : graph_semantics_l G XG)
    (hXF : SecondOrderFunctions.function_l XF) (hXG : SecondOrderFunctions.function_l XG) :
    ∃ X : set_l ℳ, SecondOrderFunctions.function_l X ∧
      graph_semantics_l (F.pair_l G) X :=
  graph_comprehension_l hℳ (F.pair_l G)
    (fun a b => ∃ u v : num_l ℳ, relation_l XF a u ∧ relation_l XG a v ∧ value_l u v = b)
    (pair_semantics_l hℳ F G XF XG hF hG) (pair_unique_l hℳ F G XF XG hXF hXG)

end YesMetaZFC.BMS.ConstructibleBridge.SecondOrderProgramConstructors
