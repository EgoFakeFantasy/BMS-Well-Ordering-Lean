import BMSConstructibleBridge.PowerlessMemberBounded
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.PowerlessRelativeCofinalDefGraph
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 同一有限初等子域捕获原集合函数的实际读值

对象语言为纯隶属 ℒ，背景为原 Z₂，正式出口为原 Derives 的图翻译句。
有限族同时反射求值存在式与完整 Δ₀ 矩阵；在 I 内回收见证后，先反射
回传递 W 核验，再由原集合函数唯一性认出同一个实际输出。I 不须传递。
陪域包含于 W 的守卫保证实际输出可在 W 中反射，不预供 I 内输出。

该闭包适用于实际 Def 图和原前史图，但不把它等同于 Def(U) 的完整
截迹、凝聚、Collection 或最终候选源存在性。所有见证保持在 Prop。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullValue

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open PowerlessRelativeLimitDeltaSeparationDerives (parameters_m parameters_formula_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

/-- 绑定槽依次为输出 y、输入 x、原图 F，自由参数完全不变。 -/
def matrix_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set, .set] Δ :=
  PowerlessValueBounded.formula_m (.bvar (.there (.there .here)))
    (.bvar (.there .here)) (.bvar .here)

def exists_m (Δ : SortContext ℒ) : Formula ℒ [.set, .set] Δ :=
  .existsE .set (matrix_m Δ)

def family_m (Δ : SortContext ℒ) : PowerlessRelativeFiniteElementarity.family_m Δ :=
  [Sigma.mk ([.set, .set] : SortContext ℒ) (exists_m Δ),
    Sigma.mk ([.set, .set, .set] : SortContext ℒ) (matrix_m Δ)]

theorem matrix_delta_l (Δ : SortContext ℒ) :
    Formula.IsDelta0 membershipLevyBound (matrix_m Δ) :=
  PowerlessValueBounded.delta_l _ _ _

variable {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 仅从传递 W 的真值回收真实读值，不在非传递 I 上使用绝对性。 -/
theorem capture_l {Δ Ε : SortContext ℒ} (ζ : Env 𝒩 [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env 𝒩 [] Δ) (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    {I₀ W₀ F x : carrier_l 𝒩}
    (hFree : ∀ v : Variable Δ .set, member_l 𝒩 (ν.freeVal v) I₀)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ a, member_l 𝒩 a W₀ → ∀ b, member_l 𝒩 b a → member_l 𝒩 b W₀)
    (hIW : subset_l (ℳ := 𝒩) I₀ W₀)
    (hF : member_l 𝒩 F I₀) (hx : member_l 𝒩 x I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hy : ∃ y, member_l 𝒩 y W₀ ∧ value_l (ℳ := 𝒩) F x y) :
    ∃ y, member_l 𝒩 y I₀ ∧ value_l (ℳ := 𝒩) F x y := by
  have hNonempty : ∃ a, member_l 𝒩 a W₀ := ⟨F, hIW F hF⟩
  change (PowerlessRelativeFiniteElementarity.entry_m (exists_m Δ) I W τ).satisfies ζ ∧
    (PowerlessRelativeFiniteElementarity.entry_m (matrix_m Δ) I W τ).satisfies ζ ∧ True at h
  have hExists := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (exists_m Δ) ζ I W τ ν hτ).mp h.1
  have hMatrix := (PowerlessRelativeFiniteElementarity.entry_formula_l
    (matrix_m Δ) ζ I W τ ν hτ).mp h.2.1
  let η : Env 𝒩 [.set, .set] Δ := (ν.pushBound F).pushBound x
  have hParams : ∀ v : Variable ([.set, .set] : SortContext ℒ) .set,
      member_l 𝒩 (η.boundVal v) I₀ := by
    intro v
    match v with
    | .here => exact hx
    | .there .here => exact hF
  have hPush (C y : carrier_l 𝒩) :
      (η.pushFree C).pushBound y = (η.pushBound y).pushFree C := by
    apply Env.ext
    · intro s v; cases s; cases v <;> rfl
    · intro s v; cases s; cases v with
      | here => rfl
      | there v => rfl
  have hRead (y : carrier_l 𝒩) :
      (matrix_m Δ).satisfies (η.pushBound y) ↔ value_l (ℳ := 𝒩) F x y := by
    rw [matrix_m, PowerlessValueBounded.formula_l]
    rfl
  have hAbsolute (y : carrier_l 𝒩) (hyW : member_l 𝒩 y W₀) :=
    PowerlessMemberBounded.relativized_l hW hNonempty (matrix_delta_l Δ)
      (η.pushBound y) (fun v => by
        cases v with
        | here => exact hyW
        | there v => exact hIW _ (hParams v)) (fun v => hIW _ (hFree v))
  obtain ⟨y, hyW, hy⟩ := hy
  have hWitness : (PowerlessRelativization.formula_m (exists_m Δ)).satisfies
      (η.pushFree W₀) := by
    change ∃ z, member_l 𝒩 z W₀ ∧
      (PowerlessRelativization.formula_m (matrix_m Δ)).satisfies ((η.pushFree W₀).pushBound z)
    refine ⟨y, hyW, ?_⟩
    rw [hPush]
    exact (hAbsolute y hyW).mpr ((hRead y).mpr hy)
  have hReflect := hExists η (fun _ _ => rfl) (fun v => hI₀.symm ▸ hParams v)
  rw [hW₀, hI₀] at hReflect
  have hInside := hReflect.mp hWitness
  change ∃ z, member_l 𝒩 z I₀ ∧
    (PowerlessRelativization.formula_m (matrix_m Δ)).satisfies ((η.pushFree I₀).pushBound z) at hInside
  obtain ⟨z, hzI, hz⟩ := hInside
  rw [hPush] at hz
  have hRecover := hMatrix (η.pushBound z) (fun _ _ => rfl) (fun v => by
    rw [hI₀]
    cases v with
    | here => exact hzI
    | there v => exact hParams v)
  rw [hW₀, hI₀] at hRecover
  exact ⟨z, hzI, (hRead z).mp ((hAbsolute z (hIW z hzI)).mp (hRecover.mpr hz))⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}

/-- 原函数的值唯一性识别同一个 y，而不是另选一个 I 内输出。 -/
theorem member_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    {I₀ W₀ F A C x y : SecondOrderQuotient.type_l hℳ}
    (hFree : ∀ v : Variable Δ .set, SecondOrderQuotient.mem_l hℳ (ν.freeVal v) I₀)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ a, SecondOrderQuotient.mem_l hℳ a W₀ → ∀ b,
      SecondOrderQuotient.mem_l hℳ b a → SecondOrderQuotient.mem_l hℳ b W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (hF : SecondOrderQuotient.mem_l hℳ F I₀) (hx : SecondOrderQuotient.mem_l hℳ x I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hMap : SecondOrderFunctionObjects.map_l hℳ F A C)
    (hy : SecondOrderFunctionObjects.value_l hℳ F x y)
    (hyW : SecondOrderQuotient.mem_l hℳ y W₀) : SecondOrderQuotient.mem_l hℳ y I₀ := by
  obtain ⟨z, hzI, hz⟩ := capture_l (I₀ := I₀) (W₀ := W₀) (F := F) (x := x)
    ζ I W τ ν hτ (fun v => hFree v) hI₀ hW₀ hW hIW hF hx h ⟨y, hyW, hy⟩
  exact (SecondOrderFunctionProperties.value_unique_l hℳ hMap hy hz).symm ▸ hzI

theorem closed_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Δ Ε : SortContext ℒ} (ζ : Env (SecondOrderQuotient.structure_l hℳ) [] Ε)
    (I W : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ)
    (hτ : ∀ v, (τ v).eval ζ = ν.freeVal v)
    {I₀ W₀ F A C : SecondOrderQuotient.type_l hℳ}
    (hFree : ∀ v : Variable Δ .set, SecondOrderQuotient.mem_l hℳ (ν.freeVal v) I₀)
    (hI₀ : I.eval ζ = I₀) (hW₀ : W.eval ζ = W₀)
    (hW : ∀ a, SecondOrderQuotient.mem_l hℳ a W₀ → ∀ b,
      SecondOrderQuotient.mem_l hℳ b a → SecondOrderQuotient.mem_l hℳ b W₀)
    (hIW : subset_l (ℳ := SecondOrderQuotient.structure_l hℳ) I₀ W₀)
    (hF : SecondOrderQuotient.mem_l hℳ F I₀)
    (h : (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ).satisfies ζ)
    (hMap : SecondOrderFunctionObjects.map_l hℳ F A C)
    (hCW : ∀ y, SecondOrderQuotient.mem_l hℳ y C → SecondOrderQuotient.mem_l hℳ y W₀) :
    ∀ x, SecondOrderQuotient.mem_l hℳ x I₀ → ∀ y,
      SecondOrderFunctionObjects.value_l hℳ F x y → SecondOrderQuotient.mem_l hℳ y I₀ := by
  intro x hx y hy
  exact member_l hℳ ζ I W τ ν hτ hFree hI₀ hW₀ hW hIW hF hx h hMap hy
    (hCW y (SecondOrderFunctionProperties.value_mem_l hℳ hMap hy).2)

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set

def closed_m {Γ Ε : SortContext ℒ} (F I : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up I)) <|
    .forallE .set <| .imp
      (PowerlessValueBounded.formula_m (up (up F)) (.bvar (.there .here)) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up I)))

theorem closed_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Ε : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Ε)
    (F I : Term ℒ Γ Ε .set) : (closed_m F I).satisfies η ↔
      ∀ x, SecondOrderQuotient.mem_l hℳ x (I.eval η) → ∀ y,
        SecondOrderFunctionObjects.value_l hℳ (F.eval η) x y →
          SecondOrderQuotient.mem_l hℳ y (I.eval η) := by
  simp only [closed_m, Formula.satisfies, PowerlessValueBounded.formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 同一 I 对全部已捕获函数的真实读值闭包；陪域仍须包含于真实 W。 -/
def functions_m {Γ Ε : SortContext ℒ} (I W : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  let w (t : Term ℒ Γ Ε .set) := up (up (up t))
  let F : Term ℒ (.set :: .set :: .set :: Γ) Ε .set := .bvar (.there (.there .here))
  let A : Term ℒ (.set :: .set :: .set :: Γ) Ε .set := .bvar (.there .here)
  let C : Term ℒ (.set :: .set :: .set :: Γ) Ε .set := .bvar .here
  .forallE .set <| .forallE .set <| .forallE .set <|
    .imp (SecondOrderObjectSyntax.member_m F (w I)) <|
      .imp (SecondOrderObjectSyntax.map_m F A C) <|
        .imp (ThirdOrderTheory.subset_m C (w W)) (closed_m F (w I))

theorem functions_formula_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Γ Ε : SortContext ℒ} (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Ε)
    (I W : Term ℒ Γ Ε .set) : (functions_m I W).satisfies η ↔
      ∀ F A C, SecondOrderQuotient.mem_l hℳ F (I.eval η) →
        SecondOrderFunctionObjects.map_l hℳ F A C →
        (∀ y, SecondOrderQuotient.mem_l hℳ y C → SecondOrderQuotient.mem_l hℳ y (W.eval η)) →
        ∀ x, SecondOrderQuotient.mem_l hℳ x (I.eval η) → ∀ y,
          SecondOrderFunctionObjects.value_l hℳ F x y →
            SecondOrderQuotient.mem_l hℳ y (I.eval η) := by
  simp only [functions_m, Formula.satisfies, SecondOrderObjectSyntax.map_l,
    ThirdOrderSemantics.subset_formula_l, subset_l, ThirdOrderSemantics.member_l,
    closed_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval,
    up, Term.eval_weakenBound, Term.eval, SecondOrderQuotient.structure_l]
  rfl

def schema_m {Θ Δ : SortContext ℒ} (F A C I W : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessNaturalOrder.transitive_m W) <| .imp (ThirdOrderTheory.subset_m I W) <|
    .imp (ThirdOrderTheory.subset_m C W) <| .imp (SecondOrderObjectSyntax.member_m F I) <|
      .imp (parameters_m Δ I τ) <|
        .imp (PowerlessRelativeFiniteElementarity.form_m (family_m Δ) I W τ) <|
          .imp (SecondOrderObjectSyntax.map_m F A C) (closed_m F I)

def sentence_m {Θ Δ : SortContext ℒ} (F A C I W : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (schema_m F A C I W τ)

theorem models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ Δ : SortContext ℒ} (F A C I W : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) :
    (sentence_m F A C I W τ).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [schema_m, Formula.satisfies, PowerlessNaturalOrder.transitive_formula_l,
    ThirdOrderSemantics.subset_formula_l, subset_l, ThirdOrderSemantics.member_l,
    parameters_formula_l, SecondOrderObjectSyntax.map_l, closed_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, SecondOrderQuotient.structure_l]
  intro hW hIW hCW hF hParams h hMap
  let ν : Env (SecondOrderQuotient.structure_l hℳ) [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (τ v).eval η }
  exact closed_l hℳ η I W τ ν (fun _ => rfl) (fun v => hParams _ v) rfl rfl
    (fun a ha b hb => hW a b ha hb) hIW hF h hMap hCW

theorem derives_m {Θ Δ : SortContext ℒ} (F A C I W : Term ℒ [] Θ .set)
    (τ : Variable Δ .set → Term ℒ [] Θ .set) : Derives SecondOrderArithmetic.theory_m []
      (GraphTranslation.form_m (sentence_m F A C I W τ)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => models_l hℳ F A C I W τ)

/-- 原 Def 的全部实际输出捕获；不是把环境 Def 改成 I 内的 Def。 -/
def def_closed_m {Γ Ε : SortContext ℒ} (U I : Term ℒ Γ Ε .set) : Formula ℒ Γ Ε :=
  .forallE .set <| .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up I)) <|
    .imp (SecondOrderObjectSyntax.member_m (.bvar .here) (up U)) <| .forallE .set <|
      .imp (PowerlessMemberDefSyntax.global_m (.bvar (.there .here)) (.bvar .here))
        (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up I)))

theorem def_closed_formula_l {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
    (K : PowerlessBMSQuotientCoding.source_coding_l hℳ) {Γ Ε : SortContext ℒ}
    (η : Env (SecondOrderQuotient.structure_l hℳ) Γ Ε) (U I : Term ℒ Γ Ε .set) :
    (def_closed_m U I).satisfies η ↔ ∀ x,
      SecondOrderQuotient.mem_l hℳ x (I.eval η) → SecondOrderQuotient.mem_l hℳ x (U.eval η) →
        ∀ y, SecondOrderMemberDef.spec_l hℳ x y → SecondOrderQuotient.mem_l hℳ y (I.eval η) := by
  simp only [def_closed_m, Formula.satisfies, PowerlessMemberDefDerives.formula_l K,
    SecondOrderObjectSyntax.member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

def def_schema_m {Θ : SortContext ℒ} (D U I : Term ℒ [] Θ .set) : Formula ℒ [] Θ :=
  .imp (PowerlessRelativeCofinalDefGraph.graph_m U D) <|
    .imp (closed_m D I) (def_closed_m U I)

def def_sentence_m {Θ : SortContext ℒ} (D U I : Term ℒ [] Θ .set) : Sentence ℒ :=
  Metatheory.Formula.forall_close (def_schema_m D U I)

theorem def_models_l (hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m)
    {Θ : SortContext ℒ} (D U I : Term ℒ [] Θ .set) :
    (def_sentence_m D U I).TrueIn (SecondOrderQuotient.structure_l hℳ) := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η
  simp only [def_schema_m, Formula.satisfies, PowerlessRelativeCofinalDefGraph.graph_formula_l K,
    closed_formula_l, def_closed_formula_l K]
  intro hGraph hClosed x hxI hxU y hy
  exact hClosed x hxI y ((hGraph.2 x y).mpr ⟨hxU, hy⟩)

theorem def_derives_m {Θ : SortContext ℒ} (D U I : Term ℒ [] Θ .set) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (def_sentence_m D U I)) :=
  SecondOrderAxioms.interpretation_m _ (fun _ hℳ => def_models_l hℳ D U I)

#print axioms matrix_delta_l
#print axioms capture_l
#print axioms member_l
#print axioms closed_l
#print axioms functions_formula_l
#print axioms models_l
#print axioms derives_m
#print axioms def_models_l
#print axioms def_derives_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteHullValue
