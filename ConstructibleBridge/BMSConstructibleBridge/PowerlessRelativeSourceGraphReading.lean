import BMSConstructibleBridge.PowerlessRelativeSourceSkolemGraph

/-!
# 原 Skolem 图规格的真实矩阵读数

从原 graph_m 的完整 payload 提取实际函数规格和最小见证读数。
原矩阵仍在 W 的成员结构中求值，原参数由指定项逐槽对应。
对同一个 raw I 的图闭包恢复原矩阵的见证闭包，不要求 I 或 J 属于 W。
本模块是原对象推导路线的语义中间桥，不替代最终 Z₂ 推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceGraphReading

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open SecondOrderObjectSyntax (member_m)
open PowerlessRelativeSourceLeastWitnessDerives (least_formula_l reading_m)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

private abbrev up {Γ Ε : SortContext ℒ} (t : Term ℒ Γ Ε .set) :=
  t.weakenBound SetTheory.SetSort.set

private def lift_m {Γ Ε Δ : SortContext ℒ} (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Variable Δ .set → Term ℒ (.set :: Γ) Ε .set := fun v => up (τ v)

/-- 默认值与原参数的映射；这里只重建参数接线，不重建原公式。 -/
private def binding_m {Γ Ε Δ : SortContext ℒ} (B : Term ℒ Γ Ε .set)
    (τ : Variable Δ .set → Term ℒ Γ Ε .set) :
    Variable (.set :: Δ) .set → Term ℒ Γ Ε .set
  | .here => B
  | .there v => τ v

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {W₀ : SecondOrderQuotient.type_l hℳ} {hW : ∃ x, mem_l hℳ x W₀}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒲" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) W₀ hW
local notation "WType" => PowerlessMemberStructure.type_l (ℳ := 𝒱) W₀

/-- 原图正文已经包含全部真实读数，不再向调用者索要读数前提。 -/
theorem reading_l {Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ζ : Env 𝒱 [] Ε)
    (B W R J : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (η : Env 𝒲 [] Δ) (d : WType)
    (hB : B.eval ζ = d.val) (hW₀ : W.eval ζ = W₀)
    (hτ : ∀ v, (τ v).eval ζ = (η.freeVal v).val)
    (hGraph : (PowerlessRelativeSourceSkolemGraph.graph_m φ B W R J τ).satisfies ζ) :
    map_l (ℳ := 𝒱) (J.eval ζ) W₀ W₀ ∧
      ∀ x y : WType, value_l (ℳ := 𝒱) (J.eval ζ) x.val y.val ↔
        (PowerlessSourceWitnessTotalization.formula_m φ).satisfies
          (((η.pushFree d).pushFree y).pushFree x) ∧
        ∀ z : WType, (PowerlessSourceWitnessTotalization.formula_m φ).satisfies
          (((η.pushFree d).pushFree z).pushFree x) →
            ¬value_l (ℳ := 𝒱) (R.eval ζ) z.val y.val := by
  let η₀ : Env 𝒱 [] Δ :=
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => (η.freeVal v).val }
  have hp := (PowerlessRelativeSourceSkolemGraph.graph_formula_l
    φ ζ B W R J τ η₀ (fun v => hτ v)).mp hGraph
  let ξ : Env 𝒱 [] (.set :: .set :: .set :: .set :: Δ) :=
    (((η₀.pushFree (B.eval ζ)).pushFree (R.eval ζ)).pushFree (W.eval ζ)).pushFree (J.eval ζ)
  have hPayload : (PowerlessRelativeSourceSkolemGraph.payload_m φ).satisfies ξ := hp
  have hMap : map_l (ℳ := 𝒱) (J.eval ζ) W₀ W₀ := by
    have h := (map_formula_l ξ (.fvar .here)
      (.fvar (.there .here)) (.fvar (.there .here))).mp hPayload.2.1
    simpa only [ξ, Term.eval, Env.pushFree_here, Env.pushFree_there, hW₀] using h
  have hRead : (reading_m (PowerlessSourceWitnessTotalization.formula_m φ)
      (.fvar (.there .here)) (.fvar (.there (.there .here))) (.fvar (.there .here))
      (.fvar .here) (binding_m (.fvar (.there (.there (.there .here))))
        (fun v => .fvar (.there (.there (.there (.there v))))))).satisfies ξ :=
    hPayload.2.2.1
  simp only [reading_m, Formula.satisfies, PowerlessValueBounded.formula_l,
    member_m, Arguments.eval, Term.eval_weakenBound, Term.eval, ξ,
    Env.pushFree_here, Env.pushFree_there] at hRead
  refine ⟨hMap, ?_⟩
  intro x y
  have hLeast := least_formula_l (PowerlessSourceWitnessTotalization.formula_m φ)
    (show Env 𝒱 [.set, .set] (.set :: .set :: .set :: .set :: Δ) from
      (ξ.pushBound x.val).pushBound y.val)
    (.fvar (.there .here)) (.fvar (.there (.there .here)))
    (.bvar (.there .here)) (.bvar .here)
    (lift_m (lift_m (binding_m (.fvar (.there (.there (.there .here))))
      (fun v => .fvar (.there (.there (.there (.there v))))))))
    (η.pushFree d) x y (by change W.eval ζ = W₀; exact hW₀) rfl rfl (by
      intro v
      cases v with
      | here => change B.eval ζ = d.val; exact hB
      | there v => rfl)
  constructor
  · intro hxy
    exact hLeast.mp ((hRead x.val y.val).mp hxy).2.2
  · intro hxy
    apply (hRead x.val y.val).mpr
    refine ⟨?_, ?_, hLeast.mpr hxy⟩
    · rw [hW₀]
      exact x.property
    · rw [hW₀]
      exact y.property

/-- 同一个 I 的真实图输出闭包恢复原矩阵见证，默认分支由原见证排除。 -/
theorem closure_l {Ε Δ : SortContext ℒ}
    (φ : Formula ℒ [] (.set :: .set :: Δ)) (ζ : Env 𝒱 [] Ε)
    (B W R J : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (η : Env 𝒲 [] Δ) (d : WType)
    (hB : B.eval ζ = d.val) (hW₀ : W.eval ζ = W₀)
    (hτ : ∀ v, (τ v).eval ζ = (η.freeVal v).val)
    (hGraph : (PowerlessRelativeSourceSkolemGraph.graph_m φ B W R J τ).satisfies ζ)
    (I : SecondOrderQuotient.type_l hℳ)
    (hIW : ∀ a, mem_l hℳ a I → mem_l hℳ a W₀)
    (hClosure : ∀ a, mem_l hℳ a I → ∃ b, mem_l hℳ b I ∧
      value_l (ℳ := 𝒱) (J.eval ζ) a b) :
    ∀ x : WType, mem_l hℳ x.val I →
      (∃ z : WType, φ.satisfies ((η.pushFree z).pushFree x)) →
        ∃ y : WType, mem_l hℳ y.val I ∧ φ.satisfies ((η.pushFree y).pushFree x) := by
  have hRead := (reading_l φ ζ B W R J τ η d hB hW₀ hτ hGraph).2
  intro x hx hSome
  obtain ⟨y, hy, hxy⟩ := hClosure x.val hx
  let y₀ : WType := ⟨y, hIW y hy⟩
  have hLeast := (hRead x y₀).mp hxy
  have hWitness := PowerlessRelativeSourceSkolemGraph.witness_l φ η d x y₀ (R.eval ζ)
    hLeast hSome
  exact ⟨y₀, hy, hWitness.1⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeSourceGraphReading
