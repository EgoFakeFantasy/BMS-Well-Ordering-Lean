import BMSConstructibleBridge.PowerlessRelativeSourceGraphReading
import BMSConstructibleBridge.PowerlessSourceTuplePairing
import BMSConstructibleBridge.PowerlessBMSClassCollapse
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute

/-! # 同一闭包像的图读数恢复原有限元数请求

原元组公式首槽是输出，原 Skolem 图首槽是输入，故编码矩阵必须交换
这两个槽位。全部求值仍在实际 W 成员结构中；I 只在原商中给出，
用谓词 x.val∈I 限定输入及输出，不把 I 当成 W 的载体对象。
不要求 W 已满足完整源理论。此语义桥供有限元素性的原对象推导使用。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativePackedRequestClosure

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

def matrix_m {Δ : SortContext ℒ} (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))) :
    Formula ℒ [] (.set :: .set :: Δ) :=
  PowerlessBMSClassCollapse.converse_m (PowerlessSourceTuple.form_m n φ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {W₀ : SecondOrderQuotient.type_l hℳ} {hW : ∃ x, mem_l hℳ x W₀}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒲" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) W₀ hW
local notation "WType" => PowerlessMemberStructure.type_l (ℳ := 𝒱) W₀

/-- 原图及同一个 I 的真实读数闭包足以恢复全部原输入列上的见证。 -/
theorem closure_l {Ε Δ : SortContext ℒ} (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))) (ζ : Env 𝒱 [] Ε)
    (B W R J : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (η : Env 𝒲 [] Δ) (d e : WType)
    (hB : B.eval ζ = d.val) (hW₀ : W.eval ζ = W₀)
    (hτ : ∀ v, (τ v).eval ζ = (η.freeVal v).val)
    (hGraph : (PowerlessRelativeSourceSkolemGraph.graph_m (matrix_m n φ) B W R J τ).satisfies ζ)
    (I : SecondOrderQuotient.type_l hℳ)
    (hIW : ∀ a, mem_l hℳ a I → mem_l hℳ a W₀) (he : mem_l hℳ e.val I)
    (hPair : ∀ a b : WType, ∃ p, ordered_l (ℳ := 𝒲) a b p)
    (hPairI : ∀ a b p : WType, mem_l hℳ a.val I → mem_l hℳ b.val I →
      ordered_l (ℳ := 𝒲) a b p → mem_l hℳ p.val I)
    (hClosure : ∀ a, mem_l hℳ a I → ∃ b, mem_l hℳ b I ∧
      value_l (ℳ := 𝒱) (J.eval ζ) a b) :
    ∀ v : Values (𝒲).Carrier (List.replicate n SetTheory.SetSort.set),
      PowerlessSourceTuplePairing.bounded_l (fun x : WType => mem_l hℳ x.val I) n v →
      (∃ y : WType, φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)) →
        ∃ y : WType, mem_l hℳ y.val I ∧
          φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y) := by
  have hCode := PowerlessRelativeSourceGraphReading.closure_l (matrix_m n φ) ζ
    B W R J τ η d hB hW₀ hτ hGraph I hIW hClosure
  have hPacked := PowerlessSourceTuplePairing.predicate_closure_l hPair η n φ
    (fun x : WType => mem_l hℳ x.val I) (fun _ => True) e he hPairI (by
      rintro p hp ⟨y, _, hφ⟩
      have hSome : ∃ y : WType, (matrix_m n φ).satisfies ((η.pushFree y).pushFree p) :=
        ⟨y, (PowerlessBMSClassCollapse.converse_formula_l
          (PowerlessSourceTuple.form_m n φ) η p y).mpr hφ⟩
      obtain ⟨z, hz, hψ⟩ := hCode p hp hSome
      exact ⟨z, hz, (PowerlessBMSClassCollapse.converse_formula_l
        (PowerlessSourceTuple.form_m n φ) η p z).mp hψ⟩)
  rintro v hv ⟨y, hφ⟩
  exact hPacked v hv ⟨y, trivial, hφ⟩

/-- 实际层与原商中的配对闭包消去内部配对前提；零元数码取原默认值 d。 -/
theorem level_closure_l {Ε Δ : SortContext ℒ} (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))) (ζ : Env 𝒱 [] Ε)
    (B β W ω R J : Term ℒ [] Ε .set) (τ : Variable Δ .set → Term ℒ [] Ε .set)
    (η : Env 𝒲 [] Δ) (d : WType)
    (hBase : ∀ x, mem_l hℳ x (B.eval ζ) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval ζ))
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ (β.eval ζ))
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval ζ) (β.eval ζ) W₀)
    (hωW : mem_l hℳ (ω.eval ζ) W₀)
    (hB : B.eval ζ = d.val) (hW₀ : W.eval ζ = W₀)
    (hτ : ∀ v, (τ v).eval ζ = (η.freeVal v).val)
    (hGraph : (PowerlessRelativeSourceSkolemGraph.graph_m (matrix_m n φ) B W R J τ).satisfies ζ)
    (I : SecondOrderQuotient.type_l hℳ)
    (hIW : ∀ a, mem_l hℳ a I → mem_l hℳ a W₀) (hd : mem_l hℳ d.val I)
    (hPairI : ∀ a b, mem_l hℳ a I → mem_l hℳ b I →
      ∃ p, mem_l hℳ p I ∧ ordered_l (ℳ := 𝒱) a b p)
    (hClosure : ∀ a, mem_l hℳ a I → ∃ b, mem_l hℳ b I ∧
      value_l (ℳ := 𝒱) (J.eval ζ) a b) :
    ∀ v : Values (𝒲).Carrier (List.replicate n SetTheory.SetSort.set),
      PowerlessSourceTuplePairing.bounded_l (fun x : WType => mem_l hℳ x.val I) n v →
      (∃ y : WType, φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)) →
        ∃ y : WType, mem_l hℳ y.val I ∧
          φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y) := by
  have hPair := (PowerlessSourceTuplePairing.level_l hBase hLimit hLevel hωW).1
  have hTrans : PowerlessNaturalOrder.transitive_l (ℳ := 𝒱) W₀ :=
    fun x y hx hy => PowerlessRelativeLevelClosure.transitive_l hℳ hBase hLevel x hx y hy
  have hPairI' (a b p : WType) (ha : mem_l hℳ a.val I) (hb : mem_l hℳ b.val I)
      (hp : ordered_l (ℳ := 𝒲) a b p) : mem_l hℳ p.val I := by
    obtain ⟨q, hq, hPair⟩ := hPairI a.val b.val ha hb
    have hp' := (PowerlessSourceGraphAbsolute.ordered_l
      (ℳ := 𝒱) (A := W₀) (hA := hW) hTrans).mp hp
    have hEq := SecondOrderPairObjects.ordered_unique_l hℳ hp' hPair
    simpa only [hEq] using hq
  exact closure_l n φ ζ B W R J τ η d d hB hW₀ hτ hGraph I hIW hd hPair hPairI' hClosure

#print axioms closure_l
#print axioms level_closure_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativePackedRequestClosure
