import BMSConstructibleBridge.PowerlessRelativePackedRequestClosure
import BMSConstructibleBridge.PowerlessSourceRequestParameters
import BMSConstructibleBridge.PowerlessRelativeFiniteElementarity

/-! # 同一原图族的真实请求闭包

原外部有限公式族平展为实际请求列表，标签参数只插在原参数区。
图规格与图列表逐项对应，使用末端原图族的逆序，不丢失原矩阵。
从同一 I 的真实图读数闭包恢复每个原请求，再消去标签提升。
这是有限元素性装配中的语义桥；图、I 和截断守卫仍须由原对象结论
共同提供，不据此宣称完整源模型或最终 BMS 推导已经完成。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteRequestFamilyClosure

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l
  PowerlessMemberStructure.structure_l

universe u

private abbrev Requests (Δ : SortContext ℒ) :=
  List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))
private abbrev Entry (Ε : SortContext ℒ) := Term ℒ [] Ε .set × Term ℒ [] Ε .set

def requests_m {Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ) :
    Requests Δ := Φ.flatMap (fun p => PowerlessSourceRequests.requests_m .truth p.2)

def family_m {Δ : SortContext ℒ} (m : Nat) (Ψ : Requests Δ) :
    List (Formula ℒ [] (.set :: .set :: (List.replicate m .set ++ Δ))) :=
  Ψ.map (fun p => PowerlessRelativePackedRequestClosure.matrix_m p.1
    (PowerlessSourceRequestParameters.inflate_m p.1 m p.2))

theorem family_length_m {Δ : SortContext ℒ} (m : Nat) (Ψ : Requests Δ) :
    (family_m m Ψ).length = Ψ.length := by simp only [family_m, List.length_map]

private theorem graph_l {α β : Type u} {R : α → β → Prop} {F : List α} {G : List β}
    (h : List.Forall₂ R F G) : ∀ φ ∈ F, ∃ p ∈ G, R φ p := by
  induction h with
  | nil => intro φ hφ; cases hφ
  | @cons φ p F G hφ hG ih =>
    intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact ⟨p, List.mem_cons_self, hφ⟩
    · obtain ⟨q, hq, hψ⟩ := ih ψ hψ
      exact ⟨q, List.mem_cons_of_mem _ hq, hψ⟩

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}
  {W₀ : SecondOrderQuotient.type_l hℳ} {hW : ∃ x, mem_l hℳ x W₀}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ
local notation "𝒲" => PowerlessMemberStructure.structure_l (ℳ := 𝒱) W₀ hW
local notation "WType" => PowerlessMemberStructure.type_l (ℳ := 𝒱) W₀

/-- 同一 I 对同一原图族关闭，则对原未提升的全部实际请求关闭。 -/
theorem closed_l {Ε Δ : SortContext ℒ} (Ψ : Requests Δ) (m : Nat)
    (ζ : Env 𝒱 [] Ε) (B β W ω R : Term ℒ [] Ε .set)
    (τ : Variable (List.replicate m .set ++ Δ) .set → Term ℒ [] Ε .set)
    (G : List (Entry Ε)) (η : Env 𝒲 [] Δ)
    (t : Values (𝒲).Carrier (List.replicate m SetTheory.SetSort.set)) (d : WType)
    (hBase : ∀ x, mem_l hℳ x (B.eval ζ) → ∀ y, mem_l hℳ y x → mem_l hℳ y (B.eval ζ))
    (hLimit : PowerlessRelativeHierarchySemantics.limit_l hℳ (β.eval ζ))
    (hLevel : PowerlessRelativeHierarchySemantics.level_l hℳ (B.eval ζ) (β.eval ζ) W₀)
    (hωW : mem_l hℳ (ω.eval ζ) W₀)
    (hB : B.eval ζ = d.val) (hW₀ : W.eval ζ = W₀)
    (hτ : ∀ v, (τ v).eval ζ = ((PowerlessSourceTuple.env_l η m t).freeVal v).val)
    (hGraphs : List.Forall₂ (fun φ p =>
      (PowerlessRelativeSourceSkolemGraph.graph_m φ B W R p.2 τ).satisfies ζ)
      (family_m m Ψ).reverse G)
    (I : SecondOrderQuotient.type_l hℳ)
    (hIW : ∀ a, mem_l hℳ a I → mem_l hℳ a W₀) (hd : mem_l hℳ d.val I)
    (hPairI : ∀ a b, mem_l hℳ a I → mem_l hℳ b I →
      ∃ p, mem_l hℳ p I ∧ ordered_l (ℳ := 𝒱) a b p)
    (hClosure : ∀ p ∈ G, ∀ a, mem_l hℳ a I → ∃ b, mem_l hℳ b I ∧
      value_l (ℳ := 𝒱) (p.2.eval ζ) a b) :
    PowerlessSourcePredicateRequests.closed_l Ψ η
      (fun x : WType => mem_l hℳ x.val I) := by
  intro n φ hφ v hv hSome
  have hMem : PowerlessRelativePackedRequestClosure.matrix_m n
      (PowerlessSourceRequestParameters.inflate_m n m φ) ∈ (family_m m Ψ).reverse := by
    apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨Sigma.mk n φ, hφ, rfl⟩
  obtain ⟨p, hp, hGraph⟩ := graph_l hGraphs _ hMem
  have h := PowerlessRelativePackedRequestClosure.level_closure_l n
    (PowerlessSourceRequestParameters.inflate_m n m φ) ζ B β W ω R p.2 τ
    (PowerlessSourceTuple.env_l η m t) d hBase hLimit hLevel hωW hB hW₀ hτ hGraph
    I hIW hd hPairI (hClosure p hp)
  obtain ⟨y, hy⟩ := hSome
  obtain ⟨z, hz, hφ⟩ := h v hv ⟨y,
    (PowerlessSourceRequestParameters.formula_l η n m v t φ y).mpr hy⟩
  exact ⟨z, hz, (PowerlessSourceRequestParameters.formula_l η n m v t φ z).mp hφ⟩

/-- 平展全部绑定上下文的请求后，逐原公式取回所需闭包。 -/
theorem requests_l {Δ : SortContext ℒ} (Φ : PowerlessRelativeFiniteElementarity.family_m Δ)
    (η : Env 𝒲 [] Δ) (I : SecondOrderQuotient.type_l hℳ)
    (h : PowerlessSourcePredicateRequests.closed_l (requests_m Φ) η
      (fun x : WType => mem_l hℳ x.val I)) :
    ∀ p ∈ Φ, PowerlessSourcePredicateRequests.closed_l
      (PowerlessSourceRequests.requests_m .truth p.2) η
      (fun x : WType => mem_l hℳ x.val I) := by
  intro p hp
  exact PowerlessSourcePredicateRequests.subset_l
    (fun q hq => List.mem_flatMap.mpr ⟨p, hp, hq⟩) h

#print axioms family_length_m
#print axioms closed_l
#print axioms requests_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeFiniteRequestFamilyClosure
