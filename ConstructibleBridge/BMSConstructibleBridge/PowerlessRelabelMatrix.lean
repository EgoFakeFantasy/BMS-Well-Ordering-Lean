import BMSConstructibleBridge.PowerlessCodedDiagram
import BMSConstructibleBridge.PowerlessAmbientDiagram
import BMSConstructibleBridge.PowerlessStableDiagram
import BMSConstructibleBridge.PowerlessDiagramFamily

/-!
# 原重标号条件的同一函数图矩阵

三基础块分别为全部好标签、下方标签到新标签的序关系、新标签间的原序图。
每项具名稳定数据包含层号数码、低高边图、高高边图；每项顶端数据包含
外部真值层号、其数码与内部下标迹。列表只枚举外部固定层号，不枚举内部列。
全部块读取同一 g 绑定槽，且唯一映射的定义域是 q，不是求值长度 N。
本模块的分块等价不替代上层共同见证的存在性或完整 BMS 重标号证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelMatrix

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

/-- 层号数码项、低高边图项、高高边图项。 -/
abbrev edge_m (Δ : SortContext ℒ) :=
  Term ℒ [] Δ .set × Term ℒ [] Δ .set × Term ℒ [] Δ .set

/-- 外部真值层号、该层号的内部数码项、顶端稳定下标迹项。 -/
abbrev trace_m (Δ : SortContext ℒ) := Nat × Term ℒ [] Δ .set × Term ℒ [] Δ .set

def lift_m {Δ : SortContext ℒ} (t : Term ℒ [] Δ .set) : Term ℒ [.set, .set] Δ .set :=
  (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set

/-- 两个共同存在见证按 g,B 压入，故函数图在第二绑定槽。 -/
def graph_m {Δ : SortContext ℒ} : Term ℒ [.set, .set] Δ .set := .bvar (.there .here)

def order_m {Δ : SortContext ℒ} : Formula ℒ [] (.set :: .set :: Δ) :=
  SecondOrderObjectSyntax.member_m (.fvar (.there .here)) (.fvar .here)

theorem lift_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env ℳ [] Δ) (g B : carrier_l ℳ) (t : Term ℒ [] Δ .set) :
    (lift_m t).eval ((η.pushBound g).pushBound B) = t.eval η := by
  simp only [lift_m, Term.eval_weakenBound]

theorem graph_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env ℳ [] Δ) (g B : carrier_l ℳ) :
    graph_m.eval ((η.pushBound g).pushBound B) = g := rfl

def matrix_m {Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c N q f D E : Term ℒ [] Δ .set)
    (Ψ : List (edge_m Δ)) (Θ : List (trace_m Δ)) : List (Formula ℒ [.set, .set] Δ) :=
  [PowerlessCodedDiagram.labels_m ω e T t₁ t₂ t₃ c N graph_m (lift_m q),
    PowerlessDiagramConstraint.instance_m order_m (lift_m D) (lift_m f) graph_m,
    PowerlessDiagramConstraint.instance_m order_m (lift_m E) graph_m graph_m] ++
  Ψ.flatMap (fun p =>
    [PowerlessDiagramConstraint.instance_m (PowerlessStableDiagram.relation_m ω e T t₁ t₂ t₃ p.1)
      (lift_m p.2.1) (lift_m f) graph_m,
     PowerlessDiagramConstraint.instance_m (PowerlessStableDiagram.relation_m ω e T t₁ t₂ t₃ p.1)
      (lift_m p.2.2) graph_m graph_m]) ++
  Θ.map (fun p => PowerlessAmbientDiagram.trace_m p.1 ω e T t₁ t₂ t₃ p.2.1 graph_m (lift_m p.2.2))

def formula_m {Δ : SortContext ℒ} (ω e T t₁ t₂ t₃ c N q f D E : Term ℒ [] Δ .set)
    (Ψ : List (edge_m Δ)) (Θ : List (trace_m Δ)) : Formula ℒ [] Δ :=
  PowerlessDiagramFamily.realize_m (matrix_m ω e T t₁ t₂ t₃ c N q f D E Ψ Θ) q

/-- 精确拆分矩阵的全部条件；每一块仍在同一个两见证环境 η 中求值。 -/
theorem matrix_formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env ℳ [.set, .set] Δ) (ω e T t₁ t₂ t₃ c N q f D E : Term ℒ [] Δ .set)
    (Ψ : List (edge_m Δ)) (Θ : List (trace_m Δ)) :
    (∀ φ ∈ matrix_m ω e T t₁ t₂ t₃ c N q f D E Ψ Θ, φ.satisfies η) ↔
      (PowerlessCodedDiagram.labels_m ω e T t₁ t₂ t₃ c N graph_m (lift_m q)).satisfies η ∧
      (PowerlessDiagramConstraint.instance_m order_m (lift_m D) (lift_m f) graph_m).satisfies η ∧
      (PowerlessDiagramConstraint.instance_m order_m (lift_m E) graph_m graph_m).satisfies η ∧
      (∀ p ∈ Ψ,
        (PowerlessDiagramConstraint.instance_m (PowerlessStableDiagram.relation_m ω e T t₁ t₂ t₃ p.1)
          (lift_m p.2.1) (lift_m f) graph_m).satisfies η ∧
        (PowerlessDiagramConstraint.instance_m (PowerlessStableDiagram.relation_m ω e T t₁ t₂ t₃ p.1)
          (lift_m p.2.2) graph_m graph_m).satisfies η) ∧
      ∀ p ∈ Θ,
        (PowerlessAmbientDiagram.trace_m p.1 ω e T t₁ t₂ t₃ p.2.1 graph_m (lift_m p.2.2)).satisfies η := by
  have h₀ : (∀ φ ∈ ([] : List (Formula ℒ [.set, .set] Δ)), φ.satisfies η) ↔ True :=
    iff_true_intro (List.forall_mem_nil _)
  simp only [matrix_m, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_flatMap, List.forall_mem_map, h₀, and_true, and_assoc]

/-- 只有一个映射存在量词块，所有分块条件共享其 g,B；不把分块分别存在化。 -/
theorem formula_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Δ : SortContext ℒ}
    (η : Env ℳ [] Δ) (ω e T t₁ t₂ t₃ c N q f D E : Term ℒ [] Δ .set)
    (Ψ : List (edge_m Δ)) (Θ : List (trace_m Δ)) :
    (formula_m ω e T t₁ t₂ t₃ c N q f D E Ψ Θ).satisfies η ↔
      ∃ g B, map_l g (q.eval η) B ∧
        ∀ φ ∈ matrix_m ω e T t₁ t₂ t₃ c N q f D E Ψ Θ,
          φ.satisfies ((η.pushBound g).pushBound B) :=
  PowerlessDiagramFamily.realize_formula_l _ q η

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelMatrix
