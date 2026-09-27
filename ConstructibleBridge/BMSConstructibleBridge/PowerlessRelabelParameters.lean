import BMSConstructibleBridge.PowerlessRelabelWitness

/-!
# 重标号矩阵的固定参数槽

十二个基础槽依次为 ω,e,T,t₁,t₂,t₃,c,N,q,f,D,E，每个外部层号另占四槽 n,D,E,S。
语法仅依赖外部层号列表；原标签、数码及关系记录只改变环境取值。
这些外部槽不是内部列数，q 仍是可非标准的模型内部自然数。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelParameters

open Logic FirstOrder ThirdOrderSemantics PowerlessRelabelMatrix

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def context_m : Nat → SortContext ℒ
  | 0 => List.replicate 12 .set
  | n + 1 => .set :: .set :: .set :: .set :: context_m n

structure packet_m (Δ : SortContext ℒ) where
  parameter_m : Fin 12 → Term ℒ [] Δ .set
  edges_m : List (edge_m Δ)
  traces_m : List (trace_m Δ)

def lift_m {Δ : SortContext ℒ} (s : Term ℒ [] Δ .set) :
    Term ℒ [] (.set :: .set :: .set :: .set :: Δ) .set :=
  (((s.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).weakenFree
    SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set

def syntax_m : (Λ : List Nat) → packet_m (context_m Λ.length)
  | List.nil => ⟨fun i => .fvar (SetTheory.Definitional.Project.fo_bound_variable i), List.nil, List.nil⟩
  | k :: Λ =>
    let p := syntax_m Λ
    ⟨fun i => lift_m (p.parameter_m i),
      (.fvar .here, .fvar (.there .here), .fvar (.there (.there .here))) ::
        p.edges_m.map (fun t => (lift_m t.1, lift_m t.2.1, lift_m t.2.2)),
      (k, .fvar .here, .fvar (.there (.there (.there .here)))) ::
        p.traces_m.map (fun t => (t.1, lift_m t.2.1, lift_m t.2.2))⟩

/-- 预算对应的就是实际将要反射的完整矩阵，不另外编码一个近似公式。 -/
def formula_m (Λ : List Nat) : Formula ℒ [] (context_m Λ.length) :=
  let p := syntax_m Λ
  let s := p.parameter_m
  PowerlessRelabelMatrix.formula_m (s 0) (s 1) (s 2) (s 3) (s 4) (s 5)
    (s 6) (s 7) (s 8) (s 9) (s 10) (s 11) p.edges_m p.traces_m

def budget_m (Λ : List Nat) : Nat := PowerlessSourceStandardBudget.budget_m (formula_m Λ)

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def env_l (a : Fin 12 → carrier_l ℳ) : (Ξ : List (PowerlessRelabelWitness.entry_l ℳ)) →
    Env ℳ [] (context_m (Ξ.map (fun s => s.k)).length)
  | List.nil =>
    { boundVal := fun v => nomatch v
      freeVal := fun {s} v => match s with | .set => a v.position }
  | s :: Ξ => ((((env_l a Ξ).pushFree s.S).pushFree s.E).pushFree s.D).pushFree s.n

private theorem position_l {n : Nat} (i : Fin n) :
    (SetTheory.Definitional.Project.fo_bound_variable i).position.val = i.val := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change (SetTheory.Definitional.Project.fo_bound_variable j).position.val + 1 = j.val + 1
      exact congrArg (fun x => x + 1) (ih j)

/-- 所有槽实际读回原数据：基础参数、具名边图与顶端迹同时对应。
证明对外部记录列表归纳，不对内部自然数或内部列数作宿主归纳。 -/
theorem source_l (a : Fin 12 → carrier_l ℳ) (Ξ : List (PowerlessRelabelWitness.entry_l ℳ)) :
    let p := syntax_m (Ξ.map (fun s => s.k))
    let η := env_l a Ξ
    (∀ i, (p.parameter_m i).eval η = a i) ∧
    p.edges_m.map (fun t => (t.1.eval η, t.2.1.eval η, t.2.2.eval η)) =
      PowerlessRelabelWitness.edges_l Ξ ∧
    p.traces_m.map (fun t => (t.1, t.2.1.eval η, t.2.2.eval η)) =
      Ξ.map (fun s => (s.k, s.n, s.S)) := by
  induction Ξ with
  | nil =>
    refine ⟨?_, rfl, rfl⟩
    intro i
    change a (SetTheory.Definitional.Project.fo_bound_variable i).position = a i
    exact congrArg a (Fin.ext (position_l i))
  | cons s Ξ ih =>
    have h (t : Term ℒ []
        (context_m (Ξ.map (fun r : PowerlessRelabelWitness.entry_l ℳ => r.k)).length) .set) :
        (lift_m t).eval (env_l a (s :: Ξ)) = t.eval (env_l a Ξ) := by
      change (lift_m t).eval
        (((((env_l a Ξ).pushFree s.S).pushFree s.E).pushFree s.D).pushFree s.n) = _
      simp only [lift_m, Term.eval_weakenFree]
    dsimp only [List.map, syntax_m]
    simp only [List.map_map, Function.comp_def]
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (h ((syntax_m (Ξ.map (fun r => r.k))).parameter_m i)).trans (ih.1 i)
    · change (s.n, s.D, s.E) :: _ = (s.n, s.D, s.E) :: _
      apply congrArg (List.cons (s.n, s.D, s.E))
      refine (List.map_congr_left ?_).trans ih.2.1
      intro t _
      exact Prod.ext (h t.1) (Prod.ext (h t.2.1) (h t.2.2))
    · change (s.k, s.n, s.S) :: _ = (s.k, s.n, s.S) :: _
      apply congrArg (List.cons (s.k, s.n, s.S))
      refine (List.map_congr_left ?_).trans ih.2.2
      intro t _
      exact Prod.ext rfl (Prod.ext (h t.2.1) (h t.2.2))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelParameters
