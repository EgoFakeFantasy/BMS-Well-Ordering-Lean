import BMSConstructibleBridge.PowerlessRelabelParameters

/-!
# 具名稳定边与顶端迹分离的重标号模板

原展开需要保留整个有限高度内的具名稳定边，但只反射低于当前行的顶端迹。
前者的层号只是内部数码参数，后者的外部层号决定部分真值公式。
因此语法只依赖具名边记录的个数与顶端迹层号列表，不读取具名边的外部层号。
每个具名记录占 n,D,E 三槽；迹沿用已有四槽记录和求值证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelTemplate

open Logic FirstOrder ThirdOrderSemantics PowerlessRelabelMatrix

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def context_m : Nat → Nat → SortContext ℒ
  | 0, k => PowerlessRelabelParameters.context_m k
  | d + 1, k => .set :: .set :: .set :: context_m d k

def lift_m {Δ : SortContext ℒ} (s : Term ℒ [] Δ .set) :
    Term ℒ [] (.set :: .set :: .set :: Δ) .set :=
  ((s.weakenFree SetTheory.SetSort.set).weakenFree SetTheory.SetSort.set).weakenFree
    SetTheory.SetSort.set

/-- 第一参数只有记录数，不含具名稳定层号。 -/
def syntax_m : (d : Nat) → (Λ : List Nat) → PowerlessRelabelParameters.packet_m (context_m d Λ.length)
  | 0, Λ =>
    let p := PowerlessRelabelParameters.syntax_m Λ
    ⟨p.parameter_m, List.nil, p.traces_m⟩
  | d + 1, Λ =>
    let p := syntax_m d Λ
    ⟨fun i => lift_m (p.parameter_m i),
      (.fvar .here, .fvar (.there .here), .fvar (.there (.there .here))) ::
        p.edges_m.map (fun t => (lift_m t.1, lift_m t.2.1, lift_m t.2.2)),
      p.traces_m.map (fun t => (t.1, lift_m t.2.1, lift_m t.2.2))⟩

def formula_m (d : Nat) (Λ : List Nat) : Formula ℒ [] (context_m d Λ.length) :=
  let p := syntax_m d Λ
  let s := p.parameter_m
  PowerlessRelabelMatrix.formula_m (s 0) (s 1) (s 2) (s 3) (s 4) (s 5)
    (s 6) (s 7) (s 8) (s 9) (s 10) (s 11) p.edges_m p.traces_m

def budget_m (d : Nat) (Λ : List Nat) : Nat :=
  PowerlessSourceStandardBudget.budget_m (formula_m d Λ)

structure edge_l (ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ) where
  n : carrier_l ℳ
  D : carrier_l ℳ
  E : carrier_l ℳ

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def env_l (a : Fin 12 → carrier_l ℳ) (Θ : List (PowerlessRelabelWitness.entry_l ℳ)) :
    (Ξ : List (edge_l ℳ)) →
      Env ℳ [] (context_m Ξ.length (Θ.map (fun r => r.k)).length)
  | List.nil => PowerlessRelabelParameters.env_l a Θ
  | r :: Ξ => (((env_l a Θ Ξ).pushFree r.E).pushFree r.D).pushFree r.n

/-- 两份独立记录同时读入同一个环境；具名边不额外要求顶端稳定。 -/
theorem source_l (a : Fin 12 → carrier_l ℳ) (Θ : List (PowerlessRelabelWitness.entry_l ℳ))
    (Ξ : List (edge_l ℳ)) :
    let p := syntax_m Ξ.length (Θ.map (fun r => r.k))
    let η := env_l a Θ Ξ
    (∀ i, (p.parameter_m i).eval η = a i) ∧
    p.edges_m.map (fun t => (t.1.eval η, t.2.1.eval η, t.2.2.eval η)) =
      Ξ.map (fun r => (r.n, r.D, r.E)) ∧
    p.traces_m.map (fun t => (t.1, t.2.1.eval η, t.2.2.eval η)) =
      Θ.map (fun r => (r.k, r.n, r.S)) := by
  induction Ξ with
  | nil =>
    have h := PowerlessRelabelParameters.source_l a Θ
    exact ⟨h.1, rfl, h.2.2⟩
  | cons r Ξ ih =>
    have h (t : Term ℒ []
        (context_m Ξ.length (Θ.map (fun s : PowerlessRelabelWitness.entry_l ℳ => s.k)).length) .set) :
        (lift_m t).eval (env_l a Θ (r :: Ξ)) = t.eval (env_l a Θ Ξ) := by
      change (lift_m t).eval ((((env_l a Θ Ξ).pushFree r.E).pushFree r.D).pushFree r.n) = _
      simp only [lift_m, Term.eval_weakenFree]
    dsimp only [List.length_cons, syntax_m]
    simp only [List.map_map, Function.comp_def]
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (h ((syntax_m Ξ.length (Θ.map (fun s => s.k))).parameter_m i)).trans (ih.1 i)
    · change (r.n, r.D, r.E) :: _ = (r.n, r.D, r.E) :: _
      apply congrArg (List.cons (r.n, r.D, r.E))
      simp only [List.map_map, Function.comp_def]
      refine (List.map_congr_left ?_).trans ih.2.1
      intro t _
      exact Prod.ext (h t.1) (Prod.ext (h t.2.1) (h t.2.2))
    · refine (List.map_congr_left ?_).trans ih.2.2
      intro t _
      exact Prod.ext rfl (Prod.ext (h t.2.1) (h t.2.2))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelabelTemplate
