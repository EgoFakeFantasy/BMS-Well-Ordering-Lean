import BMSConstructibleBridge.PrimitiveFormulas
import BMSConstructibleBridge.Bisimulation

/-!
# 跨图双模拟的纯二阶算术公式

图和见证均为实数变量，节点为数变量。配对关系使用已经消去额外符号的纯
加乘模板；双模拟见证正文仅含数量词。最大双模拟实际写成单个存在集合量词，
不是把宿主谓词加进签名。本文件核验标准语义，还没有生成对象推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphSyntax

open Logic FirstOrder SecondOrderSyntax

set_option autoImplicit false

/-- 实数的自然数二元关系解释。 -/
def relation_l (X : Set Nat) (a b : Nat) : Prop := Nat.pair a b ∈ X

/-- 用纯加乘配对图读取实数中的一条边。 -/
def edge_m {Γ Δ : SortContext signature_m} (X : Term signature_m Γ Δ .set)
    (s t : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  .existsE .num (.conj
    (PrimitiveFormulas.pair_m (s.weakenBound sort_m.num) (t.weakenBound sort_m.num) (.bvar .here))
    (.rel .mem (.cons (.bvar .here) (.cons (X.weakenBound sort_m.num) .nil))))

theorem edge_pure_m {Γ Δ : SortContext signature_m} (X : Term signature_m Γ Δ .set)
    (s t : Term signature_m Γ Δ .num) (hX : pure_term_m X = true)
    (hs : pure_term_m s = true) (ht : pure_term_m t = true) :
    pure_m (edge_m X s t) = true := by
  change (pure_m (PrimitiveFormulas.pair_m (s.weakenBound sort_m.num)
    (t.weakenBound sort_m.num) (.bvar .here)) &&
      (true && (pure_term_m (X.weakenBound sort_m.num) && true))) = true
  rw [PrimitiveFormulas.pair_pure_l _ _ _
    ((PrimitiveFormulas.weaken_l s).trans hs) ((PrimitiveFormulas.weaken_l t).trans ht) rfl,
    PrimitiveFormulas.weaken_l, hX]
  rfl

theorem edge_l {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (X : Term signature_m Γ Δ .set) (s t : Term signature_m Γ Δ .num) :
    Formula.satisfies η (edge_m X s t) ↔ relation_l (X.eval η) (s.eval η) (t.eval η) := by
  simp only [edge_m, Formula.satisfies, PrimitiveFormulas.pair_l,
    Term.eval_weakenBound, Term.eval, Arguments.eval]
  change (∃ p : Nat, Nat.pair (s.eval η) (t.eval η) = p ∧ p ∈ X.eval η) ↔ _
  simp [relation_l]

private abbrev R {Γ : SortContext signature_m} : Term signature_m Γ [.set, .set, .set] .set :=
  .fvar .here

private abbrev S {Γ : SortContext signature_m} : Term signature_m Γ [.set, .set, .set] .set :=
  .fvar (.there .here)

private abbrev H {Γ : SortContext signature_m} : Term signature_m Γ [.set, .set, .set] .set :=
  .fvar (.there (.there .here))

/-- 三个自由实数依次为 R、S、H；两个匹配方向均保留 H 的原坐标顺序。 -/
def witness_m : Formula signature_m [] [.set, .set, .set] :=
  .forallE .num (.forallE .num (.imp (edge_m H (.bvar (.there .here)) (.bvar .here))
    (.conj
      (.forallE .num (.imp (edge_m R (.bvar .here) (.bvar (.there (.there .here))))
        (.existsE .num (.conj
          (edge_m S (.bvar .here) (.bvar (.there (.there .here))))
          (edge_m H (.bvar (.there .here)) (.bvar .here))))))
      (.forallE .num (.imp (edge_m S (.bvar .here) (.bvar (.there .here)))
        (.existsE .num (.conj
          (edge_m R (.bvar .here) (.bvar (.there (.there (.there .here)))))
          (edge_m H (.bvar .here) (.bvar (.there .here))))))))))

/-- 见证正文是纯算术矩阵，没有集合量词或未消去的配对符号。 -/
theorem witness_pure_m : pure_m witness_m = true := rfl

theorem witness_l (η : Env structure_l [] [.set, .set, .set]) :
    Formula.satisfies η witness_m ↔ Bisimulation.witness_l
      (relation_l (η.freeVal .here)) (relation_l (η.freeVal (.there .here)))
      (relation_l (η.freeVal (.there (.there .here)))) := by
  simp only [witness_m, Formula.satisfies, edge_l, R, S, H, Term.eval]
  rfl

private def bind : Substitution signature_m [] [.set, .set, .set]
    [.set] [.set, .set, .num, .num] :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .fvar .here
    | .there .here => .fvar (.there .here)
    | .there (.there .here) => .bvar .here)

/-- 最大双模拟的算术矩阵；根参数置于两个实数参数之后。 -/
def matrix_m : Formula signature_m [.set] [.set, .set, .num, .num] :=
  .conj (witness_m.substitute bind)
    (edge_m (.bvar .here) (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here)))))

/-- 最大双模拟的实际 Σ¹₁ 公式，恰有一个集合存在量词。 -/
def eq_m : Formula signature_m [] [.set, .set, .num, .num] := .existsE .set matrix_m

theorem matrix_pure_m : pure_m matrix_m = true := rfl

theorem eq_l (η : Env structure_l [] [.set, .set, .num, .num]) :
    Formula.satisfies η eq_m ↔ Bisimulation.eq_l
      (relation_l (η.freeVal .here)) (relation_l (η.freeVal (.there .here)))
      (η.freeVal (.there (.there .here))) (η.freeVal (.there (.there (.there .here)))) := by
  rw [eq_m, Formula.satisfies, Bisimulation.coded_l]
  apply exists_congr
  intro X
  rw [matrix_m, Formula.satisfies, Formula.satisfies_substitute, witness_l, edge_l]
  rfl

private def mem_bind : Substitution signature_m [] [.set, .set, .set]
    [.num, .set] [.set, .set, .num, .num] :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => .fvar .here
    | .there .here => .fvar (.there .here)
    | .there (.there .here) => .bvar (.there .here))

/-- 成员解释的算术矩阵：选择右图的子节点并提供到该节点的跨图双模拟见证。 -/
def mem_matrix_m : Formula signature_m [.set] [.set, .set, .num, .num] :=
  .existsE .num (.conj (witness_m.substitute mem_bind)
    (.conj
      (edge_m (.fvar (.there .here)) (.bvar .here) (.fvar (.there (.there (.there .here)))))
      (edge_m (.bvar (.there .here)) (.fvar (.there (.there .here))) (.bvar .here))))

/-- 成员关系也实际处于单存在集合量词的纯 Σ¹₁ 片段。 -/
def mem_m : Formula signature_m [] [.set, .set, .num, .num] := .existsE .set mem_matrix_m

theorem mem_matrix_pure_m : pure_m mem_matrix_m = true := rfl

private theorem mem_body_l (η : Env structure_l [] [.set, .set, .num, .num]) (X : Set Nat) :
    Formula.satisfies (η.pushBound X) mem_matrix_m ↔ ∃ c,
      Bisimulation.witness_l (relation_l (η.freeVal .here))
        (relation_l (η.freeVal (.there .here))) (relation_l X) ∧
      relation_l (η.freeVal (.there .here)) c (η.freeVal (.there (.there (.there .here)))) ∧
      relation_l X (η.freeVal (.there (.there .here))) c := by
  simp only [mem_matrix_m, Formula.satisfies, Formula.satisfies_substitute, witness_l, edge_l]
  rfl

/-- 公式语义精确等于先取右图直接子节点再跨图换码的成员关系。 -/
theorem mem_l (η : Env structure_l [] [.set, .set, .num, .num]) :
    Formula.satisfies η mem_m ↔ ∃ c,
      relation_l (η.freeVal (.there .here)) c (η.freeVal (.there (.there (.there .here)))) ∧
      Bisimulation.eq_l (relation_l (η.freeVal .here))
        (relation_l (η.freeVal (.there .here))) (η.freeVal (.there (.there .here))) c := by
  rw [mem_m, Formula.satisfies]
  simp_rw [mem_body_l]
  constructor
  · rintro ⟨X, c, h, h₁, h₂⟩
    exact ⟨c, h₁, (Bisimulation.coded_l _ _ _ _).mpr ⟨X, h, h₂⟩⟩
  · rintro ⟨c, h, h₁⟩
    obtain ⟨X, h₁, h₂⟩ := (Bisimulation.coded_l _ _ _ _).mp h₁
    exact ⟨X, c, h₁, h, h₂⟩

end YesMetaZFC.BMS.ConstructibleBridge.GraphSyntax
