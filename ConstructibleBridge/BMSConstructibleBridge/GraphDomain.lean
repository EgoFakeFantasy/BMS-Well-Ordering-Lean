import BMSConstructibleBridge.GraphSyntax
import BMSConstructibleBridge.CountableGraph

/-!
# 有根图解释域的纯 Π¹₁ 公式

用单个全称集合量词检查从指定根出发的每条全域数值链都有断点。只约束指定
根，不把域改为整张数关系全局良基。核验该公式与宿主根可达性的精确等价，
再将已有图码的相等、成员与实际纯二阶公式接线。

这些等价针对标准全二阶环境；它们不是从任意 Henkin 模型内部良基性推出
外部可达性的定理，更没有增加这样的可靠性公理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphDomain

open Logic FirstOrder SecondOrderSyntax GraphSyntax

set_option autoImplicit false

/-- 域矩阵使用的实际全函数图模板，供非标准语义核验复用。 -/
def function_m : Formula signature_m [.set] [.set, .num] :=
  .forallE .num (.existsE .num (.conj
    (edge_m (.bvar (.there (.there .here))) (.bvar (.there .here)) (.bvar .here))
    (.forallE .num (.imp
      (edge_m (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))) (.bvar .here))
      (.equal (.bvar .here) (.bvar (.there .here)))))))

private def zero {Γ Δ : SortContext signature_m} : Term signature_m Γ Δ .num :=
  Term.app (σ := signature_m) .zero .nil

private def succ {Γ Δ : SortContext signature_m} (t : Term signature_m Γ Δ .num) :
    Term signature_m Γ Δ .num := Term.app (σ := signature_m) .succ (.cons t .nil)

/-- 域公式的矩阵：量化任意函数图，固定起点，并要求某条相邻边失败。 -/
def matrix_m : Formula signature_m [.set] [.set, .num] :=
  .imp function_m (.imp (edge_m (.bvar .here) zero (.fvar (.there .here)))
    (.existsE .num (.existsE .num (.existsE .num (.conj
      (edge_m (.bvar (.there (.there (.there .here))))
        (.bvar (.there (.there .here))) (.bvar (.there .here)))
      (.conj
        (edge_m (.bvar (.there (.there (.there .here))))
          (succ (.bvar (.there (.there .here)))) (.bvar .here))
        (.neg (edge_m (.fvar .here) (.bvar .here) (.bvar (.there .here))))))))))

/-- 第一个自由参数是关系实数，第二个是指定根。 -/
def formula_m : Formula signature_m [] [.set, .num] := .forallE .set matrix_m

theorem matrix_pure_m : pure_m matrix_m = true := rfl

/-- 单全称实数的根无下降链命题，所有内部量词均为数量词。 -/
def sentence_l (X : Set Nat) (a : Nat) : Prop :=
  ∀ Y : Set Nat, SecondOrderPresentation.function_l Y → Nat.pair 0 a ∈ Y →
    ∃ i b c, Nat.pair i b ∈ Y ∧ Nat.pair (i + 1) c ∈ Y ∧ ¬relation_l X c b

theorem formula_l (η : Env structure_l [] [.set, .num]) :
    Formula.satisfies η formula_m ↔ sentence_l (η.freeVal .here) (η.freeVal (.there .here)) := by
  simp only [formula_m, matrix_m, function_m, Formula.satisfies, edge_l, zero, succ,
    Term.eval, Arguments.eval]
  rfl

theorem no_chain_l (X : Set Nat) (a : Nat) : sentence_l X a ↔
    ¬∃ f : Nat → Nat, f 0 = a ∧ ∀ n, relation_l X (f (n + 1)) (f n) := by
  classical
  open SecondOrderPresentation in
    constructor
    · intro h
      rintro ⟨f, h₁, h₂⟩
      obtain ⟨i, b, c, h₃, h₄, h₅⟩ := h (graph_l f) (function_graph_l f)
        ((mem_graph_l f 0 a).mpr h₁.symm)
      have h₃ := (mem_graph_l f i b).mp h₃
      have h₄ := (mem_graph_l f (i + 1) c).mp h₄
      exact h₅ (h₃ ▸ h₄ ▸ h₂ i)
    · intro h Y h₁ h₂
      obtain ⟨f, h₃⟩ := (function_iff_l Y).mp h₁
      have h₄ : f 0 = a := ((h₃ 0 a).mp h₂).symm
      by_contra h₅
      apply h
      refine ⟨f, h₄, ?_⟩
      intro n
      by_contra h₆
      exact h₅ ⟨n, f n, f (n + 1), (h₃ n _).mpr rfl, (h₃ (n + 1) _).mpr rfl, h₆⟩

/-- 在标准全二阶环境中，域公式精确表示指定根的 Acc。 -/
theorem acc_l (X : Set Nat) (a : Nat) : sentence_l X a ↔ Acc (relation_l X) a := by
  classical
  rw [no_chain_l, ← not_acc_iff_exists_descending_chain]
  exact not_not

/-- 标准域参数环境，不从良基证书选择任何对象。 -/
def environment_l (X : Set Nat) (a : Nat) : Env structure_l [] [.set, .num] where
  boundVal := Assignment.empty
  freeVal := Assignment.push (M := structure_l) (sort := .set) X
    (Assignment.push (M := structure_l) (sort := .num) a Assignment.empty)

/-- 关系实数的逐边编码与原关系完全相同。 -/
theorem relation_real_l (A : CountableGraph.code_l) :
    relation_l (CountableGraph.real_l A) = A.rel := by
  funext a b
  exact propext (CountableGraph.real_iff_l A a b)

/-- 每个已有有根图码都满足同一个实际域公式。 -/
theorem code_l (A : CountableGraph.code_l) :
    Formula.satisfies (environment_l (CountableGraph.real_l A) A.root) formula_m := by
  rw [formula_l, acc_l]
  change Acc (relation_l (CountableGraph.real_l A)) A.root
  rw [relation_real_l]
  exact A.wf

/-- 从满足实际域公式的实数和根直接构造图码，明确限定为标准环境。 -/
def decode_l (X : Set Nat) (a : Nat)
    (h : Formula.satisfies (environment_l X a) formula_m) : CountableGraph.code_l :=
  ⟨relation_l X, a, (acc_l X a).mp ((formula_l _).mp h)⟩

/-- 解码不丢弃关系实数中未从根访问的边。 -/
theorem real_decode_l (X : Set Nat) (a : Nat)
    (h : Formula.satisfies (environment_l X a) formula_m) :
    CountableGraph.real_l (decode_l X a h) = X := by
  apply Set.ext
  intro n
  change Nat.pair n.unpair.1 n.unpair.2 ∈ X ↔ n ∈ X
  rw [Nat.pair_unpair]

/-- 相等与成员公式的四个参数使用原关系实数及原根，不另选代码。 -/
def pair_environment_l (A B : CountableGraph.code_l) :
    Env structure_l [] [.set, .set, .num, .num] where
  boundVal := Assignment.empty
  freeVal := Assignment.push (M := structure_l) (sort := .set) (CountableGraph.real_l A)
    (Assignment.push (M := structure_l) (sort := .set) (CountableGraph.real_l B)
      (Assignment.push (M := structure_l) (sort := .num) A.root
        (Assignment.push (M := structure_l) (sort := .num) B.root Assignment.empty)))

/-- 实际纯二阶等词公式与此前图码域的双模拟相等精确一致。 -/
theorem eq_l (A B : CountableGraph.code_l) :
    Formula.satisfies (pair_environment_l A B) GraphSyntax.eq_m ↔ CountableGraph.eq_l A B := by
  rw [GraphSyntax.eq_l]
  change Bisimulation.eq_l (relation_l (CountableGraph.real_l A))
    (relation_l (CountableGraph.real_l B)) A.root B.root ↔ _
  rw [relation_real_l, relation_real_l]
  rfl

/-- 实际纯二阶成员公式保留不同关系之间的直接子节点换码语义。 -/
theorem mem_l (A B : CountableGraph.code_l) :
    Formula.satisfies (pair_environment_l A B) GraphSyntax.mem_m ↔ CountableGraph.mem_l A B := by
  rw [GraphSyntax.mem_l]
  change (∃ c, relation_l (CountableGraph.real_l B) c B.root ∧
    Bisimulation.eq_l (relation_l (CountableGraph.real_l A))
      (relation_l (CountableGraph.real_l B)) A.root c) ↔ _
  rw [relation_real_l, relation_real_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.GraphDomain
