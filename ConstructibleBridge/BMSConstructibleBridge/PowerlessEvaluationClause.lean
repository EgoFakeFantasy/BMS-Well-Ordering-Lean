import BMSConstructibleBridge.PowerlessFormulaConstructor
import BMSConstructibleBridge.PowerlessAssignmentUpdate

/-!
# 实际赋值图上的局部求值公式

四类构造子为隶属、等号、与非及存在量词。量词显式记录变量索引，
替换保持原有限定义域。这里只定义固定纯算子，未假设统一真谓词存在。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationClause

open Logic FirstOrder ThirdOrderSemantics PowerlessFormulaConstructor

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SetTheory.Definitional.Project.FirstOrderSemantics.reduct

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

def query_l (H n f : carrier_l ℳ) : Prop := ∃ Y, value_l H n Y ∧ member_l ℳ f Y

def query_m {Γ Δ : SortContext ℒ} (H n f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .existsE .set (.conj (SecondOrderObjectSyntax.value_m (H.weakenBound SetTheory.SetSort.set)
    (n.weakenBound SetTheory.SetSort.set) (.bvar .here))
    (SecondOrderObjectSyntax.member_m (f.weakenBound SetTheory.SetSort.set) (.bvar .here)))

theorem query_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (H n f : Term ℒ Γ Δ .set) :
    (query_m H n f).satisfies η ↔ query_l (H.eval η) (n.eval η) (f.eval η) := by
  simp only [query_m, query_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def equal_l (f i j : carrier_l ℳ) : Prop := ∃ a, value_l f i a ∧ value_l f j a

def equal_m {Γ Δ : SortContext ℒ} (f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (SecondOrderObjectSyntax.value_m (w f) (w i) (.bvar .here))
    (SecondOrderObjectSyntax.value_m (w f) (w j) (.bvar .here)))

theorem equal_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f i j : Term ℒ Γ Δ .set) :
    (equal_m f i j).satisfies η ↔ equal_l (f.eval η) (i.eval η) (j.eval η) := by
  simp only [equal_m, equal_l, Formula.satisfies, value_formula_l, Term.eval_weakenBound]
  rfl

def member_l (f i j : carrier_l ℳ) : Prop :=
  ∃ a b, value_l f i a ∧ value_l f j b ∧ ThirdOrderSemantics.member_l ℳ a b

def member_m {Γ Δ : SortContext ℒ} (f i j : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.existsE .set (.conj (SecondOrderObjectSyntax.value_m (w f) (w i) (.bvar (.there .here)))
    (.conj (SecondOrderObjectSyntax.value_m (w f) (w j) (.bvar .here))
      (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (.bvar .here)))))

theorem member_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (f i j : Term ℒ Γ Δ .set) :
    (member_m f i j).satisfies η ↔ member_l (f.eval η) (i.eval η) (j.eval η) := by
  simp only [member_m, member_l, Formula.satisfies, value_formula_l,
    SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def exists_l (ω A H f i b : carrier_l ℳ) : Prop :=
  ∃ n, ThirdOrderSemantics.member_l ℳ n ω ∧ map_l f n A ∧ ThirdOrderSemantics.member_l ℳ i n ∧
    ∃ a, ThirdOrderSemantics.member_l ℳ a A ∧ ∃ g,
      map_l g n A ∧ PowerlessAssignmentUpdate.update_l f i a g ∧ query_l H b g

def exists_m {Γ Δ : SortContext ℒ} (ω A H f i b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set
  let v (t : Term ℒ Γ Δ .set) := ((w t).weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  .existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) (w ω))
    (.conj (SecondOrderObjectSyntax.map_m (w f) (.bvar .here) (w A))
      (.conj (SecondOrderObjectSyntax.member_m (w i) (.bvar .here))
        (.existsE .set (.conj (SecondOrderObjectSyntax.member_m (.bvar .here) ((w A).weakenBound SetTheory.SetSort.set))
          (.existsE .set (.conj (SecondOrderObjectSyntax.map_m (.bvar .here) (.bvar (.there (.there .here))) (v A))
            (.conj (PowerlessAssignmentUpdate.update_m (v f) (v i) (.bvar (.there .here)) (.bvar .here))
              (query_m (v H) (v b) (.bvar .here))))))))))

theorem exists_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ) (ω A H f i b : Term ℒ Γ Δ .set) :
    (exists_m ω A H f i b).satisfies η ↔
      exists_l (ω.eval η) (A.eval η) (H.eval η) (f.eval η) (i.eval η) (b.eval η) := by
  simp only [exists_m, exists_l, Formula.satisfies, map_formula_l, PowerlessAssignmentUpdate.update_formula_l,
    query_formula_l, SecondOrderObjectSyntax.member_m, Arguments.eval, Term.eval_weakenBound]
  rfl

def clause_l (ω e T A t₁ t₂ t₃ H n f : carrier_l ℳ) : Prop :=
  (∃ i j, constructor_l ω e T e i j n ∧ member_l f i j) ∨
  (∃ i j, constructor_l ω e T t₁ i j n ∧ equal_l f i j) ∨
  (∃ a b, constructor_l ω e T t₂ a b n ∧ ¬(query_l H a f ∧ query_l H b f)) ∨
  (∃ i b, constructor_l ω e T t₃ i b n ∧ exists_l ω A H f i b)

def clause_m {Γ Δ : SortContext ℒ} (ω e T A t₁ t₂ t₃ H n f : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  let w (t : Term ℒ Γ Δ .set) := (t.weakenBound SetTheory.SetSort.set).weakenBound SetTheory.SetSort.set
  let c (t : Term ℒ Γ Δ .set) : Formula ℒ (.set :: .set :: Γ) Δ := constructor_m (w ω) (w e) (w T) (w t)
    (.bvar (.there .here)) (.bvar .here) (w n)
  .disj (.existsE .set (.existsE .set (.conj (c e) (member_m (w f) (.bvar (.there .here)) (.bvar .here)))))
    (.disj (.existsE .set (.existsE .set (.conj (c t₁) (equal_m (w f) (.bvar (.there .here)) (.bvar .here)))))
      (.disj (.existsE .set (.existsE .set (.conj (c t₂) (.neg (.conj
        (query_m (w H) (.bvar (.there .here)) (w f)) (query_m (w H) (.bvar .here) (w f)))))))
        (.existsE .set (.existsE .set (.conj (c t₃)
          (exists_m (w ω) (w A) (w H) (w f) (.bvar (.there .here)) (.bvar .here)))))))

theorem clause_formula_l {Γ Δ : SortContext ℒ} (η : Env ℳ Γ Δ)
    (ω e T A t₁ t₂ t₃ H n f : Term ℒ Γ Δ .set) :
    (clause_m ω e T A t₁ t₂ t₃ H n f).satisfies η ↔
      clause_l (ω.eval η) (e.eval η) (T.eval η) (A.eval η) (t₁.eval η) (t₂.eval η)
        (t₃.eval η) (H.eval η) (n.eval η) (f.eval η) := by
  simp only [clause_m, clause_l, Formula.satisfies, constructor_formula_l, member_formula_l,
    equal_formula_l, query_formula_l, exists_formula_l, Term.eval_weakenBound]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessEvaluationClause
