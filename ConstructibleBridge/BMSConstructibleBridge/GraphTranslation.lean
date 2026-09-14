import BMSConstructibleBridge.GraphDomain
import BMSConstructibleBridge.GraphQuotient
import BMSConstructibleBridge.SecondOrderSubstitution

/-!
# 纯集合论公式到双排序算术的递归翻译

每个集合变量展开为一个根数变量和一个关系实数变量。量词引入两个变量并
使用实际根良基域公式限制范围；等词和成员使用已核验的跨图公式。全部绑定
和自由变量由原有类型化语法核管理，不把含参数公式偷偷视为闭句。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.GraphTranslation

open Logic FirstOrder SecondOrderSyntax

set_option autoImplicit false

/-- 一个源集合变量展开为根、关系两个槽位。 -/
def context_m : SortContext ℒ → SortContext signature_m
  | [] => []
  | _ :: Γ => .num :: .set :: context_m Γ

def root_var_m {Γ : SortContext ℒ} : Variable Γ .set → Variable (context_m Γ) .num
  | .here => .here
  | .there v => .there (.there (root_var_m v))

def graph_var_m {Γ : SortContext ℒ} : Variable Γ .set → Variable (context_m Γ) .set
  | .here => .there .here
  | .there v => .there (.there (graph_var_m v))

/-- 源语言没有函数符号，每个项都由对应的数根槽位表示。 -/
def root_m {Γ Δ : SortContext ℒ} : Term ℒ Γ Δ .set →
    Term signature_m (context_m Γ) (context_m Δ) .num
  | .bvar v => .bvar (root_var_m v)
  | .fvar v => .fvar (root_var_m v)
  | .app f _ => nomatch f

def graph_m {Γ Δ : SortContext ℒ} : Term ℒ Γ Δ .set →
    Term signature_m (context_m Γ) (context_m Δ) .set
  | .bvar v => .bvar (graph_var_m v)
  | .fvar v => .fvar (graph_var_m v)
  | .app f _ => nomatch f

private def domain_bind {Γ Δ : SortContext signature_m}
    (X : Term signature_m Γ Δ .set) (a : Term signature_m Γ Δ .num) :
    Substitution signature_m [] [.set, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => X
    | .there .here => a)

/-- 域模板在任意根项及关系项上的捕获避免实例化。 -/
def domain_m {Γ Δ : SortContext signature_m}
    (X : Term signature_m Γ Δ .set) (a : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  GraphDomain.formula_m.substitute (domain_bind X a)

private def atom_bind {Γ Δ : SortContext signature_m}
    (X Y : Term signature_m Γ Δ .set) (a b : Term signature_m Γ Δ .num) :
    Substitution signature_m [] [.set, .set, .num, .num] Γ Δ :=
  .map (fun v => nomatch v) (fun v => match v with
    | .here => X
    | .there .here => Y
    | .there (.there .here) => a
    | .there (.there (.there .here)) => b)

/-- 原子模板保留四个实际参数的顺序，不重选语义等价公式。 -/
def atom_m {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m [] [.set, .set, .num, .num])
    (X Y : Term signature_m Γ Δ .set) (a b : Term signature_m Γ Δ .num) : Formula signature_m Γ Δ :=
  φ.substitute (atom_bind X Y a b)

/-- 所有纯集合论公式的实际递归编译；量词范围明确限制到根良基图码。 -/
def form_m {Γ Δ : SortContext ℒ} : Formula ℒ Γ Δ →
    Formula signature_m (context_m Γ) (context_m Δ)
  | .falsum => .falsum
  | .truth => .truth
  | .rel .membership (.cons s (.cons t .nil)) =>
      atom_m GraphSyntax.mem_m (graph_m s) (graph_m t) (root_m s) (root_m t)
  | @Formula.equal _ _ _ .set s t =>
      atom_m GraphSyntax.eq_m (graph_m s) (graph_m t) (root_m s) (root_m t)
  | .neg φ => .neg (form_m φ)
  | .conj φ ψ => .conj (form_m φ) (form_m ψ)
  | .disj φ ψ => .disj (form_m φ) (form_m ψ)
  | .imp φ ψ => .imp (form_m φ) (form_m ψ)
  | .iff φ ψ => .iff (form_m φ) (form_m ψ)
  | .forallE .set φ => .forallE .set (.forallE .num
      (.imp (domain_m (.bvar (.there .here)) (.bvar .here)) (form_m φ)))
  | .existsE .set φ => .existsE .set (.existsE .num
      (.conj (domain_m (.bvar (.there .here)) (.bvar .here)) (form_m φ)))

/-- 实际源项的两个槽位均只含变量，不会引入额外函数符号。 -/
theorem root_pure_m {Γ Δ : SortContext ℒ} (s : Term ℒ Γ Δ .set) :
    pure_term_m (root_m s) = true :=
  match s with
  | .bvar _ | .fvar _ => rfl
  | .app f _ => nomatch f

theorem graph_pure_m {Γ Δ : SortContext ℒ} (s : Term ℒ Γ Δ .set) :
    pure_term_m (graph_m s) = true :=
  match s with
  | .bvar _ | .fvar _ => rfl
  | .app f _ => nomatch f

theorem domain_pure_m {Γ Δ : SortContext signature_m}
    (X : Term signature_m Γ Δ .set) (a : Term signature_m Γ Δ .num)
    (hX : pure_term_m X = true) (ha : pure_term_m a = true) :
    SecondOrderArithmetic.language_m (domain_m X a) = true := by
  refine (SecondOrderSubstitution.form_subst_m GraphDomain.formula_m _ _ ?_ ?_).trans ?_
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hX
    | .there .here => exact ha
  · exact SecondOrderArithmetic.pure_language_m GraphDomain.matrix_m GraphDomain.matrix_pure_m

theorem atom_pure_m {Γ Δ : SortContext signature_m}
    (φ : Formula signature_m [] [.set, .set, .num, .num])
    (X Y : Term signature_m Γ Δ .set) (a b : Term signature_m Γ Δ .num)
    (hφ : SecondOrderArithmetic.language_m φ = true)
    (hX : pure_term_m X = true) (hY : pure_term_m Y = true)
    (ha : pure_term_m a = true) (hb : pure_term_m b = true) :
    SecondOrderArithmetic.language_m (atom_m φ X Y a b) = true := by
  refine (SecondOrderSubstitution.form_subst_m φ _ _ ?_ ?_).trans hφ
  · intro s v
    nomatch v
  · intro s v
    match v with
    | .here => exact hX
    | .there .here => exact hY
    | .there (.there .here) => exact ha
    | .there (.there (.there .here)) => exact hb

private theorem all_pure {Γ Δ : SortContext signature_m}
    (ψ φ : Formula signature_m (.num :: .set :: Γ) Δ)
    (hψ : SecondOrderArithmetic.language_m ψ = true)
    (hφ : SecondOrderArithmetic.language_m φ = true) :
    SecondOrderArithmetic.language_m (.forallE .set (.forallE .num (.imp ψ φ))) = true := by
  change (SecondOrderArithmetic.language_m ψ && SecondOrderArithmetic.language_m φ) = true
  rw [hψ, hφ]
  rfl

private theorem exists_pure {Γ Δ : SortContext signature_m}
    (ψ φ : Formula signature_m (.num :: .set :: Γ) Δ)
    (hψ : SecondOrderArithmetic.language_m ψ = true)
    (hφ : SecondOrderArithmetic.language_m φ = true) :
    SecondOrderArithmetic.language_m (.existsE .set (.existsE .num (.conj ψ φ))) = true := by
  change (SecondOrderArithmetic.language_m ψ && SecondOrderArithmetic.language_m φ) = true
  rw [hψ, hφ]
  rfl

/-- 任意源公式的实际翻译都通过纯二阶语言检查，可用作对象模式正文。 -/
theorem form_pure_m {Γ Δ : SortContext ℒ} (φ : Formula ℒ Γ Δ) :
    SecondOrderArithmetic.language_m (form_m φ) = true := by
  match φ with
  | .falsum | .truth => rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      exact atom_pure_m _ _ _ _ _
        (SecondOrderArithmetic.pure_language_m GraphSyntax.mem_matrix_m GraphSyntax.mem_matrix_pure_m)
        (graph_pure_m s) (graph_pure_m t) (root_pure_m s) (root_pure_m t)
  | @Formula.equal _ _ _ .set s t =>
      exact atom_pure_m _ _ _ _ _
        (SecondOrderArithmetic.pure_language_m GraphSyntax.matrix_m GraphSyntax.matrix_pure_m)
        (graph_pure_m s) (graph_pure_m t) (root_pure_m s) (root_pure_m t)
  | .neg φ => exact form_pure_m φ
  | .conj φ ψ | .disj φ ψ | .imp φ ψ | .iff φ ψ =>
      change (SecondOrderArithmetic.language_m (form_m φ) &&
        SecondOrderArithmetic.language_m (form_m ψ)) = true
      rw [form_pure_m φ, form_pure_m ψ]
      rfl
  | .forallE .set φ =>
      exact all_pure _ _ (domain_pure_m _ _ rfl rfl) (form_pure_m φ)
  | .existsE .set φ =>
      exact exists_pure _ _ (domain_pure_m _ _ rfl rfl) (form_pure_m φ)
termination_by φ.size
decreasing_by all_goals simp only [Formula.size]; omega

/-- 固定关系参数并让根数变化，实际翻译可直接进入对象理解模式。 -/
theorem comprehension_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.comprehension_m (form_m φ)) :=
  SecondOrderArithmetic.comprehension_derives_m _ (form_pure_m φ)

/-- 同一实际翻译的根数归纳实例；不等于对所有图码的良基归纳。 -/
theorem induction_m {Δ : SortContext ℒ} (φ : Formula ℒ [] (.set :: Δ)) :
    Derives SecondOrderArithmetic.theory_m []
      (SecondOrderArithmetic.induction_m (form_m φ)) :=
  SecondOrderArithmetic.induction_derives_m _ (form_pure_m φ)

/-- 域模板在任意标准项环境中都表达该项所给关系的根可达性。 -/
theorem domain_l {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (X : Term signature_m Γ Δ .set) (a : Term signature_m Γ Δ .num) :
    Formula.satisfies η (domain_m X a) ↔ Acc (GraphSyntax.relation_l (X.eval η)) (a.eval η) := by
  rw [domain_m, Formula.satisfies_substitute, GraphDomain.formula_l, GraphDomain.acc_l]
  rfl

theorem eq_l {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (X Y : Term signature_m Γ Δ .set) (a b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (atom_m GraphSyntax.eq_m X Y a b) ↔
      Bisimulation.eq_l (GraphSyntax.relation_l (X.eval η)) (GraphSyntax.relation_l (Y.eval η))
        (a.eval η) (b.eval η) := by
  rw [atom_m, Formula.satisfies_substitute, GraphSyntax.eq_l]
  rfl

theorem mem_l {Γ Δ : SortContext signature_m} (η : Env structure_l Γ Δ)
    (X Y : Term signature_m Γ Δ .set) (a b : Term signature_m Γ Δ .num) :
    Formula.satisfies η (atom_m GraphSyntax.mem_m X Y a b) ↔
      ∃ c, GraphSyntax.relation_l (Y.eval η) c (b.eval η) ∧
        Bisimulation.eq_l (GraphSyntax.relation_l (X.eval η)) (GraphSyntax.relation_l (Y.eval η))
          (a.eval η) c := by
  rw [atom_m, Formula.satisfies_substitute, GraphSyntax.mem_l]
  rfl

end YesMetaZFC.BMS.ConstructibleBridge.GraphTranslation
