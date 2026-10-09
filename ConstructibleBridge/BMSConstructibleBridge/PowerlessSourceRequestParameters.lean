import BMSConstructibleBridge.PowerlessSourceRequests

/-!
# 有限请求族的标签参数提升

对象语言固定为纯集合论语言 ℒ，使用原 Formula、Substitution 与满足关系。
提升在输出及全部输入之后、原参数上下文之前插入外部有限多个标签槽。
语义桥对任意结构和任意标签值成立，不要求标签已经存在或彼此不同。
本模块是语法与宿主语义辅助接口，不是原对象理论中的最终可推导性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRequestParameters

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 保持前 k 个槽，在其后的原参数区之前插入 m 个标签槽。 -/
def insert_m {Δ : SortContext ℒ} (k m : Nat) :
    Variable (List.replicate k .set ++ Δ) .set →
      Variable (List.replicate k .set ++ (List.replicate m .set ++ Δ)) .set :=
  match k with
  | 0 => PowerlessSourceOpening.skip_m m
  | k + 1 => fun v => match v with
    | .here => .here
    | .there v => .there (insert_m k m v)

/-- 替换只改变自由变量；前缀中的输出和输入不会被标签整体推后。 -/
def binding_m {Δ : SortContext ℒ} (k m : Nat) :
    Substitution ℒ [] (List.replicate k .set ++ Δ) []
      (List.replicate k .set ++ (List.replicate m .set ++ Δ)) :=
  .map (fun v => nomatch v)
    (fun {s} v => match s with | .set => .fvar (insert_m k m v))

def term_m {Δ : SortContext ℒ} (k m : Nat)
    (s : Term ℒ [] (List.replicate k .set ++ Δ) .set) :
    Term ℒ [] (List.replicate k .set ++ (List.replicate m .set ++ Δ)) .set :=
  s.substitute (binding_m k m)

/-- 请求首槽是输出，随后 n 槽是输入，标签插在这 n+1 槽之后。 -/
def inflate_m {Δ : SortContext ℒ} (n m : Nat)
    (χ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))) :
    Formula ℒ [] (.set :: (List.replicate n .set ++ (List.replicate m .set ++ Δ))) :=
  χ.substitute (binding_m (n + 1) m)

theorem insert_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ) (k m : Nat)
    (v : Values ℳ.Carrier (List.replicate k .set))
    (w : Values ℳ.Carrier (List.replicate m .set))
    (x : Variable (List.replicate k .set ++ Δ) .set) :
    (PowerlessSourceTuple.env_l (PowerlessSourceTuple.env_l η m w) k v).freeVal
        (insert_m k m x) = (PowerlessSourceTuple.env_l η k v).freeVal x := by
  match k, v, x with
  | 0, .nil, x => exact PowerlessSourceOpening.skip_l η m w x
  | k + 1, .cons _ v, .here => rfl
  | k + 1, .cons _ v, .there x => exact insert_l η k m v w x

theorem pullback_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ) (k m : Nat)
    (v : Values ℳ.Carrier (List.replicate k .set))
    (w : Values ℳ.Carrier (List.replicate m .set)) :
    Env.pullback
        (PowerlessSourceTuple.env_l (PowerlessSourceTuple.env_l η m w) k v)
        (binding_m k m) = PowerlessSourceTuple.env_l η k v := by
  apply Env.ext
  · intro _ x
    nomatch x
  · intro s x
    cases s
    exact insert_l η k m v w x

theorem term_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ) (k m : Nat)
    (v : Values ℳ.Carrier (List.replicate k .set))
    (w : Values ℳ.Carrier (List.replicate m .set))
    (s : Term ℒ [] (List.replicate k .set ++ Δ) .set) :
    (term_m k m s).eval
        (PowerlessSourceTuple.env_l (PowerlessSourceTuple.env_l η m w) k v) =
      s.eval (PowerlessSourceTuple.env_l η k v) := by
  rw [term_m, Term.eval_substitute, pullback_l]

theorem prefix_formula_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ) (k m : Nat)
    (v : Values ℳ.Carrier (List.replicate k .set))
    (w : Values ℳ.Carrier (List.replicate m .set))
    (χ : Formula ℒ [] (List.replicate k .set ++ Δ)) :
    (χ.substitute (binding_m k m)).satisfies
        (PowerlessSourceTuple.env_l (PowerlessSourceTuple.env_l η m w) k v) ↔
      χ.satisfies (PowerlessSourceTuple.env_l η k v) := by
  rw [Formula.satisfies_substitute, pullback_l]

/-- 任意标签值下，提升后的请求与原请求使用相同的输出及输入求值。 -/
theorem formula_l {Δ : SortContext ℒ} (η : Env ℳ [] Δ) (n m : Nat)
    (v : Values ℳ.Carrier (List.replicate n .set))
    (w : Values ℳ.Carrier (List.replicate m .set))
    (χ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))) (y : carrier_l ℳ) :
    (inflate_m n m χ).satisfies
        ((PowerlessSourceTuple.env_l (PowerlessSourceTuple.env_l η m w) n v).pushFree y) ↔
      χ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y) :=
  prefix_formula_l η (n + 1) m (.cons y v) w χ

/-- 标签槽依上下文首槽到末槽排列；这里只生成变量，不生成模型中的标签。 -/
def tags_m (Δ : SortContext ℒ) :
    (m : Nat) → List (Variable (List.replicate m .set ++ Δ) .set)
  | 0 => []
  | m + 1 => .here :: (tags_m Δ m).map (fun v => .there v)

theorem tags_length_m (Δ : SortContext ℒ) (m : Nat) :
    (tags_m Δ m).length = m := by
  induction m with
  | zero => rfl
  | succ m h => simp only [tags_m, List.length_cons, List.length_map, h]

/-- 语法槽不重复；模型中标签值不同仍须由调用者另行提供。 -/
theorem tags_nodup_m (Δ : SortContext ℒ) (m : Nat) :
    (tags_m Δ m).Nodup := by
  induction m with
  | zero => exact List.nodup_nil
  | succ m h =>
    rw [tags_m, List.nodup_cons]
    constructor
    · intro h₀
      obtain ⟨v, _, h₁⟩ := List.mem_map.mp h₀
      cases h₁
    · exact h.map (fun _ _ h₀ => Variable.there.inj h₀)

/-- 对原有限公式族平展全部请求，保留存在矩阵与全称反例矩阵。 -/
def family_m {Γ Δ : SortContext ℒ} (Φ : List (Formula ℒ Γ Δ)) :
    List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))) :=
  Φ.flatMap (PowerlessSourceRequests.requests_m (.truth : Formula ℒ [] (.set :: Δ)))

/-- 每条请求的外部元数保持不变，只提升它的原参数区。 -/
def entries_m {Δ : SortContext ℒ} (m : Nat)
    (F : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))) :
    List (Σ n : Nat, Formula ℒ []
      (.set :: (List.replicate n .set ++ (List.replicate m .set ++ Δ)))) :=
  F.map (fun p => ⟨p.1, inflate_m p.1 m p.2⟩)

theorem entries_length_m {Δ : SortContext ℒ} (m : Nat)
    (F : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))) :
    (entries_m m F).length = F.length := by
  simp only [entries_m, List.length_map]

theorem entry_mem_m {Δ : SortContext ℒ} (m : Nat)
    {F : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))}
    {n : Nat} {χ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))}
    (hχ : Sigma.mk n χ ∈ F) :
    Sigma.mk n (inflate_m n m χ) ∈ entries_m m F :=
  List.mem_map.mpr ⟨Sigma.mk n χ, hχ, rfl⟩

theorem request_mem_m {Γ Δ : SortContext ℒ} {Φ : List (Formula ℒ Γ Δ)}
    {φ : Formula ℒ Γ Δ}
    {p : Σ n : Nat, Formula ℒ []
      (.set :: (List.replicate (α := (ℒ).SortSymbol) n .set ++ Δ))}
    (hφ : φ ∈ Φ)
    (hp : p ∈ PowerlessSourceRequests.requests_m (Γ := Γ) (Δ := Δ)
      (.truth : Formula ℒ [] (.set :: Δ)) φ) :
    p ∈ family_m (Γ := Γ) (Δ := Δ) Φ := by
  change p ∈ Φ.flatMap (fun ψ : Formula ℒ Γ Δ =>
    PowerlessSourceRequests.requests_m (Γ := Γ) (Δ := Δ)
      (.truth : Formula ℒ [] (.set :: Δ)) ψ)
  exact List.mem_flatMap.mpr ⟨φ, hφ, hp⟩

#print axioms formula_l
#print axioms term_l
#print axioms tags_nodup_m
#print axioms entry_mem_m

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessSourceRequestParameters
