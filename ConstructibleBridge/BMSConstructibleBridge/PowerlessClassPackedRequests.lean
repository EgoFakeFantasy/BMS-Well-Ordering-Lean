import BMSConstructibleBridge.PowerlessClassRelativeParameters
import BMSConstructibleBridge.PowerlessSourcePredicateRequests

/-!
# 类相对请求的有限元组编码

原请求先按实际有限元数打包，再相对化到同一个类。输出槽显式带类
守卫；输入与输出仍采用原求值的槽序。环境元数据与原参数分别传入。
二元捕获恢复的是原类结构中的请求闭包，不是环境模型的元素性。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassPackedRequests

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature
  PowerlessSourceClass.structure_l PowerlessSourceClass.type_l

universe u

variable {𝒱 : FirstOrder.Structure.{0, 0, 0, u} ℒ}

/-- 插入输入与输出两槽，同时保持一元域公式的受限变量。 -/
def domain_m {Θ : SortContext ℒ} (D : Formula ℒ [] (.set :: Θ)) :
    Formula ℒ [] (.set :: .set :: .set :: Θ) :=
  (D.substitute PowerlessSourceTuple.empty_binding_m).substitute
    PowerlessSourceTuple.empty_binding_m

theorem domain_formula_l {Θ : SortContext ℒ} (D : Formula ℒ [] (.set :: Θ))
    (ξ : Env 𝒱 [] Θ) (p y z : carrier_l 𝒱) :
    (domain_m D).satisfies (((ξ.pushFree p).pushFree y).pushFree z) ↔
      D.satisfies (ξ.pushFree z) :=
  (PowerlessSourceTuple.empty_formula_l _ (ξ.pushFree p) y z).trans
    (PowerlessSourceTuple.empty_formula_l D ξ p z)

def binding_m {Δ Θ : SortContext ℒ} (ν : VariableSubstitution ℒ Δ [] Θ) :
    VariableSubstitution ℒ (.set :: .set :: Δ) [] (.set :: .set :: Θ) :=
  fun {s} v => match s with
    | .set => match v with
      | .here => .fvar .here
      | .there .here => .fvar (.there .here)
      | .there (.there v) => Term.weakenFree (σ := ℒ) SetTheory.SetSort.set
          (Term.weakenFree (σ := ℒ) SetTheory.SetSort.set (ν v))

def form_m {Δ Θ : SortContext ℒ} (D : Formula ℒ [] (.set :: Θ)) (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))
    (ν : VariableSubstitution ℒ Δ [] Θ) : Formula ℒ [] (.set :: .set :: Θ) :=
  .conj (PowerlessSourceClass.domain_m (domain_m D) (.fvar .here))
    (PowerlessClassRelativeParameters.instance_m (domain_m D)
      (PowerlessSourceTuple.form_m n φ) (binding_m ν))

/-- 打包正文逐输出忠实；输出的类守卫不是靠相对化内部量词隐含取得的。 -/
theorem formula_l {P : carrier_l 𝒱 → Prop} {hP : ∃ x, P x} {Δ Θ : SortContext ℒ}
    (D : Formula ℒ [] (.set :: Θ)) (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))
    (ν : VariableSubstitution ℒ Δ [] Θ) (ξ : Env 𝒱 [] Θ)
    (η : Env (PowerlessSourceClass.structure_l P hP) [] Δ)
    (hν : ∀ v : Variable Δ .set, (ν v).eval ξ = (η.freeVal v).val)
    (hD : ∀ x, D.satisfies (ξ.pushFree x) ↔ P x)
    (p y : PowerlessSourceClass.type_l P) :
    (form_m D n φ ν).satisfies ((ξ.pushFree p.val).pushFree y.val) ↔
      (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y) := by
  have hξ : PowerlessSourceClass.free_l ((ξ.pushFree p.val).pushFree y.val) =
      (ξ.pushFree p.val).pushFree y.val := by
    apply Env.ext
    · intro _ v
      nomatch v
    · intro _ _
      rfl
  have h₀ (x : carrier_l 𝒱) :
      (domain_m D).satisfies
        ((PowerlessSourceClass.free_l ((ξ.pushFree p.val).pushFree y.val)).pushFree x) ↔ P x := by
    rw [hξ]
    exact (domain_formula_l D ξ p.val y.val x).trans (hD x)
  have h₁ := PowerlessClassRelativeParameters.instance_l (domain_m D)
    (PowerlessSourceTuple.form_m n φ) (binding_m ν)
    ((ξ.pushFree p.val).pushFree y.val) ((η.pushFree p).pushFree y)
    (fun v => by
      cases v with
      | here => rfl
      | there v =>
        cases v with
        | here => rfl
        | there v => simpa only [binding_m, Term.eval_weakenFree, Env.pushFree_there] using hν v) h₀
  have h₂ := (PowerlessSourceClass.domain_formula_l (domain_m D)
    ((ξ.pushFree p.val).pushFree y.val) (.fvar .here)).trans (h₀ y.val)
  change (_ ∧ _) ↔ _
  rw [h₂, h₁]
  exact ⟨fun h => h.2, fun h => ⟨y.property, h⟩⟩

/-- 原类结构中的实际元组码把二元捕获恢复为任意固定有限元数的捕获。 -/
theorem closure_l {P : carrier_l 𝒱 → Prop} {hP : ∃ x, P x} {Δ Θ : SortContext ℒ}
    (D : Formula ℒ [] (.set :: Θ)) (n : Nat)
    (φ : Formula ℒ [] (.set :: (List.replicate n .set ++ Δ)))
    (ν : VariableSubstitution ℒ Δ [] Θ) (ξ : Env 𝒱 [] Θ)
    (η : Env (PowerlessSourceClass.structure_l P hP) [] Δ)
    (hν : ∀ v : Variable Δ .set, (ν v).eval ξ = (η.freeVal v).val)
    (hD : ∀ x, D.satisfies (ξ.pushFree x) ↔ P x)
    (I : carrier_l 𝒱 → Prop) (hI : ∀ x, I x → P x)
    (e : PowerlessSourceClass.type_l P) (he : I e.val)
    (hPair : ∀ a b : PowerlessSourceClass.type_l P, ∃ p,
      ordered_l (ℳ := PowerlessSourceClass.structure_l P hP) a b p)
    (hClosed : ∀ a b p : PowerlessSourceClass.type_l P,
      I a.val → I b.val →
        ordered_l (ℳ := PowerlessSourceClass.structure_l P hP) a b p → I p.val)
    (h : ∀ p, I p → (∃ y, P y ∧
      (form_m D n φ ν).satisfies ((ξ.pushFree p).pushFree y)) →
        ∃ y, I y ∧ (form_m D n φ ν).satisfies ((ξ.pushFree p).pushFree y)) :
    ∀ v, PowerlessSourceTuplePairing.bounded_l
      (ℳ := PowerlessSourceClass.structure_l P hP) (fun x => I x.val) n v →
      (∃ y, φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y)) →
        ∃ y, I y.val ∧ φ.satisfies ((PowerlessSourceTuple.env_l η n v).pushFree y) := by
  intro v hv hφ
  have h₀ : ∀ p : PowerlessSourceClass.type_l P, I p.val →
      (∃ y, True ∧ (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y)) →
        ∃ y, I y.val ∧ (PowerlessSourceTuple.form_m n φ).satisfies ((η.pushFree p).pushFree y) := by
    rintro p hp ⟨y, _, hy⟩
    obtain ⟨z, hz, hψ⟩ := h p.val hp
      ⟨y.val, y.property, (formula_l D n φ ν ξ η hν hD p y).mpr hy⟩
    exact ⟨⟨z, hI z hz⟩, hz,
      (formula_l D n φ ν ξ η hν hD p ⟨z, hI z hz⟩).mp hψ⟩
  apply PowerlessSourceTuplePairing.predicate_closure_l
    (ℳ := PowerlessSourceClass.structure_l P hP) hPair η n φ
    (fun x => I x.val) (fun _ => True) e he hClosed h₀ v hv
  obtain ⟨y, hy⟩ := hφ
  exact ⟨y, True.intro, hy⟩

def family_m {Δ Θ : SortContext ℒ} (D : Formula ℒ [] (.set :: Θ))
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))))
    (ν : VariableSubstitution ℒ Δ [] Θ) : List (Formula ℒ [] (.set :: .set :: Θ)) :=
  Φ.map fun p => form_m D p.1 p.2 ν

theorem family_l {P : carrier_l 𝒱 → Prop} {hP : ∃ x, P x} {Δ Θ : SortContext ℒ}
    (D : Formula ℒ [] (.set :: Θ))
    (Φ : List (Σ n : Nat, Formula ℒ [] (.set :: (List.replicate n .set ++ Δ))))
    (ν : VariableSubstitution ℒ Δ [] Θ) (ξ : Env 𝒱 [] Θ)
    (η : Env (PowerlessSourceClass.structure_l P hP) [] Δ)
    (hν : ∀ v : Variable Δ .set, (ν v).eval ξ = (η.freeVal v).val)
    (hD : ∀ x, D.satisfies (ξ.pushFree x) ↔ P x)
    (I : carrier_l 𝒱 → Prop) (hI : ∀ x, I x → P x)
    (e : PowerlessSourceClass.type_l P) (he : I e.val)
    (hPair : ∀ a b : PowerlessSourceClass.type_l P, ∃ p,
      ordered_l (ℳ := PowerlessSourceClass.structure_l P hP) a b p)
    (hClosed : ∀ a b p : PowerlessSourceClass.type_l P,
      I a.val → I b.val →
        ordered_l (ℳ := PowerlessSourceClass.structure_l P hP) a b p → I p.val)
    (h : ∀ ψ ∈ family_m D Φ ν, ∀ p, I p →
      (∃ y, P y ∧ ψ.satisfies ((ξ.pushFree p).pushFree y)) →
        ∃ y, I y ∧ ψ.satisfies ((ξ.pushFree p).pushFree y)) :
    PowerlessSourcePredicateRequests.closed_l
      (ℳ := PowerlessSourceClass.structure_l P hP) Φ η (fun x => I x.val) := by
  intro n φ hφ
  exact closure_l D n φ ν ξ η hν hD I hI e he hPair hClosed
    (h _ (List.mem_map.mpr ⟨⟨n, φ⟩, hφ, rfl⟩))

#print axioms formula_l
#print axioms closure_l
#print axioms family_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessClassPackedRequests
