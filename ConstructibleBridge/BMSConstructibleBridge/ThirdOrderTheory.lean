import BMSConstructibleBridge.PowerlessTheory
import BMSConstructibleBridge.SecondOrderOmegaSyntax

/-!
# 三阶算术的集合论背景

采用完整分离、完整收集、集合良序选择、P(ω) 存在及每个集合可单射到
P(ω) 的呈现。全部附加公理都是纯 ℒ 闭句，没有加入 BM4 或反射公理。
这是明确的新背景定义，不是其内部 BM4 良序性或与类型化 Z₃ 等价的证明。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderTheory

open Logic FirstOrder SecondOrderObjectSyntax

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature

universe u

def subset_m {Γ Δ : SortContext ℒ} (a b : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.imp (member_m (.bvar .here) (a.weakenBound SetTheory.SetSort.set))
    (member_m (.bvar .here) (b.weakenBound SetTheory.SetSort.set)))

def power_m {Γ Δ : SortContext ℒ} (a p : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .forallE .set (.iff (member_m (.bvar .here) (p.weakenBound SetTheory.SetSort.set))
    (subset_m (.bvar .here) (a.weakenBound SetTheory.SetSort.set)))

/-- 最小归纳对象的幂集，而非任意对象的幂集。 -/
def reals_m : Sentence ℒ :=
  .existsE .set <| .existsE .set <|
    .conj (SecondOrderOmegaSyntax.omega_m (.bvar (.there .here)))
      (power_m (.bvar (.there .here)) (.bvar .here))

/-- 每个集合有一个实际集合函数单射到 P(ω)，不假定 CH。 -/
def bound_m : Sentence ℒ :=
  .forallE .set <| .existsE .set <| .existsE .set <| .existsE .set <|
    .conj (SecondOrderOmegaSyntax.omega_m (.bvar (.there (.there .here))))
      (.conj (power_m (.bvar (.there (.there .here))) (.bvar (.there .here)))
        (.conj (map_m (.bvar .here) (.bvar (.there (.there (.there .here)))) (.bvar (.there .here)))
          (injective_m (.bvar .here))))

/-- 关系在 A 上严格线性，且模型内部每个非空子集均有极小元。 -/
def wellOrder_template_m : Formula ℒ [] [.set, .set] :=
  .conj
    (.forallE .set (.imp (member_m (.bvar .here) (.fvar .here))
      (.neg (value_m (.fvar (.there .here)) (.bvar .here) (.bvar .here)))))
    (.conj
      (.forallE .set <| .forallE .set <| .forallE .set <|
        .imp (.conj (member_m (.bvar (.there (.there .here))) (.fvar .here))
          (.conj (member_m (.bvar (.there .here)) (.fvar .here)) (member_m (.bvar .here) (.fvar .here))))
          (.imp (value_m (.fvar (.there .here)) (.bvar (.there (.there .here))) (.bvar (.there .here)))
            (.imp (value_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
              (value_m (.fvar (.there .here)) (.bvar (.there (.there .here))) (.bvar .here)))))
      (.conj
        (.forallE .set <| .forallE .set <|
          .imp (.conj (member_m (.bvar (.there .here)) (.fvar .here)) (member_m (.bvar .here) (.fvar .here)))
            (.disj (value_m (.fvar (.there .here)) (.bvar (.there .here)) (.bvar .here))
              (.disj (.equal (.bvar (.there .here)) (.bvar .here))
                (value_m (.fvar (.there .here)) (.bvar .here) (.bvar (.there .here))))))
        (.forallE .set <|
          .imp (.conj (subset_m (.bvar .here) (.fvar .here))
            (.existsE .set (member_m (.bvar .here) (.bvar (.there .here)))))
            (.existsE .set <| .conj (member_m (.bvar .here) (.bvar (.there .here)))
              (.forallE .set <| .imp (member_m (.bvar .here) (.bvar (.there (.there .here))))
                (.neg (value_m (.fvar (.there .here)) (.bvar .here) (.bvar (.there .here)))))))))

def choice_m : Sentence ℒ :=
  let σ : Substitution ℒ [] [.set, .set] [.set] [.set] :=
    .map (fun v => nomatch v) (fun {s} v => match s, v with
      | .set, .here => .fvar .here
      | .set, .there .here => .bvar .here)
  Metatheory.Formula.forall_close (.existsE .set (wellOrder_template_m.substitute σ))

inductive axiom_m : Sentence ℒ → Prop where
  | base {φ : Sentence ℒ} (h : PowerlessTheory.theory_m φ) : axiom_m φ
  | reals : axiom_m reals_m
  | bound : axiom_m bound_m
  | choice : axiom_m choice_m

def theory_m : FirstOrder.Theory ℒ := axiom_m

theorem core_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : FirstOrder.Theory.Models ℳ theory_m) : FirstOrder.Theory.Models ℳ PowerlessTheory.theory_m :=
  fun _ h => hℳ _ (.base h)

theorem reals_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : FirstOrder.Theory.Models ℳ theory_m) : reals_m.TrueIn ℳ := hℳ _ .reals

theorem bound_l {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (hℳ : FirstOrder.Theory.Models ℳ theory_m) : bound_m.TrueIn ℳ := hℳ _ .bound

end YesMetaZFC.BMS.ConstructibleBridge.ThirdOrderTheory
