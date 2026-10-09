import BMSConstructibleBridge.PowerlessMemberDefImageBounded
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessMemberBounded

/-! # 原 Def 检查器函数图在传递成员域中的完整规格

固定同一实际 D 与旧翻译图 Q。函数图的全域性和图值由传递成员域
绝对性保留，八槽纯 Δ₀ 检查器逐行运输；结论不另选 Def 图。
这里只运输已证明的原读数，不预设非传递共同域 I 的绝对性或源模型。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefFunctionAbsolute

open Logic FirstOrder ThirdOrderSemantics

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature PowerlessMemberStructure.structure_l
  PowerlessMemberStructure.type_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} ℒ} {W : carrier_l ℳ}
  {hW : ∃ x, member_l ℳ x W}

local notation "𝒩₀" => PowerlessMemberStructure.structure_l W hW
local notation "M" => PowerlessMemberStructure.type_l (ℳ := ℳ) W

def spec_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (ω e N Q U G D : carrier_l 𝒩) : Prop :=
  map_l (ℳ := 𝒩) D U U ∧ ∀ a r, value_l (ℳ := 𝒩) D a r ↔
    member_l 𝒩 a U ∧ member_l 𝒩 r U ∧
      PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒩) ω e N Q U G a r

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def graph_m {Γ Δ : SortContext ℒ} (ω e N Q U G D : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.map_m D U U) <|
    .forallE .set <| .forallE .set <|
      .iff (SecondOrderObjectSyntax.value_m (up (up D))
        (.bvar (.there .here)) (.bvar .here)) <|
        .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up U))) <|
          .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up U)))
            (PowerlessMemberDefImageBounded.formula_m (up (up ω)) (up (up e))
              (up (up N)) (up (up Q)) (up (up U)) (up (up G))
              (.bvar (.there .here)) (.bvar .here))

theorem graph_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e N Q U G D : Term ℒ Γ Δ .set) :
    (graph_m ω e N Q U G D).satisfies η ↔
      spec_l (ω.eval η) (e.eval η) (N.eval η) (Q.eval η) (U.eval η) (G.eval η) (D.eval η) := by
  simp only [graph_m, spec_l, Formula.satisfies, map_formula_l, value_formula_l,
    SecondOrderObjectSyntax.member_m, PowerlessMemberDefImageBounded.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 全部域内原读数均保留；候选输出不预设满足原 Def。 -/
theorem graph_l (hTrans : PowerlessNaturalOrder.transitive_l W)
    (ω e N Q U G D : M)
    (hD : map_l (ℳ := ℳ) D.val U.val U.val)
    (hRead : ∀ a r : carrier_l ℳ, value_l (ℳ := ℳ) D.val a r ↔
      member_l ℳ a U.val ∧ member_l ℳ r U.val ∧
        PowerlessMemberDefImageBounded.holds_l (𝒩 := ℳ)
          ω.val e.val N.val Q.val U.val G.val a r) :
    spec_l (𝒩 := 𝒩₀) ω e N Q U G D := by
  refine ⟨(PowerlessSourceGraphAbsolute.map_l hTrans).mpr hD, ?_⟩
  intro a r
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree r |>.pushFree a |>.pushFree G |>.pushFree U
      |>.pushFree Q |>.pushFree N |>.pushFree e |>.pushFree ω
  have hMatrix : PowerlessMemberDefImageBounded.holds_l (𝒩 := 𝒩₀) ω e N Q U G a r ↔
      PowerlessMemberDefImageBounded.holds_l (𝒩 := ℳ)
        ω.val e.val N.val Q.val U.val G.val a.val r.val := by
    let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set] :=
      PowerlessMemberDefImageBounded.formula_m
        (.fvar .here)
        (.fvar (.there .here))
        (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
    have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
      PowerlessMemberDefImageBounded.delta_l _ _ _ _ _ _ _ _
    have h := PowerlessMemberBounded.formula_l
      (fun x hx y hy => hTrans x y hx hy) hφ η
    simpa only [φ, PowerlessMemberDefImageBounded.formula_l, Term.eval,
      Env.pushFree_here, Env.pushFree_there, PowerlessRelativization.env_l, η] using h
  exact (PowerlessSourceGraphAbsolute.value_l hTrans).trans
    ((hRead a.val r.val).trans (and_congr Iff.rfl (and_congr Iff.rfl hMatrix.symm)))

#print axioms graph_l
#print axioms graph_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberDefFunctionAbsolute
