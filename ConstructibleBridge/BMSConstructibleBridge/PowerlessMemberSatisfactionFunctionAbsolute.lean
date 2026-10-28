import BMSConstructibleBridge.PowerlessSatisfactionFunctionGraph
import BMSConstructibleBridge.PowerlessSourceGraphAbsolute
import BMSConstructibleBridge.PowerlessMemberBounded

/-! # 同一完整 Sat 函数图在传递成员域中的规格

原规范矩阵为纯 Δ₀，但完整函数图并非仅由该分类直接运输。
全域映射及同一 G 的图值使用真实传递成员域绝对性；全部域内
输入和输出的原规范矩阵逐行使用 Δ₀ 绝对性。没有另选 Sat、
预供完整源理论，或把非传递的共同域 I 当成传递域。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberSatisfactionFunctionAbsolute

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
    (ω e t₁ t₂ t₃ P N F U G : carrier_l 𝒩) : Prop :=
  map_l (ℳ := 𝒩) G U U ∧ ∀ a r, value_l (ℳ := 𝒩) G a r ↔
    member_l 𝒩 a U ∧ member_l 𝒩 r U ∧
      PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒩)
        ω a e N P U U t₁ t₂ t₃ F r

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

/-- 完整图规格保留无界输入输出量词，不能误分类为逐行 Δ₀。 -/
def graph_m {Γ Δ : SortContext ℒ}
    (ω e t₁ t₂ t₃ P N F U G : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (SecondOrderObjectSyntax.map_m G U U) <|
    .forallE .set <| .forallE .set <|
      .iff (SecondOrderObjectSyntax.value_m (up (up G))
        (.bvar (.there .here)) (.bvar .here)) <|
        .conj (SecondOrderObjectSyntax.member_m (.bvar (.there .here)) (up (up U))) <|
          .conj (SecondOrderObjectSyntax.member_m (.bvar .here) (up (up U)))
            (PowerlessSatisfactionNormalizedMatrix.formula_m (up (up ω))
              (.bvar (.there .here)) (up (up e)) (up (up N)) (up (up P))
              (up (up U)) (up (up U)) (up (up t₁)) (up (up t₂)) (up (up t₃))
              (up (up F)) (.bvar .here))

theorem graph_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e t₁ t₂ t₃ P N F U G : Term ℒ Γ Δ .set) :
    (graph_m ω e t₁ t₂ t₃ P N F U G).satisfies η ↔
      spec_l (ω.eval η) (e.eval η) (t₁.eval η) (t₂.eval η) (t₃.eval η)
        (P.eval η) (N.eval η) (F.eval η) (U.eval η) (G.eval η) := by
  simp only [graph_m, spec_l, Formula.satisfies, map_formula_l, value_formula_l,
    SecondOrderObjectSyntax.member_m, PowerlessSatisfactionNormalizedMatrix.formula_l,
    Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

/-- 原 G、U 与全部参数保持不变，结论是成员域中的完整原图规格。 -/
theorem graph_l (hTrans : PowerlessNaturalOrder.transitive_l W)
    (ω e t₁ t₂ t₃ P N F U G : M)
    (hG : map_l (ℳ := ℳ) G.val U.val U.val)
    (hRead : ∀ a r : carrier_l ℳ, value_l (ℳ := ℳ) G.val a r ↔
      member_l ℳ a U.val ∧ member_l ℳ r U.val ∧
        PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := ℳ)
          ω.val a e.val N.val P.val U.val U.val t₁.val t₂.val t₃.val F.val r) :
    spec_l (𝒩 := 𝒩₀) ω e t₁ t₂ t₃ P N F U G := by
  refine ⟨(PowerlessSourceGraphAbsolute.map_l hTrans).mpr hG, ?_⟩
  intro a r
  let η : Env 𝒩₀ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
    Env.empty |>.pushFree r |>.pushFree F |>.pushFree t₃ |>.pushFree t₂ |>.pushFree t₁
      |>.pushFree U |>.pushFree U |>.pushFree P |>.pushFree N |>.pushFree e
      |>.pushFree a |>.pushFree ω
  have hMatrix : PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := 𝒩₀)
      ω a e N P U U t₁ t₂ t₃ F r ↔
      PowerlessSatisfactionNormalizedMatrix.holds_l (𝒩 := ℳ)
        ω.val a.val e.val N.val P.val U.val U.val t₁.val t₂.val t₃.val F.val r.val := by
    let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set, .set] :=
      PowerlessSatisfactionNormalizedMatrix.formula_m
        (.fvar .here)
        (.fvar (.there .here))
        (.fvar (.there (.there .here)))
        (.fvar (.there (.there (.there .here))))
        (.fvar (.there (.there (.there (.there .here)))))
        (.fvar (.there (.there (.there (.there (.there .here))))))
        (.fvar (.there (.there (.there (.there (.there (.there .here)))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there .here))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
        (.fvar (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
    have hφ : Formula.IsDelta0 StabilityFrame.membershipLevyBound φ :=
      PowerlessSatisfactionNormalizedMatrix.delta_l _ _ _ _ _ _ _ _ _ _ _ _
    have h := PowerlessMemberBounded.formula_l
      (fun x hx y hy => hTrans x y hx hy) hφ η
    simpa only [φ, PowerlessSatisfactionNormalizedMatrix.formula_l, Term.eval,
      Env.pushFree_here, Env.pushFree_there, PowerlessRelativization.env_l, η] using h
  exact (PowerlessSourceGraphAbsolute.value_l hTrans).trans
    ((hRead a.val r.val).trans (and_congr Iff.rfl (and_congr Iff.rfl hMatrix.symm)))

/-- 原有限赋值覆盖保持同一 U；不把有界 Seq 检查冒充完整覆盖。 -/
theorem coverage_l (hTrans : PowerlessNaturalOrder.transitive_l W) (ω U : M)
    (hCoverage : ∀ a : carrier_l ℳ, member_l ℳ a U.val → ∀ f,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := ℳ) ω.val a f → member_l ℳ f U.val) :
    ∀ a : M, member_l 𝒩₀ a U → ∀ f : M,
      PowerlessFiniteSequencesSyntax.sequence_l (ℳ := 𝒩₀) ω a f → member_l 𝒩₀ f U := by
  intro a ha f h
  obtain ⟨n, hn, hf⟩ := h
  exact hCoverage a.val ha f.val ⟨n.val, hn, (PowerlessSourceGraphAbsolute.map_l hTrans).mp hf⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessMemberSatisfactionFunctionAbsolute
