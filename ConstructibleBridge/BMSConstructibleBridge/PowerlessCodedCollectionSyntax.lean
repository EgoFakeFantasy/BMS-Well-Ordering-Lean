import BMSConstructibleBridge.PowerlessRootedRealSyntax
import BMSConstructibleBridge.PowerlessSuccessorBounded

/-! # 带标签收集图的纯有界检查器

实际索引集合筛选各行，数配对将它们移入互不相交副本；随后继
移位并加新根。全部量词界于原内部 ω，不量化类外行族或选择函数。
这是集合 C 的码图检查器，不是 C 的 Class／遗传资格定理。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedCollectionSyntax

open Logic FirstOrder StabilityFrame ThirdOrderSemantics
open SecondOrderObjectSyntax (member_m)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set

def roots_m {Γ Δ : SortContext ℒ} (ω e S I c : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj (member_m (.bvar .here) (up I))
    (PowerlessBoundedNumericPairing.formula_m (up ω) (up e) (up S) (.bvar .here) (up e) (up c))

def tagged_m {Γ Δ : SortContext ℒ} (ω e S U I c d : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| membershipLevyBound.boundedExists (up ω) <|
    membershipLevyBound.boundedExists (up (up ω)) <|
      membershipLevyBound.boundedExists (up (up (up ω))) <|
        let w (t : Term ℒ Γ Δ .set) := up (up (up (up t)))
        let i := Term.bvar (.there (.there (.there .here)))
        let a := Term.bvar (.there (.there .here))
        let b := Term.bvar (.there .here)
        let t := Term.bvar .here
        .conj (member_m i (w I)) <| .conj
          (PowerlessBoundedNumericPairing.formula_m (w ω) (w e) (w S) i a (w c)) <| .conj
          (PowerlessBoundedNumericPairing.formula_m (w ω) (w e) (w S) i b (w d)) <| .conj
          (PowerlessBoundedNumericPairing.formula_m (w ω) (w e) (w S) a b t)
          (PowerlessRootedRealSyntax.row_m (w ω) (w e) (w S) (w U) i t)

def graft_m {Γ Δ : SortContext ℒ} (ω e S G P c d : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  membershipLevyBound.boundedExists ω <| .conj
    (PowerlessSuccessorBounded.formula_m (.bvar .here) (up c)) <| .disj
    (.conj (.equal (up d) (up e)) (member_m (.bvar .here) (up P)))
    (membershipLevyBound.boundedExists (up ω) <| .conj
      (PowerlessSuccessorBounded.formula_m (.bvar .here) (up (up d)))
      (PowerlessRootedRealSyntax.row_m (up (up ω)) (up (up e)) (up (up S)) (up (up G))
        (.bvar (.there .here)) (.bvar .here)))

theorem roots_delta_m {Γ Δ : SortContext ℒ} (ω e S I c : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (roots_m ω e S I c) :=
  .bounded_exists _ (.conj (.rel _ _) (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _))

theorem tagged_delta_m {Γ Δ : SortContext ℒ} (ω e S U I c d : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (tagged_m ω e S U I c d) :=
  .bounded_exists _ (.bounded_exists _ (.bounded_exists _ (.bounded_exists _ (.conj (.rel _ _)
    (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
      (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
        (.conj (PowerlessBoundedNumericPairing.delta_l _ _ _ _ _ _)
          (PowerlessRootedRealSyntax.row_delta_m _ _ _ _ _ _))))))))

theorem graft_delta_m {Γ Δ : SortContext ℒ} (ω e S G P c d : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (graft_m ω e S G P c d) :=
  .bounded_exists _ (.conj (PowerlessSuccessorBounded.delta_l _ _)
    (.disj (.conj (.equal _ _) (.rel _ _))
      (.bounded_exists _ (.conj (PowerlessSuccessorBounded.delta_l _ _)
        (PowerlessRootedRealSyntax.row_delta_m _ _ _ _ _ _)))))

def roots_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S I c : carrier_l 𝒩) : Prop :=
  ∃ i, member_l 𝒩 i ω ∧ member_l 𝒩 i I ∧
    PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S i e c

def tagged_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S U I c d : carrier_l 𝒩) : Prop :=
  ∃ i, member_l 𝒩 i ω ∧ ∃ a, member_l 𝒩 a ω ∧ ∃ b, member_l 𝒩 b ω ∧
    ∃ t, member_l 𝒩 t ω ∧ member_l 𝒩 i I ∧
      PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S i a c ∧
      PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S i b d ∧
      PowerlessBoundedNumericPairing.holds_l (𝒩 := 𝒩) ω e S a b t ∧
      PowerlessRootedRealSyntax.row_l (𝒩 := 𝒩) ω e S U i t

def graft_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} (ω e S G P c d : carrier_l 𝒩) : Prop :=
  ∃ a, member_l 𝒩 a ω ∧ PowerlessNatural.successor_l (ℳ := 𝒩) a c ∧
    ((d = e ∧ member_l 𝒩 a P) ∨ ∃ b, member_l 𝒩 b ω ∧
      PowerlessNatural.successor_l (ℳ := 𝒩) b d ∧ PowerlessRootedRealSyntax.row_l (𝒩 := 𝒩) ω e S G a b)

theorem roots_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S I c : Term ℒ Γ Δ .set) :
    (roots_m ω e S I c).satisfies η ↔ roots_l
      (ω.eval η) (e.eval η) (S.eval η) (I.eval η) (c.eval η) := by
  simp only [roots_m, roots_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem tagged_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S U I c d : Term ℒ Γ Δ .set) :
    (tagged_m ω e S U I c d).satisfies η ↔ tagged_l
      (ω.eval η) (e.eval η) (S.eval η) (U.eval η) (I.eval η) (c.eval η) (d.eval η) := by
  simp only [tagged_m, tagged_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessBoundedNumericPairing.formula_l,
    PowerlessRootedRealSyntax.row_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

theorem graft_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ} {Γ Δ : SortContext ℒ}
    (η : Env 𝒩 Γ Δ) (ω e S G P c d : Term ℒ Γ Δ .set) :
    (graft_m ω e S G P c d).satisfies η ↔ graft_l
      (ω.eval η) (e.eval η) (S.eval η) (G.eval η) (P.eval η) (c.eval η) (d.eval η) := by
  simp only [graft_m, graft_l, Formula.LevyBound.boundedExists, Formula.LevyBound.membership,
    membershipLevyBound, Formula.satisfies, PowerlessSuccessorBounded.formula_l,
    PowerlessRootedRealSyntax.row_formula_l, member_m, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
  rfl

#print axioms tagged_delta_m
#print axioms graft_delta_m
#print axioms tagged_formula_l
#print axioms graft_formula_l

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCodedCollectionSyntax
