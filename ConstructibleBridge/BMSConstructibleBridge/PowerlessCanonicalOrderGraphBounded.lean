import BMSConstructibleBridge.PowerlessRelationBounded
import BMSConstructibleBridge.PowerlessRelativeClassRowOrderCanonical
import BMSConstructibleBridge.SecondOrderWellOrderEndExtensionUnique

/-! # 规范行序及末端扩张图的有界检查

良序性不放入 Δ₀ 检查器：它仍由真实前阶段的良序和规范构造恢复。
这里同时保留干净成员条件与母域上的双向读数，在原商中精确恢复原
行序 graph_l 与末端扩张 graph_l。候选图不预先要求 Class 或良序。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderGraphBounded

open Logic FirstOrder ThirdOrderSemantics StabilityFrame

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) :=
  t.weakenBound SetTheory.SetSort.set
private abbrev up₂ {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := up (up t)

def row_m {Γ Δ : SortContext ℒ} (I U A Q Y L : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelationBounded.clean_m L Y Y) <|
    membershipLevyBound.boundedForall Y <|
      membershipLevyBound.boundedForall (up Y) <|
        .iff (PowerlessValueBounded.formula_m (up₂ L) (.bvar (.there .here)) (.bvar .here))
          (PowerlessRelativeClassRowOrderCanonical.comparison_m (up₂ I) (up₂ U)
            (up₂ A) (up₂ Q) (.bvar (.there .here)) (.bvar .here))

theorem row_delta_l {Γ Δ : SortContext ℒ} (I U A Q Y L : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (row_m I U A Q Y L) :=
  .conj (PowerlessRelationBounded.clean_delta_l _ _ _)
    (.bounded_forall _ (.bounded_forall _ (.iff (PowerlessValueBounded.delta_l _ _ _)
      (PowerlessRelativeClassRowOrderCanonical.comparison_delta_l _ _ _ _ _ _))))

def row_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (I U A Q Y L : carrier_l 𝒩) : Prop :=
  PowerlessRelationBounded.clean_l (𝒩 := 𝒩) L Y Y ∧
    ∀ x, member_l 𝒩 x Y → ∀ y, member_l 𝒩 y Y →
      (value_l (ℳ := 𝒩) L x y ↔
        PowerlessRelativeClassRowOrderCanonical.comparison_l (ℳ₀ := 𝒩) I U A Q x y)

theorem row_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (I U A Q Y L : Term ℒ Γ Δ .set) :
    (row_m I U A Q Y L).satisfies η ↔
      row_holds_l (I.eval η) (U.eval η) (A.eval η) (Q.eval η) (Y.eval η) (L.eval η) := by
  simp only [row_m, row_holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessRelationBounded.clean_formula_l, PowerlessValueBounded.formula_l,
    PowerlessRelativeClassRowOrderCanonical.comparison_formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

def extension_m {Γ Δ : SortContext ℒ} (A P L D E : Term ℒ Γ Δ .set) : Formula ℒ Γ Δ :=
  .conj (PowerlessRelationBounded.clean_m E D D) <|
    membershipLevyBound.boundedForall D <|
      membershipLevyBound.boundedForall (up D) <|
        .iff (PowerlessValueBounded.formula_m (up₂ E) (.bvar (.there .here)) (.bvar .here))
          (SecondOrderWellOrderEndExtension.body_m (up₂ A) (up₂ P) (up₂ L)
            (.bvar (.there .here)) (.bvar .here))

theorem extension_delta_l {Γ Δ : SortContext ℒ} (A P L D E : Term ℒ Γ Δ .set) :
    Formula.IsDelta0 membershipLevyBound (extension_m A P L D E) :=
  .conj (PowerlessRelationBounded.clean_delta_l _ _ _)
    (.bounded_forall _ (.bounded_forall _ (.iff (PowerlessValueBounded.delta_l _ _ _)
      (SecondOrderWellOrderEndExtension.body_delta_l _ _ _ _ _))))

def extension_holds_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    (A P L D E : carrier_l 𝒩) : Prop :=
  PowerlessRelationBounded.clean_l (𝒩 := 𝒩) E D D ∧
    ∀ x, member_l 𝒩 x D → ∀ y, member_l 𝒩 y D →
      (value_l (ℳ := 𝒩) E x y ↔ SecondOrderWellOrderEndExtension.body_l (ℳ₀ := 𝒩) A P L x y)

theorem extension_formula_l {𝒩 : FirstOrder.Structure.{0, 0, 0, u} ℒ}
    {Γ Δ : SortContext ℒ} (η : Env 𝒩 Γ Δ) (A P L D E : Term ℒ Γ Δ .set) :
    (extension_m A P L D E).satisfies η ↔
      extension_holds_l (A.eval η) (P.eval η) (L.eval η) (D.eval η) (E.eval η) := by
  simp only [extension_m, extension_holds_l, Formula.LevyBound.boundedForall,
    Formula.LevyBound.membership, membershipLevyBound, Formula.satisfies,
    PowerlessRelationBounded.clean_formula_l, PowerlessValueBounded.formula_l,
    SecondOrderWellOrderEndExtension.body_formula_l,
    Arguments.eval, up₂, up, Term.eval_weakenBound, Term.eval]
  rfl

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m}

local notation "𝒱" => SecondOrderQuotient.structure_l hℳ

/-- 所有 raw 行对象与图成员均保留；不以母域外值未知的规格代替原图。 -/
theorem row_graph_iff_l (I U A Q Y L : SecondOrderQuotient.type_l hℳ) :
    row_holds_l (𝒩 := 𝒱) I U A Q Y L ↔
      PowerlessRelativeClassRowOrderCanonical.graph_l (ℳ₀ := 𝒱) I U A Q Y L := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
    PowerlessRelativeClassRowOrderCanonical.comparison_m
      (.fvar (.there (.there .here))) (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here)))))
      (.fvar (.there (.there (.there (.there (.there .here))))))
      (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set, .set] :=
    (((Env.empty.pushFree Q).pushFree A).pushFree U).pushFree I
  have hφ x y : φ.satisfies ((η.pushFree y).pushFree x) ↔
      PowerlessRelativeClassRowOrderCanonical.comparison_l (ℳ₀ := 𝒱) I U A Q x y :=
    PowerlessRelativeClassRowOrderCanonical.comparison_formula_l _ _ _ _ _ _ _
  have hLocal : row_holds_l (𝒩 := 𝒱) I U A Q Y L ↔
      PowerlessRelationBounded.holds_l φ η Y Y L :=
    and_congr Iff.rfl (forall_congr' fun x => imp_congr_right fun _ =>
      forall_congr' fun y => imp_congr_right fun _ => iff_congr Iff.rfl (hφ x y).symm)
  apply hLocal.trans
  apply (PowerlessRelationBounded.spec_iff_l φ η Y Y L).trans
  exact forall_congr' fun p => iff_congr Iff.rfl (exists_congr fun x => exists_congr fun y =>
    and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (hφ x y))))

/-- 原末端扩张正文的顺序保持，不改变其既有 graph_l 或良序恢复接口。 -/
theorem extension_graph_iff_l (A P L D E : SecondOrderQuotient.type_l hℳ) :
    extension_holds_l (𝒩 := 𝒱) A P L D E ↔
      SecondOrderWellOrderEndExtensionUnique.graph_l (ℳ₀ := 𝒱) A D P L E := by
  let φ : Formula ℒ [] [.set, .set, .set, .set, .set] :=
    SecondOrderWellOrderEndExtension.body_m (.fvar (.there (.there .here)))
      (.fvar (.there (.there (.there .here))))
      (.fvar (.there (.there (.there (.there .here))))) (.fvar .here) (.fvar (.there .here))
  let η : Env 𝒱 [] [.set, .set, .set] := ((Env.empty.pushFree L).pushFree P).pushFree A
  have hφ x y : φ.satisfies ((η.pushFree y).pushFree x) ↔
      SecondOrderWellOrderEndExtension.body_l (ℳ₀ := 𝒱) A P L x y :=
    SecondOrderWellOrderEndExtension.body_formula_l _ _ _ _ _ _
  have hLocal : extension_holds_l (𝒩 := 𝒱) A P L D E ↔
      PowerlessRelationBounded.holds_l φ η D D E :=
    and_congr Iff.rfl (forall_congr' fun x => imp_congr_right fun _ =>
      forall_congr' fun y => imp_congr_right fun _ => iff_congr Iff.rfl (hφ x y).symm)
  apply hLocal.trans
  apply (PowerlessRelationBounded.spec_iff_l φ η D D E).trans
  exact forall_congr' fun p => iff_congr Iff.rfl (exists_congr fun x => exists_congr fun y =>
    and_congr Iff.rfl (and_congr Iff.rfl ((and_congr Iff.rfl (hφ x y)).trans and_comm)))

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessCanonicalOrderGraphBounded
