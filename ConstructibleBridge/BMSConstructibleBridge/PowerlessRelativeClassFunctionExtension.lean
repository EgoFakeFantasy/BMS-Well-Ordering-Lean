import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 相对类中的常值图与单点函数延拓

值域保持为给定类对象；有界求值公式给出实际类内关系图。
只用已核验的 Δ₀ 图存在和坐标唯一性，不调用完整源理论的 Mapping／Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionExtension

open Logic FirstOrder ThirdOrderSemantics StabilityFrame
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem constant_l (A D d : type_l hℳ B) (hd : mem_l hℳ d.val D.val) :
    ∃ f : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) f A D ∧
      ∀ x y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) f x y ↔
        mem_l hℳ x.val A.val ∧ y = d := by
  let φ : Formula ℒ [] [.set, .set, .set] := .equal (.fvar (.there .here)) (.fvar (.there (.there .here)))
  let η := (Env.empty (M := structure_l hℳ B hBase)).pushFree (sort := SetTheory.SetSort.set) d
  obtain ⟨f, hf, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l
    (show Formula.IsDelta0 membershipLevyBound φ from .equal _ _) η A D
    (fun x _ => ⟨d, ⟨hd, rfl⟩, fun y hy => hy.2⟩)
  refine ⟨f, hf, fun x y => (hValue x y).trans ?_⟩
  change (mem_l hℳ x.val A.val ∧ mem_l hℳ y.val D.val ∧ y = d) ↔ _
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.2.symm ▸ hd, h.2⟩⟩

def extension_m : Formula ℒ [] [.set, .set, .set, .set, .set] :=
  .disj (PowerlessValueBounded.formula_m (.fvar (.there (.there .here))) (.fvar .here) (.fvar (.there .here)))
    (.conj (.equal (.fvar .here) (.fvar (.there (.there (.there .here)))))
      (.equal (.fvar (.there .here)) (.fvar (.there (.there (.there (.there .here)))))))

theorem extension_delta_l : Formula.IsDelta0 membershipLevyBound extension_m :=
  .disj (PowerlessValueBounded.delta_l _ _ _) (.conj (.equal _ _) (.equal _ _))

theorem exists_l {f A D S c d : type_l hℳ B}
    (hf : map_l (ℳ := structure_l hℳ B hBase) f A D) (hc : ¬mem_l hℳ c.val A.val)
    (hd : mem_l hℳ d.val D.val)
    (hS : ∀ x : type_l hℳ B, mem_l hℳ x.val S.val ↔ mem_l hℳ x.val A.val ∨ x = c) :
    ∃ g : type_l hℳ B, map_l (ℳ := structure_l hℳ B hBase) g S D ∧
      ∀ x y : type_l hℳ B, value_l (ℳ := structure_l hℳ B hBase) g x y ↔
        value_l (ℳ := structure_l hℳ B hBase) f x y ∨ x = c ∧ y = d := by
  let η := (Env.empty (M := structure_l hℳ B hBase)).pushFree (sort := SetTheory.SetSort.set) d
    |>.pushFree (sort := SetTheory.SetSort.set) c |>.pushFree (sort := SetTheory.SetSort.set) f
  have hRead (x y : type_l hℳ B) : extension_m.satisfies ((η.pushFree y).pushFree x) ↔
      value_l (ℳ := structure_l hℳ B hBase) f x y ∨ x = c ∧ y = d := by
    simp only [extension_m, Formula.satisfies, PowerlessValueBounded.formula_l, Term.eval]
    rfl
  have hfGlobal := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f A D).mp hf
  have hMem (x y : type_l hℳ B) (hxy : value_l (ℳ := structure_l hℳ B hBase) f x y) :
      mem_l hℳ x.val A.val ∧ mem_l hℳ y.val D.val :=
    SecondOrderFunctionProperties.value_mem_l hℳ hfGlobal
      ((PowerlessRelativeClassFunctionAbsolute.value_l f x y).mp hxy)
  have hUnique (x y z : type_l hℳ B)
      (hy : extension_m.satisfies ((η.pushFree y).pushFree x))
      (hz : extension_m.satisfies ((η.pushFree z).pushFree x)) : y = z := by
    rcases (hRead x y).mp hy with hy | ⟨hx, hy⟩
    · rcases (hRead x z).mp hz with hz | ⟨hx, _⟩
      · exact Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ hfGlobal
          ((PowerlessRelativeClassFunctionAbsolute.value_l f x y).mp hy)
          ((PowerlessRelativeClassFunctionAbsolute.value_l f x z).mp hz))
      · exact (hc (hx ▸ (hMem x y hy).1)).elim
    · rcases (hRead x z).mp hz with hz | ⟨_, hz⟩
      · exact (hc (hx ▸ (hMem x z hz).1)).elim
      · exact hy.trans hz.symm
  have hTotal (x : type_l hℳ B) (hx : mem_l hℳ x.val S.val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val D.val ∧ extension_m.satisfies ((η.pushFree y).pushFree x) := by
    have hWitness : ∃ y : type_l hℳ B, mem_l hℳ y.val D.val ∧ extension_m.satisfies ((η.pushFree y).pushFree x) := by
      rcases (hS x).mp hx with hx | hx
      · obtain ⟨y, hy, _⟩ := hf.2 x hx
        exact ⟨y, hy.1, (hRead x y).mpr (Or.inl hy.2)⟩
      · exact ⟨d, hd, (hRead x d).mpr (Or.inr ⟨hx, rfl⟩)⟩
    obtain ⟨y, hy⟩ := hWitness
    exact ⟨y, hy, fun z hz => hUnique x z y hz.2 hy.2⟩
  obtain ⟨g, hg, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l extension_delta_l η S D hTotal
  refine ⟨g, hg, fun x y => (hValue x y).trans ?_⟩
  constructor
  · exact fun h => (hRead x y).mp h.2.2
  · intro h
    have hx : mem_l hℳ x.val S.val := (hS x).mpr (h.elim
      (fun h => Or.inl (hMem x y h).1) (fun h => Or.inr h.1))
    have hy : mem_l hℳ y.val D.val := h.elim
      (fun h => (hMem x y h).2) (fun h => h.2.symm ▸ hd)
    exact ⟨hx, hy, (hRead x y).mpr h⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessRelativeClassFunctionExtension
