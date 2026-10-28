import BMSConstructibleBridge.PowerlessHereditaryStructure

/-! # 遗传类的逐公式相对化与原 Z₂ 推导

实际载体是已核验遗传类。量词 guard 使用其纯对象定义，每个公式的真值
双向对应；外延、正则、无穷、传递超集均回传原推导核。
配对、并集、完整分离和 Collection 仍须另证，不能由相对化本身获得。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRelativization

open Logic FirstOrder PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessHereditaryStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

def formula_m {Γ Δ : SortContext ℒ} : Formula ℒ Γ Δ → Formula ℒ Γ (.set :: Δ)
  | .falsum => .falsum
  | .truth => .truth
  | .rel r a => .rel r (a.weakenFree SetTheory.SetSort.set)
  | .equal s t => .equal (s.weakenFree SetTheory.SetSort.set) (t.weakenFree SetTheory.SetSort.set)
  | .neg φ => .neg (formula_m φ)
  | .conj φ ψ => .conj (formula_m φ) (formula_m ψ)
  | .disj φ ψ => .disj (formula_m φ) (formula_m ψ)
  | .imp φ ψ => .imp (formula_m φ) (formula_m ψ)
  | .iff φ ψ => .iff (formula_m φ) (formula_m ψ)
  | .forallE .set φ => .forallE .set (.imp
      (PowerlessHereditaryClass.formula_m (.fvar .here) (.bvar .here)) (formula_m φ))
  | .existsE .set φ => .existsE .set (.conj
      (PowerlessHereditaryClass.formula_m (.fvar .here) (.bvar .here)) (formula_m φ))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B} {Γ Δ : SortContext ℒ}

def env_l (η : Env (structure_l hℳ B hBase) Γ Δ) : Env (SecondOrderQuotient.structure_l hℳ) Γ Δ where
  boundVal {s} v := match s with | .set => (η.boundVal v).val
  freeVal {s} v := match s with | .set => (η.freeVal v).val

theorem term_l (η : Env (structure_l hℳ B hBase) Γ Δ) (t : Term ℒ Γ Δ .set) :
    (t.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree B) = (t.eval η).val := by
  match t with
  | .bvar _ => rfl
  | .fvar _ => rfl
  | .app f _ => nomatch f

theorem push_l (η : Env (structure_l hℳ B hBase) Γ Δ) (x : type_l hℳ B) :
    (env_l (η.pushBound (sort := SetTheory.SetSort.set) x)).pushFree (sort := SetTheory.SetSort.set) B =
      ((env_l η).pushFree (sort := SetTheory.SetSort.set) B).pushBound (sort := SetTheory.SetSort.set) x.val := by
  apply Env.ext
  · intro s v
    cases s
    cases v <;> rfl
  · intro s v
    cases s
    cases v <;> rfl

theorem formula_l (K : source_coding_l hℳ) {Γ Δ : SortContext ℒ}
    (φ : Formula ℒ Γ Δ) (η : Env (structure_l hℳ B hBase) Γ Δ) :
    (formula_m φ).satisfies ((env_l η).pushFree B) ↔ φ.satisfies η := by
  match φ with
  | .falsum => rfl
  | .truth => rfl
  | .rel .membership (.cons s (.cons t .nil)) =>
      change mem_l hℳ ((s.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree B))
        ((t.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree B)) ↔ mem_l hℳ (s.eval η).val (t.eval η).val
      rw [term_l, term_l]
  | .equal (sort := SetTheory.SetSort.set) s t =>
      change (s.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree B) =
        (t.weakenFree SetTheory.SetSort.set).eval ((env_l η).pushFree B) ↔ s.eval η = t.eval η
      rw [term_l, term_l]
      exact ⟨Subtype.ext, congrArg Subtype.val⟩
  | .neg φ => exact not_congr (formula_l K φ η)
  | .conj φ ψ => exact and_congr (formula_l K φ η) (formula_l K ψ η)
  | .disj φ ψ => exact or_congr (formula_l K φ η) (formula_l K ψ η)
  | .imp φ ψ => exact imp_congr (formula_l K φ η) (formula_l K ψ η)
  | .iff φ ψ => exact iff_congr (formula_l K φ η) (formula_l K ψ η)
  | .forallE .set φ =>
      change (∀ x : SecondOrderQuotient.type_l hℳ,
        (PowerlessHereditaryClass.formula_m (.fvar .here) (.bvar .here)).satisfies
          (((env_l η).pushFree B).pushBound x) →
        (formula_m φ).satisfies (((env_l η).pushFree B).pushBound x)) ↔
        ∀ x : type_l hℳ B, φ.satisfies (η.pushBound x)
      have h (x : type_l hℳ B) := formula_l K φ (η.pushBound x)
      simp only [push_l] at h
      have hGuard x := PowerlessHereditaryClass.formula_l K
        (((env_l η).pushFree B).pushBound x) (.fvar .here) (.bvar .here)
      exact ⟨fun hφ x => (h x).mp (hφ x.val ((hGuard x.val).mpr x.property)),
        fun hφ x hx => (h ⟨x, (hGuard x).mp hx⟩).mpr (hφ ⟨x, (hGuard x).mp hx⟩)⟩
  | .existsE .set φ =>
      change (∃ x : SecondOrderQuotient.type_l hℳ,
        (PowerlessHereditaryClass.formula_m (.fvar .here) (.bvar .here)).satisfies
          (((env_l η).pushFree B).pushBound x) ∧
        (formula_m φ).satisfies (((env_l η).pushFree B).pushBound x)) ↔
        ∃ x : type_l hℳ B, φ.satisfies (η.pushBound x)
      have h (x : type_l hℳ B) := formula_l K φ (η.pushBound x)
      simp only [push_l] at h
      have hGuard x := PowerlessHereditaryClass.formula_l K
        (((env_l η).pushFree B).pushBound x) (.fvar .here) (.bvar .here)
      constructor
      · rintro ⟨x, hx, hφ⟩
        exact ⟨⟨x, (hGuard x).mp hx⟩, (h ⟨x, (hGuard x).mp hx⟩).mp hφ⟩
      · rintro ⟨x, hφ⟩
        exact ⟨x.val, (hGuard x.val).mpr x.property, (h x).mpr hφ⟩

theorem sentence_l (K : source_coding_l hℳ) (φ : Sentence ℒ) :
    (formula_m φ).satisfies ((Env.empty (M := SecondOrderQuotient.structure_l hℳ)).pushFree B) ↔
      φ.TrueIn (structure_l hℳ B hBase) := by
  have h := formula_l K φ (Env.empty (M := structure_l hℳ B hBase))
  have hη : env_l (Env.empty (M := structure_l hℳ B hBase)) = Env.empty := by
    apply Env.ext <;> intro _ v <;> nomatch v
  simpa only [hη, Formula.TrueIn] using h

def guarded_m (φ : Sentence ℒ) : Sentence ℒ := Metatheory.Formula.forall_close
  (.imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar .here)) (formula_m φ))

theorem derives_m (φ : Sentence ℒ)
    (h : ∀ (𝒩 : FirstOrder.Structure.{0, 0, 0, 0} SecondOrderSyntax.signature_m)
      (h𝒩 : Theory.Models 𝒩 SecondOrderArithmetic.theory_m) (B : SecondOrderQuotient.type_l h𝒩)
      (hBase : ∀ x, mem_l h𝒩 x B → ∀ y, mem_l h𝒩 y x → mem_l h𝒩 y B),
        φ.TrueIn (structure_l h𝒩 B hBase)) :
    Derives SecondOrderArithmetic.theory_m [] (GraphTranslation.form_m (guarded_m φ)) := by
  apply SecondOrderAxioms.interpretation_m
  intro 𝒩 h𝒩
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l h𝒩
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hTrans
  have hBase := (PowerlessRelativeHierarchyDerives.transitive_formula_l h𝒩 η (.fvar .here)).mp hTrans
  have hη : η = (Env.empty (M := SecondOrderQuotient.structure_l h𝒩)).pushFree (η.freeVal .here) := by
    apply Env.ext
    · intro _ v; nomatch v
    · intro _ v
      cases v with
      | here => rfl
      | there v => nomatch v
  rw [hη]
  exact (sentence_l (hBase := hBase) K φ).mpr (h 𝒩 h𝒩 (η.freeVal .here) hBase)

theorem extensionality_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (guarded_m SecondOrderAxioms.extensionality_m)) :=
  derives_m _ (fun _ h𝒩 B hBase => PowerlessHereditaryStructure.extensionality_l h𝒩 B hBase)

theorem foundation_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (guarded_m SecondOrderFoundation.formula_m)) :=
  derives_m _ (fun _ h𝒩 B hBase => PowerlessHereditaryStructure.foundation_l h𝒩 B hBase)

theorem infinity_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (guarded_m SecondOrderInfinityAxiom.formula_m)) :=
  derives_m _ (fun _ h𝒩 B hBase => PowerlessHereditaryStructure.infinity_l h𝒩 B hBase)

theorem transitive_superset_derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (guarded_m SecondOrderTransitiveSuperset.formula_m)) :=
  derives_m _ (fun _ h𝒩 B hBase => PowerlessHereditaryStructure.transitive_superset_l h𝒩 B hBase)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryRelativization
