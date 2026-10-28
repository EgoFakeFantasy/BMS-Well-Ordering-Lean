import BMSConstructibleBridge.PowerlessHereditaryClassInternals
import BMSConstructibleBridge.PowerlessRelativeClassFunctionRelation
import BMSConstructibleBridge.PowerlessRelativeClassBasicAxioms
import BMSConstructibleBridge.PowerlessSuccessorBounded
import BMSConstructibleBridge.PowerlessValueBounded
import BMSConstructibleBridge.SecondOrderNaturalCases
import BMSConstructibleBridge.SecondOrderFunctionProperties

/-! # 类内可数传递包络的单点扩张

若 X 是类内可数传递集合 C 的子集，则 C ∪ {X} 仍传递。新枚举把零映到
X，把后继映到旧枚举的前驱值；有界求值确保新图真正属于类。
结论是原 Z₂ 的类相对化包络扩张句，不包含 Collection。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryExtension

open Logic FirstOrder ThirdOrderSemantics StabilityFrame PowerlessBMSQuotientCoding
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false

attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

private abbrev up {Γ Δ : SortContext ℒ} (t : Term ℒ Γ Δ .set) := t.weakenBound SetTheory.SetSort.set

def shift_m : Formula ℒ [] [.set, .set, .set, .set, .set, .set] :=
  .disj (.conj (.equal (.fvar .here) (.fvar (.there (.there (.there (.there (.there .here)))))))
    (.equal (.fvar (.there .here)) (.fvar (.there (.there .here))))) <|
    membershipLevyBound.boundedExists (.fvar (.there (.there (.there (.there .here))))) <|
      .conj (PowerlessSuccessorBounded.formula_m (.bvar .here) (up (.fvar .here)))
        (PowerlessValueBounded.formula_m (up (.fvar (.there (.there (.there .here)))))
          (.bvar .here) (up (.fvar (.there .here))))

theorem shift_delta_l : Formula.IsDelta0 membershipLevyBound shift_m :=
  .disj (.conj (.equal _ _) (.equal _ _)) (.bounded_exists _
    (.conj (PowerlessSuccessorBounded.delta_l _ _) (PowerlessValueBounded.delta_l _ _ _)))

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

include hBase in
private theorem adjoin_l (X C : type_l hℳ B) : ∃ T : type_l hℳ B, ∀ x : type_l hℳ B,
    mem_l hℳ x.val T.val ↔ mem_l hℳ x.val C.val ∨ x = X := by
  have hPair := PowerlessRelativeClassStructure.pairing_l hℳ B hBase
  change ∀ a b : type_l hℳ B, ∃ p : type_l hℳ B, ∀ x : type_l hℳ B,
    mem_l hℳ x.val p.val ↔ x = a ∨ x = b at hPair
  obtain ⟨S, hS⟩ := hPair X X
  obtain ⟨P, hP⟩ := hPair C S
  have hUnion := PowerlessRelativeClassBasicAxioms.union_l hℳ B hBase
  change ∀ a : type_l hℳ B, ∃ t : type_l hℳ B, ∀ x : type_l hℳ B,
    mem_l hℳ x.val t.val ↔ ∃ y : type_l hℳ B, mem_l hℳ y.val a.val ∧ mem_l hℳ x.val y.val at hUnion
  obtain ⟨T, hT⟩ := hUnion P
  refine ⟨T, fun x => (hT x).trans ?_⟩
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hP y).mp hy with hEq | hEq
    · exact Or.inl (hEq ▸ hxy)
    · exact Or.inr (((hS x).mp (hEq ▸ hxy)).elim id id)
  · rintro (hx | hEq)
    · exact ⟨C, (hP C).mpr (Or.inl rfl), hx⟩
    · exact ⟨S, (hP S).mpr (Or.inr rfl), (hS x).mpr (Or.inl hEq)⟩

theorem exists_l (ω X C f : type_l hℳ B)
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hTrans : ∀ x : type_l hℳ B, mem_l hℳ x.val C.val → ∀ y : type_l hℳ B,
      mem_l hℳ y.val x.val → mem_l hℳ y.val C.val)
    (hSubset : ∀ x : type_l hℳ B, mem_l hℳ x.val X.val → mem_l hℳ x.val C.val)
    (hMap : map_l (ℳ := structure_l hℳ B hBase) f ω C)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val C.val → ∃ a : type_l hℳ B,
      mem_l hℳ a.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) f a y) :
    PowerlessHereditaryClassInternals.envelope_l (𝒩 := structure_l hℳ B hBase) X := by
  obtain ⟨K⟩ := PowerlessBMSQuotientCoding.exists_l hℳ
  have hωEq := SecondOrderOmega.unique_l hℳ
    ((PowerlessRelativeClassOmegaAbsolute.omega_l ω).mp hω) K.omega_spec
  let e : type_l hℳ B := ⟨(numberCode_l K (SecondOrderModel.zero_l ℳ)).val,
    PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property
      (hωEq.symm ▸ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property)⟩
  have heω : mem_l hℳ e.val ω.val := hωEq.symm ▸ (numberCode_l K (SecondOrderModel.zero_l ℳ)).property
  have hEmpty (a : type_l hℳ B) : ¬mem_l hℳ a.val e.val := PowerlessBMSQuotientSuccessor.zero_l K a.val
  obtain ⟨T, hT⟩ := adjoin_l (hBase := hBase) X C
  let η := (Env.empty (M := structure_l hℳ B hBase)).pushFree (sort := SetTheory.SetSort.set) e
    |>.pushFree (sort := SetTheory.SetSort.set) ω |>.pushFree (sort := SetTheory.SetSort.set) f
    |>.pushFree (sort := SetTheory.SetSort.set) X
  have hRead (n y : type_l hℳ B) : shift_m.satisfies
      ((η.pushFree (sort := SetTheory.SetSort.set) y).pushFree (sort := SetTheory.SetSort.set) n) ↔
      (n = e ∧ y = X) ∨ ∃ a : type_l hℳ B, mem_l hℳ a.val ω.val ∧
        PowerlessNatural.successor_l (ℳ := structure_l hℳ B hBase) a n ∧
          value_l (ℳ := structure_l hℳ B hBase) f a y := by
    simp only [shift_m, Formula.satisfies, Formula.LevyBound.boundedExists,
      Formula.LevyBound.membership, membershipLevyBound, PowerlessSuccessorBounded.formula_l,
      PowerlessValueBounded.formula_l, Arguments.eval, up, Term.eval_weakenBound, Term.eval]
    rfl
  have hfGlobal := (PowerlessRelativeClassFunctionAbsolute.map_l (hBase := hBase) f ω C).mp hMap
  have hUnique (n y z : type_l hℳ B)
      (hy : shift_m.satisfies ((η.pushFree y).pushFree n))
      (hz : shift_m.satisfies ((η.pushFree z).pushFree n)) : y = z := by
    rcases (hRead n y).mp hy with ⟨hn, hy⟩ | ⟨a, _, ha, hay⟩
    · rcases (hRead n z).mp hz with ⟨_, hz⟩ | ⟨a, _, ha, _⟩
      · exact hy.trans hz.symm
      · have hMem := (ha a).mpr (Or.inr rfl)
        rw [hn] at hMem
        exact (hEmpty a hMem).elim
    · rcases (hRead n z).mp hz with ⟨hn, _⟩ | ⟨b, _, hb, hbz⟩
      · have hMem := (ha a).mpr (Or.inr rfl)
        rw [hn] at hMem
        exact (hEmpty a hMem).elim
      · have hab : a = b := Subtype.ext (SecondOrderNaturalCases.successor_injective_l hℳ
          (a := a.val) (b := b.val) (c := n.val)
          ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) a n).mp ha)
          ((PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) b n).mp hb))
        have haz : value_l (ℳ := structure_l hℳ B hBase) f a z := hab.symm ▸ hbz
        exact Subtype.ext (SecondOrderFunctionProperties.value_unique_l hℳ hfGlobal
          ((PowerlessRelativeClassFunctionAbsolute.value_l f a y).mp hay)
          ((PowerlessRelativeClassFunctionAbsolute.value_l f a z).mp haz))
  have hTotal (n : type_l hℳ B) (hn : mem_l hℳ n.val ω.val) :
      ∃! y : type_l hℳ B, mem_l hℳ y.val T.val ∧ shift_m.satisfies ((η.pushFree y).pushFree n) := by
    have hWitness : ∃ y : type_l hℳ B, mem_l hℳ y.val T.val ∧ shift_m.satisfies ((η.pushFree y).pushFree n) := by
      rcases SecondOrderNaturalCases.cases_l K (hωEq ▸ hn) with hZero | ⟨a, ha, hSucc⟩
      · exact ⟨X, (hT X).mpr (Or.inr rfl), (hRead n X).mpr (Or.inl ⟨Subtype.ext hZero, rfl⟩)⟩
      · let a' : type_l hℳ B := ⟨a, PowerlessRelativeClassCorrespondence.transitive_l hℳ hBase ω.property (hωEq.symm ▸ ha)⟩
        have haω : mem_l hℳ a'.val ω.val := hωEq.symm ▸ ha
        obtain ⟨y, ⟨hy, hay⟩, _⟩ := hMap.2 a' haω
        exact ⟨y, (hT y).mpr (Or.inl hy), (hRead n y).mpr (Or.inr ⟨a', haω,
          (PowerlessRelativeClassOmegaAbsolute.successor_l (hBase := hBase) a' n).mpr hSucc, hay⟩)⟩
    obtain ⟨y, hy, hny⟩ := hWitness
    exact ⟨y, ⟨hy, hny⟩, fun z hz => hUnique n z y hz.2 hny⟩
  obtain ⟨g, hg, hValue⟩ := PowerlessRelativeClassFunctionRelation.exists_l shift_delta_l η ω T hTotal
  have hOnto' : ∀ y : type_l hℳ B, mem_l hℳ y.val T.val → ∃ n : type_l hℳ B,
      mem_l hℳ n.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) g n y := by
    intro y hy
    rcases (hT y).mp hy with hyC | hyX
    · obtain ⟨a, ha, hay⟩ := hOnto y hyC
      obtain ⟨n, hn, hSucc⟩ := ((PowerlessNatural.inductive_iff_l
        (ℳ := structure_l hℳ B hBase) ω).mp hω.1).2 a ha
      exact ⟨n, hn, (hValue n y).mpr ⟨hn, hy, (hRead n y).mpr (Or.inr ⟨a, ha, hSucc, hay⟩)⟩⟩
    · exact ⟨e, heω, (hValue e y).mpr ⟨heω, hy, (hRead e y).mpr (Or.inl ⟨rfl, hyX⟩)⟩⟩
  refine ⟨T, g, ω, (hT X).mpr (Or.inr rfl), ?_, hω, hg, hOnto'⟩
  intro x hx y hy
  apply (hT y).mpr
  apply Or.inl
  rcases (hT x).mp hx with hxC | hxX
  · exact hTrans x hxC y hy
  · exact hSubset y (hxX ▸ hy)

def schema_m : Formula ℒ [] [.set, .set, .set, .set] :=
  .imp (SecondOrderOmegaSyntax.omega_m (.fvar (.there (.there (.there .here))))) <|
    .imp (PowerlessRelativeHierarchyDerives.transitive_m (.fvar (.there .here))) <|
      .imp (ThirdOrderTheory.subset_m (.fvar .here) (.fvar (.there .here))) <|
        .imp (SecondOrderObjectSyntax.map_m (.fvar (.there (.there .here)))
          (.fvar (.there (.there (.there .here)))) (.fvar (.there .here))) <|
          .imp (PowerlessMemberDefSyntax.onto_m (.fvar (.there (.there (.there .here))))
            (.fvar (.there .here)) (.fvar (.there (.there .here))))
            (PowerlessHereditaryClassInternals.envelope_m (.fvar .here))

def sentence_m : Sentence ℒ := Metatheory.Formula.forall_close schema_m

theorem models_l : sentence_m.TrueIn (structure_l hℳ B hBase) := by
  apply (_root_.YesMetaZFC.Automation.ModelClosure.forall_close_iff _).mpr
  intro η hω hTrans hSubset hMap hOnto
  apply (PowerlessHereditaryClassInternals.envelope_formula_l η (.fvar .here)).mpr
  exact exists_l (η.freeVal (.there (.there (.there .here)))) (η.freeVal .here)
    (η.freeVal (.there .here)) (η.freeVal (.there (.there .here)))
    ((ThirdOrderSemantics.omega_formula_l η _).mp hω)
    ((PowerlessHereditaryClassInternals.transitive_formula_l η _).mp hTrans)
    ((ThirdOrderSemantics.subset_formula_l η _ _).mp hSubset)
    ((ThirdOrderSemantics.map_formula_l η _ _ _).mp hMap)
    ((PowerlessHereditaryClassInternals.onto_formula_l η _ _ _).mp hOnto)

theorem derives_m : Derives SecondOrderArithmetic.theory_m []
    (GraphTranslation.form_m (PowerlessRelativeClassRelativization.guarded_m sentence_m)) :=
  PowerlessRelativeClassRelativization.derives_m _ (fun _ _ _ _ => models_l)

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryExtension
