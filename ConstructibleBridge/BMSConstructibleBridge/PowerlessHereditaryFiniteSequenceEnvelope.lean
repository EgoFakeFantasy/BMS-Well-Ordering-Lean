import BMSConstructibleBridge.PowerlessRelativeClassPairFamilyEnumeration
import BMSConstructibleBridge.PowerlessRelativeClassBinaryUnion
import BMSConstructibleBridge.PowerlessHereditaryExtension

/-! # 给定含 ω 的可数传递包络上的有限序列包络

取 T、T 上无序对族、其上的无序对族、全部 T 值有限序列之并。两个对族
精确覆盖函数图的 Kuratowski 中间对象；不以各元素分别遗传替代统一包络。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFiniteSequenceEnvelope

open Logic FirstOrder ThirdOrderSemantics
open SecondOrderQuotient (mem_l)
open PowerlessRelativeClassStructure (type_l structure_l)

set_option autoImplicit false
attribute [local implicit_reducible] SetTheory.signature SecondOrderQuotient.structure_l structure_l

universe u

variable {ℳ : FirstOrder.Structure.{0, 0, 0, u} SecondOrderSyntax.signature_m}
  {hℳ : Theory.Models ℳ SecondOrderArithmetic.theory_m} {B : SecondOrderQuotient.type_l hℳ}
  {hBase : ∀ x, mem_l hℳ x B → ∀ y, mem_l hℳ y x → mem_l hℳ y B}

theorem map_widen_l {f A X T : type_l hℳ B}
    (hf : map_l (ℳ := structure_l hℳ B hBase) f A X)
    (hSubset : ∀ y : type_l hℳ B, mem_l hℳ y.val X.val → mem_l hℳ y.val T.val) :
    map_l (ℳ := structure_l hℳ B hBase) f A T := by
  constructor
  · intro p hp
    obtain ⟨x, y, hx, hy, hxy⟩ := hf.1 p hp
    exact ⟨x, y, hx, hSubset y hy, hxy⟩
  · intro x hx
    obtain ⟨y, ⟨hy, hxy⟩, hUnique⟩ := hf.2 x hx
    refine ⟨y, ⟨hSubset y hy, hxy⟩, ?_⟩
    rintro z ⟨_, hxz⟩
    exact hUnique z ⟨(PowerlessRelativeClassSequenceComposition.value_mem_l hf hxz).2, hxz⟩

theorem exists_l {ω X T G : type_l hℳ B}
    (hω : omega_l (ℳ := structure_l hℳ B hBase) ω)
    (hXT : mem_l hℳ X.val T.val) (hωT : mem_l hℳ ω.val T.val)
    (hTrans : ∀ x : type_l hℳ B, mem_l hℳ x.val T.val → ∀ y : type_l hℳ B,
      mem_l hℳ y.val x.val → mem_l hℳ y.val T.val)
    (hG : map_l (ℳ := structure_l hℳ B hBase) G ω T)
    (hOnto : ∀ y : type_l hℳ B, mem_l hℳ y.val T.val → ∃ i : type_l hℳ B,
      mem_l hℳ i.val ω.val ∧ value_l (ℳ := structure_l hℳ B hBase) G i y) :
    ∃ S : type_l hℳ B, PowerlessFiniteSequencesSyntax.spec_l (ℳ := structure_l hℳ B hBase) ω X S ∧
      PowerlessHereditaryClassInternals.envelope_l (𝒩 := structure_l hℳ B hBase) S := by
  obtain ⟨P, hP, GP, hGP, hPonto⟩ := PowerlessRelativeClassPairFamilyEnumeration.exists_l hω hG hOnto
  obtain ⟨Q, hQ, GQ, hGQ, hQonto⟩ := PowerlessRelativeClassPairFamilyEnumeration.exists_l hω hGP hPonto
  obtain ⟨N, hN, GN, hGN, hNonto⟩ := PowerlessRelativeClassFiniteSequenceEnumeration.exists_l hω hG hOnto
  obtain ⟨U, hU, GU, hGU, hUonto⟩ := PowerlessRelativeClassBinaryUnion.enumeration_l hω hG hGP hOnto hPonto
  obtain ⟨V, hV, GV, hGV, hVonto⟩ := PowerlessRelativeClassBinaryUnion.enumeration_l hω hGU hGQ hUonto hQonto
  obtain ⟨W, hW, F, hF, hWonto⟩ := PowerlessRelativeClassBinaryUnion.enumeration_l hω hGV hGN hVonto hNonto
  have hTW (x : type_l hℳ B) (hx : mem_l hℳ x.val T.val) : mem_l hℳ x.val W.val :=
    (hW x).mpr (Or.inl ((hV x).mpr (Or.inl ((hU x).mpr (Or.inl hx)))))
  have hPW (x : type_l hℳ B) (hx : mem_l hℳ x.val P.val) : mem_l hℳ x.val W.val :=
    (hW x).mpr (Or.inl ((hV x).mpr (Or.inl ((hU x).mpr (Or.inr hx)))))
  have hQW (x : type_l hℳ B) (hx : mem_l hℳ x.val Q.val) : mem_l hℳ x.val W.val :=
    (hW x).mpr (Or.inl ((hV x).mpr (Or.inr hx)))
  have hWTrans (x : type_l hℳ B) (hx : mem_l hℳ x.val W.val)
      (y : type_l hℳ B) (hy : mem_l hℳ y.val x.val) : mem_l hℳ y.val W.val := by
    rcases (hW x).mp hx with hx | hx
    · rcases (hV x).mp hx with hx | hx
      · rcases (hU x).mp hx with hx | hx
        · exact hTW y (hTrans x hx y hy)
        · obtain ⟨a, b, ha, hb, hPair⟩ := (hP x).mp hx
          rcases (hPair y).mp hy with rfl | rfl
          · exact hTW _ ha
          · exact hTW _ hb
      · obtain ⟨a, b, ha, hb, hPair⟩ := (hQ x).mp hx
        rcases (hPair y).mp hy with rfl | rfl
        · exact hPW _ ha
        · exact hPW _ hb
    · obtain ⟨n, hn, hxMap⟩ := (hN x).mp hx
      obtain ⟨k, v, hk, hv, s, t, hs, ht, hyPair⟩ := hxMap.1 y hy
      have hkT := hTrans n (hTrans ω hωT n hn) k hk
      have hsP := (hP s).mpr ⟨k, k, hkT, hkT, hs⟩
      have htP := (hP t).mpr ⟨k, v, hkT, hv, ht⟩
      exact hQW y ((hQ y).mpr ⟨s, t, hsP, htP, hyPair⟩)
  obtain ⟨S, hS⟩ := PowerlessRelativeClassFiniteSequencesDerives.exists_l (hBase := hBase) (X := X) hω
  have hSW (f : type_l hℳ B) (hf : mem_l hℳ f.val S.val) : mem_l hℳ f.val W.val := by
    obtain ⟨n, hn, hfMap⟩ := (hS f).mp hf
    exact (hW f).mpr (Or.inr ((hN f).mpr
      ⟨n, hn, map_widen_l hfMap (fun y hy => hTrans X hXT y hy)⟩))
  exact ⟨S, hS, PowerlessHereditaryExtension.exists_l ω S W F hω hWTrans hSW hF hWonto⟩

end YesMetaZFC.BMS.ConstructibleBridge.PowerlessHereditaryFiniteSequenceEnvelope
