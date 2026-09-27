import YesMetaZFC.BMS.HeightDescent

/-!
# 当前行数有界的精确目标

包括由任意高度种子生成、但当前行数不超过上界的数组。
高度层分解只使用展开不增高，不借用整个 BMS 的良基性或可比性。
这些是宿主层目标等价，不是 Z₂ 内部推导。
-/

namespace YesMetaZFC.BMS.ConstructibleBridge.FiniteHeight

open StabilityFrame HeightDescent

set_option autoImplicit false

/-- 当前高度有界，不限制起始种子的高度。 -/
abbrev carrier_l (N : Nat) := {a : GeneratedArray // height_l a.1 ≤ N}

/-- 有界载体上的实际严格一步展开。 -/
def step_l (N : Nat) (a b : carrier_l N) : Prop := GeneratedStep a.1 b.1

/-- 行数有界目标恰好要求上界以内的每个高度层良基。 -/
theorem wf_iff_l (N : Nat) :
    WellFounded (step_l N) ↔
      ∀ n, n ≤ N → WellFounded (HeightDescent.step_l n) := by
  constructor
  · intro h n hn
    let f : fiber_l n → carrier_l N := fun a => ⟨a.1, by rw [a.2]; exact hn⟩
    exact InvImage.wf f h
  · intro h
    refine ⟨fun a => ?_⟩
    exact InvImage.accessible Subtype.val
      (HeightDescent.acc_bounded_l h (height_l a.1.1) a.2 a.1 rfl)

/-- 有界载体的无限下降恰好对应某个有界高度层的无限下降。 -/
theorem descent_iff_l (N : Nat) :
    (∃ f : Nat → carrier_l N, ∀ i, step_l N (f (i + 1)) (f i)) ↔
      ∃ n, n ≤ N ∧ ∃ f : Nat → fiber_l n,
        ∀ i, HeightDescent.step_l n (f (i + 1)) (f i) := by
  constructor
  · rintro ⟨f, h⟩
    obtain ⟨k, hk⟩ := HeightDescent.tail_l (fun i => (f i).1) h
    exact ⟨height_l (f k).1.1, (f k).2,
      (fun i => ⟨(f (k + i)).1, hk i⟩),
      fun i => by simpa only [HeightDescent.step_l, step_l, Nat.add_assoc] using h (k + i)⟩
  · rintro ⟨n, hn, f, h⟩
    exact ⟨(fun i => ⟨(f i).1, by rw [(f i).2]; exact hn⟩), h⟩

end YesMetaZFC.BMS.ConstructibleBridge.FiniteHeight
