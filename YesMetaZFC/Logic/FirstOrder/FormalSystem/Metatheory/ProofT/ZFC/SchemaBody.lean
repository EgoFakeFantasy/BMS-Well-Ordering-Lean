import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.AxiomEncode
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.SchemaTerm
/-!
# 模式正文的完整递归识别

成功识别恰好对应一个作用域正确、自由闭合的 Project 正文，并保持原始树。
本层证明宿主递归的可靠性、完备性和拒绝边界；统一对象图的正负表示见 SchemaBodyDerives。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaBody
open Nonlogical.BasicSetTheory NatPacket
open _root_.YesMetaZFC.SetTheory.Definitional
set_option autoImplicit false

theorem term_decode_spec {depth : Nat} {input : Tree} {result : Project.Term depth}
    (h : ProjectDecode.term depth input = some result) :
    result.freeSupport = [] ∧ ProjectEncode.term result = input := by
  have hCheck : SchemaTerm.check depth input = true := by
    unfold SchemaTerm.check
    rw [h]
    rfl
  obtain ⟨index, hIndex, rfl⟩ := (SchemaTerm.check_eq_true_iff depth input).mp hCheck
  change (if h : index < depth then some (.bound ⟨index, h⟩) else none) = some result at h
  rw [dif_pos hIndex] at h
  cases h
  exact ⟨rfl, rfl⟩

/-- 成功解码自动给出完整自由闭性，且重新编码逐节点恢复原始树。 -/
theorem decode_spec (depth : Nat) (input : Tree) :
    ∀ result, ProjectDecode.formula depth input = some result →
      result.FreeClosed ∧ ProjectEncode.formula result = input := by
  fun_induction ProjectDecode.formula depth input
  case case1 | case2 =>
    intro result h
    cases h
    exact ⟨by simp only [Formula.FreeClosed] , rfl⟩
  case case3 | case4 | case12 =>
    intro result h
    obtain ⟨left, hLeft, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨right, hRight, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    obtain ⟨hLeftClosed, rfl⟩ := term_decode_spec hLeft
    obtain ⟨hRightClosed, rfl⟩ := term_decode_spec hRight
    constructor
    · simpa [Project.Formula.extensionalEq, Project.Formula.subset, Formula.FreeClosed]
        using And.intro hLeftClosed hRightClosed
    · simp [ProjectEncode.formula, Project.Formula.extensionalEq, Project.Formula.subset]
  case case5 depth body ih | case10 depth body ih | case11 depth body ih =>
    intro result h
    obtain ⟨decoded, hBody, hResult⟩ := Option.bind_eq_some_iff.mp h
    cases hResult
    obtain ⟨hClosed, rfl⟩ := ih _ hBody
    exact ⟨by simpa only [Formula.FreeClosed] using hClosed, rfl⟩
  case case6 depth left right ihLeft ihRight
     | case7 depth left right ihLeft ihRight
     | case8 depth left right ihLeft ihRight
     | case9 depth left right ihLeft ihRight =>
    intro result h
    obtain ⟨decodedLeft, hLeft, hRest⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨decodedRight, hRight, hResult⟩ := Option.bind_eq_some_iff.mp hRest
    cases hResult
    obtain ⟨hLeftClosed, rfl⟩ := ihLeft _ hLeft
    obtain ⟨hRightClosed, rfl⟩ := ihRight _ hRight
    exact ⟨by simpa only [Formula.FreeClosed] using And.intro hLeftClosed hRightClosed, rfl⟩
  case case13 => intro result h; cases h

theorem decode_eq_some_iff (depth : Nat) (input : Tree) (result : Project.Formula 1 depth) :
    ProjectDecode.formula depth input = some result ↔
      result.FreeClosed ∧ ProjectEncode.formula result = input := by
  constructor
  · exact decode_spec depth input result
  · rintro ⟨hClosed, rfl⟩
    exact ProjectEncode.formula_roundtrip result hClosed

/-- 识别实际解码器的成功；没有外部深度或长度截断。 -/
def check (depth : Nat) (input : Tree) : Bool := (ProjectDecode.formula depth input).isSome

theorem check_eq_true_iff (depth : Nat) (input : Tree) :
    check depth input = true ↔
      ∃ body : Project.Formula 1 depth, body.FreeClosed ∧ ProjectEncode.formula body = input := by
  constructor
  · intro hCheck
    cases h : ProjectDecode.formula depth input with
    | none => simp [check, h] at hCheck
    | some body => exact ⟨body, (decode_eq_some_iff depth input body).mp h⟩
  · rintro ⟨body, hClosed, hCode⟩
    unfold check
    rw [(decode_eq_some_iff depth input body).mpr ⟨hClosed, hCode⟩]
    rfl

theorem check_eq_false_iff (depth : Nat) (input : Tree) :
    check depth input = false ↔
      ∀ body : Project.Formula 1 depth, body.FreeClosed → ProjectEncode.formula body ≠ input := by
  have h := not_congr (check_eq_true_iff depth input)
  simpa only [Bool.not_eq_true, not_exists, not_and] using h

/-- 实际一元模式解码器的闭性检查不会额外拒绝已识别正文。 -/
theorem unarySchema_isSome (parameterCount : Nat) (input : Tree) :
    (ProjectDecode.unarySchema parameterCount input).isSome = check (parameterCount + 1) input := by
  unfold ProjectDecode.unarySchema check
  cases h : ProjectDecode.formula (parameterCount + 1) input with
  | none => rfl
  | some body =>
      simp only [bind, Option.bind_some, dif_pos (decode_spec _ _ _ h).1, Option.isSome_some]

/-- 二元模式也恰好使用同一个递归识别器，仅源作用域相差一个主变量。 -/
theorem binarySchema_isSome (parameterCount : Nat) (input : Tree) :
    (ProjectDecode.binarySchema parameterCount input).isSome = check (parameterCount + 2) input := by
  unfold ProjectDecode.binarySchema check
  cases h : ProjectDecode.formula (parameterCount + 2) input with
  | none => rfl
  | some body =>
      simp only [bind, Option.bind_some, dif_pos (decode_spec _ _ _ h).1, Option.isSome_some]

/-- 直接恢复当前类型安全内核的 AST，闭性证明来自实际解码结果。 -/
def intrinsic (depth : Nat) (input : Tree) :
    Option (SetFormula (QuineEncoding.project_bound_context depth) []) :=
  match h : ProjectDecode.formula depth input with
  | none => none
  | some body => some (QuineEncoding.project_formula body (decode_spec _ _ _ h).1)

theorem intrinsic_of_decode (depth : Nat) (input : Tree) (body : Project.Formula 1 depth)
    (h : ProjectDecode.formula depth input = some body) :
    intrinsic depth input = some (QuineEncoding.project_formula body (decode_spec _ _ _ h).1) := by
  unfold intrinsic
  split
  · rename_i hNone
    rw [hNone] at h
    cases h
  · rename_i decoded hDecoded
    cases Option.some.inj (hDecoded.symm.trans h)
    rfl

theorem intrinsic_encode (depth : Nat) (body : Project.Formula 1 depth)
    (hClosed : body.FreeClosed) :
    intrinsic depth (ProjectEncode.formula body) = some (QuineEncoding.project_formula body hClosed) :=
  intrinsic_of_decode _ _ _ (ProjectEncode.formula_roundtrip body hClosed)

theorem intrinsic_isSome (depth : Nat) (input : Tree) :
    (intrinsic depth input).isSome = check depth input := by
  unfold intrinsic check
  split <;> simp_all only [Option.isSome_none, Option.isSome_some]

theorem intrinsic_eq_none_iff (depth : Nat) (input : Tree) :
    intrinsic depth input = none ↔ ProjectDecode.formula depth input = none := by
  have h := Iff.of_eq (congrArg (fun value => value = false) (intrinsic_isSome depth input))
  simpa only [check, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] using h

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.SchemaBody
