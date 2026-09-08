import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.NatPacketRoundtrip

/-! # 版本一传输包的规范性：成功解码后精确恢复原自然数 -/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket
set_option autoImplicit false

theorem varint_small (n : Nat) (h : n < 128) : varint n = [n] := by rw [varint, dif_pos h]

theorem varint_large (digit rest : Nat) (hDigit : digit < 128) (hRest : 0 < rest) :
    varint (digit + 128 * rest) = (digit + 128) :: varint rest := by
  rw [varint, dif_neg (by omega)]
  have hDiv : (digit + 128 * rest) / 128 = rest := by omega
  have hMod : (digit + 128 * rest) % 128 = digit := by omega
  rw [hDiv, hMod]

theorem varint_ne_nil (n : Nat) : varint n ≠ [] := by
  rw [varint]
  split <;> simp

theorem readBytes_inverse (code : Nat) (acc result : List Nat)
    (h : readBytes code acc = some result) :
    ∃ bytes, result = acc.reverse ++ bytes ∧ code = packBytes bytes ∧ ∀ b ∈ bytes, b < 256 := by
  induction code using Nat.strongRecOn generalizing acc with
  | ind code ih =>
    rw [readBytes.eq_def] at h
    split at h
    · split at h
      · have hCode : code = 1 := by simpa using ‹(code == 1) = true›
        exact ⟨[], by simpa using (Option.some.inj h).symm, hCode, by simp⟩
      · cases h
    · rename_i hLarge
      obtain ⟨bytes, hResult, hCode, hBytes⟩ := ih (code / 256)
        (Nat.div_lt_self (by omega) (by decide)) (code % 256 :: acc) h
      refine ⟨code % 256 :: bytes, ?_, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using hResult
      · change code = code % 256 + 256 * packBytes bytes
        rw [← hCode, Nat.mod_add_div]
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Nat.mod_lt _ (by decide)
        · exact hBytes b hb

/-- 成功的非空字节流必先消费一个规范 varint；累加器可处于任意合法正比例状态。 -/
theorem readTokens_prefix (bytes : List Nat) (hBytes : ∀ b ∈ bytes, b < 256)
    (hNonempty : bytes ≠ []) (value scale : Nat) (hScale : 0 < scale) (acc result : List Nat)
    (h : readTokens bytes value scale acc = some result) :
    ∃ n rest, bytes = varint n ++ rest ∧ (scale ≠ 1 → n ≠ 0) ∧
      readTokens rest 0 1 ((value + n * scale) :: acc) = some result := by
  induction bytes generalizing value scale acc with
  | nil => exact False.elim (hNonempty rfl)
  | cons byte bytes ih =>
    have hByte := hBytes byte List.mem_cons_self
    rw [readTokens] at h
    split at h
    · rename_i hSmall
      split at h
      · cases h
      · rename_i hCanonical
        refine ⟨byte, bytes, by rw [varint_small byte hSmall]; rfl, ?_, h⟩
        simpa using hCanonical
    · rename_i hLarge
      have hScale' : 0 < scale * 128 := by omega
      have hNonempty' : bytes ≠ [] := by
        intro hEmpty
        rw [hEmpty, readTokens] at h
        simp [show scale * 128 ≠ 1 by omega] at h
      obtain ⟨n, rest, hBytes', hCanonical, hResult⟩ :=
        ih (fun b hb => hBytes b (List.mem_cons_of_mem _ hb)) hNonempty'
          (value + (byte - 128) * scale) (scale * 128) hScale' acc h
      have hn : 0 < n := Nat.pos_of_ne_zero (hCanonical (by omega))
      refine ⟨byte - 128 + 128 * n, rest, ?_, by omega, ?_⟩
      · rw [varint_large _ _ (by omega) hn]
        have hByte' : byte - 128 + 128 = byte := by omega
        rw [hByte', List.cons_append, ← hBytes']
      · have hValue : value + (byte - 128) * scale + n * (scale * 128) =
            value + (byte - 128 + 128 * n) * scale := by
          simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]
        rwa [hValue] at hResult

theorem readTokens_inverse (bytes : List Nat) (hBytes : ∀ b ∈ bytes, b < 256)
    (acc result : List Nat) (h : readTokens bytes 0 1 acc = some result) :
    ∃ tokens, result = acc.reverse ++ tokens ∧ bytes = tokens.flatMap varint := by
  induction bytes using (measure List.length).wf.induction generalizing acc with
  | h bytes ih =>
    cases bytes with
    | nil => exact ⟨[], by simpa [readTokens] using (Option.some.inj h).symm, rfl⟩
    | cons byte bytes =>
      obtain ⟨n, rest, hPrefix, _, hRest⟩ :=
        readTokens_prefix (byte :: bytes) hBytes (by simp) 0 1 (by decide) acc result h
      have hRestBytes : ∀ b ∈ rest, b < 256 := by
        intro b hb
        exact hBytes b (hPrefix ▸ List.mem_append_right _ hb)
      have hRest' : readTokens rest 0 1 (n :: acc) = some result := by simpa using hRest
      obtain ⟨tokens, hResult, hTokens⟩ := ih rest (by
        change rest.length < (byte :: bytes).length
        simp only [List.length_cons]
        have hLength := congrArg List.length hPrefix
        have hPositive : 0 < (varint n).length := List.length_pos_iff.mpr (varint_ne_nil n)
        simp only [List.length_cons, List.length_append] at hLength
        omega) hRestBytes (n :: acc) hRest'
      refine ⟨n :: tokens, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using hResult
      · rw [hPrefix, List.flatMap_cons, hTokens]

mutual
theorem readTree_inverse (fuel : Nat) (tokens : List Nat) (tree : Tree) (rest : List Nat)
    (h : readTree fuel tokens = some (tree, rest)) : tokens = treeTokens tree ++ rest := by
  cases fuel with
  | zero => cases h
  | succ fuel =>
    cases tokens with
    | nil => cases h
    | cons tag tokens =>
      cases tokens with
      | nil => cases h
      | cons count tokens =>
        obtain ⟨⟨children, tail⟩, hForest, hResult⟩ := Option.bind_eq_some_iff.mp h
        cases hResult
        obtain ⟨hTokens, hCount⟩ := readForest_inverse fuel count tokens children rest hForest
        rw [treeTokens, ← hCount, List.cons_append, List.cons_append, ← hTokens]
termination_by fuel

theorem readForest_inverse (fuel count : Nat) (tokens : List Nat) (trees : List Tree) (rest : List Nat)
    (h : readForest fuel count tokens = some (trees, rest)) :
    tokens = trees.flatMap treeTokens ++ rest ∧ count = trees.length := by
  cases count with
  | zero => cases fuel <;> cases h <;> exact ⟨rfl, rfl⟩
  | succ count =>
    cases fuel with
    | zero => cases h
    | succ fuel =>
      obtain ⟨⟨head, tail⟩, hHead, hTail⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨⟨children, final⟩, hChildren, hResult⟩ := Option.bind_eq_some_iff.mp hTail
      cases hResult
      have hHead := readTree_inverse fuel tokens head tail hHead
      obtain ⟨hTail, hCount⟩ := readForest_inverse fuel count tail children rest hChildren
      constructor
      · rw [hHead, hTail, List.flatMap_cons, List.append_assoc]
      · simp [hCount]
termination_by fuel
end

/-- 不仅往返合法编码：所有实际解码成功的原始自然数均是该树的规范编码。 -/
theorem encode_of_decode {code : Nat} {tree : Tree} (h : decode code = some tree) : encode tree = code := by
  unfold decode at h
  obtain ⟨bytes, hBytes, hTokens⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tokens, hTokens, hTree⟩ := Option.bind_eq_some_iff.mp hTokens
  obtain ⟨actualBytes, hBytesEq, hCode, hBound⟩ := readBytes_inverse code [] bytes hBytes
  simp only [List.reverse_nil, List.nil_append] at hBytesEq
  subst actualBytes
  obtain ⟨actualTokens, hTokensEq, hPacked⟩ := readTokens_inverse bytes hBound [] tokens hTokens
  simp only [List.reverse_nil, List.nil_append] at hTokensEq
  subst actualTokens
  cases tokens with
  | nil => cases hTree
  | cons version payload =>
    cases version with
    | zero => cases hTree
    | succ version =>
      cases version with
      | succ _ => cases hTree
      | zero =>
        obtain ⟨⟨decoded, tail⟩, hDecoded, hResult⟩ := Option.bind_eq_some_iff.mp hTree
        change (if tail.isEmpty then some decoded else none) = some tree at hResult
        split at hResult
        · rename_i hEmpty
          have hEmpty : tail = [] := by simpa using hEmpty
          subst tail
          cases hResult
          have hPayload := readTree_inverse _ payload tree [] hDecoded
          simp only [List.append_nil] at hPayload
          rw [hPayload] at hPacked
          rw [hCode, hPacked]
          rfl
        · cases hResult

theorem decode_eq_some_iff (code : Nat) (tree : Tree) : decode code = some tree ↔ encode tree = code :=
  ⟨encode_of_decode, fun h => h ▸ decode_encode tree⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket
