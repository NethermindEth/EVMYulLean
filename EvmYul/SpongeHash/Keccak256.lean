import Mathlib.Tactic

import EvmYul.SpongeHash.Wheels

open BigOperators
open Vector

abbrev SHA3SR : Type := Array UInt64

instance : Coe Bool (Fin 2) := ⟨(if · then 1 else 0)⟩
instance : Coe (Fin 2) Bool := ⟨(·.1 == 1)⟩

def Rounds : Nat := 24

def NumLanes : Nat := 25

def LaneWidth : Nat := 64

def RoundConstants : Array UInt64 :=
  #[ 0x0000000000000001, 0x0000000000008082, 0x800000000000808A
   , 0x8000000080008000, 0x000000000000808B, 0x0000000080000001
   , 0x8000000080008081, 0x8000000000008009, 0x000000000000008A
   , 0x0000000000000088, 0x0000000080008009, 0x000000008000000A
   , 0x000000008000808B, 0x800000000000008B, 0x8000000000008089
   , 0x8000000000008003, 0x8000000000008002, 0x8000000000000080
   , 0x000000000000800A, 0x800000008000000A, 0x8000000080008081
   , 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ]

def rotationConstants : Array Nat :=
  #[  0, 36,  3, 41, 18
   ,  1, 44, 10, 45,  2
   , 62,  6, 43, 15, 61
   , 28, 55, 25, 21, 56
   , 27, 20, 39,  8, 14 ]

def piConstants : Array Nat :=
  #[ 0, 15, 5, 20, 10
   , 6, 21, 11, 1, 16
   , 12, 2, 17, 7, 22
   , 18, 8, 23, 13, 3
   , 24, 14, 4, 19, 9 ]

def rotateL (a : UInt64) (n : Nat) : UInt64 := UInt64.ofNat (BitVec.ofNat 64 a.toNat |>.rotateLeft n).toNat

def complement (a : UInt64) : UInt64 := UInt64.ofNat (Complement.complement <| BitVec.ofNat 64 a.toNat).toNat

def Array.foldl1 {β : Type} [Inhabited β] (f : β → β → β) (as : Array β) : β :=
  Array.foldl f (as[0]!) ⟨as.data.drop 1⟩

def θ (state : SHA3SR) : SHA3SR :=
  let indexed := Array.zip (Array.range 25) d
  indexed.concatMap λ (i, e) ↦ Array.map (· ^^^ e) (state.extract (i * 5) (i * 5 + 5))
  where c : SHA3SR := Array.range 5 |>.map λ i ↦ (state.extract (i * 5) (i * 5 + 5)).foldl1 (·^^^·)
        d : SHA3SR := Array.range 5 |>.map λ i ↦ c[(Int.ofNat i - 1) % 5 |>.toNat]! ^^^ rotateL (c[(Int.ofNat i + 1) % 5 |>.toNat]!) 1

def ρ (state : SHA3SR) : SHA3SR := Array.zipWith rotationConstants state (flip rotateL)

def Array.backpermute {α} [Inhabited α] : Array α → Array Nat → Array α := λ xs ↦ Array.map (xs[·]!)

def π (state : SHA3SR) : SHA3SR := state.backpermute piConstants

def Array.imap {α β} (f : ℕ → α → β) (arr : Array α) : Array β :=
  let indexed := Array.zip (Array.range arr.size) arr
  indexed.map (Function.uncurry f)

def χ (b : SHA3SR) : SHA3SR := Array.imap subChi b
  where subChi z el := el ^^^ (complement (b[(z + 5) % 25]!) &&& (b[(z + 10) % 25]!))

def ι (roundNumber : Nat) (state : SHA3SR) : SHA3SR := state.setD 0 (RoundConstants[roundNumber]! ^^^ (state[0]!))

def keccak_round (r : ℕ) : SHA3SR → SHA3SR := ι r ∘ χ ∘ π ∘ ρ ∘ θ

def keccakF'' (s : SHA3SR) : SHA3SR :=
  let f : ℕ × SHA3SR → ℕ × SHA3SR := λ (r, s) => (.succ r, keccak_round r $ s)
  (List.foldl Function.comp id (List.replicate 24 f) (0, s)).2

def keccakF (state : SHA3SR) : SHA3SR :=
  (·.2) <| Array.foldl1 (·∘·) (⟨List.replicate Rounds f⟩) (0, state)
    where f : Nat × SHA3SR → Nat × SHA3SR := λ (r, s) ↦ (r.succ, ι r ∘ χ ∘ π ∘ ρ <| θ s)

def bytesOfList (l : List (Fin 2)) : List UInt8 :=
  l.toChunks 8 |>.map λ bits ↦ bits.zip (List.iota 8 |>.map Nat.pred) |>.foldl (init := 0)
    λ acc (bit, exp) ↦ acc + (UInt8.ofNat <| bit.val * 2^exp)

def hexOfByte (byte : UInt8) : String :=
  hexDigitRepr (byte.toNat >>> 4 &&& 0b00001111) ++
  hexDigitRepr (byte.toNat &&& 0b00001111)

namespace Absorb

partial def unfoldr {α β} (f : β → Option (α × β)) (b0 : β) : Array α :=
  build λ c n ↦
    let rec go b := match f b with
                      | .some (a, new_b) => c a <| go new_b
                      | .none            => n
    go b0
  where build g := g push_front #[]
        push_front (elem : α) (arr : Array α) : Array α := ⟨elem :: arr.toList⟩

partial def unfoldrN {α β} (m : Nat) (f : β → Option (α × β)) (b0 : β) : Array α :=
  build λ c n ↦
    let rec go b i := if i == 0 then n else
                      match f b with
                        | .some (a, new_b) => c a <| go new_b (i - 1)
                        | .none            => n
    go b0 m
  where build g := g push_front #[]
        push_front {α} (elem : α) (arr : Array α) : Array α := ⟨elem :: arr.toList⟩

def ifoldl {α β : Type} (f : α → Nat → β → α) (init : α) (as : Array β) : α :=
  Array.range as.size |>.zip as |>.foldl (λ acc (i, elem) ↦ f acc i elem) init

def toBlocks : ByteArray → Array UInt64 :=
  unfoldr toLane
    where toLane (input : ByteArray) : Option (UInt64 × ByteArray) :=
            if input.isEmpty then .none
            else let (h, t) := input.data.splitAt 8
                 .some (ifoldl createWord64 0 h, ⟨t⟩)
          createWord64 acc offset octet := acc ^^^ (octet.toUInt64 <<< (UInt64.ofNat offset * 8))

partial def absorbBlock (rate : Nat) (state : Array UInt64) (input : Array UInt64) : Array UInt64 :=
  if input.size == 0 then state
  else -- dbg_trace s!"initial state: {state} | istream: {input}"
       -- dbg_trace s!"applying keccak to: {state'} to get: {keccakF state'}"
       absorbBlock rate (keccakF state') (input.drop (rate / 64))
  where state' : SHA3SR := Array.imap (λ z el ↦ if z / 5 + 5 * (z % 5) < rate / 64
                                                 then el ^^^ (input[z / 5 + 5 * (z % 5)]!)
                                                 else el) state

def absorb (rate : Nat) : ByteArray → Array UInt64 := absorbBlock rate ⟨List.replicate 25 0⟩ ∘ toBlocks
end Absorb

def multiratePadding (bitrateBytes : Nat) (padByte : UInt8) (input : ByteArray) : ByteArray :=
  ByteArray.mk <| Array.range totalLength |>.map λ i ↦ process i
  where msglen := input.size
        padlen := bitrateBytes - (msglen % bitrateBytes)
        totalLength := padlen + msglen
        process x := if x < msglen then input[x]! else
                     if x == (totalLength - 1) && padlen == 1 then 0x80 ||| padByte else
                     if x == (totalLength - 1) then 0x80 else
                     if x == msglen then padByte
                     else 0x00

def byteArrayOfSHA3SR (arr : SHA3SR) : ByteArray :=
  arr.foldl (init := ByteArray.empty)
    λ acc word ↦
      acc.push (word >>> UInt64.ofNat 56).toUInt8
       |>.push (word >>> UInt64.ofNat 48).toUInt8
       |>.push (word >>> UInt64.ofNat 40).toUInt8
       |>.push (word >>> UInt64.ofNat 32).toUInt8
       |>.push (word >>> UInt64.ofNat 24).toUInt8
       |>.push (word >>> UInt64.ofNat 16).toUInt8
       |>.push (word >>> UInt64.ofNat 8).toUInt8
       |>.push (word >>> UInt64.ofNat 0).toUInt8

def SHA3SRofByteArray (arr : ByteArray) : SHA3SR :=
  let arr : ByteArray := ⟨Array.mkArray ((8 - arr.size % 8) % 8) 0⟩ ++ arr
  (·.1) <| arr.foldl (init := (#[], 0, 7))
    λ (res, word, i) byte ↦
      let byteVal : UInt64 := (2^(8 * i)).toUInt64 * byte.toUInt64
      if i == 0
      then (res.push (word + byteVal), 0, 7)
      else (res, word + byteVal, i - 1)

def paddingKeccak (bitrateBytes : Nat) : ByteArray → SHA3SR :=
  SHA3SRofByteArray ∘ multiratePadding bitrateBytes 0x01

partial def squeeze' (rate : Nat) (l : Nat) (state : SHA3SR) : ByteArray :=
  ByteArray.extract (b := 0) (e := l) ∘ toLittleEndian <| stateToBytes state
  where lanesToExtract := Int.toNat ∘ Rat.ceil <| l / (64 / 8)
        threshold := rate / 64
        extract := λ (x, s) ↦
                     if x < threshold
                     then Option.some (s[x / 5 + x % 5 * 5]!, (x.succ, s))
                     else extract (0, keccakF s)
        stateToBytes (s : Array UInt64) : Array UInt64 := Absorb.unfoldrN lanesToExtract extract (0, s)
        toLittleEndian (arr : Array UInt64) : ByteArray :=
          arr.foldl (init := ByteArray.empty) λ acc elem ↦
            let res :=
            acc.push (elem >>> UInt64.ofNat 0).toUInt8
             |>.push (elem >>> UInt64.ofNat 8).toUInt8
             |>.push (elem >>> UInt64.ofNat 16).toUInt8
             |>.push (elem >>> UInt64.ofNat 24).toUInt8
             |>.push (elem >>> UInt64.ofNat 32).toUInt8
             |>.push (elem >>> UInt64.ofNat 40).toUInt8
             |>.push (elem >>> UInt64.ofNat 48).toUInt8
             |>.push (elem >>> UInt64.ofNat 56).toUInt8
            res

open Absorb

def hashFunction (paddingFunction : Nat → ByteArray → SHA3SR) (rate : Nat) (inp : ByteArray) : ByteArray :=
  -- dbg_trace s!"padded result': {paddingFunction (rate / 8) $ inp}"
  -- dbg_trace s!"absorbed result': {Absorb.absorb rate ∘ byteArrayOfSHA3SR ∘ paddingFunction (rate / 8) $ inp}"
  squeeze' rate outputBytes ∘ Absorb.absorb rate ∘ byteArrayOfSHA3SR ∘ paddingFunction (rate / 8) $ inp
  where outputBytes := (1600 - rate) / 16

def KEC : ByteArray → ByteArray := hashFunction paddingKeccak 1088

instance : Coe UInt8 (Fin (2^8)) := ⟨(·.val)⟩
instance : Coe (Fin (2^8)) UInt8 := ⟨(⟨·⟩)⟩
instance : Coe UInt64 (Fin (2^64)) := ⟨(·.val)⟩
instance : Coe (Fin (2^64)) UInt64 := ⟨(⟨·⟩)⟩

instance : Fintype UInt64 := ⟨⟨List.finRange (2^64) |>.map UInt64.mk, sorry⟩, sorry⟩
instance : Fintype UInt8 := ⟨⟨List.finRange (2^8) |>.map UInt8.mk, sorry⟩, sorry⟩
