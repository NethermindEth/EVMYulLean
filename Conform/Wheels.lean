import Lean.Data.Json
import EvmYul.UInt256
import EvmYul.Wheels

import Mathlib.Data.Multiset.Sort

namespace Lean.Json

def getObjValAs!
  (self : Json) (α : Type) (key : String) [Inhabited α] [FromJson α] : α :=
  match self.getObjValAs? α key with
          | .error _ => panic! s!"Expected the key {key} in the map."
          | .ok pre => pre

/--
Turn non-existance of the key into default initialisation.

This silences ONLY the `property not found:` error.
If the parsing of an existing value fails, we propagate the error.
-/
def getObjValAsOrInitWith? (j : Json) (α : Type) [FromJson α] (k : String) (default : α) : Except String α :=
  match j.getObjVal? k with
    | .error _   => pure default
    | .ok    val => fromJson? val

/--
`getObjValAsOrInit = getObjValAsOrInitWith default` for inhabited types.
-/
def getObjValAsOrInit? (j : Json) (α : Type) [FromJson α] [Inhabited α] (k : String) : Except String α :=
  getObjValAsOrInitWith? j α k default

open Batteries (RBMap) in
def getObjVals?
  (self : Json) (α β : Type) [Ord α] [FromJson α] [FromJson β] : Except String (RBMap α β compare) := do
  let keys ← Array.map Sigma.fst <$> RBNode.toArray <$> self.getObj?
  let mut result : RBMap α β compare := ∅
  for k in keys do
    if let .ok key := FromJson.fromJson? k then
    result := result.insert key (← self.getObjValAs? β k)
  pure result

def fromFile (path : System.FilePath) : IO Json := do
  let .ok json ← Json.parse <$> IO.FS.readFile path | panic! s!"Failed to parse Json at: {path}"
  pure json

end Lean.Json

namespace EvmYul

namespace Conform

def TargetSchedule := "Cancun"

def isHexDigitChar (c : Char) : Bool :=
  '0' <= c && c <= '9' || 'a' <= c.toLower && c.toLower <= 'f'

def Blob := String

instance : Inhabited Blob := inferInstanceAs (Inhabited String)

def Blob.toString : Blob → String := λ blob ↦ blob

instance : ToString Blob := ⟨Blob.toString⟩

def getBlob? (s : String) : Except String Blob :=
  if isHex s then
    let rest := s.drop Hex.length
    if rest.any (not ∘ isHexDigitChar)
    then .error "Blobs must consist of valid hex digits."
    else .ok rest.toLower
  else .error "Input does not begin with 0x."
  where
    Hex := "0x"
    isHex (s : String) := s.startsWith Hex

def getBlob! (s : String) : Blob := getBlob? s |>.toOption.get!

def toHex (c : Char) : Except String Nat :=
  if '0' ≤ c ∧ c ≤ '9'
  then .ok <| c.toString.toNat!
  else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f'
        then let Δ := c.toLower.toNat - 'a'.toNat
            .ok <| 10 + Δ
        else .error s!"Not a hex digit: {c}"

end Conform

section WithConform

open Conform

namespace UInt256

def fromBlob? (blob : Blob) : Except String UInt256 :=
  Fin.ofNat <$> ((·.1) <| blob.foldr (init := (.ok 0, 0)) λ digit (acc, exp) ↦
    (do pure <| (←acc) + (16 ^ exp) * (←Conform.toHex digit), exp + 1))

def fromBlob! (blob : Blob) : UInt256 := fromBlob? blob |>.toOption.get!

end UInt256

namespace Address

def fromBlob? (s : Blob) : Except String Address := (Fin.ofNat ·.toNat) <$> UInt256.fromBlob? s

def fromBlob! (blob : Blob) : Address := fromBlob? blob |>.toOption.get!

end Address

end WithConform

end EvmYul

open EvmYul.Conform (toHex) in
def UInt8.ofHex? : List Char → Except String UInt8
  | [] => pure 0
  | [msb, lsb] => do pure ∘ UInt8.ofNat <| (← toHex msb) * 16 + (← toHex lsb)
  | _ => throw "Need two hex digits for every byte."

def ByteArray.ofBlob (self : EvmYul.Conform.Blob) : Except String ByteArray := do
  let chunks ← self.toList.toChunks 2 |>.mapM UInt8.ofHex?
  pure ⟨chunks.toArray⟩

def computeToList! {α}
                   [LE α] [IsTrans α (· ≤ ·)] [IsAntisymm α (· ≤ ·)] [IsTotal α (· ≤ ·)]
                   [DecidableRel (α := α) (· ≤ ·)] (m : Multiset α) : List α :=
  m.sort (· ≤ ·)
