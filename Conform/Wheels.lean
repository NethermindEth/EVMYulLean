import Lean.Data.Json
import EvmYul.UInt256
import EvmYul.Wheels

import Mathlib.Data.Multiset.Sort

namespace Lean.Json

def getObjValAs!
  (self : Json) (α : Type) (key : String) [Inhabited α] [FromJson α] : α :=
  match self.getObjValAs? α key with
          | .error _ => panic! s!"Expected the key {key} in the map."
          | .ok pre  => pre

/--
Turn non-existance of the key into default initialisation.

This silences ONLY the `property not found:` error.
If the parsing of an existing value fails, we propagate the error.
-/
def getObjValAsD (j : Json) (α : Type) [FromJson α] (k : String) (D : α) : Except String α :=
  match j.getObjVal? k with
    | .error _   => pure D
    | .ok    val => fromJson? val

/--
`getObjValAsD! = getObjValAsD default` for inhabited types.
-/
def getObjValAsD! (j : Json) (α : Type) [FromJson α] [Inhabited α] (k : String) : Except String α :=
  getObjValAsD j α k default

def getObjVals?
  (self : Json) (α β : Type) [Ord α] [FromJson α] [FromJson β] : Except String (Batteries.RBMap α β compare) := do
  let keys ← Array.map Sigma.fst <$> RBNode.toArray <$> self.getObj?
  let mut result : Batteries.RBMap α β compare := ∅
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

end Conform

section WithConform

open Conform

namespace UInt256

def fromBlob? (blob : Blob) : Except String UInt256 :=
  .ofNat <$> ((·.1) <| blob.foldr (init := (.ok 0, 0)) λ digit (acc, exp) ↦
    (do pure <| (←acc) + (16 ^ exp) * (←cToHex? digit), exp + 1))

def fromBlob! (blob : Blob) : UInt256 := fromBlob? blob |>.toOption.get!

end UInt256

def Nat.fromBlob? (blob : Blob) : Except String ℕ :=
  ((·.1) <| blob.foldr (init := (.ok 0, 0)) λ digit (acc, exp) ↦
    (do pure <| (←acc) + (16 ^ exp) * (←cToHex? digit), exp + 1))

namespace AccountAddress

def fromBlob? (s : Blob) : Except String AccountAddress := (Fin.ofNat ·.toNat) <$> UInt256.fromBlob? s

def fromBlob! (blob : Blob) : AccountAddress := fromBlob? blob |>.toOption.get!

end AccountAddress

end WithConform

namespace DebuggingAndProfiling

section

set_option autoImplicit true

unsafe def report [Inhabited β] (s : String) (f : α → β) (a : α) : β :=
  dbg_trace s!"BEGIN: {s}"
  let res := timeit s!"The function '{s}' took:" <| pure (f a)
  dbg_trace s!"END: {s}"
  unsafeIO res |>.toOption.get!

def testJsonParser (α : Type) [Repr α] [Lean.FromJson α] (s : String) : String :=
  match Lean.FromJson.fromJson? (α := α) <| (Lean.Json.parse s).toOption.getD Lean.Json.null with
    | .error e  => s!"err: {e}"
    | .ok    ok => s!"ok: {repr ok}"

end

end DebuggingAndProfiling

end EvmYul

def computeToList! {α}
                   [LE α] [IsTrans α (· ≤ ·)] [IsAntisymm α (· ≤ ·)] [IsTotal α (· ≤ ·)]
                   [DecidableRel (α := α) (· ≤ ·)] (m : Multiset α) : List α :=
  m.sort (· ≤ ·)

def Batteries.RBMap.partition {α β : Type} {cmp : α → α → Ordering}
  (t : Batteries.RBMap α β cmp) (p : α → β → Bool) : Batteries.RBMap α β cmp × Batteries.RBMap α β cmp :=
  (t.filter p, t.filter (λ k v ↦ not (p k v)))

namespace Std

namespace HashSet

def diff {α : Type} [DecidableEq α] [Hashable α] (a b : HashSet α) : HashSet α := Id.run do
  let mut res := a
  for elem in b do
    res := res.erase elem
  return res

end HashSet

end Std
