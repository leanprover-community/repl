/-
Utilities for working with Lean's string Trie without deep recursion.
We provide iterative insert and matchPrefix to avoid stack overflows for
very long strings (e.g., multi-KB inputs).
-/

import Lean.Data.Trie

namespace REPL.Util.Trie

open Lean
open Lean.Data

namespace Internal

/-- Frames for rebuilding parent nodes after iteratively descending the trie. -/
inductive Frame (α : Type) where
  | node1 (v : Option α) (c : UInt8) : Frame α
  | node (v : Option α) (cs : ByteArray) (ts : Array (Lean.Data.Trie α)) (idx : Nat) : Frame α
  deriving Inhabited

end Internal

/-- Insert or replace the value at key `s` into trie `t` iteratively. -/
def insert {α} (t : Lean.Data.Trie α) (s : String) (val : α) : Lean.Data.Trie α :=
  Id.run do
    let bytes := s.toUTF8
    let n := bytes.size

    -- Build the suffix path from position `start` to the end of `s`.
    let mkSuffixFrom (start : Nat) : Lean.Data.Trie α :=
      Id.run do
        let mut r : Lean.Data.Trie α := Lean.Data.Trie.leaf (some val)
        let mut j : Nat := n
        while j > start do
          let jp := j - 1
          let c := bytes.get! jp
          r := Lean.Data.Trie.node1 none c r
          j := jp
        return r

    -- Descent state
    let mut i : Nat := 0
    let mut cur : Lean.Data.Trie α := t
    let mut stack : Array (Internal.Frame α) := #[]

    -- Iteratively descend until we either finish the key or need to branch/extend.
    let mut done := false
    let mut out := cur
    while !done do
      match cur with
      | Lean.Data.Trie.leaf v =>
        if i < n then
          let c := bytes.get! i
          let suffix := mkSuffixFrom (i + 1)
          out := Lean.Data.Trie.node1 v c suffix
        else
          out := Lean.Data.Trie.leaf (some val)
        done := true
      | Lean.Data.Trie.node1 v c' t' =>
        if i < n then
          let c := bytes.get! i
          if c == c' then
            stack := stack.push (Internal.Frame.node1 v c')
            cur := t'
            i := i + 1
          else
            let suffix := mkSuffixFrom (i + 1)
            out := Lean.Data.Trie.node v (ByteArray.mk #[c, c']) (#[(suffix), t'])
            done := true
        else
          out := Lean.Data.Trie.node1 (some val) c' t'
          done := true
      | Lean.Data.Trie.node v cs ts =>
        if i < n then
          let c := bytes.get! i
          match cs.findIdx? (· == c) with
          | none =>
            let suffix := mkSuffixFrom (i + 1)
            out := Lean.Data.Trie.node v (cs.push c) (ts.push suffix)
            done := true
          | some idx =>
            stack := stack.push (Internal.Frame.node v cs ts idx)
            cur := ts[idx]!
            i := i + 1
        else
          out := Lean.Data.Trie.node (some val) cs ts
          done := true

    -- Rebuild parents from the stack
    let mut res := out
    for frame in stack.reverse do
      match frame with
      | Internal.Frame.node1 v c =>
        res := Lean.Data.Trie.node1 v c res
      | Internal.Frame.node v cs ts idx =>
        res := Lean.Data.Trie.node v cs (ts.set! idx res)
    return res

/--
Find the longest key in the trie that is contained in the given string `s` at position `i`,
and return the associated value, implemented iteratively to avoid stack overflows.

Note the argument order is `(t s i)` to match usages in `Main.lean`.
-/
def matchPrefix {α} (t : Lean.Data.Trie α) (s : String) (i : String.Pos.Raw) : Option α :=
  Id.run do
    let bytes := s.toUTF8
    let n := bytes.size
    let mut idx : Nat := i.byteIdx
    let mut cur : Lean.Data.Trie α := t
    let mut best : Option α := none
    let mut done := false
    while !done do
      match cur with
      | Lean.Data.Trie.leaf v =>
        if v.isSome then
          return v
        else
          return best
      | Lean.Data.Trie.node1 v c' t' =>
        if v.isSome then best := v
        if idx < n then
          let c := bytes.get! idx
          if c == c' then
            idx := idx + 1
            cur := t'
          else
            done := true
        else
          done := true
      | Lean.Data.Trie.node v cs ts =>
        if v.isSome then best := v
        if idx < n then
          let c := bytes.get! idx
          match cs.findIdx? (· == c) with
          | some j =>
            idx := idx + 1
            cur := ts[j]!
          | none =>
            done := true
        else
          done := true
    return best

end REPL.Util.Trie
