import FastMemset

import Batteries

import EvmYul.Maps.ByteMap
import EvmYul.UInt256

namespace EvmYul

open Batteries

abbrev Memory := HashMap ℕ ByteArray

-- 2²²⁶ intervals of length 2³⁰
-- Interval i: [i * 2³⁰, (i + 1) * 2³⁰)

def indexInterval (i : ℕ) : ℕ := i / 2^30

def Memory.writeMemory (self : Memory) (source : ByteArray) (addr len : ℕ) : Memory := Id.run do
  let mut self := self
  let mut sourceOffset := 0
  let left₀ := indexInterval addr
  let right₀ := left₀ + 1
  -- dbg_trace s!"W - first inteval: [{left₀} * 2^30, {right₀} * 2^30)"

  -- The first interval is [`left₀` * 2³⁰, `right₀` * 2³⁰),
  -- stored at key `left₀`

  let offset : ℕ := addr - left₀ * 2^30
  let firstLength := right₀ * 2^30 - addr

  let firstDestination := self.find? left₀ |>.getD (ByteArray.zeroes ⟨2^30⟩)
  let firstInterval : ByteArray :=
    ByteArray.copySlice
      source
      (srcOff := sourceOffset)
      (dest := firstDestination)
      (destOff := offset)
      (len := firstLength)

  self := self.insert left₀ firstInterval
  sourceOffset := sourceOffset + firstLength

  let lastAddress := addr + len - 1
  let lastIndex := indexInterval lastAddress
  -- dbg_trace s!"W - right₀: {right₀}"
  -- dbg_trace s!"W - lastIndex: {lastIndex}"

  for left in [right₀ : lastIndex] do
    -- dbg_trace s!"W - inteval: [{left} * 2^30, {left+1} * 2^30)"
    let interval : ByteArray := source.extract sourceOffset (sourceOffset + 2^30)
    self := self.insert left interval
    sourceOffset := sourceOffset + 2^30

  if left₀ < lastIndex then
    let left := lastIndex
    -- dbg_trace s!"W - last inteval: [{left} * 2^30, {left+1} * 2^30)"
    let lastDestination := self.find? left₀ |>.getD (ByteArray.zeroes ⟨2^30⟩)
    let interval : ByteArray :=
      ByteArray.copySlice
        source
        (srcOff := sourceOffset)
        (dest := lastDestination)
        (destOff := 0)
        (len := addr + len - left * 2^30)
    self := self.insert lastIndex interval
  self

def Memory.readMemory (self : Memory) (addr len : ℕ) : ByteArray := Id.run do
  let mut result : ByteArray := .empty
  let left₀ := indexInterval addr
  let right₀ := left₀ + 1
  -- dbg_trace s!"R - first inteval: [{left₀} * 2^30, {right₀} * 2^30)"

  let firstInterval : ByteArray :=
    let len₀ : ℕ := min len (right₀ * 2^30 - addr)
    match self.find? left₀ with
      | none => ByteArray.zeroes ⟨len₀⟩
      | some be =>
        let offset := addr - left₀ * 2^30
        be.extract offset (addr - left₀ * 2^30 + len)

  result := result ++ firstInterval

  let lastAddress := addr + len - 1
  let lastIndex := indexInterval lastAddress

  for left in [right₀ : lastIndex] do
    -- dbg_trace s!"R - inteval: [{left} * 2^30, {left+1} * 2^30)"
    let interval : ByteArray :=
      match self.find? left with
        | none => ByteArray.zeroes ⟨2^30⟩
        | some be => be
    result := result ++ interval

  if left₀ < lastIndex then
    let left := lastIndex
    -- dbg_trace s!"R - last inteval: [{left} * 2^30, {left+1} * 2^30)"
    let interval : ByteArray :=
      let len₀ : ℕ := addr + len - left * 2^30
      match self.find? left with
        | none => ByteArray.zeroes ⟨len₀⟩
        | some be => be.extract 0 len₀
    result := result ++ interval

  result

open Memory

/-- Write one byte at address `2^255` -/
private example :
  ( writeMemory
      .empty
      (source := ⟨#[0x01]⟩)
      (addr := 2^255)
      (len := 1)
  ).readMemory (addr := 2^255) (len := 1) == ByteArray.mk #[0x01]
:= by native_decide

/-- Read uninitialized memory -/
private example : (readMemory .empty (addr := 0) (len := 2^30)).size == 2^30 :=
  by native_decide

-- Write and read long ByteArray

private def powTwoTwentynineBytes1 :=
  ⟨#[0x01]⟩ ++ ByteArray.zeroes ⟨2^29 - 2⟩ ++ ⟨#[0x01]⟩
private def powTwoThirtyBytes2 :=
  ⟨#[0x02]⟩ ++ ByteArray.zeroes ⟨2^30 - 2⟩ ++ ⟨#[0x02]⟩
private def powTwoThirtyBytes3 :=
  ⟨#[0x03]⟩ ++ ByteArray.zeroes ⟨2^30 - 2⟩ ++ ⟨#[0x03]⟩
private def powTwoTwentynineBytes4 :=
  ⟨#[0x04]⟩ ++ ByteArray.zeroes ⟨2^29 - 2⟩ ++ ⟨#[0x04]⟩

private def longByteArray :=
  powTwoTwentynineBytes1
    ++ powTwoThirtyBytes2
    ++ powTwoThirtyBytes3
    ++ powTwoTwentynineBytes4

private def written :=
  writeMemory .empty
    (source := longByteArray)
    (addr := 2^29)
    (len := longByteArray.size)

private def read :=
  readMemory written (addr := 2^29) (len := longByteArray.size)

-- The first element of `longByteArray` was recovered correctly
-- private example :
--   read.get? 0
--     == some 1
-- := by native_decide

-- The last element of `longByteArray` was recovered correctly
-- private example :
--   read.get? (2^29 + 2^30 + 2^30 + 2^29 - 1)
--     == some 4
-- := by native_decide
