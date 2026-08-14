import Proofs.Erdos85DimacsSatBridge
import Proofs.Erdos85OrderFortyNineProfileMasks

namespace Erdos85

open Std.Tactic.BVDecide

/-- Pure parser used by every embedded order-49 LRAT certificate.  Falling
back to the empty proof is fail-safe: the subsequent positive `LRAT.check`
theorem cannot close if parsing fails. -/
def parseOrderFortyNineLratProof (text : String) : Array LRAT.IntAction :=
  match LRAT.parseLRATProof text.toUTF8 with
  | .ok proof => proof
  | .error _ => #[]

/-- Decode the UTF-8-safe 7-bit packing used for embedded binary LRAT files.
Each input byte contributes seven low-order bits to the output stream.  The
expected binary byte count removes the single possible padding bit. -/
partial def unpackOrderFortyNineSevenBit
    (packed : ByteArray) (outputSize : Nat) : ByteArray :=
  go 0 0 0 (ByteArray.emptyWithCapacity outputSize)
where
  go (i : Nat) (bits acc : UInt64) (output : ByteArray) : ByteArray :=
    if output.size = outputSize then
      output
    else if h : i < packed.size then
      let acc := acc ||| (packed[i].toUInt64 <<< bits)
      let bits := bits + 7
      if bits >= 8 then
        go (i + 1) (bits - 8) (acc >>> 8) (output.push acc.toUInt8)
      else
        go (i + 1) bits acc output
    else
      output

/-- Parse a native binary LRAT certificate embedded through `include_str`
after reversible 7-bit packing.  A truncated payload fails closed to the empty
proof, whose later positive `LRAT.check` obligation cannot close. -/
def parsePackedOrderFortyNineLratProof
    (packed : String) (binaryBytes : Nat) : Array LRAT.IntAction :=
  let binary := unpackOrderFortyNineSevenBit packed.toUTF8 binaryBytes
  if binary.size != binaryBytes then
    #[]
  else
    match LRAT.parseLRATProof binary with
    | .ok proof => proof
    | .error _ => #[]

private def readOrderFortyNineUInt32LE
    (data : ByteArray) (pos : Nat) : Option UInt32 := do
  if pos + 4 > data.size then none else
  return (data.get! pos).toUInt32 |||
    (data.get! (pos + 1)).toUInt32 <<< 8 |||
    (data.get! (pos + 2)).toUInt32 <<< 16 |||
    (data.get! (pos + 3)).toUInt32 <<< 24

private partial def readOrderFortyNineLz4Length
    (data : ByteArray) (stop pos total : Nat) : Option (Nat × Nat) := do
  if pos >= stop then none else
  let byte := data.get! pos |>.toNat
  let total := total + byte
  if byte = 255 then
    readOrderFortyNineLz4Length data stop (pos + 1) total
  else
    return (total, pos + 1)

private partial def copyOrderFortyNineLz4Match
    (maximum offset count : Nat) (output : ByteArray) : Option ByteArray := do
  if count = 0 then return output
  if output.size >= maximum || offset = 0 || offset > output.size then none else
  let output := output.push (output.get! (output.size - offset))
  copyOrderFortyNineLz4Match maximum offset (count - 1) output

private partial def decodeOrderFortyNineLz4Block
    (data : ByteArray) (start stop maximum : Nat)
    (initial : ByteArray) : Option ByteArray :=
  go start initial
where
  go (pos : Nat) (output : ByteArray) : Option ByteArray := do
    if pos = stop then return output
    if pos > stop then none else
    let token := data.get! pos
    let literalNibble := (token >>> 4).toNat
    let (literalLength, pos) ←
      if literalNibble = 15 then
        readOrderFortyNineLz4Length data stop (pos + 1) 15
      else
        some (literalNibble, pos + 1)
    if pos + literalLength > stop || output.size + literalLength > maximum then
      none
    else
      let output := output.append (data.extract pos (pos + literalLength))
      let pos := pos + literalLength
      if pos = stop then return output
      if pos + 2 > stop then none else
      let offset := (data.get! pos).toNat + 256 * (data.get! (pos + 1)).toNat
      let matchNibble := (token &&& 15).toNat
      let (matchLength, pos) ←
        if matchNibble = 15 then
          readOrderFortyNineLz4Length data stop (pos + 2) 19
        else
          some (matchNibble + 4, pos + 2)
      if output.size + matchLength > maximum then none else
      let output ← copyOrderFortyNineLz4Match maximum offset matchLength output
      go pos output

/-- Decode one ordinary LZ4 frame, with output bounded by and required to equal
`expectedSize`.  Header and content checksums are skipped: certificate integrity
is supplied by the subsequent pure LRAT parse and positive checker theorem, and
operational tooling additionally records SHA-256 provenance. -/
partial def decodeOrderFortyNineLz4Frame
    (data : ByteArray) (expectedSize : Nat) : Option ByteArray := do
  if data.size < 7 then none else
  if readOrderFortyNineUInt32LE data 0 != some 0x184D2204 then none else
  let flags := data.get! 4
  if flags &&& 0xC0 != 0x40 || flags &&& 0x02 != 0 then none else
  let hasBlockChecksum := flags &&& 0x10 != 0
  let hasContentSize := flags &&& 0x08 != 0
  let hasContentChecksum := flags &&& 0x04 != 0
  let hasDictionary := flags &&& 0x01 != 0
  let headerBytes := 2 + (if hasContentSize then 8 else 0) +
    (if hasDictionary then 4 else 0) + 1
  let start := 4 + headerBytes
  if start > data.size then none else
  blocks start (ByteArray.emptyWithCapacity expectedSize) hasBlockChecksum
    hasContentChecksum
where
  blocks (pos : Nat) (output : ByteArray)
      (hasBlockChecksum hasContentChecksum : Bool) : Option ByteArray := do
    let rawSize ← readOrderFortyNineUInt32LE data pos
    let pos := pos + 4
    if rawSize = 0 then
      let endPos := pos + (if hasContentChecksum then 4 else 0)
      if endPos = data.size && output.size = expectedSize then return output else none
    else
      let uncompressed := rawSize &&& 0x80000000 != 0
      let blockSize := (rawSize &&& 0x7fffffff).toNat
      if pos + blockSize > data.size then none else
      let output ←
        if uncompressed then
          if output.size + blockSize > expectedSize then none else
          some (output.append (data.extract pos (pos + blockSize)))
        else
          decodeOrderFortyNineLz4Block data pos (pos + blockSize) expectedSize output
      let pos := pos + blockSize + (if hasBlockChecksum then 4 else 0)
      blocks pos output hasBlockChecksum hasContentChecksum

/-- Parse a 7-bit-packed LZ4 frame containing native binary LRAT.  Every
decode or parse error fails closed to the empty proof. -/
def parsePackedLz4OrderFortyNineLratProof
    (packed : String) (frameBytes binaryBytes : Nat) : Array LRAT.IntAction :=
  let frame := unpackOrderFortyNineSevenBit packed.toUTF8 frameBytes
  if frame.size != frameBytes then
    #[]
  else
    match decodeOrderFortyNineLz4Frame frame binaryBytes with
    | none => #[]
    | some binary =>
        match LRAT.parseLRATProof binary with
        | .ok proof => proof
        | .error _ => #[]

end Erdos85
