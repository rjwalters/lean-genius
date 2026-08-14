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

end Erdos85
