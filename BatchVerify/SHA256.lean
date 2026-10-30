/-!
# SHA-256 and BIP340's byte-level helpers

A plain implementation of SHA-256 (FIPS 180-4) and the tagged hashes of
BIP340, used only to run the BIP340 test vectors against the model
(`BatchVerify.TestVectors`). No proof depends on this file.
-/

namespace BatchVerify.SHA256

/-- The SHA-256 round constants. -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- SHA-256 of a byte array. -/
def hash (msg : ByteArray) : ByteArray := Id.run do
  let mut data := msg.push 0x80
  while data.size % 64 != 56 do
    data := data.push 0
  let bits := msg.size * 8
  for i in [0:8] do
    data := data.push (bits >>> (8 * (7 - i))).toUInt8
  let mut h : Array UInt32 :=
    #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for blk in [0:data.size / 64] do
    let mut w : Array UInt32 := #[]
    for t in [0:16] do
      let o := blk * 64 + 4 * t
      w := w.push ((data[o]!.toUInt32 <<< 24) ||| (data[o + 1]!.toUInt32 <<< 16) |||
        (data[o + 2]!.toUInt32 <<< 8) ||| data[o + 3]!.toUInt32)
    for t in [16:64] do
      let s0 := rotr w[t - 15]! 7 ^^^ rotr w[t - 15]! 18 ^^^ (w[t - 15]! >>> 3)
      let s1 := rotr w[t - 2]! 17 ^^^ rotr w[t - 2]! 19 ^^^ (w[t - 2]! >>> 10)
      w := w.push (w[t - 16]! + s0 + w[t - 7]! + s1)
    let mut a := h[0]!
    let mut b := h[1]!
    let mut c := h[2]!
    let mut d := h[3]!
    let mut e := h[4]!
    let mut f := h[5]!
    let mut g := h[6]!
    let mut hh := h[7]!
    for t in [0:64] do
      let t1 := hh + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) +
        K[t]! + w[t]!
      let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
      hh := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g,
      h[7]! + hh]
  let mut out := ByteArray.empty
  for x in h do
    out := out.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8
      |>.push x.toUInt8
  return out

/-- BIP340 `hash_tag(x) = SHA256(SHA256(tag) ‖ SHA256(tag) ‖ x)`. -/
def taggedHash (tag : String) (x : ByteArray) : ByteArray :=
  let t := hash tag.toUTF8
  hash (t ++ t ++ x)

/-- Big-endian bytes to a natural number (BIP340 `int`). -/
def toNat (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- A natural number as 32 big-endian bytes (BIP340 `bytes`). -/
def bytes32 (x : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:32] do
    out := out.push (x >>> (8 * (31 - i))).toUInt8
  return out

/-- Parse a hex string (no prefix) into bytes. -/
def ofHex (s : String) : ByteArray := Id.run do
  let digit (c : Char) : Nat :=
    if c.isDigit then c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
    else c.toNat - 'A'.toNat + 10
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:cs.size / 2] do
    out := out.push (digit cs[2 * i]! * 16 + digit cs[2 * i + 1]!).toUInt8
  return out

-- FIPS 180-4 examples.
#guard hash "abc".toUTF8 =
  ofHex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hash ByteArray.empty =
  ofHex "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8 =
  ofHex "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"

end BatchVerify.SHA256
