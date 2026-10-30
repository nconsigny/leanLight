import LeanLight.El.Rlp
import LeanLight.Base.Common

/-!
# Block header specification

A block header is the RLP list of its fields, and the block hash is Keccak-256 of that
encoding (Yellow Paper, section 4.3, with the fields each fork since London appends:
EIP-1559, EIP-4895, EIP-4844, EIP-4788, EIP-7685, EIP-7928, EIP-7843). Forks only append
fields, so the number of fields names the fork (`forks`): 16 London, 17 Shanghai, 20 Cancun,
21 Prague (and Osaka, which adds none), 23 Amsterdam. Any other count is refused.

Field `i` has a shape (`fits`): a byte array of exactly 32 bytes (the hashes and roots), 20
(the coinbase), 256 (the bloom) or 8 (the nonce); at most 32 bytes (extra data); or a scalar
without a leading zero byte, of at most 8 bytes (number, gas limit, gas used, timestamp, blob
gas used, excess blob gas, slot number), 16 (the base fee, read as a `u128`) or 32 (the
difficulty). `shapes` lists them, field by field (`shapes_eq`).

`decode` is what `lkd_verified::header::decode` computes, over `Spec.RlpDecode`'s positional
reading. Its theorem `decode_iff` says what it accepts, in terms an outside reviewer can check
without reading it: exactly the canonical RLP list of a known fork's fields, each of its shape,
and nothing else. So `verify_hash`: a header `verify` accepts against a block hash `H` is a
known fork's field list whose `keccak(rlp(fields))` is `H`, and the values read are those
fields'.
-/

namespace LeanLight.Spec.Header

open LeanLight.Spec.Rlp LeanLight.Spec.RlpDecode

/-- The field counts of the forks known: London, Shanghai, Cancun, Prague and Osaka,
Amsterdam. -/
def forks : List Nat := [16, 17, 20, 21, 23]

/-- Whether field `i` is a scalar: difficulty, number, gas limit, gas used, timestamp, base
fee, blob gas used, excess blob gas, slot number. -/
def isScalar (i : Nat) : Bool :=
  i = 7 || i = 8 || i = 9 || i = 10 || i = 11 || i = 15 || i = 17 || i = 18 || i = 22

/-- Field `i`'s length: exact for a byte array, greatest for a scalar or the extra data. -/
def maxLen (i : Nat) : Nat :=
  if i = 2 then 20
  else if i = 6 then 256
  else if i = 14 || i = 8 || i = 9 || i = 10 || i = 11 || i = 17 || i = 18 || i = 22 then 8
  else if i = 15 then 16
  else 32

/-- Whether `b` has the shape of field `i`. -/
def fits (i : Nat) (b : Bytes) : Bool :=
  if isScalar i then b.length ≤ maxLen i && (b.length = 0 || b[0]?.getD 0 != 0)
  else if i = 12 then b.length ≤ maxLen i
  else b.length = maxLen i

/-- A field's shape: exactly `n` bytes, at most `n` bytes, or a scalar of at most `n` bytes with
no leading zero byte. -/
inductive Shape where
  | exact (n : Nat)
  | atMost (n : Nat)
  | scalar (n : Nat)
  deriving DecidableEq

/-- Field `i`'s shape, as the three cases of `fits` read it. -/
def shapeOf (i : Nat) : Shape :=
  if isScalar i then .scalar (maxLen i)
  else if i = 12 then .atMost (maxLen i)
  else .exact (maxLen i)

/-- The shapes, field by field, as a reviewer reads them off the Yellow Paper and the EIPs:
`(name, shape)`. -/
def shapes : List (String × Shape) :=
  [("parentHash", .exact 32), ("ommersHash", .exact 32), ("coinbase", .exact 20),
   ("stateRoot", .exact 32), ("transactionsRoot", .exact 32), ("receiptsRoot", .exact 32),
   ("logsBloom", .exact 256), ("difficulty", .scalar 32), ("number", .scalar 8),
   ("gasLimit", .scalar 8), ("gasUsed", .scalar 8), ("timestamp", .scalar 8),
   ("extraData", .atMost 32), ("mixHash", .exact 32), ("nonce", .exact 8),
   ("baseFeePerGas", .scalar 16), ("withdrawalsRoot", .exact 32), ("blobGasUsed", .scalar 8),
   ("excessBlobGas", .scalar 8), ("parentBeaconBlockRoot", .exact 32), ("requestsHash", .exact 32),
   ("blockAccessListHash", .exact 32), ("slotNumber", .scalar 8)]

/-- `isScalar`, `maxLen` and `fits`' bound for field 12 are the table `shapes`. -/
theorem shapes_eq : (List.range 23).map shapeOf = shapes.map (·.2) := by decide

/-- The fields of a header the wallet reads. -/
structure Header where
  /-- The number of fields, which names the fork (`forks`). -/
  fields : Nat
  parentHash : Bytes
  stateRoot : Bytes
  number : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  baseFee : Nat
deriving DecidableEq, Repr

/-- Field `i` of a field list. -/
def field (fs : List Bytes) (i : Nat) : Bytes := fs[i]?.getD []

/-- The header a field list reads as: field 0 the parent hash, 3 the state root, 8 to 11 the
number, gas limit, gas used and timestamp, 15 the base fee. -/
def headerOf (fs : List Bytes) : Header :=
  { fields := fs.length, parentHash := field fs 0, stateRoot := field fs 3,
    number := beValue (field fs 8), gasLimit := beValue (field fs 9),
    gasUsed := beValue (field fs 10), timestamp := beValue (field fs 11),
    baseFee := beValue (field fs 15) }

/-- The header a field list is: `none` unless its length names a known fork and every field
has its shape. -/
def ofFields (fs : List Bytes) : Option Header :=
  if fs.length ∈ forks ∧ ∀ i < fs.length, fits i (field fs i) then some (headerOf fs) else none

/-- The payload of an item found in `bs`. -/
def payloadOf (bs : Bytes) (it : Span) : Bytes := window bs it.start it.stop

/-- The header `bs` encodes, read as `lkd_verified::header::decode` reads it: one canonical
list spanning `bs`, whose items are byte arrays forming a known fork's field list. -/
def decode (bs : Bytes) : Option Header :=
  match itemAt bs 0 bs.length with
  | none => none
  | some top =>
    if top.list = true ∧ top.stop = bs.length then
      match itemsAt bs top.start top.stop with
      | none => none
      | some its =>
        if its.all (fun it => !it.list) then ofFields (its.map (payloadOf bs)) else none
    else none

/-- The canonical RLP encoding of a known fork's header field list `fs`, or `none` unless
`ofFields fs` accepts `fs` (`encodeFields_isSome`, `decode_encodeFields`). -/
def encodeFields (fs : List Bytes) : Option Bytes :=
  if fs.length ∈ forks ∧ ∀ i < fs.length, fits i (field fs i) then
    encodeTree (.branch (fs.map .leaf))
  else none

export Common (keccak)

/-- `decode`, when Keccak-256 of the bytes is the block hash `hash`:
`lkd_verified::header::verify`. -/
def verify (bs hash : Bytes) : Option Header :=
  if keccak bs = hash then decode bs else none

/-! ## What `decode` accepts -/

theorem window_all (bs : Bytes) : window bs 0 bs.length = bs := by
  simp [window]

theorem window_drop (bs : Bytes) (p k stop : Nat) :
    window bs (p + k) stop = (window bs p stop).drop k := by
  simp [window, List.drop_drop]

/-- Leaves whose encodings are the given spans encode to those spans one after the other. -/
theorem encodeTrees_spans (bs : Bytes) : ∀ (l : List Span),
    (∀ it ∈ l, encodeBytes (payloadOf bs it) = some (window bs it.pos it.stop)) →
    encodeTrees (l.map fun it => .leaf (payloadOf bs it)) =
      some (l.map fun it => window bs it.pos it.stop).flatten
  | [], _ => rfl
  | it :: rest, h => by
    simp only [List.map_cons, List.flatten_cons]
    exact encodeTrees_cons (h it (by simp))
      (encodeTrees_spans bs rest (fun x hx => h x (by simp [hx])))

/-- The items of a payload made of encoded byte arrays are those byte arrays. -/
theorem itemsF_leaves (bs : Bytes) {stop : Nat} (hs : stop ≤ bs.length) : ∀ (fs : List Bytes)
    (p : Nat) {s : Bytes}, encodeTrees (fs.map .leaf) = some s → window bs p stop = s →
    ∃ its, itemsF (stop - p + 1) bs p stop = some its ∧ its.map (payloadOf bs) = fs ∧
      ∀ it ∈ its, it.list = false
  | [], p, s, h, hw => by
    simp only [List.map_nil, encodeTrees, Option.some.injEq] at h
    subst h
    have := congrArg List.length hw
    rw [window_length hs] at this
    simp only [List.length_nil] at this
    refine ⟨[], ?_, rfl, by simp⟩
    rw [show stop - p + 1 = 0 + 1 by omega]
    simp only [itemsF]
    rw [if_neg (by omega)]
  | f :: fs, p, s, h, hw => by
    simp only [List.map_cons, encodeTrees] at h
    cases he : encodeTree (.leaf f) with
    | none => simp [he] at h
    | some e =>
      cases hr : encodeTrees (fs.map .leaf) with
      | none => simp [he, hr] at h
      | some s' =>
        simp only [he, hr, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        have he' : encodeItem false f = some e := he
        have hne : e ≠ [] := encodeTree_ne_nil he
        have hlen := List.length_pos_iff.mpr hne
        have hwl := congrArg List.length hw
        rw [window_length hs, List.length_append] at hwl
        have hi := itemAt_encodeItem he' hs hw
        obtain ⟨its, h1, h2, h3⟩ := itemsF_leaves bs hs fs (p + e.length) hr
          (by rw [window_drop, hw, List.drop_left' rfl])
        refine ⟨⟨false, p, p + (e.length - f.length), p + e.length⟩ :: its, ?_, ?_, ?_⟩
        · rw [itemsF_succ (by omega) hi]
          simp only
          rw [show stop - (p + e.length) + 1 = stop - (p + e.length) + 1 from rfl, h1]
          rfl
        · simp only [List.map_cons, h2, List.cons.injEq, and_true]
          have hsuf := encodeItem_suffix he'
          simp only [payloadOf]
          rw [show p + (e.length - f.length) = p + (e.length - f.length) from rfl,
            ← window_window bs (e := stop) (by omega), hw]
          simp only [window]
          rw [List.take_left' rfl, hsuf.2]
        · intro it hit
          simp only [List.mem_cons] at hit
          rcases hit with rfl | hit
          · rfl
          · exact h3 it hit

/-- What `decode` accepts is exactly the canonical RLP list of a known fork's fields, each of
its shape; and the header read is that field list's. -/
theorem decode_iff (bs : Bytes) (h : Header) :
    decode bs = some h ↔
      ∃ fs, ofFields fs = some h ∧ encodeTree (.branch (fs.map .leaf)) = some bs := by
  constructor
  · intro hd
    unfold decode at hd
    split at hd
    · contradiction
    · rename_i top htop
      split at hd
      · rename_i hc
        split at hd
        · contradiction
        · rename_i its hits
          split at hd
          · rename_i hall
            refine ⟨its.map (payloadOf bs), hd, ?_⟩
            obtain ⟨-, -, -, -, -, -, -, htopenc⟩ := itemAt_span htop
            obtain ⟨hspans, hflat⟩ := itemsAt_spans hits
            have hleaf : ∀ it ∈ its, encodeBytes (payloadOf bs it) = some (window bs it.pos it.stop) := by
              intro it hit
              obtain ⟨-, -, hat⟩ := hspans it hit
              obtain ⟨hp, -, -, -, -, -, -, henc⟩ := itemAt_span hat
              have hl : it.list = false := by
                have := List.all_eq_true.mp hall it hit
                simpa using this
              rw [hl] at henc
              rw [hp] at henc
              exact henc
            simp only [encodeTree, List.map_map]
            have := encodeTrees_spans bs its hleaf
            simp only [Function.comp_def]
            rw [this, hflat, Option.bind_some]
            rw [hc.1, hc.2, window_all] at htopenc
            rw [hc.2]
            exact htopenc
          · contradiction
      · contradiction
  · rintro ⟨fs, hof, henc⟩
    simp only [encodeTree] at henc
    cases hs : encodeTrees (fs.map .leaf) with
    | none => simp [hs] at henc
    | some s =>
      rw [hs, Option.bind_some] at henc
      have henc' : encodeItem true s = some bs := henc
      have hsuf := encodeItem_suffix henc'
      have htop := itemAt_encodeItem henc' (Nat.le_refl _) (r := []) (by rw [window_all, List.append_nil])
      unfold decode
      rw [htop]
      simp only [true_and]
      rw [if_pos (by omega)]
      have hw : window bs (0 + (bs.length - s.length)) bs.length = s := by
        rw [window_drop, window_all, hsuf.2]
      obtain ⟨its, h1, h2, h3⟩ := itemsF_leaves bs (Nat.le_refl _) fs _ hs hw
      have hitems : itemsAt bs (0 + (bs.length - s.length)) (0 + bs.length) = some its := by
        unfold itemsAt
        rw [if_pos ⟨by omega, by omega⟩, show 0 + bs.length - (0 + (bs.length - s.length)) + 1 =
          bs.length - (0 + (bs.length - s.length)) + 1 by omega]
        rw [show 0 + bs.length = bs.length by omega]
        exact h1
      rw [hitems]
      simp only
      rw [if_pos (List.all_eq_true.mpr fun it hit => by simp [h3 it hit]), h2]
      exact hof

/-- What the header read says about the field list: its length names a known fork, every field
has its shape, and the header is the fields' (`headerOf`). -/
theorem ofFields_some {fs : List Bytes} {h : Header} (hof : ofFields fs = some h) :
    fs.length ∈ forks ∧ (∀ i < fs.length, fits i (field fs i)) ∧ h = headerOf fs := by
  unfold ofFields at hof
  split at hof
  · rename_i hc
    cases hof
    exact ⟨hc.1, hc.2, rfl⟩
  · contradiction

/-- The block hash is `keccak(rlp(fields))` of a known fork's field list: a header `verify`
accepts against `hash` is such a list, and the values read are its fields'. -/
theorem verify_hash {bs hash : Bytes} {h : Header} (hv : verify bs hash = some h) :
    ∃ fs e, ofFields fs = some h ∧ encodeTree (.branch (fs.map .leaf)) = some e ∧
      keccak e = hash := by
  unfold verify at hv
  split at hv
  · rename_i hk
    obtain ⟨fs, hof, henc⟩ := (decode_iff bs h).mp hv
    exact ⟨fs, bs, hof, henc, hk⟩
  · contradiction

/-- Every header of a known fork is read, from its canonical encoding, against its hash. -/
theorem verify_encoding {fs : List Bytes} {h : Header} {e : Bytes} (hof : ofFields fs = some h)
    (henc : encodeTree (.branch (fs.map .leaf)) = some e) : verify e (keccak e) = some h := by
  unfold verify
  rw [if_pos rfl]
  exact (decode_iff e h).mpr ⟨fs, hof, henc⟩

theorem fits_length_le {i : Nat} {b : Bytes} (hf : fits i b = true) : b.length ≤ 256 := by
  have hm : maxLen i ≤ 256 := by
    unfold maxLen
    split
    · omega
    · split
      · omega
      · split
        · omega
        · split <;> omega
  unfold fits at hf
  split at hf
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hf; omega
  · split at hf
    · simp only [decide_eq_true_eq] at hf; omega
    · simp only [decide_eq_true_eq] at hf; omega

private theorem encodeBytes_total {b : Bytes} (hb : b.length < 2 ^ 64) :
    ∃ e, encodeBytes b = some e := by
  have _ := hb
  unfold encodeBytes
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · simp

private theorem encodeTrees_leaves_total : ∀ (fs : List Bytes),
    (∀ f ∈ fs, f.length ≤ 256) → ∃ s, encodeTrees (fs.map .leaf) = some s ∧ s.length ≤ 265 * fs.length
  | [], _ => ⟨[], rfl, by simp⟩
  | f :: fs, h => by
    have hf := h f (by simp)
    obtain ⟨e, he⟩ := encodeBytes_total (b := f) (by omega)
    obtain ⟨s, hs, hsl⟩ := encodeTrees_leaves_total fs (fun g hg => h g (by simp [hg]))
    have hel := encodeBytes_length_le he
    refine ⟨e ++ s, encodeTrees_cons he hs, ?_⟩
    simp only [List.length_append, List.length_cons]
    omega

/-- Every field list `ofFields` accepts has a canonical RLP encoding (`encodeFields`). -/
theorem encodeFields_isSome {fs : List Bytes} {h : Header} (hof : ofFields fs = some h) :
    ∃ bs, encodeFields fs = some bs := by
  obtain ⟨hfork, hfits, -⟩ := ofFields_some hof
  have hlen : fs.length ≤ 23 := by
    simp only [forks, List.mem_cons, List.not_mem_nil, or_false] at hfork
    omega
  have hall : ∀ f ∈ fs, f.length ≤ 256 := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
    have hfi : field fs i = fs[i] := by simp [field, hi]
    exact fits_length_le (hfi ▸ hfits i hi)
  obtain ⟨s, hs, hsl⟩ := encodeTrees_leaves_total fs hall
  have hlist : ∃ bs, encodeList s = some bs := by
    unfold encodeList
    split
    · exact ⟨_, rfl⟩
    · have hs64 : s.length < 2 ^ 64 := by omega
      simp [hs64]
  obtain ⟨bs, hbs⟩ := hlist
  refine ⟨bs, ?_⟩
  unfold encodeFields
  rw [ite_eq_left ⟨hfork, hfits⟩]
  simp [encodeTree, hs, hbs]

/-- `encodeFields` succeeds only on a valid fork field list, and `decode` reads its header back. -/
theorem decode_encodeFields {fs : List Bytes} {bs : Bytes} (he : encodeFields fs = some bs) :
    decode bs = some (headerOf fs) ∧ ofFields fs = some (headerOf fs) := by
  unfold encodeFields at he
  split at he
  · rename_i hc
    have hof : ofFields fs = some (headerOf fs) := by
      unfold ofFields
      rw [ite_eq_left hc]
    exact ⟨(decode_iff bs (headerOf fs)).mpr ⟨fs, hof, he⟩, hof⟩
  · cases he

/-- Characterisation of `encodeFields`: `ofFields` accepts `fs` and `bs` is the RLP encoding of
its leaf list. -/
theorem encodeFields_iff (fs : List Bytes) (bs : Bytes) :
    encodeFields fs = some bs ↔
      ofFields fs = some (headerOf fs) ∧ encodeTree (.branch (fs.map .leaf)) = some bs := by
  unfold encodeFields ofFields
  split <;> simp

/-! ## Over a `ByteArray`: what runs

`verifyB` is `verify` over a `ByteArray` (`verifyB_eq`): Keccak-256 of the bytes as they are,
and the fields found by `itemAtB` and `itemsAtB` in place, each copied once. -/

open LeanLight.Lc.Bytes (slice slice_eq size_eq)

/-- The payload of an item found in `bs`, copied. -/
def payloadOfB (bs : ByteArray) (it : Span) : Bytes := slice bs it.start it.stop

/-- `decode`, over a `ByteArray` (`decodeB_eq`). -/
def decodeB (bs : ByteArray) : Option Header :=
  match itemAtB bs 0 bs.size with
  | none => none
  | some top =>
    if top.list = true ∧ top.stop = bs.size then
      match itemsAtB bs top.start top.stop with
      | none => none
      | some its =>
        if its.all (fun it => !it.list) then ofFields (its.map (payloadOfB bs)) else none
    else none

/-- Keccak-256 of a `ByteArray`, as a byte list. -/
def keccakB (bs : ByteArray) : Bytes := (Spec.Keccak.keccak256 bs).data.toList

/-- `verify`, over a `ByteArray` (`verifyB_eq`): what the light client runs. -/
def verifyB (bs : ByteArray) (hash : Bytes) : Option Header :=
  if keccakB bs = hash then decodeB bs else none

theorem payloadOfB_eq (bs : ByteArray) (it : Span) :
    payloadOfB bs it = payloadOf bs.data.toList it :=
  slice_eq bs it.start it.stop

theorem keccakB_eq (bs : ByteArray) : keccakB bs = keccak bs.data.toList := rfl

theorem decodeB_eq (bs : ByteArray) : decodeB bs = decode bs.data.toList := by
  have hp : payloadOfB bs = payloadOf bs.data.toList := funext (payloadOfB_eq bs)
  simp only [decodeB, decode, itemAtB_eq, itemsAtB_eq, hp, size_eq]

theorem verifyB_eq (bs : ByteArray) (hash : Bytes) :
    verifyB bs hash = verify bs.data.toList hash := by
  simp only [verifyB, verify, keccakB_eq, decodeB_eq]

/-- `encodeFields`, as a `ByteArray` (`decodeB_encodeFieldsB`). -/
def encodeFieldsB (fs : List Bytes) : Option ByteArray :=
  (encodeFields fs).map fun bs => ⟨bs.toArray⟩

theorem decodeB_encodeFieldsB {fs : List Bytes} {bs : ByteArray}
    (he : encodeFieldsB fs = some bs) :
    decodeB bs = some (headerOf fs) ∧ ofFields fs = some (headerOf fs) := by
  unfold encodeFieldsB at he
  cases h : encodeFields fs with
  | none => simp [h] at he
  | some l =>
    simp only [h, Option.map_some, Option.some.injEq] at he
    subst he
    rw [decodeB_eq]
    simpa using decode_encodeFields h

end LeanLight.Spec.Header
