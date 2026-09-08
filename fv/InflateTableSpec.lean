/-
  Memory-safety specification for `inflate_table` (inftrees.c:46-311).

  This file defines:
    * the concrete values of the four static tables (`lbase`/`lext`/`dbase`/`dext`),
    * the footprint layout (assumption A1 of fv/memory-safety.md),
    * the minimal assumption set A2-A5, each justified by a concrete
      counterexample in fv/memory-safety.md — nothing here is assumed
      "because the caller happens to guarantee it",
    * the separation-logic `FunSpec` for `f_inflate_table`.

  Design notes
  ------------
  * The spec is a *safety* spec: the postcondition returns every resource but
    pins almost no contents (the planned functional strengthening — `*table`
    advanced by `used`, root-table well-formedness — is recorded as comments).
    Because the CCLib triple is total-correctness, proving `SatisfiesAt` at
    this weak postcondition already IS the memory-safety theorem: the
    execution it exhibits contains no stuck (= faulting) step.
  * There is deliberately NO assumption on the initial `*bits` value for
    LENS/DISTS (the code clamps root into [min,max] ⊆ [1,15] at
    inftrees.c:122-137), and NO Kraft/ENOUGH combinatorial hypothesis
    (the runtime checks at inftrees.c:216-218 and 284-287 guard every table
    write; the exhaustive-search constants matter only for functional
    correctness).
  * The four static tables are readonly globals of the generated program
    (InftreesAST.lean: v_lbase/v_lext/v_dbase/v_dext).  Their contents enter
    the precondition as owned read-only resources, and the theorem takes
    `Genv.findSymbol` hypotheses tying the identifiers to their blocks —
    exactly what CompCert's `init_mem` establishes.
-/
import InftreesAST

open CC CC.HProp
open Inftrees

namespace InflateTable

/-! ## Constants (inftrees.h / inftrees.c) -/

/-- `enum codetype` — CODES = 0, LENS = 1, DISTS = 2 (matches the `Sswitch`
    labels in the generated AST). -/
def CODES : _root_.Int := 0
def LENS  : _root_.Int := 1
def DISTS : _root_.Int := 2

def MAXBITS : Nat := 15
/-- inftrees.h: maximum table sizes, found by exhaustive search (examples/enough.c).
    For memory safety these are only the values the runtime checks compare
    against — their adequacy for all valid Huffman codes is NOT needed here. -/
def ENOUGH_LENS : Nat := 852
def ENOUGH_DISTS : Nat := 592

/-- `sizeof(struct code)` — {uchar op, uchar bits, ushort val}, the anonymous
    struct `__1353` of the generated AST.  Alignment is 2. -/
def codeSize : Nat := 4

/-! ## The static tables (inftrees.c:69-82) -/

def lbaseVals : List Nat :=
  [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
   35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258, 0, 0]

def lextVals : List Nat :=
  [16, 16, 16, 16, 16, 16, 16, 16, 17, 17, 17, 17, 18, 18, 18, 18,
   19, 19, 19, 19, 20, 20, 20, 20, 21, 21, 21, 21, 16, 199, 75]

def dbaseVals : List Nat :=
  [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
   257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
   8193, 12289, 16385, 24577, 0, 0]

def dextVals : List Nat :=
  [16, 16, 16, 16, 17, 17, 18, 18, 19, 19, 20, 20, 21, 21, 22, 22,
   23, 23, 24, 24, 25, 25, 26, 26, 27, 27, 28, 28, 29, 29, 64, 64]

def lbaseF (i : Nat) : Nat := lbaseVals.getD i 0
def lextF  (i : Nat) : Nat := lextVals.getD i 0
def dbaseF (i : Nat) : Nat := dbaseVals.getD i 0
def dextF  (i : Nat) : Nat := dextVals.getD i 0

/-- The four static tables are `getD … 0` over literal lists, so they are u16
    **everywhere**: inside the list by `decide`, outside because the default is
    `0`.  `LoopEnv.hxb`/`hbb` want exactly this unrestricted form. -/
theorem staticF_lt (vals : List Nat) (hall : ∀ v ∈ vals, v < 65536) (j : Nat) :
    vals.getD j 0 < 65536 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : vals[j]? with
  | none => simp
  | some v => exact hall v (List.mem_of_getElem? h)

theorem lbaseF_lt (j : Nat) : lbaseF j < 65536 :=
  staticF_lt lbaseVals (by decide) j
theorem lextF_lt (j : Nat) : lextF j < 65536 :=
  staticF_lt lextVals (by decide) j
theorem dbaseF_lt (j : Nat) : dbaseF j < 65536 :=
  staticF_lt dbaseVals (by decide) j
theorem dextF_lt (j : Nat) : dextF j < 65536 :=
  staticF_lt dextVals (by decide) j

/-! ## Footprint layout (assumption A1) -/

/-- Everything the caller lends to `inflate_table`, plus the blocks of the four
    readonly globals.  Offsets are `Ptrofs` (the values actually inside `Vptr`s);
    the heap predicates below place resources at their `unsigned` images. -/
structure Layout where
  /-- permission on `lens[0..codes)` — read-only suffices -/
  pl : Permission
  /-- permission on `work[0..codes)` -/
  pw : Permission
  /-- permission on the `*table` cell -/
  pt : Permission
  /-- permission on the `*bits` cell -/
  pb : Permission
  /-- permission on the table region `t[0..cap)` -/
  pr : Permission
  /-- permission on the four static tables -/
  pg : Permission
  lensB  : Block
  workB  : Block
  tblB   : Block
  bitsB  : Block
  /-- the block the current `*table` value points into -/
  tB     : Block
  lbB    : Block
  lxB    : Block
  dbB    : Block
  dxB    : Block
  lensO  : Integers.Ptrofs
  workO  : Integers.Ptrofs
  tblO   : Integers.Ptrofs
  bitsO  : Integers.Ptrofs
  /-- the current `*table` value's offset -/
  tO     : Integers.Ptrofs

/-- One scalar slot, contents unconstrained.  `Vundef` is included, so a fresh
    (uninitialised) table satisfies this. -/
def anyCell (chunk : Chunk) (p : Permission) (b : Block) (ofs : _root_.Int) :
    HProp :=
  HProp.hexists (fun v : Val => mapsto chunk p b ofs v)

/-- One `struct code` entry, held field by field.  Alignment is carried by the
    `mapsto`s themselves, so the predicate needs no side condition. -/
def codeCell (p : Permission) (b : Block) (ofs : _root_.Int) : HProp :=
  anyCell .Mint8unsigned p b ofs
  ∗ (anyCell .Mint8unsigned p b (ofs + 1)
     ∗ anyCell .Mint16unsigned p b (ofs + 2))

/-- The table region: `cap` entries of `struct code`, held **field by field**.

    **Why not `anyBytes p b ofs (4*cap)`**: the body performs single-field
    writes into the region — the root back-pointers of inftrees.c:291-293
    assign `next[..].op`, `.bits`, `.val` separately — and `Sep.triple_assign`
    needs the target field's `mapsto`.  An arbitrary 4-byte run is **not**
    three `mapsto`s: a `mapsto` requires the bytes to be exactly
    `encodeVal chunk v`, so a run
    holding, say, a pointer fragment is excluded.  `Body.codeCell_anyBytes`
    gives cells ⊢ bytes, and its docstring records that the converse is false —
    so with `anyBytes` here the body triple is *unprovable*, not merely hard.

    This is a strengthening of A1, and a faithful one: the C type of the region
    is `code FAR *`, i.e. an array of `struct code`, and `anyCell` admits
    `Vundef`, so a freshly allocated (uninitialised) table qualifies — as does
    any table a previous `inflate_table` call filled.  `postHeap` uses the same
    predicate, so the three successive calls inflate.c makes on one shared
    `code[ENOUGH]` array compose. -/
def codeRegion (p : Permission) (b : Block) : _root_.Int → Nat → HProp
  | _, 0 => HProp.emp
  | ofs, (n + 1) => codeCell p b ofs ∗ codeRegion p b (ofs + 4) n

/-- The heap the caller hands over.
    `lensF` gives the code lengths, `workF` the (irrelevant) initial contents
    of the work area, `tO`/`b0` the initial `*table` and `*bits` values,
    `cap` the number of code entries available at `t`. -/
def preHeap (L : Layout) (codes cap b0 : Nat) (lensF workF : Nat → Nat) : HProp :=
  arrayU16 L.pl L.lensB (Integers.Ptrofs.unsigned L.lensO) codes lensF
  ∗ arrayU16 L.pw L.workB (Integers.Ptrofs.unsigned L.workO) codes workF
  ∗ mapsto Mptr L.pt L.tblB (Integers.Ptrofs.unsigned L.tblO) (.Vptr L.tB L.tO)
  ∗ mapsto .Mint32 L.pb L.bitsB (Integers.Ptrofs.unsigned L.bitsO)
      (.Vint (Integers.Int.repr b0))
  ∗ codeRegion L.pr L.tB (Integers.Ptrofs.unsigned L.tO) cap
  ∗ arrayU16 L.pg L.lbB 0 31 lbaseF
  ∗ arrayU16 L.pg L.lxB 0 31 lextF
  ∗ arrayU16 L.pg L.dbB 0 32 dbaseF
  ∗ arrayU16 L.pg L.dxB 0 32 dextF

/-- The heap handed back: same footprint, `lens` and the statics unchanged,
    everything the function may write existentially quantified.
    (Functional strengthening, out of scope for the safety milestone: when the
    result is 0, `*table = t + 4*used` with `used ≤ cap`, `*bits = root ∈ [1,15]`,
    and the region `t[0..used)` is a well-formed decoding table — the
    data-structure invariant `inflate_fast`'s own proof will one day need.) -/
def postHeap (L : Layout) (codes cap : Nat) (lensF : Nat → Nat) : HProp :=
  arrayU16 L.pl L.lensB (Integers.Ptrofs.unsigned L.lensO) codes lensF
  ∗ (hexists fun workF' =>
       arrayU16 L.pw L.workB (Integers.Ptrofs.unsigned L.workO) codes workF')
  ∗ (hexists fun tv =>
       mapsto Mptr L.pt L.tblB (Integers.Ptrofs.unsigned L.tblO) tv)
  -- any `Val`, matching the `*table` slot just above.  Requiring `.Vint` here
  -- would be gratuitously stronger — the postcondition's job is to hand the
  -- cell back, not to describe what is in it — and the main loop's invariant
  -- carries `*bits` as an unconstrained `Val` (it never writes it), so the
  -- stricter form is not dischargeable at the ENOUGH-check return.
  ∗ (hexists fun bv =>
       mapsto .Mint32 L.pb L.bitsB (Integers.Ptrofs.unsigned L.bitsO) bv)
  ∗ codeRegion L.pr L.tB (Integers.Ptrofs.unsigned L.tO) cap
  ∗ arrayU16 L.pg L.lbB 0 31 lbaseF
  ∗ arrayU16 L.pg L.lxB 0 31 lextF
  ∗ arrayU16 L.pg L.dbB 0 32 dbaseF
  ∗ arrayU16 L.pg L.dxB 0 32 dextF

/-! ## Normalising `lens[]` outside the array

`preHeap` owns `arrayU16 … codes lensF`, so nothing constrains `lensF` at
indices `≥ codes` — yet the main loop's `LoopEnv` wants `∀ j, lensF j ≤ 15`.
Rather than strengthen A2 to cover values the function never reads, the top of
the proof replaces `lensF` by `normLens`, which agrees with it on `[0, codes)`
and is `0` elsewhere.  `preHeap` and `postHeap` cannot tell the difference
(`preHeap_normLens`/`postHeap_normLens`), so the whole chain runs at the
normalised function and *establishes its own* model facts — no transfer of
`count`/`maxLen`/`Placed`/… is needed. -/

/-- `lensF` restricted to the array, `0` outside. -/
def normLens (lensF : Nat → Nat) (codes : Nat) : Nat → Nat :=
  fun j => if j < codes then lensF j else 0

theorem normLens_eq (lensF : Nat → Nat) (codes i : Nat) (hi : i < codes) :
    normLens lensF codes i = lensF i := by
  simp [normLens, hi]

/-- Under A2, the normalised function is bounded **everywhere**, which is what
    `LoopEnv` needs. -/
theorem normLens_le (lensF : Nat → Nat) (codes : Nat)
    (hb : ∀ i, i < codes → lensF i ≤ MAXBITS) (j : Nat) :
    normLens lensF codes j ≤ MAXBITS := by
  simp only [normLens]
  split
  · exact hb _ (by assumption)
  · omega

/-- An `arrayU16` depends only on its element function inside the array. -/
theorem arrayU16_congr (p : Permission) (b : Block) (ofs : _root_.Int) (n : Nat)
    (f g : Nat → Nat) (h : ∀ i, i < n → f i = g i) :
    arrayU16 p b ofs n f = arrayU16 p b ofs n g := by
  refine arrayOf_congr 2 ofs n (fun j hj => ?_)
  show (fun off => mapsto .Mint16unsigned p b off
          (.Vint (Integers.Int.repr ((f j : Nat)))))
     = (fun off => mapsto .Mint16unsigned p b off
          (.Vint (Integers.Int.repr ((g j : Nat)))))
  rw [h j hj]

theorem preHeap_normLens (L : Layout) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat) :
    preHeap L codes cap b0 lensF workF
      = preHeap L codes cap b0 (normLens lensF codes) (normLens workF codes) := by
  simp only [preHeap]
  rw [arrayU16_congr L.pl L.lensB (Integers.Ptrofs.unsigned L.lensO) codes lensF
      (normLens lensF codes) (fun i hi => (normLens_eq lensF codes i hi).symm),
    arrayU16_congr L.pw L.workB (Integers.Ptrofs.unsigned L.workO) codes workF
      (normLens workF codes) (fun i hi => (normLens_eq workF codes i hi).symm)]

/-- The normalised `work` is u16 everywhere: inside the array by `work_repr`,
    outside because it is `0`. -/
theorem normWork_lt (workF : Nat → Nat) (codes : Nat)
    (hw : ∀ i, i < codes → workF i < 65536) (j : Nat) :
    normLens workF codes j < 65536 := by
  simp only [normLens]
  split
  · exact hw _ (by assumption)
  · omega

theorem postHeap_normLens (L : Layout) (codes cap : Nat) (lensF : Nat → Nat) :
    postHeap L codes cap lensF
      = postHeap L codes cap (normLens lensF codes) := by
  simp only [postHeap]
  rw [arrayU16_congr L.pl L.lensB (Integers.Ptrofs.unsigned L.lensO) codes lensF
    (normLens lensF codes) (fun i hi => (normLens_eq lensF codes i hi).symm)]

/-- The argument list `inflate_table(type, lens, codes, table, bits, work)`. -/
def argVals (L : Layout) (ty : _root_.Int) (codes : Nat) : List Val :=
  [.Vint (Integers.Int.repr ty), .Vptr L.lensB L.lensO,
   .Vint (Integers.Int.repr codes), .Vptr L.tblB L.tblO,
   .Vptr L.bitsB L.bitsO, .Vptr L.workB L.workO]

/-! ## The assumption set

Split in two:

* `SideConds` — representation side conditions of the block/offset memory
  model (permissions adequate, pointer arithmetic non-wrapping, arguments
  representable).  These are not "assumptions about the caller" so much as
  the translation of "these are real, distinct C objects" into the model —
  the same role as `hno` in IsSortedSep.
* `Assumptions` — A2-A5: genuine caller obligations, each with a concrete
  violating input that makes the C code fault (see fv/memory-safety.md §4
  and the per-field comments). -/

def PTROFS_MOD : _root_.Int := 18446744073709551616  -- 2^64

structure SideConds (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (workF : Nat → Nat) : Prop where
  perm_lens : permOrder L.pl .Readable = true
  perm_work : permOrder L.pw .Writable = true
  perm_tbl  : permOrder L.pt .Writable = true
  perm_bits : permOrder L.pb .Writable = true
  perm_reg  : permOrder L.pr .Writable = true
  perm_glob : permOrder L.pg .Readable = true
  /-- `codes` is a genuine `unsigned` -/
  codes_repr : (codes : _root_.Int) < 4294967296
  /-- `*bits` is a genuine `unsigned` -/
  b0_repr : (b0 : _root_.Int) < 4294967296
  /-- `work[]` is `unsigned short FAR *` in C, so its model function describes
      u16 values.  Purely a representation fact, like the `perm_*` fields — the
      *contents* of `work` are irrelevant to safety (the sort loop overwrites
      them), but the model has to be able to *hold* them. -/
  work_repr : ∀ i, i < codes → workF i < 65536
  /-- `lens + 2*codes` does not wrap -/
  no_wrap_lens : Integers.Ptrofs.unsigned L.lensO + 2 * (codes : _root_.Int) < PTROFS_MOD
  /-- `work + 2*codes` does not wrap -/
  no_wrap_work : Integers.Ptrofs.unsigned L.workO + 2 * (codes : _root_.Int) < PTROFS_MOD
  /-- `t + 4*cap` does not wrap -/
  no_wrap_tbl : Integers.Ptrofs.unsigned L.tO + 4 * (cap : _root_.Int) < PTROFS_MOD
  /-- the region size is a genuine `int` — the body compares `used` against it
      with signed arithmetic -/
  cap_repr : (cap : _root_.Int) < 2147483648
  /-- **`*table` is 4-aligned.**  ⚠ This is *stronger* than the C type
      guarantees: CompCert's `alignof (struct code)` is 2 (fields `op`:1,
      `bits`:1, `val`:2), so a `code[]` array is only 2-aligned in principle.
      The `% 4` comes from `Body.codeCell_eq_bytes`, whose own proof only ever
      needs `% 2` (it discharges alignments 1, 1, 2) — so this can be weakened
      to `% 2` by relaxing that lemma and the few that inherit it.  Recorded as
      a caveat rather than silently assumed; every real allocator returns
      4-aligned storage for a 4-byte struct, so it costs no call site. -/
  tbl_align : Integers.Ptrofs.unsigned L.tO % 4 = 0

structure Assumptions (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF : Nat → Nat) : Prop where
  /-- `type` is one of the three enum values (the `Sswitch` has no default arm;
      the code after it reads `base`/`extra`, which stay NULL otherwise). -/
  ty_valid : ty = CODES ∨ ty = LENS ∨ ty = DISTS
  /-- **A2** (inftrees.c:97-98, documented unchecked precondition).
      Necessary: `lens[0] = 9999` indexes `count[9999]` at inftrees.c:119,
      a stack out-of-bounds write. -/
  lens_le_MAXBITS : ∀ i, i < codes → lensF i ≤ MAXBITS
  /-- **A3-LENS**.  Necessary: a symbol `s ≥ 288` with nonzero length makes
      `work[sym] - 257 ≥ 31` and overruns `lbase[31]`/`lext[31]`
      (inftrees.c:229-230). -/
  codes_lens : ty = LENS → codes ≤ 288
  /-- **A3-DISTS**.  Same shape against `dbase[32]`/`dext[32]`. -/
  codes_dists : ty = DISTS → codes ≤ 32
  /-- **A3-CODES**.  Necessary: with `codes ≥ 21` a symbol `≥ 20 = match`
      reaches `extra[work[sym] - 20]` with `extra = NULL` (inftrees.c:228-230)
      — a null dereference.  (`work[sym] = 19` still takes the safe
      end-of-block branch, hence 20, not 19.) -/
  codes_codes : ty = CODES → codes ≤ 20
  /-- **A4** unconditional part: the `max == 0` branch writes two entries
      through `*table` before any capacity check (inftrees.c:130-131). -/
  cap_min : 2 ≤ cap
  /-- **A4-LENS**: with `cap ≥ ENOUGH_LENS` the runtime checks at
      inftrees.c:216-218 and 284-287 guard every write into the region.
      No Kraft/enough.c combinatorics enter the safety proof. -/
  cap_lens : ty = LENS → ENOUGH_LENS ≤ cap
  /-- **A4-DISTS**. -/
  cap_dists : ty = DISTS → ENOUGH_DISTS ≤ cap
  /-- **A5** (CODES only — the one case with NO runtime capacity check).
      If every length is ≤ Lc and the requested root `b0 ≥ Lc`, then after
      clamping `root = max ≤ Lc`, no code is longer than the root table, the
      sub-table branch (inftrees.c:265-294) is never taken, and
      `used = 2^root ≤ 2^Lc ≤ cap`.  Necessary: without a bound of this shape,
      CODES inputs can build unchecked sub-tables past any fixed capacity.
      The only call site (inflate.c, TABLE state) instantiates
      Lc = b0 = 7, cap = ENOUGH = 1444. -/
  codes_cap : ty = CODES →
    ∃ Lc, (∀ i, i < codes → lensF i ≤ Lc) ∧ Lc ≤ b0 ∧ 2 ^ Lc ≤ cap

/-! ## The specification -/

/-- The safety `FunSpec` for `inflate_table`.  `measure := 0`: the function is
    a leaf (its body contains no `Scall`), so any measure closes the spec
    table.  The return value is one of {-1, 0, 1} (inftrees.c returns -1 for
    invalid/over-subscribed codes, +1 for insufficient ENOUGH space, 0 on
    success — including the empty-code case). -/
def inflateTableSpec (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat) : Sep.FunSpec where
  tyargs := [tint, tptr tushort, tuint,
             tptr (tptr (Ty.Tstruct __1353 noattr)), tptr tuint, tptr tushort]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = argVals L ty codes
    ∧ preHeap L codes cap b0 lensF workF hp
  post := fun v hp =>
    (∃ r : _root_.Int, v = .Vint (Integers.Int.repr r)
        ∧ (r = -1 ∨ r = 0 ∨ r = 1))
    ∧ postHeap L codes cap lensF hp
  measure := fun _ => 0

end InflateTable
