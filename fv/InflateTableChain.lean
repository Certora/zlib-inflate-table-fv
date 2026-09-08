/-
  The phase chain.

  `InflateTableEntry.safe_of_body` reduces memory safety to one triple over
  `f_inflate_table.fn_body`, which `Body.body_matches` pins to `Body.fullBody` —
  a 33-segment right-nested `Ssequence`.  Every segment has a triple in
  InflateTableBody.lean; this file chains them.

  The two things that make the chain work, and cost the most to get right:

  * **Footprint order.**  Each segment states the *smallest* heap it touches, in
    the order its own statements consume it.  The ambient heap is `Pbody`'s, in
    `preHeap`'s order.  So every link is a `Body.localst_perm` (reassociate,
    `sep_cancel` proves the equality) followed by the segment's triple.
  * **Framing vs `Hrest`.**  A segment that cannot `return` gets its frame from
    `Body.frame_seg`.  A segment that *can* return is already polymorphic in an
    explicit `Hrest`, and its `hret` receives exactly the residual the `return`
    hands back after `freeList` — framing such a segment would wrongly place the
    frame inside `Ret`.  Getting this backwards is the mistake §8's
    `return_const_triple` interface is designed to prevent.
-/
import InflateTableEntry

open CC CC.Sep CC.HProp
open Inftrees

namespace InflateTable.Chain

open InflateTable.Body
open InflateTable.Model (kraftOk maxLen minLen nlive leftAt maxLen_char
  minLen_char nlive_le_codes le_maxLen)

section Chain

variable (ge : CGenv) (fe : EntryRel) (bh bc bo : Block)
variable (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
variable (lensF workF : Nat → Nat)

/-! ## The ambient heap

`Entry.Pbody`'s heap, with the three locals in front of `preHeap`.  The chain
reassociates *out of* this at every segment and back into it afterwards. -/

/-- The heap `Pbody` hands the body, named so the links can talk about it. -/
abbrev Hpro : HProp :=
  undefBytes .Freeable bh 0 4
  ∗ (undefBytes .Freeable bc 0 32
     ∗ (undefBytes .Freeable bo 0 32
        ∗ preHeap L codes cap b0 lensF workF))

/-- Everything except `count` — the frame the first loop runs under. -/
abbrev Hnc : HProp :=
  undefBytes .Freeable bh 0 4
  ∗ (undefBytes .Freeable bo 0 32 ∗ preHeap L codes cap b0 lensF workF)

theorem Hpro_count_first :
    Hpro bh bc bo L codes cap b0 lensF workF
      = undefBytes .Freeable bc 0 32 ∗ Hnc bh bo L codes cap b0 lensF workF := by
  show undefBytes .Freeable bh 0 4 ∗ _ = _
  simp only [Hnc]
  sep_cancel

/-! ## The heap, component by component

From link 7 on the chain is long enough that spelling `∗`-chains out becomes a
paren-counting exercise.  These twelve names are the
whole footprint; every link states its permutation as a chain of them, and
`sep_cancel` proves the reassociation after `simp only` unfolds them. -/

/-- `count[0..15]`, once the zeroing loop has made it a real array. -/
abbrev Ccnt (cntF : Nat → Nat) : HProp := arrayU16 .Freeable bc 0 16 cntF
/-- `offs[0..15]`, still undefined until §11 writes it. -/
abbrev Cofs : HProp := undefBytes .Freeable bo 0 32
/-- `here` — four undefined bytes until §13 or the main loop writes it. -/
abbrev Chere : HProp := undefBytes .Freeable bh 0 4
/-- The caller's `lens[]`, read-only for the whole function. -/
abbrev Clens : HProp :=
  arrayU16 L.pl L.lensB (Integers.Ptrofs.unsigned L.lensO) codes lensF
/-- The caller's `work[]`, whose contents safety never constrains. -/
abbrev Cwork (wF : Nat → Nat) : HProp :=
  arrayU16 L.pw L.workB (Integers.Ptrofs.unsigned L.workO) codes wF
/-- The `*table` cell. -/
abbrev Ctbl : HProp :=
  mapsto Mptr L.pt L.tblB (Integers.Ptrofs.unsigned L.tblO) (.Vptr L.tB L.tO)
/-- The `*bits` cell, at whatever value it currently holds. -/
abbrev Cbits (v : Val) : HProp :=
  mapsto .Mint32 L.pb L.bitsB (Integers.Ptrofs.unsigned L.bitsO) v
/-- The table region the caller lent us. -/
abbrev Creg : HProp := codeRegion L.pr L.tB (Integers.Ptrofs.unsigned L.tO) cap
/-- The four static tables, always owned and never written. -/
abbrev Cglob : HProp :=
  arrayU16 L.pg L.lbB 0 31 lbaseF
  ∗ (arrayU16 L.pg L.lxB 0 31 lextF
     ∗ (arrayU16 L.pg L.dbB 0 32 dbaseF ∗ arrayU16 L.pg L.dxB 0 32 dextF))

/-- Everything the caller lent that the three locals are not: the frame that
    rides through the scanning loops untouched, and exactly the residual a
    `return` hands back after `freeList` frees the locals. -/
abbrev Cout (wF : Nat → Nat) (v : Val) : HProp :=
  Clens L codes lensF
  ∗ (Cwork L codes wF ∗ (Ctbl L ∗ (Cbits L v ∗ (Creg L cap ∗ Cglob L))))

/-- The canonical mid-chain order: the three locals, then `Cout`.  Segments
    §5-§11 all want a prefix of this. -/
abbrev Hmid (cntF : Nat → Nat) (wF : Nat → Nat) (v : Val) : HProp :=
  Ccnt bc cntF ∗ (Chere bh ∗ (Cofs bo ∗ Cout L codes cap lensF wF v))

/-- The residual a `return` hands back: `Cout` with the two cells the function
    may have written left at arbitrary values.  §8's `return_const_triple` frees
    the three locals, so this — and nothing about `count`/`offs`/`here` — is what
    the postcondition receives. -/
abbrev Cret (wF : Nat → Nat) (tv : Val) (bv : Val) : HProp :=
  Clens L codes lensF
  ∗ (Cwork L codes wF
     ∗ (mapsto Mptr L.pt L.tblB (Integers.Ptrofs.unsigned L.tblO) tv
        ∗ (Cbits L bv ∗ (Creg L cap ∗ Cglob L))))

/-- **The return obligation, once.**  `inflate_table` has six `return` sites;
    each hands back a `Cret`, and this is what makes each of them satisfy the
    spec's `postHeap`.  The three existentials of `postHeap` are exactly the
    three cells the function is allowed to have written. -/
theorem postHeap_of_Cret (wF : Nat → Nat) (tv : Val) (bv : Val) :
    Cret L codes cap lensF wF tv bv ⊢ postHeap L codes cap lensF := by
  intro h hx
  obtain ⟨h1, r1, d1, q1, hlens, hx⟩ := hx
  obtain ⟨h2, r2, d2, q2, hwork, hx⟩ := hx
  obtain ⟨h3, r3, d3, q3, htbl, hx⟩ := hx
  obtain ⟨h4, r4, d4, q4, hbits, hrest⟩ := hx
  exact ⟨h1, r1, d1, q1, hlens,
         h2, r2, d2, q2, ⟨wF, hwork⟩,
         h3, r3, d3, q3, ⟨tv, htbl⟩,
         h4, r4, d4, q4, ⟨bv, hbits⟩, hrest⟩

/-! ## Spine helpers

`fullBody`'s spine is right-nested, so **every slot needs its own triple**: a
bundled lemma like `Body.seg6_triple` (`offs1Init ; seg15` as one `Ssequence`)
does not fit, and neither would a three-`Sset` "prologue" lemma.  The three
prologue `Sset`s are therefore applied individually in the spine below. -/

/-- Weakening the tracked list.  `TempsHold` is a `∀ … ∈ …`, so any sublist —
    in any order — still holds.  This is how the spine both **permutes** the
    list (to put a segment's variable at the head) and **drops stale entries**
    (an assignment to an already-tracked identifier must remove the old
    binding, or `TempsHold` becomes unsatisfiable). -/
theorem localst_mono (E : Env) (l l' : List (Ident × Val)) (H : HProp)
    (hsub : ∀ q ∈ l', q ∈ l) :
    ∀ e le hp, LocalSt E l H e le hp → LocalSt E l' H e le hp := by
  rintro e le hp ⟨henv, hT, hH⟩
  exact ⟨henv, TempsHold_mono hsub hT, hH⟩

/-- Consume a pure fact carried by a segment's postcondition. -/
theorem triple_pure (φ : Prop) (P : Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (h : φ → Triple ge fe f_inflate_table P s R) :
    Triple ge fe f_inflate_table (fun e le hp => φ ∧ P e le hp) s R := by
  intro k e le hp hf m hd hag hP
  exact h hP.1 k e le hp hf m hd hag hP.2

/-- `preHeap` with `lens` removed — the frame loop 2 runs under. -/
abbrev preRest : HProp :=
  arrayU16 L.pw L.workB (Integers.Ptrofs.unsigned L.workO) codes workF
  ∗ (mapsto Mptr L.pt L.tblB (Integers.Ptrofs.unsigned L.tblO) (.Vptr L.tB L.tO)
     ∗ (mapsto .Mint32 L.pb L.bitsB (Integers.Ptrofs.unsigned L.bitsO)
          (.Vint (Integers.Int.repr ((b0 : _root_.Int))))
        ∗ (codeRegion L.pr L.tB (Integers.Ptrofs.unsigned L.tO) cap
           ∗ (arrayU16 L.pg L.lbB 0 31 lbaseF
              ∗ (arrayU16 L.pg L.lxB 0 31 lextF
                 ∗ (arrayU16 L.pg L.dbB 0 32 dbaseF
                    ∗ arrayU16 L.pg L.dxB 0 32 dextF))))))

/-- The frame loop 2 runs under: `here`, `offs`, and `preHeap` minus `lens`. -/
abbrev Hnlc : HProp :=
  undefBytes .Freeable bh 0 4
  ∗ (undefBytes .Freeable bo 0 32 ∗ preRest L codes cap b0 workF)

/-! ## Link 4 — `fullBody` segment 3: `len = 0;` then loop 1

The first framed segment.  `seg1_triple`'s footprint is `count`'s 32 undefined
bytes alone, so everything else rides along in `Hnc` via `Body.frame_seg`. -/

/-- `for (len = 0; len <= MAXBITS; len++) count[len] = 0;` — inftrees.c:116-117,
    against the full ambient footprint. -/
theorem link_zero_count (R : Sep.ExitConds) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) (T0 L ty codes)
        (Hpro bh bc bo L codes cap b0 lensF workF))
      seg3
      { normal := LocalSt (envOf bh bc bo)
          ((_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
            :: T0 L ty codes)
          (Hcnt bc 16 ∗ Hnc bh bo L codes cap b0 lensF workF),
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine localst_perm ge fe (envOf bh bc bo) _ _ _
    (Hpro_count_first bh bc bo L codes cap b0 lensF workF) _ _ ?_
  exact frame_seg ge fe (envOf bh bc bo) (T0 L ty codes) _
    (undefBytes .Freeable bc 0 32) (Hcnt bc 16)
    (Hnc bh bo L codes cap b0 lensF workF) seg3 R
    (fun R' => seg1_triple ge fe bh bc bo (T0 L ty codes) (by temps_ne) R')

/-! ## Link 5 — `fullBody` segment 4: `sym = 0;` then loop 2

`count[lens[sym]]++` over all symbols.  Footprint is `lens` and the zeroed
`count`, so `lens` has to come out of `preHeap`'s head and sit next to `count`. -/

theorem Hcnt_lens_first :
    Hcnt bc 16 ∗ Hnc bh bo L codes cap b0 lensF workF
      = (arrayU16 L.pl L.lensB (Integers.Ptrofs.unsigned L.lensO) codes lensF
          ∗ arrayU16 .Freeable bc 0 16 (fun _ => 0))
        ∗ Hnlc bh bo L codes cap b0 workF := by
  show (arrayU16 .Freeable bc 0 16 (fun _ => 0) ∗ _) ∗ _ = _
  rw [show undefBytes .Freeable bc (2 * ((16 : Nat) : _root_.Int))
          (32 - 2 * 16) = emp from rfl, sep_emp_eq]
  simp only [Hnc, Hnlc, preHeap, preRest]
  sep_cancel

/-- `for (sym = 0; sym < codes; sym++) count[lens[sym]]++;` — inftrees.c:118-119,
    against the full ambient footprint. -/
theorem link_count_lens (R : Sep.ExitConds)
    (hpl : permOrder L.pl .Readable = true)
    (hb : ∀ j, lensF j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned L.lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
          :: T0 L ty codes)
        (Hcnt bc 16 ∗ Hnc bh bo L codes cap b0 lensF workF))
      seg4
      { normal := LocalSt (envOf bh bc bo)
          ((_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
            :: (_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
            :: T0 L ty codes)
          (Hc2 L.pl L.lensB L.lensO codes lensF bc codes
            ∗ Hnlc bh bo L codes cap b0 workF),
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine localst_perm ge fe (envOf bh bc bo) _ _ _
    (Hcnt_lens_first bh bc bo L codes cap b0 lensF workF) _ _ ?_
  exact frame_seg ge fe (envOf bh bc bo) _ _ _ _
    (Hnlc bh bo L codes cap b0 workF) seg4 R
    (fun R' => seg2_triple ge fe bh bc bo L.pl L.lensB L.lensO codes lensF _
      hpl hb hlens15 hc16 hnoL (by temps_mem) (by temps_mem)
      (by temps_ne) (by temps_ne) R')

/-! ## Link 6 — `fullBody` segment 5: `root = *bits;`

The narrowest footprint in the whole function: `read_root_triple` mentions only
the `*bits` cell.  Everything else — including `count`, which the next segment
needs back — is framed. -/

/-- The ambient heap with `*bits` at the head. -/
abbrev HnoBits : HProp :=
  Hc2 L.pl L.lensB L.lensO codes lensF bc codes
  ∗ (undefBytes .Freeable bh 0 4
     ∗ (undefBytes .Freeable bo 0 32
        ∗ (arrayU16 L.pw L.workB (Integers.Ptrofs.unsigned L.workO) codes workF
           ∗ (mapsto Mptr L.pt L.tblB (Integers.Ptrofs.unsigned L.tblO)
                (.Vptr L.tB L.tO)
              ∗ (codeRegion L.pr L.tB (Integers.Ptrofs.unsigned L.tO) cap
                 ∗ (arrayU16 L.pg L.lbB 0 31 lbaseF
                    ∗ (arrayU16 L.pg L.lxB 0 31 lextF
                       ∗ (arrayU16 L.pg L.dbB 0 32 dbaseF
                          ∗ arrayU16 L.pg L.dxB 0 32 dextF))))))))

theorem Hc2_bits_first :
    Hc2 L.pl L.lensB L.lensO codes lensF bc codes
        ∗ Hnlc bh bo L codes cap b0 workF
      = mapsto .Mint32 L.pb L.bitsB (Integers.Ptrofs.unsigned L.bitsO)
          (.Vint (Integers.Int.repr ((b0 : _root_.Int))))
        ∗ HnoBits bh bc bo L codes cap lensF workF := by
  simp only [Hc2, Hnlc, HnoBits, preRest]
  sep_cancel

/-- `root = *bits;` — inftrees.c:122, against the full ambient footprint. -/
theorem link_read_root (R : Sep.ExitConds)
    (hpb : permOrder L.pb .Readable = true) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
          :: (_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
          :: T0 L ty codes)
        (Hc2 L.pl L.lensB L.lensO codes lensF bc codes
          ∗ Hnlc bh bo L codes cap b0 workF))
      readRoot
      { normal := LocalSt (envOf bh bc bo)
          ((_root, .Vint (Integers.Int.repr ((b0 : _root_.Int))))
            :: (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
            :: (_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
            :: T0 L ty codes)
          (mapsto .Mint32 L.pb L.bitsB (Integers.Ptrofs.unsigned L.bitsO)
             (.Vint (Integers.Int.repr ((b0 : _root_.Int))))
           ∗ HnoBits bh bc bo L codes cap lensF workF),
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine localst_perm ge fe (envOf bh bc bo) _ _ _
    (Hc2_bits_first bh bc bo L codes cap b0 lensF workF) _ _ ?_
  exact frame_seg_only ge fe (envOf bh bc bo) _ _ _ _
    (HnoBits bh bc bo L codes cap lensF workF) readRoot R
    (read_root_triple ge fe (envOf bh bc bo) L.pb L.bitsB L.bitsO b0 _
      hpb (by temps_mem) (by temps_ne))

/-! ## The bridge into the canonical order

`Hc2`/`Hnc`/`Hnlc`/`HnoBits` were introduced ad hoc for links 4-6; from here on
everything is stated in components. -/

/-- The counts after loop 2 — the model's `count`, which is what `Hc2` holds. -/
abbrev cntC : Nat → Nat := fun l => InflateTable.Model.count lensF codes l

theorem cntC_lt (l : Nat) (hc16 : codes < 65536) : cntC codes lensF l < 65536 :=
  Nat.lt_of_le_of_lt (InflateTable.Model.count_le lensF codes l) hc16

theorem link6_as_Hmid :
    Cbits L (.Vint (Integers.Int.repr ((b0 : _root_.Int))))
        ∗ HnoBits bh bc bo L codes cap lensF workF
      = Hmid bh bc bo L codes cap lensF (cntC codes lensF) workF
          (.Vint (Integers.Int.repr ((b0 : _root_.Int)))) := by
  simp only [Hmid, HnoBits, Hc2, Cout, Ccnt, Cofs, Chere, Clens, Cwork, Ctbl,
    Cbits, Creg, Cglob]
  sep_cancel

/-! ## Link 7 — `fullBody` segment 6: `max = MAXBITS;` then loop 3

`for (max = MAXBITS; max >= 1; max--) if (count[max] != 0) break;`  The post is
an existential over the found bound, so this is the first use of
`Body.frame_seg_gen`. -/

theorem link_max_scan (R : Sep.ExitConds) (hc16 : codes < 65536)
    (T : List (Ident × Val))
    (hT33 : ∀ p ∈ T, p.1 ≠ _t'33) (hTmax : ∀ p ∈ T, p.1 ≠ _max) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T
        (Hmid bh bc bo L codes cap lensF (cntC codes lensF) workF
          (.Vint (Integers.Int.repr ((b0 : _root_.Int))))))
      seg6
      { normal := fun e le hp => ∃ M, M ≤ 15
          ∧ (∀ l, M < l → l ≤ 15 → cntC codes lensF l = 0)
          ∧ (M = 0 ∨ cntC codes lensF M ≠ 0)
          ∧ LocalSt (envOf bh bc bo)
              ((_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: T)
              (Hmid bh bc bo L codes cap lensF (cntC codes lensF) workF
                (.Vint (Integers.Int.repr ((b0 : _root_.Int))))) e le hp,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine localst_perm ge fe (envOf bh bc bo) _ _ _
    (show Hmid bh bc bo L codes cap lensF (cntC codes lensF) workF
        (.Vint (Integers.Int.repr ((b0 : _root_.Int))))
      = Hscan bc (cntC codes lensF)
        ∗ (Chere bh ∗ (Cofs bo ∗ Cout L codes cap lensF workF
            (.Vint (Integers.Int.repr ((b0 : _root_.Int)))))) from rfl) _ _ ?_
  refine frame_seg_gen ge fe (envOf bh bc bo) T _ _ seg6 _ _ R
    (fun R' => seg3_triple ge fe bh bc bo (cntC codes lensF) T
      (fun j => cntC_lt codes lensF j hc16) hT33 hTmax R') ?_
  intro e le hp hx
  obtain ⟨h1, h2, hd, heq, ⟨M, hM15, hz, hnz, hst⟩, hQ⟩ := hx
  exact ⟨M, hM15, hz, hnz,
    (localst_sep (envOf bh bc bo) _ _ _ e le hp).mp ⟨h1, h2, hd, heq, hst, hQ⟩⟩

/-! ## Link 8 — `fullBody` segment 7: `if (root > max) root = max;` -/

theorem link_clamp1 (R : Sep.ExitConds) (r M : Nat)
    (hr : r < 4294967296) (hM : M < 4294967296) (H : HProp)
    (rest : List (Ident × Val))
    (hmemM : (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) ∈ rest)
    (hne : ∀ p ∈ rest, p.1 ≠ _root) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_root, .Vint (Integers.Int.repr ((r : _root_.Int)))) :: rest) H)
      clamp1Stmt
      { normal := LocalSt (envOf bh bc bo)
          ((_root, .Vint (Integers.Int.repr ((Nat.min r M : Nat)))) :: rest) H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_conseq ge fe f_inflate_table
    (clamp1_triple ge fe (envOf bh bc bo) r M rest H hr hM hmemM hne)
    (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-! ## Link 9 — `fullBody` segment 8: `if (max == 0) { … return 0; }`

The empty-code case.  `Body.maxzero_if_triple` proves the statement; the work
here is presenting the ambient heap in its shape — `count` and `offs` as raw
byte runs (they are about to be freed, so their structure is irrelevant) and the
region split as *two entries plus a remainder*, which is where `A4`'s
`2 ≤ cap` enters as `cap = 2 + k`. -/

theorem Hmid_as_MZpre (k : Nat) (cntF wF : Nat → Nat) (v : Val) :
    Hmid bh bc bo L codes (2 + k) lensF cntF wF v
      = MZpre bh bc bo L.pt L.pb L.pr L.tblB L.bitsB L.tB L.tblO L.bitsO L.tO
          k v (u16Bytes cntF 16) (List.replicate 32 .Undef)
          (Clens L codes lensF ∗ (Cwork L codes wF ∗ Cglob L)) := by
  simp only [Hmid, Cout, MZpre, Ccnt, Chere, Cofs, Clens, Cwork, Ctbl, Cbits,
    Creg, Cglob]
  -- `sep_cancel` matches syntactically, so both locals have to be *written*
  -- as byte runs first — `undefBytes` is definitionally one, but not
  -- syntactically.
  rw [arrayU16_bytes .Freeable bc 0 cntF (by decide) 16,
      show undefBytes .Freeable bo 0 32
        = bytesPtsTo bo .Freeable 0 (List.replicate 32 (MemVal.Undef)) from rfl]
  sep_cancel

/-- What the `max == 0` block hands back, reassembled into `Cret`.  The two
    entries it wrote are concretely `hereBytes`, so `Body.hereBytes_codeCell`
    turns them back into cells and `Body.mz_region_split` rejoins them with the
    untouched remainder — this is the direction that only works *at a written
    entry*, and the reason the region is carried as cells at all. -/
theorem maxzero_ret_heap (k : Nat) (wF : Nat → Nat) (tv : Val)
    (hal : Integers.Ptrofs.unsigned L.tO % 4 = 0) :
    Cbits L (.Vint (Integers.Int.repr 1))
      ∗ (mapsto Mptr L.pt L.tblB (Integers.Ptrofs.unsigned L.tblO) tv
         ∗ (bytesPtsTo L.tB L.pr (Integers.Ptrofs.unsigned L.tO + 4)
              (hereBytes 64 1 0)
            ∗ (bytesPtsTo L.tB L.pr (Integers.Ptrofs.unsigned L.tO)
                 (hereBytes 64 1 0)
               ∗ (codeRegion L.pr L.tB (Integers.Ptrofs.unsigned L.tO + 8) k
                  ∗ (Clens L codes lensF ∗ (Cwork L codes wF ∗ Cglob L))))))
    ⊢ Cret L codes (2 + k) lensF wF tv (.Vint (Integers.Int.repr 1)) := by
  refine entails_trans (sep_mono (entails_refl _) (sep_mono (entails_refl _)
    (sep_mono (hereBytes_codeCell L.pr L.tB _ ?_ 64 1 0)
      (sep_mono (hereBytes_codeCell L.pr L.tB _ hal 64 1 0)
        (entails_refl _))))) ?_
  · obtain ⟨A, hA⟩ : ∃ A : _root_.Int,
      Integers.Ptrofs.unsigned L.tO = A := ⟨_, rfl⟩
    have hal' : A % (4 : _root_.Int) = 0 := by rw [← hA]; exact hal
    rw [hA]; omega
  · rw [show Cret L codes (2 + k) lensF wF tv (.Vint (Integers.Int.repr 1))
        = Cbits L (.Vint (Integers.Int.repr 1))
          ∗ (mapsto Mptr L.pt L.tblB (Integers.Ptrofs.unsigned L.tblO) tv
             ∗ (codeCell L.pr L.tB (Integers.Ptrofs.unsigned L.tO + 4)
                ∗ (codeCell L.pr L.tB (Integers.Ptrofs.unsigned L.tO)
                   ∗ (codeRegion L.pr L.tB
                        (Integers.Ptrofs.unsigned L.tO + 8) k
                      ∗ (Clens L codes lensF
                         ∗ (Cwork L codes wF ∗ Cglob L))))))
      from by
        simp only [Cret, Clens, Cwork, Cbits, Creg, Cglob]
        rw [mz_region_split L.pr L.tB (Integers.Ptrofs.unsigned L.tO) k]
        sep_cancel]
    exact entails_refl _

/-- `if (max == 0) { … return 0; }` — inftrees.c:126-134, against the ambient
    footprint.  `A4`'s `2 ≤ cap` appears as `cap = 2 + k`. -/
theorem link_maxzero (R : Sep.ExitConds) (M : Nat) (hM32 : M < 4294967296)
    (k : Nat) (cntF wF : Nat → Nat) (v : Val) (l : List (Ident × Val))
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hptR : permOrder L.pt .Readable = true)
    (hptW : permOrder L.pt .Writable = true)
    (hpb : permOrder L.pb .Writable = true)
    (hpr : permOrder L.pr .Writable = true)
    (hal : Integers.Ptrofs.unsigned L.tO % 4 = 0)
    (haddr1 : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed L.tO
        (Integers.Int.repr 1)) = Integers.Ptrofs.unsigned L.tO + 4)
    (hmemM : (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) ∈ l)
    (hmemT : (_table, .Vptr L.tblB L.tblO) ∈ l)
    (hmemB : (_bits, .Vptr L.bitsB L.bitsO) ∈ l)
    (hT1 : ∀ p ∈ l, p.1 ≠ _t'1) (hT2 : ∀ p ∈ l, p.1 ≠ _t'2)
    (Ret : Val → HProp)
    (hretP : ∀ hr, postHeap L codes (2 + k) lensF hr →
      Ret (.Vint (Integers.Int.repr 0)) hr) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hmid bh bc bo L codes (2 + k) lensF cntF wF v))
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar _max tuint)
        (.Econst_int (Integers.Int.repr 0) tint) tint) maxZeroBlock .Sskip)
      { normal := fun e le hp => M ≠ 0 ∧
          LocalSt (envOf bh bc bo) l
            (Hmid bh bc bo L codes (2 + k) lensF cntF wF v) e le hp,
        brk := Assn.no, cont := Assn.no, ret := Ret,
        goto := fun _ => Assn.no } := by
  refine localst_perm ge fe (envOf bh bc bo) _ _ _
    (Hmid_as_MZpre bh bc bo L codes lensF k cntF wF v) _ _ ?_
  refine triple_conseq ge fe f_inflate_table
    (maxzero_if_triple ge fe bh bc bo L.pt L.pb L.pr L.tblB L.bitsB L.tB
      L.tblO L.bitsO L.tO k v (u16Bytes cntF 16) (List.replicate 32 .Undef)
      (Clens L codes lensF ∗ (Cwork L codes wF ∗ Cglob L))
      M hM32 l hcenv hd1 hd2 hd3 hptR hptW hpb hpr
      (u16Bytes_length cntF 16) (List.length_replicate) hal haddr1
      hmemM hmemT hmemB hT1 hT2 Ret
      (fun hr hx => hretP hr
        (postHeap_of_Cret L codes (2 + k) lensF wF _
          (.Vint (Integers.Int.repr 1)) hr
          (maxzero_ret_heap L codes lensF k wF _ hal hr
            (by rw [haddr1] at hx; exact hx)))))
    (fun _ _ _ x => x)
    (fun e le hp hx => ⟨hx.1, by
      rw [Hmid_as_MZpre bh bc bo L codes lensF k cntF wF v]; exact hx.2⟩)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ x => x)

/-- Re-heading the tracked list.  `TempsHold` is order-insensitive, so an entry
    the list already holds can be *duplicated to the front* — which is how a
    segment stated with its variable at the head (`seg4_triple` wants `_max`
    there) is applied after another segment has pushed something else on. -/
theorem localst_cons (E : Env) (l : List (Ident × Val)) (H : HProp)
    (id : Ident) (v : Val) (hm : (id, v) ∈ l) :
    ∀ e le hp, LocalSt E l H e le hp → LocalSt E ((id, v) :: l) H e le hp := by
  rintro e le hp ⟨henv, hT, hH⟩
  exact ⟨henv, TempsHold_cons (hT.get hm) hT, hH⟩

/-! ## Link 10 — `fullBody` segment 9: `min = 1;` then loop 4 -/

theorem link_min_scan (R : Sep.ExitConds) (M : Nat) (hM1 : 1 ≤ M) (hM15 : M ≤ 15)
    (hc16 : codes < 65536) (cntF wF : Nat → Nat) (v : Val)
    (l : List (Ident × Val))
    (hcb : ∀ j, cntF j < 65536)
    (hmemM : (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) ∈ l)
    (hT32 : ∀ p ∈ l, p.1 ≠ _t'32) (hTmin : ∀ p ∈ l, p.1 ≠ _min) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hmid bh bc bo L codes cap lensF cntF wF v))
      seg9
      { normal := fun e le hp => ∃ Mn, 1 ≤ Mn ∧ Mn ≤ M
          ∧ (∀ j, 1 ≤ j → j < Mn → cntF j = 0) ∧ (Mn = M ∨ cntF Mn ≠ 0)
          ∧ LocalSt (envOf bh bc bo)
              ((_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
                :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: l)
              (Hmid bh bc bo L codes cap lensF cntF wF v) e le hp,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_conseq ge fe f_inflate_table
    (?_ : Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) :: l)
        (Hmid bh bc bo L codes cap lensF cntF wF v)) seg9 _)
    (localst_cons (envOf bh bc bo) l _ _ _ hmemM)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  refine localst_perm ge fe (envOf bh bc bo) _ _ _
    (show Hmid bh bc bo L codes cap lensF cntF wF v
      = Hscan bc cntF
        ∗ (Chere bh ∗ (Cofs bo ∗ Cout L codes cap lensF wF v)) from rfl) _ _ ?_
  refine frame_seg_gen ge fe (envOf bh bc bo) _ _ _ seg9 _ _ R
    (fun R' => seg4_triple ge fe bh bc bo cntF M l hcb hM1 hM15 hT32 hTmin R') ?_
  intro e le hp hx
  obtain ⟨h1, h2, hd, heq, ⟨Mn, h1', h2', h3', h4', hst⟩, hQ⟩ := hx
  exact ⟨Mn, h1', h2', h3', h4',
    (localst_sep (envOf bh bc bo) _ _ _ e le hp).mp ⟨h1, h2, hd, heq, hst, hQ⟩⟩

/-! ## Link 11 — `fullBody` segment 10: `if (root < min) root = min;` -/

theorem link_clamp2 (R : Sep.ExitConds) (r Mn : Nat)
    (hr : r < 4294967296) (hMn : Mn < 4294967296) (H : HProp)
    (rest : List (Ident × Val))
    (hmemM : (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int)))) ∈ rest)
    (hne : ∀ p ∈ rest, p.1 ≠ _root) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_root, .Vint (Integers.Int.repr ((r : _root_.Int)))) :: rest) H)
      clamp2Stmt
      { normal := LocalSt (envOf bh bc bo)
          ((_root, .Vint (Integers.Int.repr ((Nat.max r Mn : Nat)))) :: rest) H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_conseq ge fe f_inflate_table
    (clamp2_triple ge fe (envOf bh bc bo) r Mn rest H hr hMn hmemM hne)
    (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-! ## Link 12 — `fullBody` segment 11: `left = 1;` -/

theorem link_init_left (R : Sep.ExitConds) (H : HProp)
    (l : List (Ident × Val)) (hne : ∀ p ∈ l, p.1 ≠ _left) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H)
      initLeft
      { normal := LocalSt (envOf bh bc bo)
          ((_left, .Vint (Integers.Int.repr 1)) :: l) H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine triple_conseq ge fe f_inflate_table
    (set_const_triple ge fe (envOf bh bc bo) l H _left 1 hne)
    (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim)

/-! ## The return condition the chain runs under -/

/-- The spec's postcondition, as the `Ret` every returning segment is given. -/
abbrev RetSpec : Val → HProp :=
  (inflateTableSpec L ty codes cap b0 lensF workF).post

/-- **Every `return` site's obligation, discharged once.**  A returning segment
    hands back `Cout` (its `Hrest`), and that is exactly `Cret` at the current
    `*table`/`*bits` values, which `postHeap_of_Cret` turns into `postHeap`. -/
theorem ret_of_Cout (r : _root_.Int) (hr3 : r = -1 ∨ r = 0 ∨ r = 1)
    (wF : Nat → Nat) (bv : Val) :
    ∀ hp, Cout L codes cap lensF wF bv hp →
      RetSpec L ty codes cap b0 lensF workF (.Vint (Integers.Int.repr r)) hp :=
  fun hp hx => ⟨⟨r, rfl, hr3⟩,
    postHeap_of_Cret L codes cap lensF wF (.Vptr L.tB L.tO) bv hp hx⟩

/-! ## Link 13 — `fullBody` segment 12: `left = 1; len = 1;` then loop 5

The over-subscription (Kraft) check.  This segment **can return** `-1`, so it is
*not* framed: `H5 bh bc bo cntF Hrest` is `Hmid` with `Hrest := Cout` — the same
heap, already in the right order — and `seg5_triple`'s `hret` receives exactly
`Cout`, the residual after `freeList` frees the three locals. -/

theorem link_kraft (R : Sep.ExitConds) (cntF wF : Nat → Nat) (bv : Integers.Int)
    (T : List (Ident × Val))
    (hcb : ∀ j, cntF j < 65536)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hT31 : ∀ p ∈ T, p.1 ≠ _t'31) (hTleft : ∀ p ∈ T, p.1 ≠ _left)
    (hTlen : ∀ p ∈ T, p.1 ≠ _len) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_left, .Vint (Integers.Int.repr 1)) :: T)
        (Hmid bh bc bo L codes cap lensF cntF wF (.Vint bv)))
      seg12
      { normal := Post5 bh bc bo cntF
          (Cout L codes cap lensF wF (.Vint bv)) T,
        brk := R.brk, cont := R.cont,
        ret := RetSpec L ty codes cap b0 lensF workF,
        goto := fun _ => Assn.no } :=
  seg5_triple ge fe bh bc bo cntF (Cout L codes cap lensF wF (.Vint bv)) T
    hcb hcenv hd1 hd2 hd3 hT31 hTleft hTlen
    (RetSpec L ty codes cap b0 lensF workF)
    (fun hr hx => ret_of_Cout L ty codes cap b0 lensF workF (-1)
      (Or.inl rfl) wF (.Vint bv) hr hx) R

/-! ## Link 14 — `fullBody` segment 13: the incomplete-set check

`if (left > 0 && (type == CODES || max != 1)) return -1;` — inftrees.c:146-147. -/

theorem link_chk6 (lv tyv : _root_.Int) (M : Nat) (cntF wF : Nat → Nat)
    (bv : Integers.Int) (l : List (Ident × Val))
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hlv1 : -2147483648 ≤ lv) (hlv2 : lv < 2147483648)
    (hty1 : 0 ≤ tyv) (hty2 : tyv < 3) (hM : M ≤ 15)
    (hmemLv : (_left, .Vint (Integers.Int.repr lv)) ∈ l)
    (hmemTy : (_type, .Vint (Integers.Int.repr tyv)) ∈ l)
    (hmemM : (_max, .Vint (Integers.Int.repr ((M : _root_.Int)))) ∈ l)
    (hT3 : ∀ p ∈ l, p.1 ≠ _t'3) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (Hmid bh bc bo L codes cap lensF cntF wF (.Vint bv)))
      chk6
      { normal := fun e le hp => (lv ≤ 0 ∨ (tyv ≠ 0 ∧ M = 1)) ∧
          LocalSt (envOf bh bc bo)
            ((_t'3, .Vint (Integers.Int.repr 0)) :: l)
            (Hmid bh bc bo L codes cap lensF cntF wF (.Vint bv)) e le hp,
        brk := Assn.no, cont := Assn.no,
        ret := RetSpec L ty codes cap b0 lensF workF,
        goto := fun _ => Assn.no } :=
  chk6_triple ge fe bh bc bo cntF (Cout L codes cap lensF wF (.Vint bv)) l
    lv tyv M hcenv hd1 hd2 hd3 hlv1 hlv2 hty1 hty2 hM hmemLv hmemTy hmemM hT3
    (RetSpec L ty codes cap b0 lensF workF)
    (fun hr hx => ret_of_Cout L ty codes cap b0 lensF workF (-1)
      (Or.inl rfl) wF (.Vint bv) hr hx)

/-! ## Links 15-16 — `fullBody` segments 14 and 15

`offs[1] = 0;` and then `for (len = 1; len < MAXBITS; len++) offs[len+1] = …`.
These are **two** slots of `fullBody`'s spine, so `Body.seg6_triple` (which
bundles them into one `Ssequence`) does not apply — `Body.seg6b_triple` is the
second half on its own. -/

/-- `count` and `offs` adjacent, with the rest framed. -/
theorem Hmid_cnt_offs (cntF wF : Nat → Nat) (v : Val) :
    Hmid bh bc bo L codes cap lensF cntF wF v
      = (Hscan bc cntF ∗ Cofs bo)
        ∗ (Chere bh ∗ Cout L codes cap lensF wF v) := by
  simp only [Hmid, Ccnt, Cofs, Chere]
  sep_cancel

theorem link_offs_init (R : Sep.ExitConds) (cntF wF : Nat → Nat) (v : Val)
    (T : List (Ident × Val)) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T
        (Hmid bh bc bo L codes cap lensF cntF wF v))
      offs1Init
      { normal := LocalSt (envOf bh bc bo) T
          (H6 bc bo cntF 1 ∗ (Chere bh ∗ Cout L codes cap lensF wF v)),
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine localst_perm ge fe (envOf bh bc bo) _ _ _
    (Hmid_cnt_offs bh bc bo L codes cap lensF cntF wF v) _ _ ?_
  exact frame_seg ge fe (envOf bh bc bo) T T _ _
    (Chere bh ∗ Cout L codes cap lensF wF v) offs1Init R
    (fun R' => triple_conseq ge fe f_inflate_table
      (offs_init_triple ge fe bh bc bo cntF T)
      (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ hx => hx.elim))

theorem link_offs_loop (R : Sep.ExitConds) (cntF wF : Nat → Nat) (v : Val)
    (T : List (Ident × Val))
    (hos : ∀ j, offsC cntF j < 65536) (hcb : ∀ j, cntF j < 65536)
    (hTlen : ∀ p ∈ T, p.1 ≠ _len)
    (hT29 : ∀ p ∈ T, p.1 ≠ _t'29) (hT30 : ∀ p ∈ T, p.1 ≠ _t'30) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T
        (H6 bc bo cntF 1 ∗ (Chere bh ∗ Cout L codes cap lensF wF v)))
      seg15
      { normal := LocalSt (envOf bh bc bo)
          ((_len, .Vint (Integers.Int.repr (((15 : Nat) : _root_.Int)))) :: T)
          (H6 bc bo cntF 15 ∗ (Chere bh ∗ Cout L codes cap lensF wF v)),
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } :=
  frame_seg ge fe (envOf bh bc bo) T _ _ _
    (Chere bh ∗ Cout L codes cap lensF wF v) seg15 R
    (fun R' => seg6b_triple ge fe bh bc bo cntF T hos hcb hTlen hT29 hT30 R')

/-! ## Link 17 — `fullBody` segment 16: `sym = 0;` then the sort loop -/

/-- After loop 6 the offsets are `offsC cnt`, which is `sortOffs cnt lensF 0`:
    no symbol has been placed yet. -/
theorem sortOffs_zero (cntF : Nat → Nat) :
    sortOffs cntF lensF 0 = offsC cntF := by
  funext l
  show offsC cntF l + InflateTable.Model.count lensF 0 l = offsC cntF l
  simp [InflateTable.Model.count]

theorem H6_as_H7 (cntF wF : Nat → Nat) (v : Val) :
    H6 bc bo cntF 15 ∗ (Chere bh ∗ Cout L codes cap lensF wF v)
      = H7 bo L.pl L.pw L.lensB L.workB L.lensO L.workO codes lensF wF
            (sortOffs cntF lensF 0)
        ∗ (Ccnt bc cntF ∗ (Chere bh
            ∗ (Ctbl L ∗ (Cbits L v ∗ (Creg L cap ∗ Cglob L))))) := by
  rw [sortOffs_zero lensF cntF]
  simp only [H6, H7, Hoffs_eq_HoffsAt, Cout, Ccnt, Chere, Clens, Cwork, Ctbl,
    Cbits, Creg, Cglob, Hscan]
  sep_cancel

theorem link_sort (R : Sep.ExitConds) (cntF wF : Nat → Nat) (v : Val)
    (T : List (Ident × Val))
    (hpl : permOrder L.pl .Readable = true)
    (hpw : permOrder L.pw .Writable = true)
    (hlb : ∀ j, lensF j < 65536) (hwb : ∀ j, wF j < 65536)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs cntF lensF s j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15) (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned L.lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoW : Integers.Ptrofs.unsigned L.workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hcnt : cntF = fun j => InflateTable.Model.count lensF codes j)
    (hmemL : (_lens, .Vptr L.lensB L.lensO) ∈ T)
    (hmemW : (_work, .Vptr L.workB L.workO) ∈ T)
    (hmemC : (_codes, .Vint (Integers.Int.repr ((codes : _root_.Int)))) ∈ T)
    (hTt : ∀ p ∈ T, p.1 ≠ _t'4 ∧ p.1 ≠ _t'26 ∧ p.1 ≠ _t'27 ∧ p.1 ≠ _t'28)
    (hTsym : ∀ p ∈ T, p.1 ≠ _sym) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) T
        (H6 bc bo cntF 15 ∗ (Chere bh ∗ Cout L codes cap lensF wF v)))
      seg16
      { normal := fun e le hp =>
          (Post7 bh bc bo L.pl L.pw L.lensB L.workB L.lensO L.workO codes lensF
             cntF T e le ∗ (Ccnt bc cntF ∗ (Chere bh
               ∗ (Ctbl L ∗ (Cbits L v ∗ (Creg L cap ∗ Cglob L))))) ) hp,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } := by
  refine localst_perm ge fe (envOf bh bc bo) _ _ _
    (H6_as_H7 bh bc bo L codes cap lensF cntF wF v) _ _ ?_
  exact frame_seg_gen ge fe (envOf bh bc bo) T _ _ seg16 _ _ R
    (fun R' => seg7_triple ge fe bh bc bo L.pl L.pw L.lensB L.workB L.lensO
      L.workO codes lensF cntF T hpl hpw hlb hgb hlens15 hc16 hnoL hnoW hcnt
      hmemL hmemW hmemC hTt hTsym wF hwb R')
    (fun _ _ _ x => x)

/-! ## Link 18 — `fullBody` segment 17: `switch (type)`

Heap-polymorphic in all three arms, so the four-vs-two static-tables question
does **not** arise here: it only matters once `Hrest` is fixed, after the
switch. -/

theorem link_switch_LENS (R : Sep.ExitConds) (H : HProp)
    (l : List (Ident × Val))
    (hnoL : (envOf bh bc bo).get _lbase = none)
    (hnoX : (envOf bh bc bo).get _lext = none)
    (hsymL : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hsymX : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hmemTy : (_type, .Vint (Integers.Int.repr 1)) ∈ l)
    (hneB : ∀ p ∈ l, p.1 ≠ _base) (hneX : ∀ p ∈ l, p.1 ≠ _extra)
    (hneM : ∀ p ∈ l, p.1 ≠ _match) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H) switchStmt
      { normal := LocalSt (envOf bh bc bo)
          ((_match, .Vint (Integers.Int.repr 257))
            :: (_extra, .Vptr L.lxB Integers.Ptrofs.zero)
            :: (_base, .Vptr L.lbB Integers.Ptrofs.zero) :: l) H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } :=
  switch_LENS_triple ge fe bh bc bo l H L.lbB L.lxB hnoL hnoX hsymL hsymX
    hmemTy hneB hneX hneM R

theorem link_switch_CODES (R : Sep.ExitConds) (H : HProp)
    (l : List (Ident × Val))
    (hmemTy : (_type, .Vint (Integers.Int.repr 0)) ∈ l)
    (hne : ∀ p ∈ l, p.1 ≠ _match) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H) switchStmt
      { normal := LocalSt (envOf bh bc bo)
          ((_match, .Vint (Integers.Int.repr 20)) :: l) H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } :=
  switch_CODES_triple ge fe bh bc bo l H hmemTy hne R

theorem link_switch_DISTS (R : Sep.ExitConds) (H : HProp)
    (l : List (Ident × Val))
    (hnoD : (envOf bh bc bo).get _dbase = none)
    (hnoX : (envOf bh bc bo).get _dext = none)
    (hsymD : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hsymX : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hmemTy : (_type, .Vint (Integers.Int.repr 2)) ∈ l)
    (hneB : ∀ p ∈ l, p.1 ≠ _base) (hneX : ∀ p ∈ l, p.1 ≠ _extra) :
    Triple ge fe f_inflate_table (LocalSt (envOf bh bc bo) l H) switchStmt
      { normal := LocalSt (envOf bh bc bo)
          ((_extra, .Vptr L.dxB Integers.Ptrofs.zero)
            :: (_base, .Vptr L.dbB Integers.Ptrofs.zero) :: l) H,
        brk := R.brk, cont := R.cont, ret := R.ret, goto := R.goto } :=
  switch_DISTS_triple ge fe bh bc bo l H L.dbB L.dxB hnoD hnoX hsymD hsymX
    hmemTy hneB hneX R

/-! ## The spine, stage A — `fullBody` slots 1-6

Six `triple_seq` steps: the three prologue `Sset`s, the two counting loops, and
the `*bits` read.  The tail is abstract, so stages B and C plug into it. -/

/-- The tracked list after slot 6 (`root = *bits`). -/
abbrev T6 : List (Ident × Val) :=
  (_root, .Vint (Integers.Int.repr ((b0 : _root_.Int))))
    :: (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
    :: (_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
    :: T0 L ty codes

theorem spine_A (tail : Stmt) (R : Sep.ExitConds)
    (hpl : permOrder L.pl .Readable = true)
    (hpb : permOrder L.pb .Readable = true)
    (hb : ∀ j, lensF j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hc16 : codes < 65536)
    (hnoL : Integers.Ptrofs.unsigned L.lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (htail : Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) (T6 L ty codes b0)
        (Hmid bh bc bo L codes cap lensF (cntC codes lensF) workF
          (.Vint (Integers.Int.repr ((b0 : _root_.Int)))))) tail R) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) (entryTemps L ty codes)
        (Hpro bh bc bo L codes cap b0 lensF workF))
      (.Ssequence setBase (.Ssequence setExtra (.Ssequence setMatch
        (.Ssequence seg3 (.Ssequence seg4 (.Ssequence readRoot tail))))))
      R := by
  refine triple_seq_fwd ge fe f_inflate_table _ _ _ _ _
    (set_null_triple ge fe (envOf bh bc bo) _ _ _base (by temps_ne)) ?_
  refine triple_seq_fwd ge fe f_inflate_table _ _ _ _ _
    (set_null_triple ge fe (envOf bh bc bo) _ _ _extra (by temps_ne)) ?_
  refine triple_seq_fwd ge fe f_inflate_table _ _ _ _ _
    (set_const_triple ge fe (envOf bh bc bo) _ _ _match 0 (by temps_ne)) ?_
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (link_zero_count ge fe bh bc bo L ty codes cap b0 lensF workF R) ?_
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (link_count_lens ge fe bh bc bo L ty codes cap b0 lensF workF R
      hpl hb hlens15 hc16 hnoL) ?_
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (link_read_root ge fe bh bc bo L ty codes cap b0 lensF workF R hpb) ?_
  -- the ambient heap is now in canonical component order
  refine localst_perm ge fe (envOf bh bc bo) _ _ _
    (link6_as_Hmid bh bc bo L codes cap b0 lensF workF) _ _ htail

/-! ## The spine, stage B — `fullBody` slots 7-12

The `max` scan, its clamp, the empty-code `if`, the `min` scan, its clamp, and
`left = 1`.  Two existential bounds (`M`, `Mn`) are peeled here, and the tracked
list is permuted twice so `_root` heads it for the clamps — **dropping the stale
`_root` binding in the process**, which is what keeps `TempsHold` satisfiable
(two entries for one identifier at different values is unsatisfiable). -/

/-- The tracked list after slot 8 (the first clamp). -/
abbrev T8 (M : Nat) : List (Ident × Val) :=
  (_root, .Vint (Integers.Int.repr ((Nat.min b0 M : Nat))))
    :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
    :: (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
    :: (_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
    :: T0 L ty codes

/-- The tracked list after slot 12 (`left = 1`). -/
abbrev T12 (M Mn : Nat) : List (Ident × Val) :=
  (_left, .Vint (Integers.Int.repr 1))
    :: (_root, .Vint (Integers.Int.repr ((Nat.max (Nat.min b0 M) Mn : Nat))))
      :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
      :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
      :: (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
      :: (_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
      :: T0 L ty codes

theorem spine_B (tail : Stmt) (R : Sep.ExitConds) (k : Nat) (hcap : cap = 2 + k)
    (hc16 : codes < 65536) (hb032 : b0 < 4294967296)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hptR : permOrder L.pt .Readable = true)
    (hptW : permOrder L.pt .Writable = true)
    (hpbW : permOrder L.pb .Writable = true)
    (hpr : permOrder L.pr .Writable = true)
    (hal : Integers.Ptrofs.unsigned L.tO % 4 = 0)
    (haddr1 : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed L.tO
        (Integers.Int.repr 1)) = Integers.Ptrofs.unsigned L.tO + 4)
    (hRret : R.ret = RetSpec L ty codes cap b0 lensF workF)
    (htail : ∀ M Mn : Nat, M ≤ 15 → M ≠ 0 → 1 ≤ Mn → Mn ≤ M →
      -- what the two scans *characterise*: `maxLen_char`/`minLen_char` need
      -- these to pin `M` and `Mn` to the model's `maxLen`/`minLen`
      (∀ l, M < l → l ≤ 15 → cntC codes lensF l = 0) →
      (M = 0 ∨ cntC codes lensF M ≠ 0) →
      (∀ j, 1 ≤ j → j < Mn → cntC codes lensF j = 0) →
      (Mn = M ∨ cntC codes lensF Mn ≠ 0) →
      Triple ge fe f_inflate_table
        (LocalSt (envOf bh bc bo) (T12 L ty codes b0 M Mn)
          (Hmid bh bc bo L codes cap lensF (cntC codes lensF) workF
            (.Vint (Integers.Int.repr ((b0 : _root_.Int)))))) tail R) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) (T6 L ty codes b0)
        (Hmid bh bc bo L codes cap lensF (cntC codes lensF) workF
          (.Vint (Integers.Int.repr ((b0 : _root_.Int))))))
      (.Ssequence seg6 (.Ssequence clamp1Stmt
        (.Ssequence (.Sifthenelse (.Ebinop .Oeq (.Etempvar _max tuint)
            (.Econst_int (Integers.Int.repr 0) tint) tint) maxZeroBlock .Sskip)
          (.Ssequence seg9 (.Ssequence clamp2Stmt
            (.Ssequence initLeft tail))))))
      R := by
  -- slot 7: the `max` scan
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (link_max_scan ge fe bh bc bo L codes cap b0 lensF workF R hc16 _
      (by temps_ne) (by temps_ne)) ?_
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (M : Nat) => ?_)
  refine triple_pure ge fe _ _ _ _ (fun hM15 => ?_)
  refine triple_pure ge fe _ _ _ _ (fun hzeroM => ?_)
  refine triple_pure ge fe _ _ _ _ (fun hnzM => ?_)
  -- slot 8: `if (root > max) root = max;` — `_root` to the head, stale copy gone
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (triple_conseq ge fe f_inflate_table
      (link_clamp1 ge fe bh bc bo R b0 M hb032 (by omega) _
        ((_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
          :: (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
          :: (_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
          :: T0 L ty codes)
        (by temps_mem) (by temps_ne))
      (localst_mono (envOf bh bc bo) _ _ _ (by temps_mem))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)) ?_
  -- slot 9: the empty-code block
  subst hcap
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (triple_conseq ge fe f_inflate_table
      (link_maxzero ge fe bh bc bo L codes lensF R M (by omega) k
        (cntC codes lensF) workF _ (T8 L ty codes b0 M) hcenv hd1 hd2 hd3
        hptR hptW hpbW hpr hal haddr1 (by temps_mem) (by temps_mem)
        (by temps_mem) (by temps_ne) (by temps_ne) R.ret
        (fun hr hx => by rw [hRret]; exact ⟨⟨0, rfl, Or.inr (Or.inl rfl)⟩, hx⟩))
      (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim) (fun _ _ x => x)
      (fun _ _ _ _ hx => hx.elim)) ?_
  refine triple_pure ge fe _ _ _ _ (fun hM0 => ?_)
  -- slot 10: the `min` scan
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (link_min_scan ge fe bh bc bo L codes (2 + k) lensF R M (by omega) hM15
      hc16 _ workF _ _ (fun j => cntC_lt codes lensF j hc16) (by temps_mem)
      (by temps_ne) (by temps_ne)) ?_
  refine triple_exists ge fe f_inflate_table _ _ _ (fun (Mn : Nat) => ?_)
  refine triple_pure ge fe _ _ _ _ (fun hMn1 => ?_)
  refine triple_pure ge fe _ _ _ _ (fun hMnM => ?_)
  refine triple_pure ge fe _ _ _ _ (fun hzeroMn => ?_)
  refine triple_pure ge fe _ _ _ _ (fun hnzMn => ?_)
  -- slot 11: `if (root < min) root = min;`
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (triple_conseq ge fe f_inflate_table
      (link_clamp2 ge fe bh bc bo R (Nat.min b0 M) Mn
        (Nat.lt_of_le_of_lt (Nat.min_le_left b0 M) hb032) (by omega) _
        ((_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
          :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
          :: (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
          :: (_len, .Vint (Integers.Int.repr (((16 : Nat) : _root_.Int))))
          :: T0 L ty codes)
        (by temps_mem) (by temps_ne))
      (localst_mono (envOf bh bc bo) _ _ _ (by temps_mem))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)) ?_
  -- slot 12: `left = 1;`
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (link_init_left ge fe bh bc bo R _ _ (by temps_ne)) ?_
  exact triple_conseq ge fe f_inflate_table
    (htail M Mn hM15 hM0 hMn1 hMnM hzeroM hnzM hzeroMn hnzMn)
    (localst_mono (envOf bh bc bo) _ _ _ (by temps_mem))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-- `left` stays in `int` range.  `leftC` starts at 1 and each step is
    `2 * left - count`, so with the nonnegativity `Post5` already carries it is
    bounded by `2^15`.  Stated with **normalised indices** — `leftC cntF (0+1)`
    and `leftC cntF 1` are different atoms to `omega`, the trap the Kraft proof
    already documents. -/
theorem leftC_bound (cntF : Nat → Nat)
    (hnn : ∀ j, j ≤ 15 → 0 ≤ leftC cntF j) :
    -2147483648 ≤ leftC cntF 15 ∧ leftC cntF 15 < 2147483648 := by
  have h0 : leftC cntF 0 = 1 := rfl
  have e1 : leftC cntF 1 = 2 * leftC cntF 0 - ((cntF 1 : Nat) : _root_.Int) := rfl
  have e2 : leftC cntF 2 = 2 * leftC cntF 1 - ((cntF 2 : Nat) : _root_.Int) := rfl
  have e3 : leftC cntF 3 = 2 * leftC cntF 2 - ((cntF 3 : Nat) : _root_.Int) := rfl
  have e4 : leftC cntF 4 = 2 * leftC cntF 3 - ((cntF 4 : Nat) : _root_.Int) := rfl
  have e5 : leftC cntF 5 = 2 * leftC cntF 4 - ((cntF 5 : Nat) : _root_.Int) := rfl
  have e6 : leftC cntF 6 = 2 * leftC cntF 5 - ((cntF 6 : Nat) : _root_.Int) := rfl
  have e7 : leftC cntF 7 = 2 * leftC cntF 6 - ((cntF 7 : Nat) : _root_.Int) := rfl
  have e8 : leftC cntF 8 = 2 * leftC cntF 7 - ((cntF 8 : Nat) : _root_.Int) := rfl
  have e9 : leftC cntF 9 = 2 * leftC cntF 8 - ((cntF 9 : Nat) : _root_.Int) := rfl
  have e10 : leftC cntF 10 = 2 * leftC cntF 9 - ((cntF 10 : Nat) : _root_.Int) := rfl
  have e11 : leftC cntF 11 = 2 * leftC cntF 10 - ((cntF 11 : Nat) : _root_.Int) := rfl
  have e12 : leftC cntF 12 = 2 * leftC cntF 11 - ((cntF 12 : Nat) : _root_.Int) := rfl
  have e13 : leftC cntF 13 = 2 * leftC cntF 12 - ((cntF 13 : Nat) : _root_.Int) := rfl
  have e14 : leftC cntF 14 = 2 * leftC cntF 13 - ((cntF 14 : Nat) : _root_.Int) := rfl
  have e15 : leftC cntF 15 = 2 * leftC cntF 14 - ((cntF 15 : Nat) : _root_.Int) := rfl
  have n0 := hnn 0 (by omega)
  have n1 := hnn 1 (by omega)
  have n2 := hnn 2 (by omega)
  have n3 := hnn 3 (by omega)
  have n4 := hnn 4 (by omega)
  have n5 := hnn 5 (by omega)
  have n6 := hnn 6 (by omega)
  have n7 := hnn 7 (by omega)
  have n8 := hnn 8 (by omega)
  have n9 := hnn 9 (by omega)
  have n10 := hnn 10 (by omega)
  have n11 := hnn 11 (by omega)
  have n12 := hnn 12 (by omega)
  have n13 := hnn 13 (by omega)
  have n14 := hnn 14 (by omega)
  have n15 := hnn 15 (by omega)
  have c0 : (0 : _root_.Int) ≤ ((cntF 0 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c1 : (0 : _root_.Int) ≤ ((cntF 1 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c2 : (0 : _root_.Int) ≤ ((cntF 2 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c3 : (0 : _root_.Int) ≤ ((cntF 3 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c4 : (0 : _root_.Int) ≤ ((cntF 4 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c5 : (0 : _root_.Int) ≤ ((cntF 5 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c6 : (0 : _root_.Int) ≤ ((cntF 6 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c7 : (0 : _root_.Int) ≤ ((cntF 7 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c8 : (0 : _root_.Int) ≤ ((cntF 8 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c9 : (0 : _root_.Int) ≤ ((cntF 9 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c10 : (0 : _root_.Int) ≤ ((cntF 10 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c11 : (0 : _root_.Int) ≤ ((cntF 11 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c12 : (0 : _root_.Int) ≤ ((cntF 12 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c13 : (0 : _root_.Int) ≤ ((cntF 13 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c14 : (0 : _root_.Int) ≤ ((cntF 14 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  have c15 : (0 : _root_.Int) ≤ ((cntF 15 : Nat) : _root_.Int) := Int.ofNat_nonneg _
  omega

/-! ## The spine, stage C — `fullBody` slots 13-17

The Kraft check, the incomplete-set check, the offsets, loop 6, and the sort
loop.  This is where **stale tracked entries have to be dropped**: `_len` before
slots 13 and 16 (loops 5 and 6 rebind it) and `_sym` before slot 17 (the sort
loop rebinds it).  Each drop is one `localst_mono` closed by `temps_mem`.

The tail begins at the `switch`, which is where the `ty` split goes. -/

/-- The tracked list entering slot 13, with the stale `_len` already dropped. -/
abbrev T13 (M Mn : Nat) : List (Ident × Val) :=
  (_root, .Vint (Integers.Int.repr ((Nat.max (Nat.min b0 M) Mn : Nat))))
    :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
    :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
    :: (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
    :: T0 L ty codes

/-- The tracked list the sort loop leaves — the `switch`'s starting point. -/
abbrev Tsort (M Mn : Nat) (lv : _root_.Int) : List (Ident × Val) :=
  (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
    :: (_len, .Vint (Integers.Int.repr (((15 : Nat) : _root_.Int))))
    :: (_t'3, .Vint (Integers.Int.repr 0))
    :: (_left, .Vint (Integers.Int.repr lv))
    :: (_root, .Vint (Integers.Int.repr ((Nat.max (Nat.min b0 M) Mn : Nat))))
    :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
    :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
    :: T0 L ty codes

/-- The heap the sort loop leaves. -/
abbrev Hsort (wF : Nat → Nat) : HProp :=
  H7 bo L.pl L.pw L.lensB L.workB L.lensO L.workO codes lensF wF
      (sortOffs (cntC codes lensF) lensF codes)
  ∗ (Ccnt bc (cntC codes lensF) ∗ (Chere bh
      ∗ (Ctbl L ∗ (Cbits L (.Vint (Integers.Int.repr ((b0 : _root_.Int))))
          ∗ (Creg L cap ∗ Cglob L)))))

theorem spine_C (tail : Stmt) (R : Sep.ExitConds) (M Mn : Nat)
    (hM15 : M ≤ 15) (hMn1 : 1 ≤ Mn) (hMnM : Mn ≤ M)
    (hc16 : codes < 65536)
    (hty0 : 0 ≤ ty) (hty3 : ty < 3)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hpl : permOrder L.pl .Readable = true)
    (hpw : permOrder L.pw .Writable = true)
    (hb : ∀ j, lensF j < 65536) (hwb : ∀ j, workF j < 65536)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs (cntC codes lensF) lensF s j < 65536)
    (hos : ∀ j, offsC (cntC codes lensF) j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hnoL : Integers.Ptrofs.unsigned L.lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoW : Integers.Ptrofs.unsigned L.workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hRret : R.ret = RetSpec L ty codes cap b0 lensF workF)
    (htail : ∀ (wF : Nat → Nat),
      (leftC (cntC codes lensF) 15 ≤ 0 ∨ (ty ≠ 0 ∧ M = 1)) →
      (∀ j, j ≤ 15 → 0 ≤ leftC (cntC codes lensF) j) →
      (∀ j, wF j < 65536) → Placed lensF wF codes codes →
      Triple ge fe f_inflate_table
        (LocalSt (envOf bh bc bo)
          (Tsort L ty codes b0 M Mn (leftC (cntC codes lensF) 15))
          (Hsort bh bc bo L codes cap b0 lensF wF)) tail R) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) (T12 L ty codes b0 M Mn)
        (Hmid bh bc bo L codes cap lensF (cntC codes lensF) workF
          (.Vint (Integers.Int.repr ((b0 : _root_.Int))))))
      (.Ssequence seg12 (.Ssequence chk6 (.Ssequence offs1Init
        (.Ssequence seg15 (.Ssequence seg16 tail)))))
      R := by
  -- slot 13: the Kraft check.  Drop the stale `_len` — loop 5 rebinds it.
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (triple_conseq ge fe f_inflate_table
      (link_kraft ge fe bh bc bo L ty codes cap b0 lensF workF R
        (cntC codes lensF) workF (Integers.Int.repr ((b0 : _root_.Int)))
        (T13 L ty codes b0 M Mn)
        (fun j => cntC_lt codes lensF j hc16) hcenv hd1 hd2 hd3
        (by temps_ne) (by temps_ne) (by temps_ne))
      (localst_mono (envOf bh bc bo) _ _ _ (by temps_mem))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => by rw [hRret]; exact x)) ?_
  refine triple_pure ge fe _ _ _ _ (fun hnn => ?_)
  -- slot 14: the incomplete-set check
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (triple_conseq ge fe f_inflate_table
      (link_chk6 ge fe bh bc bo L ty codes cap b0 lensF workF
        (leftC (cntC codes lensF) 15) ty M (cntC codes lensF) workF
        (Integers.Int.repr ((b0 : _root_.Int))) _
        hcenv hd1 hd2 hd3 (leftC_bound (cntC codes lensF) hnn).1
        (leftC_bound (cntC codes lensF) hnn).2 hty0 hty3 hM15
        (by temps_mem) (by temps_mem) (by temps_mem) (by temps_ne))
      (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ hx => hx.elim) (fun _ _ _ hx => hx.elim)
      (fun _ _ x => by rw [hRret]; exact x)
      (fun _ _ _ _ hx => hx.elim)) ?_
  refine triple_pure ge fe _ _ _ _ (fun hchk => ?_)
  -- slot 15: `offs[1] = 0;`
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (link_offs_init ge fe bh bc bo L codes cap lensF R (cntC codes lensF)
      workF _ _) ?_
  -- slot 16: loop 6.  Drop the stale `_len` again — loop 6 rebinds it.
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (triple_conseq ge fe f_inflate_table
      (link_offs_loop ge fe bh bc bo L codes cap lensF R (cntC codes lensF)
        workF _
        ((_t'3, .Vint (Integers.Int.repr 0))
          :: (_left, .Vint (Integers.Int.repr (leftC (cntC codes lensF) 15)))
          :: T13 L ty codes b0 M Mn)
        hos (fun j => cntC_lt codes lensF j hc16)
        (by temps_ne) (by temps_ne) (by temps_ne))
      (localst_mono (envOf bh bc bo) _ _ _ (by temps_mem))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)) ?_
  -- slot 17: the sort loop.  Drop the stale `_sym` — it rebinds that.
  refine triple_seq ge fe f_inflate_table _ _ _ _ _
    (triple_conseq ge fe f_inflate_table
      (link_sort ge fe bh bc bo L codes cap lensF R (cntC codes lensF) workF _
        ((_len, .Vint (Integers.Int.repr (((15 : Nat) : _root_.Int))))
          :: (_t'3, .Vint (Integers.Int.repr 0))
          :: (_left, .Vint (Integers.Int.repr (leftC (cntC codes lensF) 15)))
          :: (_root, .Vint (Integers.Int.repr
               ((Nat.max (Nat.min b0 M) Mn : Nat))))
          :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
          :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
          :: T0 L ty codes)
        hpl hpw hb hwb hgb hlens15 hc16 hnoL hnoW rfl
        (by temps_mem) (by temps_mem) (by temps_mem)
        -- the four-way conjunction defeats `temps_ne`'s single `decide`;
        -- split it and let each disequality be decided on its own
        (by intro p hp
            refine ⟨?_, ?_, ?_, ?_⟩ <;> (revert hp; revert p; temps_ne))
        (by temps_ne))
      (localst_mono (envOf bh bc bo) _ _ _ (by temps_mem))
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x)) ?_
  -- peel the sort loop's existential `work` contents and hand off
  refine triple_conseq ge fe f_inflate_table
    (triple_exists ge fe f_inflate_table
      (fun (wF : Nat → Nat) e le hp => (∀ j, wF j < 65536) ∧
        (Placed lensF wF codes codes ∧
         LocalSt (envOf bh bc bo)
           (Tsort L ty codes b0 M Mn (leftC (cntC codes lensF) 15))
           (Hsort bh bc bo L codes cap b0 lensF wF) e le hp))
      tail R
      (fun wF => triple_pure ge fe _ _ _ _ (fun hwF =>
        triple_pure ge fe _ _ _ _ (fun hplc => htail wF hchk hnn hwF hplc))))
    (fun e le hp hx => ?_)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  obtain ⟨h1, h2, hdx, heq, ⟨wF, hwF, hplc, hst⟩, hQ⟩ := hx
  exact ⟨wF, hwF, hplc,
    localst_mono (envOf bh bc bo) _ _ _ (by temps_mem) e le hp
      ((localst_sep (envOf bh bc bo) _ _ _ e le hp).mp
        ⟨h1, h2, hdx, heq, hst, hQ⟩)⟩

/-! ## The spine, assembled — `fullBody` slots 1-17

Stages A, B and C composed.  The tail begins at the `switch` (slot 18), which is
where the `ty` split goes, so everything here is proved **once** for all three
code types. -/

theorem spine_prefix (tail : Stmt) (R : Sep.ExitConds) (k : Nat)
    (hcap : cap = 2 + k)
    (hc16 : codes < 65536) (hb032 : b0 < 4294967296)
    (hty0 : 0 ≤ ty) (hty3 : ty < 3)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hpl : permOrder L.pl .Readable = true)
    (hpw : permOrder L.pw .Writable = true)
    (hpbR : permOrder L.pb .Readable = true)
    (hpbW : permOrder L.pb .Writable = true)
    (hptR : permOrder L.pt .Readable = true)
    (hptW : permOrder L.pt .Writable = true)
    (hpr : permOrder L.pr .Writable = true)
    (hb : ∀ j, lensF j < 65536) (hwb : ∀ j, workF j < 65536)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs (cntC codes lensF) lensF s j < 65536)
    (hos : ∀ j, offsC (cntC codes lensF) j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hnoL : Integers.Ptrofs.unsigned L.lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoW : Integers.Ptrofs.unsigned L.workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hal : Integers.Ptrofs.unsigned L.tO % 4 = 0)
    (haddr1 : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed L.tO
        (Integers.Int.repr 1)) = Integers.Ptrofs.unsigned L.tO + 4)
    (hRret : R.ret = RetSpec L ty codes cap b0 lensF workF)
    (htail : ∀ (M Mn : Nat) (wF : Nat → Nat), M ≤ 15 → M ≠ 0 → 1 ≤ Mn → Mn ≤ M →
      (∀ l, M < l → l ≤ 15 → cntC codes lensF l = 0) →
      (M = 0 ∨ cntC codes lensF M ≠ 0) →
      (∀ j, 1 ≤ j → j < Mn → cntC codes lensF j = 0) →
      (Mn = M ∨ cntC codes lensF Mn ≠ 0) →
      (leftC (cntC codes lensF) 15 ≤ 0 ∨ (ty ≠ 0 ∧ M = 1)) →
      (∀ j, j ≤ 15 → 0 ≤ leftC (cntC codes lensF) j) →
      (∀ j, wF j < 65536) → Placed lensF wF codes codes →
      Triple ge fe f_inflate_table
        (LocalSt (envOf bh bc bo)
          (Tsort L ty codes b0 M Mn (leftC (cntC codes lensF) 15))
          (Hsort bh bc bo L codes cap b0 lensF wF)) tail R) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) (entryTemps L ty codes)
        (Hpro bh bc bo L codes cap b0 lensF workF))
      (.Ssequence setBase (.Ssequence setExtra (.Ssequence setMatch
        (.Ssequence seg3 (.Ssequence seg4 (.Ssequence readRoot
          (.Ssequence seg6 (.Ssequence clamp1Stmt
            (.Ssequence (.Sifthenelse (.Ebinop .Oeq (.Etempvar _max tuint)
                (.Econst_int (Integers.Int.repr 0) tint) tint)
                maxZeroBlock .Sskip)
              (.Ssequence seg9 (.Ssequence clamp2Stmt (.Ssequence initLeft
                (.Ssequence seg12 (.Ssequence chk6 (.Ssequence offs1Init
                  (.Ssequence seg15 (.Ssequence seg16 tail)))))))))))))))))
      R :=
  spine_A ge fe bh bc bo L ty codes cap b0 lensF workF _ R hpl hpbR hb hlens15
    hc16 hnoL
    (spine_B ge fe bh bc bo L ty codes cap b0 lensF workF _ R k hcap hc16 hb032
      hcenv hd1 hd2 hd3 hptR hptW hpbW hpr hal haddr1 hRret
      (fun M Mn hM15 hM0 hMn1 hMnM hzeroM hnzM hzeroMn hnzMn =>
        spine_C ge fe bh bc bo L ty codes cap b0 lensF workF _ R M Mn hM15 hMn1
          hMnM hc16 hty0 hty3 hcenv hd1 hd2 hd3 hpl hpw hb hwb hgb hos hlens15
          hnoL hnoW hRret
          (fun wF hchk hnn hwF hplc => htail M Mn wF hM15 hM0 hMn1 hMnM hzeroM
            hnzM hzeroMn hnzMn hchk hnn hwF hplc)))

/-! ## The spine guard

`spine_prefix` is stated over a hand-written `Ssequence` nest, so it needs the
same protection `Body.body_matches` gives the segments: a `rfl` pinning it to
the real program.  Without this, a mis-transcribed spine would be a proof about
a statement `inflate_table` does not contain — and the association traps that
bit `bwIncBlock` and `seg6_triple` show that is not a hypothetical. -/

/-- Everything after the sort loop: the `switch`, the main loop's setup, the
    loop itself, and the epilogue — the part `body_of_tail` reduces
    `Entry.BodyTriple` to. -/
abbrev fullBodyTail : Stmt :=
  .Ssequence switchStmt
  (.Ssequence setHuff0
  (.Ssequence setSym0
  (.Ssequence setLenMin
  (.Ssequence setNextTbl
  (.Ssequence setCurrRoot
  (.Ssequence setDrop0
  (.Ssequence setLowM1
  (.Ssequence setUsed
  (.Ssequence setMask
  (.Ssequence (enoughChk _t'5 _t'6)
  (.Ssequence (.Sloop loopBody .Sskip)
  (.Ssequence epilogueIf
  (.Ssequence bumpTableUsed
  (.Ssequence setBitsRoot
  (retZero)))))))))))))))

/-- **THE SPINE GUARD.**  The seventeen slots `spine_prefix` chains are exactly
    `f_inflate_table`'s first seventeen, in order, with `fullBodyTail` after. -/
theorem spine_matches :
    f_inflate_table.fn_body
      = (.Ssequence setBase (.Ssequence setExtra (.Ssequence setMatch
        (.Ssequence seg3 (.Ssequence seg4 (.Ssequence readRoot
          (.Ssequence seg6 (.Ssequence clamp1Stmt
            (.Ssequence (.Sifthenelse (.Ebinop .Oeq (.Etempvar _max tuint)
                (.Econst_int (Integers.Int.repr 0) tint) tint)
                maxZeroBlock .Sskip)
              (.Ssequence seg9 (.Ssequence clamp2Stmt (.Ssequence initLeft
                (.Ssequence seg12 (.Ssequence chk6 (.Ssequence offs1Init
                  (.Ssequence seg15
                    (.Ssequence seg16 fullBodyTail))))))))))))))))) := rfl

/-! ## The `ty` split

The `switch` is the point where the body stops being `type`-independent.  Three
things get instantiated here, all at once:

* **`Hrest`** — `preHeap` owns all four static tables, but `HLoop` carries one
  `base`/`extra` pair; the other pair rides in `Hrest`.  For **CODES** the arm
  assigns *neither*, so `nx = nb = 0` (making `arrayU16 … 0 …` empty) and all
  four tables sit in `Hrest`.
* **`vx`/`vb`** — the `_base`/`_extra` *values*.  For LENS/DISTS they are real
  pointers; for CODES they keep the prologue's `nullv`, which is why `Tfix`
  holds `Val`s rather than pointers — otherwise the CODES branch below would
  be unstatable.
* **`mtch`** — 20, 257, or 0.

`here` is carved into its three fields here too: `HLoop` holds them separately,
because the entry writes them one at a time. -/

/-- The statement after the `switch`: the main loop's setup, the loop, and the
    epilogue.  All three `ty` branches converge on this. -/
abbrev postSwitch : Stmt :=
  .Ssequence setHuff0
  (.Ssequence setSym0
  (.Ssequence setLenMin
  (.Ssequence setNextTbl
  (.Ssequence setCurrRoot
  (.Ssequence setDrop0
  (.Ssequence setLowM1
  (.Ssequence setUsed
  (.Ssequence setMask
  (.Ssequence (enoughChk _t'5 _t'6)
  (.Ssequence (.Sloop loopBody .Sskip)
  (.Ssequence epilogueIf
  (.Ssequence bumpTableUsed
  (.Ssequence setBitsRoot
  (retZero))))))))))))))

theorem fullBodyTail_split : fullBodyTail = .Ssequence switchStmt postSwitch :=
  rfl

/-- `Hsort` in `HLoop`'s order, with the static tables split as `type` dictates.
    `xB`/`bB`/`nx`/`nb`/`extraF`/`baseF`/`Hrest` are the parameters the caller
    chooses; the hypothesis is that they really do partition `Cglob`. -/
theorem Hsort_as_HLoop (wF : Nat → Nat)
    (xB bB : Block) (nx nb : Nat) (extraF baseF : Nat → Nat) (Hrest : HProp)
    (hglob : Cglob L
      = arrayU16 L.pg xB 0 nx extraF
        ∗ (arrayU16 L.pg bB 0 nb baseF ∗ Hrest)) :
    Hsort bh bc bo L codes cap b0 lensF wF
      = HLoop bh bc bo L.pt L.pb L.pr L.pw L.pl L.pg L.tblB L.tblO L.bitsB
          L.bitsO L.tB L.tO cap L.workB L.workO codes wF L.lensB L.lensO codes
          lensF xB bB nx nb extraF baseF Hrest (cntC codes lensF)
          (sortOffs (cntC codes lensF) lensF codes) .Vundef .Vundef .Vundef
          (.Vint (Integers.Int.repr ((b0 : _root_.Int)))) := by
  simp only [Hsort, H7, HLoop, Ccnt, Chere, Ctbl, Cbits, Creg]
  rw [here_carve bh, hglob]
  sep_cancel

/-- **LENS**: `base = lbase`, `extra = lext`, both 31 entries; `dbase`/`dext`
    ride in `Hrest`. -/
theorem glob_LENS :
    Cglob L
      = arrayU16 L.pg L.lxB 0 31 lextF
        ∗ (arrayU16 L.pg L.lbB 0 31 lbaseF
           ∗ (arrayU16 L.pg L.dbB 0 32 dbaseF
              ∗ arrayU16 L.pg L.dxB 0 32 dextF)) := by
  simp only [Cglob]
  sep_cancel

/-- **DISTS**: `base = dbase`, `extra = dext`, both 32 entries. -/
theorem glob_DISTS :
    Cglob L
      = arrayU16 L.pg L.dxB 0 32 dextF
        ∗ (arrayU16 L.pg L.dbB 0 32 dbaseF
           ∗ (arrayU16 L.pg L.lbB 0 31 lbaseF
              ∗ arrayU16 L.pg L.lxB 0 31 lextF)) := by
  simp only [Cglob]
  sep_cancel

/-- **CODES**: neither pair is chosen, so both are empty and all four tables
    stay in `Hrest`.  `arrayU16 … 0 …` is `emp` definitionally, and the blocks
    are arbitrary — `L.lbB` is picked only because it is in scope. -/
theorem glob_CODES :
    Cglob L
      = arrayU16 L.pg L.lbB 0 0 lextF
        ∗ (arrayU16 L.pg L.lbB 0 0 lbaseF ∗ Cglob L) := by
  show Cglob L = HProp.emp ∗ (HProp.emp ∗ Cglob L)
  rw [emp_sep_eq, emp_sep_eq]

/-- `Tsort` with the stale `_match` dropped — the CODES arm rebinds it, but
    leaves `_base`/`_extra` at the prologue's `nullv`. -/
abbrev TsortC (M Mn : Nat) (lv : _root_.Int) : List (Ident × Val) :=
  (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
    :: (_len, .Vint (Integers.Int.repr (((15 : Nat) : _root_.Int))))
    :: (_t'3, .Vint (Integers.Int.repr 0))
    :: (_left, .Vint (Integers.Int.repr lv))
    :: (_root, .Vint (Integers.Int.repr ((Nat.max (Nat.min b0 M) Mn : Nat))))
    :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
    :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
    :: (_extra, nullv)
    :: (_base, nullv)
    :: entryTemps L ty codes

/-- `Tsort` with `_base`, `_extra` and `_match` all dropped — LENS rebinds all
    three. -/
abbrev TsortL (M Mn : Nat) (lv : _root_.Int) : List (Ident × Val) :=
  (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
    :: (_len, .Vint (Integers.Int.repr (((15 : Nat) : _root_.Int))))
    :: (_t'3, .Vint (Integers.Int.repr 0))
    :: (_left, .Vint (Integers.Int.repr lv))
    :: (_root, .Vint (Integers.Int.repr ((Nat.max (Nat.min b0 M) Mn : Nat))))
    :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
    :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
    :: entryTemps L ty codes

/-- `Tsort` with `_base` and `_extra` dropped; DISTS leaves `match` at the
    prologue's 0, which is exactly the `mtch` the loop wants. -/
abbrev TsortD (M Mn : Nat) (lv : _root_.Int) : List (Ident × Val) :=
  (_sym, .Vint (Integers.Int.repr ((codes : _root_.Int))))
    :: (_len, .Vint (Integers.Int.repr (((15 : Nat) : _root_.Int))))
    :: (_t'3, .Vint (Integers.Int.repr 0))
    :: (_left, .Vint (Integers.Int.repr lv))
    :: (_root, .Vint (Integers.Int.repr ((Nat.max (Nat.min b0 M) Mn : Nat))))
    :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
    :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
    :: (_match, .Vint (Integers.Int.repr 0))
    :: entryTemps L ty codes

/-- The `HLoop` the main loop runs under, parameterised by the `switch`'s
    choice.  Spelled once so the three branches differ only in their arguments. -/
abbrev HLoopAt (wF : Nat → Nat) (xB bB : Block) (nx nb : Nat)
    (extraF baseF : Nat → Nat) (Hrest : HProp) : HProp :=
  HLoop bh bc bo L.pt L.pb L.pr L.pw L.pl L.pg L.tblB L.tblO L.bitsB L.bitsO
    L.tB L.tO cap L.workB L.workO codes wF L.lensB L.lensO codes lensF xB bB
    nx nb extraF baseF Hrest (cntC codes lensF)
    (sortOffs (cntC codes lensF) lensF codes) .Vundef .Vundef .Vundef
    (.Vint (Integers.Int.repr ((b0 : _root_.Int))))

/-- **The `ty` split.**  Consumes the `switch` and hands each code type its own
    `HLoop` — with its own `base`/`extra` pair, its own `Hrest`, and its own
    `match`.  Everything before this point was proved once for all three. -/
theorem ty_split (R : Sep.ExitConds) (M Mn : Nat) (lv : _root_.Int)
    (wF : Nat → Nat)
    (hnoLb : (envOf bh bc bo).get _lbase = none)
    (hnoLx : (envOf bh bc bo).get _lext = none)
    (hnoDb : (envOf bh bc bo).get _dbase = none)
    (hnoDx : (envOf bh bc bo).get _dext = none)
    (hsymLb : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hsymLx : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hsymDb : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hsymDx : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hty : ty = 0 ∨ ty = 1 ∨ ty = 2)
    (hC : ty = 0 → Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_match, .Vint (Integers.Int.repr 20)) :: TsortC L ty codes b0 M Mn lv)
        (HLoopAt bh bc bo L codes cap b0 lensF wF L.lbB L.lbB 0 0 lextF lbaseF
          (Cglob L))) postSwitch R)
    (hL : ty = 1 → Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_match, .Vint (Integers.Int.repr 257))
          :: (_extra, .Vptr L.lxB Integers.Ptrofs.zero)
          :: (_base, .Vptr L.lbB Integers.Ptrofs.zero)
          :: TsortL L ty codes b0 M Mn lv)
        (HLoopAt bh bc bo L codes cap b0 lensF wF L.lxB L.lbB 31 31 lextF
          lbaseF (arrayU16 L.pg L.dbB 0 32 dbaseF
                  ∗ arrayU16 L.pg L.dxB 0 32 dextF))) postSwitch R)
    (hD : ty = 2 → Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_extra, .Vptr L.dxB Integers.Ptrofs.zero)
          :: (_base, .Vptr L.dbB Integers.Ptrofs.zero)
          :: TsortD L ty codes b0 M Mn lv)
        (HLoopAt bh bc bo L codes cap b0 lensF wF L.dxB L.dbB 32 32 dextF
          dbaseF (arrayU16 L.pg L.lbB 0 31 lbaseF
                  ∗ arrayU16 L.pg L.lxB 0 31 lextF))) postSwitch R) :
    Triple ge fe f_inflate_table
      (LocalSt (envOf bh bc bo) (Tsort L ty codes b0 M Mn lv)
        (Hsort bh bc bo L codes cap b0 lensF wF))
      fullBodyTail R := by
  rw [fullBodyTail_split]
  rcases hty with h0 | h1 | h2
  · -- CODES: only `match` is assigned; `base`/`extra` stay `nullv`
    refine triple_seq ge fe f_inflate_table _ _ _ _ _
      (triple_conseq ge fe f_inflate_table
        (link_switch_CODES ge fe bh bc bo R
          (Hsort bh bc bo L codes cap b0 lensF wF)
          (TsortC L ty codes b0 M Mn lv) (by rw [h0]; temps_mem) (by temps_ne))
        (localst_mono (envOf bh bc bo) _ _ _ (by temps_mem))
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x)) ?_
    refine localst_perm ge fe (envOf bh bc bo) _ _ _
      (Hsort_as_HLoop bh bc bo L codes cap b0 lensF wF L.lbB L.lbB 0 0 lextF
        lbaseF (Cglob L) (glob_CODES L)) _ _ (hC h0)
  · -- LENS: `base = lbase; extra = lext; match = 257`
    refine triple_seq ge fe f_inflate_table _ _ _ _ _
      (triple_conseq ge fe f_inflate_table
        (link_switch_LENS ge fe bh bc bo L R
          (Hsort bh bc bo L codes cap b0 lensF wF)
          (TsortL L ty codes b0 M Mn lv) hnoLb hnoLx hsymLb hsymLx
          (by rw [h1]; temps_mem) (by temps_ne) (by temps_ne) (by temps_ne))
        (localst_mono (envOf bh bc bo) _ _ _ (by temps_mem))
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x)) ?_
    refine localst_perm ge fe (envOf bh bc bo) _ _ _
      (Hsort_as_HLoop bh bc bo L codes cap b0 lensF wF L.lxB L.lbB 31 31 lextF
        lbaseF _ (glob_LENS L)) _ _ (hL h1)
  · -- DISTS: `base = dbase; extra = dext`; `match` stays 0 from the prologue
    refine triple_seq ge fe f_inflate_table _ _ _ _ _
      (triple_conseq ge fe f_inflate_table
        (link_switch_DISTS ge fe bh bc bo L R
          (Hsort bh bc bo L codes cap b0 lensF wF)
          (TsortD L ty codes b0 M Mn lv) hnoDb hnoDx hsymDb hsymDx
          (by rw [h2]; temps_mem) (by temps_ne) (by temps_ne))
        (localst_mono (envOf bh bc bo) _ _ _ (by temps_mem))
        (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x)
        (fun _ _ x => x)) ?_
    refine localst_perm ge fe (envOf bh bc bo) _ _ _
      (Hsort_as_HLoop bh bc bo L codes cap b0 lensF wF L.dxB L.dbB 32 32 dextF
        dbaseF _ (glob_DISTS L)) _ _ (hD h2)

/-- The three globals are not block-scoped locals, so `Evar` resolves them
    through the genv.  `envOf` has exactly `here`/`count`/`offs`. -/
theorem envOf_lbase (bh bc bo : Block) :
    (envOf bh bc bo).get _lbase = none := rfl
theorem envOf_lext (bh bc bo : Block) :
    (envOf bh bc bo).get _lext = none := rfl
theorem envOf_dbase (bh bc bo : Block) :
    (envOf bh bc bo).get _dbase = none := rfl
theorem envOf_dext (bh bc bo : Block) :
    (envOf bh bc bo).get _dext = none := rfl

/-! ## The three `postSwitch` obligations

Each is `loop_setup_triple` (tail form) → `main_loop_triple` → `exit_epilogue`.
The three code types differ only in the parameters `ty_split` chose, so the work
is done once here and instantiated three times. -/

/-- Both `return` sites inside the loop hand back the same chain — the ENOUGH
    check's `HenoughRest` and the epilogue's residual — and both are `Cret` once
    the chosen `base`/`extra` pair is folded back into `Cglob`. -/
theorem retChain_as_Cret (wF : Nat → Nat) (tv bv : Val)
    (xB bB : Block) (nx nb : Nat) (extraF baseF : Nat → Nat) (Hrest : HProp)
    (hglob : Cglob L
      = arrayU16 L.pg xB 0 nx extraF ∗ (arrayU16 L.pg bB 0 nb baseF ∗ Hrest)) :
    codeRegion L.pr L.tB (Integers.Ptrofs.unsigned L.tO) cap
      ∗ (mapsto Mptr L.pt L.tblB (Integers.Ptrofs.unsigned L.tblO) tv
         ∗ (mapsto .Mint32 L.pb L.bitsB (Integers.Ptrofs.unsigned L.bitsO) bv
            ∗ (arrayU16 L.pw L.workB (Integers.Ptrofs.unsigned L.workO) codes wF
               ∗ (arrayU16 L.pl L.lensB (Integers.Ptrofs.unsigned L.lensO) codes
                    lensF
                  ∗ (arrayU16 L.pg xB 0 nx extraF
                     ∗ (arrayU16 L.pg bB 0 nb baseF ∗ Hrest))))))
      = Cret L codes cap lensF wF tv bv := by
  simp only [Cret, Clens, Cwork, Cbits, Creg]
  rw [show Cglob L
        = arrayU16 L.pg xB 0 nx extraF
          ∗ (arrayU16 L.pg bB 0 nb baseF ∗ Hrest) from hglob]
  sep_cancel

/-- **One `postSwitch` obligation**, parameterised by everything the `switch`
    chose.  Instantiated three times below.

    The chain is `loop_setup_triple` (tail form) → `main_loop_triple` →
    `exit_epilogue`; the loop's entry `LoopFacts` comes from `loopfacts_entry`
    and its `WorkChar` from `workchar_of_placed`. -/
theorem postSwitch_triple
    (bh bc bo : Block) (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (M Mn root mtch : Nat) (wF : Nat → Nat) (lv : _root_.Int)
    (xB bB : Block) (vx vb : Val) (nx nb : Nat) (extraF baseF : Nat → Nat)
    (Hrest : HProp) (tyN : Nat) (l : List (Ident × Val))
    -- `l` is the list the `switch` leaves; `l'` is it with `_sym` and `_len`
    -- dropped, since the nine setup `Sset`s rebind both
    (l' : List (Ident × Val)) (hdrop : ∀ q ∈ l', q ∈ l)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    -- permissions and representation side conditions
    (hpt : permOrder L.pt .Readable = true)
    (hptW : permOrder L.pt .Writable = true)
    (hpb : permOrder L.pb .Writable = true)
    (hpr : permOrder L.pr .Writable = true)
    (hpw : permOrder L.pw .Readable = true)
    (hpl : permOrder L.pl .Readable = true)
    (hpg : permOrder L.pg .Readable = true)
    (hwb : ∀ j, wF j < 65536) (hlb : ∀ j, lensF j < 65536)
    (hxb : ∀ j, extraF j < 65536) (hbb : ∀ j, baseF j < 65536)
    (hc31 : (codes : _root_.Int) < 2147483648)
    (hnoW : Integers.Ptrofs.unsigned L.workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoL : Integers.Ptrofs.unsigned L.lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnx31 : (nx : _root_.Int) < 2147483648)
    (hnb31 : (nb : _root_.Int) < 2147483648)
    (hm32 : mtch < 4294967296)
    (hcap31 : (cap : _root_.Int) < 2147483648)
    (hnoC : Integers.Ptrofs.unsigned L.tO + 4 * (cap : _root_.Int)
              < 18446744073709551616)
    (htO4 : Integers.Ptrofs.unsigned L.tO % 4 = 0)
    -- the model facts the scans and the sort loop established
    (hb : ∀ i, i < codes → lensF i ≤ 15)
    (hplaced : Placed lensF wF codes codes)
    (hkraft : kraftOk lensF codes)
    (hmaxdef : M = maxLen lensF codes) (hM0 : M ≠ 0) (hM15 : M ≤ 15)
    (hmnroot : minLen lensF codes ≤ root)
    (hroot1 : 1 ≤ root) (hroot15 : root ≤ 15) (hrootmax : root ≤ M)
    (hc16 : codes < 65536) (hnlive : nlive lensF codes ≤ codes)
    (hlensmax : ∀ j, lensF j ≤ M) (hlens15 : ∀ j, lensF j ≤ 15)
    -- A3 and the `base`/`extra` pointer facts, per code type
    (ha3x : ∀ i, i < codes → mtch ≤ i → i - mtch < nx)
    (ha3b : ∀ i, i < codes → mtch ≤ i → i - mtch < nb)
    (hvx : ∀ i, i < codes → mtch ≤ i → vx = .Vptr xB Integers.Ptrofs.zero)
    (hvb : ∀ i, i < codes → mtch ≤ i → vb = .Vptr bB Integers.Ptrofs.zero)
    -- the type
    (hty : tyN = 0 ∨ tyN = 1 ∨ tyN = 2)
    (htyeq : ty = ((tyN : Nat) : _root_.Int))
    (hcapL : tyN = 1 → 852 ≤ cap) (hcapD : tyN = 2 → 592 ≤ cap)
    (hA5 : tyN = 0 → M ≤ root)
    -- the ENOUGH check's outcome, and the `switch`'s partition of the globals
    (hglob : Cglob L
      = arrayU16 L.pg xB 0 nx extraF ∗ (arrayU16 L.pg bB 0 nb baseF ∗ Hrest))
    -- the `next[huff]` in-bounds fact (the incomplete-code argument)
    (hchk : 0 < leftAt lensF codes 15 → tyN ≠ 0 ∧ M = 1)
    (hA5used : tyN = 0 → 2 ^ root ≤ cap)
    (hoffsb : ∀ j, sortOffs (cntC codes lensF) lensF codes j < 65536)
    -- the tracked list
    (hmemMin : (_min, .Vint (Integers.Int.repr
      ((minLen lensF codes : Nat) : _root_.Int))) ∈ l')
    (hmemRoot : (_root, .Vint (Integers.Int.repr ((root : _root_.Int)))) ∈ l')
    (hmemTbl : (_table, .Vptr L.tblB L.tblO) ∈ l')
    (hfr : ∀ p ∈ l', p.1 ≠ _huff ∧ p.1 ≠ _sym ∧ p.1 ≠ _len ∧ p.1 ≠ _next
            ∧ p.1 ≠ _curr ∧ p.1 ≠ _drop ∧ p.1 ≠ _low ∧ p.1 ≠ _used
            ∧ p.1 ≠ _mask)
    (hsub : ∀ q ∈ TLoop L.tblB L.tblO L.bitsB L.bitsO L.tB L.workB L.workO
        L.lensB L.lensO vx vb tyN codes root M mtch
        (entrySt (minLen lensF codes) root L.tO lensF wF codes
          (sortOffs (cntC codes lensF) lensF codes) .Vundef .Vundef
          (Integers.Int.repr lv) .Vundef .Vundef .Vundef
          (.Vint (Integers.Int.repr ((b0 : _root_.Int))))),
      q ∈ (_mask, Val.Vint (Integers.Int.repr (((2 ^ root - 1 : Nat) : _root_.Int))))
        :: (_used, Val.Vint (Integers.Int.repr (((2 ^ root : Nat) : _root_.Int))))
        :: (_low, Val.Vint (Integers.Int.repr (((4294967295 : Nat) : _root_.Int))))
        :: (_drop, Val.Vint (Integers.Int.repr ((0 : _root_.Int))))
        :: (_curr, Val.Vint (Integers.Int.repr ((root : _root_.Int))))
        :: (_next, Val.Vptr L.tB L.tO)
        :: (_len, Val.Vint (Integers.Int.repr
             ((minLen lensF codes : Nat) : _root_.Int)))
        :: (_sym, Val.Vint (Integers.Int.repr ((0 : _root_.Int))))
        :: (_huff, Val.Vint (Integers.Int.repr ((0 : _root_.Int)))) :: l')
    (hfrT : ∀ q ∈ TLoop L.tblB L.tblO L.bitsB L.bitsO L.tB L.workB L.workO
        L.lensB L.lensO vx vb tyN codes root M mtch
        (entrySt (minLen lensF codes) root L.tO lensF wF codes
          (sortOffs (cntC codes lensF) lensF codes) .Vundef .Vundef
          (Integers.Int.repr lv) .Vundef .Vundef .Vundef
          (.Vint (Integers.Int.repr ((b0 : _root_.Int))))),
      q.1 ≠ _t'5 ∧ q.1 ≠ _t'6) :
    Triple ge (FunctionEntry2 ge) f_inflate_table
      (LocalSt (envOf bh bc bo) l
        (HLoopAt bh bc bo L codes cap b0 lensF wF xB bB nx nb extraF baseF
          Hrest))
      postSwitch
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := RetSpec L ty codes cap b0 lensF workF } := by
  have hwc := workchar_of_placed (vx := vx) (vb := vb) (xB := xB) (bB := bB)
    codes codes M mtch nx nb codes wF lensF hb hplaced hkraft hmaxdef hnlive
    (Nat.le_refl codes) ha3x ha3b hvx hvb
  have henv : LoopEnv ge bh bc bo L.pt L.pb L.pr L.pw L.pl L.pg L.tO cap
      L.workO codes wF L.lensO codes lensF nx nb extraF baseF tyN root M mtch :=
    { hcenv := hcenv, hd1 := hd1, hd2 := hd2, hd3 := hd3
      hpt := hpt, hptW := hptW, hpb := hpb, hpr := hpr, hpw := hpw
      hpl := hpl, hpg := hpg
      hwb := hwb, hlb := hlb, hlens15 := hlens15, hlensmax := hlensmax
      hxb := hxb, hbb := hbb
      hn31 := hc31, hnow := hnoW, hc31 := hc31, hnol := hnoL
      hnx31 := hnx31, hnb31 := hnb31, hm32 := hm32
      hcap31 := hcap31, hnoC := hnoC, htO4 := htO4
      hmax15 := hM15, hroot15 := hroot15, hroot1 := hroot1
      hr32 := by omega
      hty := hty, hcapL := hcapL, hcapD := hcapD }
  -- the ENOUGH check's residual, and the epilogue's, are the same chain
  have hretE : ∀ (v : Val) (hr : Heap),
      HenoughRest L.pt L.pb L.pr L.pw L.pl L.pg L.tblB L.tblO L.bitsB L.bitsO
        L.tB L.tO cap L.workB L.workO codes wF L.lensB L.lensO codes lensF
        xB bB nx nb extraF baseF Hrest v hr →
      RetSpec L ty codes cap b0 lensF workF (.Vint (Integers.Int.repr 1)) hr :=
    fun v hr hx => ⟨⟨1, rfl, Or.inr (Or.inr rfl)⟩,
      postHeap_of_Cret L codes cap lensF wF (.Vptr L.tB L.tO) v hr
        (by rw [← retChain_as_Cret L codes cap lensF wF (.Vptr L.tB L.tO) v
                  xB bB nx nb extraF baseF Hrest hglob]
            exact hx)⟩
  -- drop the stale `_sym`/`_len`: the setup rebinds both
  refine triple_conseq ge _ f_inflate_table (?_ : Sep.Triple _ _ _
      (LocalSt (envOf bh bc bo) l'
        (HLoopAt bh bc bo L codes cap b0 lensF wF xB bB nx nb extraF baseF
          Hrest)) _ _)
    (localst_mono (envOf bh bc bo) l l' _ hdrop)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  refine loop_setup_triple ge (FunctionEntry2 ge) bh bc bo L.pt L.pb L.pr L.pw
    L.pl L.pg L.tblB L.tblO L.bitsB L.bitsO L.tB L.tO cap L.workB L.workO codes
    wF L.lensB L.lensO codes lensF xB bB vx vb nx nb extraF baseF tyN codes root
    M mtch Hrest (minLen lensF codes) l' _
    hcenv hd1 hd2 hd3 hpt (by omega) hmemMin hmemRoot hmemTbl hfr hsub hfrT
    hty hcapL hcapD
    (fun h => by
      show (2 : Nat) ^ root ≤ cap
      exact hA5used h)
    (by show (2 : Nat) ^ root < 4294967296
        have : (2 : Nat) ^ root ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) hroot15
        omega)
    (RetSpec L ty codes cap b0 lensF workF) (hretE _)
    { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
      ret := RetSpec L ty codes cap b0 lensF workF,
      goto := fun _ => Sep.Assn.no } _ ?_
  -- the ENOUGH check established `used ≤ cap`, i.e. `2 ^ root ≤ cap`
  refine triple_exists ge _ f_inflate_table _ _ _
    (fun (hused : (2 : Nat) ^ root ≤ cap) => ?_)
  refine triple_seq ge _ f_inflate_table _ _ _ _ _
    (triple_conseq ge _ f_inflate_table
      (main_loop_triple ge (FunctionEntry2 ge) bh bc bo L.pt L.pb L.pr L.pw L.pl
        L.pg L.tblB L.tblO L.bitsB L.bitsO L.tB L.tO cap L.workB L.workO codes
        wF L.lensB L.lensO codes lensF xB bB vx vb nx nb extraF baseF tyN codes
        root M mtch (nlive lensF codes) Hrest henv hwc
        (RetSpec L ty codes cap b0 lensF workF) (fun s hr hx => hretE s.vbits hr hx)
        hused hA5 _ (nlive lensF codes))
      (fun e le hp hx =>
        ⟨_, loopfacts_entry (vx := vx) (vb := vb) (xB := xB) (bB := bB)
          codes codes M mtch nx nb cap codes root lensF wF L.tO
          (sortOffs (cntC codes lensF) lensF codes) .Vundef .Vundef
          (Integers.Int.repr lv) .Vundef .Vundef .Vundef
          (.Vint (Integers.Int.repr ((b0 : _root_.Int))))
          hwc hb hplaced hmaxdef hM0 hroot1 hroot15 hrootmax hmnroot hc16
          hoffsb hused, hx⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x))
    ?_
  -- the loop's exit meets the epilogue
  exact exit_epilogue ge (FunctionEntry2 ge) bh bc bo L.pt L.pb L.pr L.pw L.pl
    L.pg L.tblB L.tblO L.bitsB L.bitsO L.tB L.tO cap L.workB L.workO codes wF
    L.lensB L.lensO codes lensF xB bB vx vb nx nb extraF baseF tyN codes root M
    mtch (nlive lensF codes) Hrest (RetSpec L ty codes cap b0 lensF workF)
    hcenv hd1 hd2 hd3 hpr hpt hptW hpb hcap31 htO4 hnoC
    (fun s hef hne0 => by
      have hw := exit_write_inbounds M root cap codes tyN wF lensF L.tO s hef hb
        hplaced hchk hne0
      exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2⟩)
    (fun s hr hx => ⟨⟨0, rfl, Or.inr (Or.inl rfl)⟩,
      postHeap_of_Cret L codes cap lensF wF _ _ hr
        (by rw [← retChain_as_Cret L codes cap lensF wF _ _ xB bB nx nb extraF
                  baseF Hrest hglob]
            exact hx)⟩)
    { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
      ret := RetSpec L ty codes cap b0 lensF workF,
      goto := fun _ => Sep.Assn.no }

/-- The normalised `lens` is bounded by `maxLen` at **every** index — outside
    the array it is `0`.  This is `LoopEnv.hlensmax`, and it is exactly what
    normalising buys: the unrestricted quantifier becomes provable. -/
theorem normLens_le_maxLen (lensF : Nat → Nat) (codes j : Nat) :
    normLens lensF codes j ≤ maxLen (normLens lensF codes) codes := by
  by_cases hj : j < codes
  · exact InflateTable.Model.le_maxLen (normLens lensF codes) codes j hj
  · simp only [normLens, if_neg hj]; omega

/-! ## Running the chain at the normalised `lens`

`LoopEnv` needs `∀ j, lensF j ≤ 15`, which A2 does not give (it bounds `lensF`
only below `codes`).  Rather than strengthen A2 to cover values the function
never reads, the body triple is proved at `normLens lensF codes` and transported
back: `preHeap` and `postHeap` cannot tell the two apart, so **no model fact has
to be transferred** — the chain establishes its own facts at whichever function
it runs at. -/

theorem Pbody_normLens (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat) :
    Entry.Pbody L ty codes cap b0 lensF workF
      = Entry.Pbody L ty codes cap b0 (normLens lensF codes)
          (normLens workF codes) := by
  unfold Entry.Pbody
  rw [preHeap_normLens]

theorem spec_post_normLens (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat) :
    (inflateTableSpec L ty codes cap b0 lensF workF).post
      = (inflateTableSpec L ty codes cap b0 (normLens lensF codes) workF).post := by
  show (fun v hp => _ ∧ postHeap L codes cap lensF hp) = _
  rw [postHeap_normLens]
  rfl

/-- **The transport.**  Proving the body triple at the normalised `lens` proves
    it at the caller's. -/
theorem BodyTriple_normLens (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat)
    (h : Entry.BodyTriple ge L ty codes cap b0 (normLens lensF codes)
      (normLens workF codes)) :
    Entry.BodyTriple ge L ty codes cap b0 lensF workF := by
  show Sep.Triple ge (FunctionEntry2 ge) f_inflate_table
    (Entry.Pbody L ty codes cap b0 lensF workF) _ _
  rw [Pbody_normLens, show (inflateTableSpec L ty codes cap b0 lensF workF).post
    = (inflateTableSpec L ty codes cap b0 (normLens lensF codes) workF).post
    from spec_post_normLens L ty codes cap b0 lensF workF]
  exact h

/-! ## The three instantiations

`postSwitch_triple` at each code type.  Everything is either a `SideConds` /
`Assumptions` field, a model fact the scans established, or a `temps_*` goal on
the now-concrete tracked list.

These are stated at the **normalised** `lens`, so `hlens15` and
`hlensmax` — which A2 cannot give for the caller's raw `lensF` — hold. -/

section Inst

variable (bh bc bo : Block) (M Mn : Nat) (wF : Nat → Nat)

/-- The hypotheses common to all three types, bundled so each instantiation
    reads as the type-specific part only. -/
structure Common (lensF' : Nat → Nat) : Prop where
  hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env
  hpt : permOrder L.pt .Readable = true
  hptW : permOrder L.pt .Writable = true
  hpb : permOrder L.pb .Writable = true
  hpr : permOrder L.pr .Writable = true
  hpw : permOrder L.pw .Readable = true
  hpl : permOrder L.pl .Readable = true
  hpg : permOrder L.pg .Readable = true
  hc31 : (codes : _root_.Int) < 2147483648
  hnoW : Integers.Ptrofs.unsigned L.workO + 2 * (codes : _root_.Int)
           < 18446744073709551616
  hnoL : Integers.Ptrofs.unsigned L.lensO + 2 * (codes : _root_.Int)
           < 18446744073709551616
  hcap31 : (cap : _root_.Int) < 2147483648
  hnoC : Integers.Ptrofs.unsigned L.tO + 4 * (cap : _root_.Int)
           < 18446744073709551616
  htO4 : Integers.Ptrofs.unsigned L.tO % 4 = 0
  hc16 : codes < 65536
  hlens15 : ∀ j, lensF' j ≤ 15
  /-- …and `0` outside the array.  This is what `normLens` buys, and what makes
      `LoopEnv.hlensmax` provable. -/
  hlensz : ∀ j, ¬ (j < codes) → lensF' j = 0

/-- `LoopEnv.hlensmax` at a normalised `lens`. -/
theorem lensmax_of (lensF' : Nat → Nat)
    (hz : ∀ j, ¬ (j < codes) → lensF' j = 0) (j : Nat) :
    lensF' j ≤ maxLen lensF' codes := by
  by_cases hj : j < codes
  · exact le_maxLen lensF' codes j hj
  · rw [hz j hj]; omega

/-- The bounds on `root = max (min b0 max) min` that the loop entry needs. -/
theorem root_bounds (b0' M' Mn' : Nat) (hMn1 : 1 ≤ Mn') (hMnM : Mn' ≤ M')
    (hM15 : M' ≤ 15) :
    1 ≤ Nat.max (Nat.min b0' M') Mn' ∧ Nat.max (Nat.min b0' M') Mn' ≤ 15
      ∧ Nat.max (Nat.min b0' M') Mn' ≤ M'
      ∧ Mn' ≤ Nat.max (Nat.min b0' M') Mn' := by
  have h1 : Nat.min b0' M' ≤ M' := Nat.min_le_right b0' M'
  have h2 : Mn' ≤ Nat.max (Nat.min b0' M') Mn' := Nat.le_max_right _ _
  have h3 : Nat.max (Nat.min b0' M') Mn' ≤ M' := Nat.max_le.mpr ⟨h1, hMnM⟩
  exact ⟨by omega, by omega, h3, h2⟩

/-- The list the nine setup `Set`s run against: what the `switch` left, minus
    `_sym` and `_len` (both rebound by the setup). -/
abbrev TsetupTail (root' : Nat) (lv : _root_.Int) : List (Ident × Val) :=
  (_t'3, .Vint (Integers.Int.repr 0))
    :: (_left, .Vint (Integers.Int.repr lv))
    :: (_root, .Vint (Integers.Int.repr ((root' : _root_.Int))))
    :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
    :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
    :: entryTemps L ty codes

/-- …with the `switch`'s three bindings in front, for LENS. -/
abbrev TsetupL (root' : Nat) (lv : _root_.Int) : List (Ident × Val) :=
  (_match, .Vint (Integers.Int.repr 257))
    :: (_extra, .Vptr L.lxB Integers.Ptrofs.zero)
    :: (_base, .Vptr L.lbB Integers.Ptrofs.zero)
    :: TsetupTail L ty codes M Mn root' lv

/-- …and for CODES: only `match` is rebound; `base`/`extra` keep `nullv`. -/
abbrev TsetupC (root' : Nat) (lv : _root_.Int) : List (Ident × Val) :=
  (_match, .Vint (Integers.Int.repr 20))
    :: (_t'3, .Vint (Integers.Int.repr 0))
    :: (_left, .Vint (Integers.Int.repr lv))
    :: (_root, .Vint (Integers.Int.repr ((root' : _root_.Int))))
    :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
    :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
    :: (_extra, nullv) :: (_base, nullv)
    :: entryTemps L ty codes

/-- …and for DISTS.  The `switch` does **not** touch `match` there, so the
    prologue's `0` is retained — and it is exactly the `mtch` the loop wants. -/
abbrev TsetupD (root' : Nat) (lv : _root_.Int) : List (Ident × Val) :=
  (_extra, .Vptr L.dxB Integers.Ptrofs.zero)
    :: (_base, .Vptr L.dbB Integers.Ptrofs.zero)
    :: (_t'3, .Vint (Integers.Int.repr 0))
    :: (_left, .Vint (Integers.Int.repr lv))
    :: (_root, .Vint (Integers.Int.repr ((root' : _root_.Int))))
    :: (_min, .Vint (Integers.Int.repr ((Mn : _root_.Int))))
    :: (_max, .Vint (Integers.Int.repr ((M : _root_.Int))))
    :: (_match, .Vint (Integers.Int.repr 0))
    :: entryTemps L ty codes

/-- **LENS.**  `base = lbase`, `extra = lext`, both 31 entries, `match = 257`;
    `dbase`/`dext` ride in `Hrest`. -/
theorem inst_LENS (lensF' workF' : Nat → Nat) (hcom : Common ge L codes cap lensF')
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hM15 : M ≤ 15) (hM0 : M ≠ 0) (hMn1 : 1 ≤ Mn) (hMnM : Mn ≤ M)
    (hzM : ∀ l, M < l → l ≤ 15 → cntC codes lensF' l = 0)
    (hnM : M = 0 ∨ cntC codes lensF' M ≠ 0)
    (hzMn : ∀ j, 1 ≤ j → j < Mn → cntC codes lensF' j = 0)
    (hnMn : Mn = M ∨ cntC codes lensF' Mn ≠ 0)
    (hchk : leftC (cntC codes lensF') 15 ≤ 0
              ∨ ((1 : _root_.Int) ≠ 0 ∧ M = 1))
    (hnn : ∀ j, j ≤ 15 → 0 ≤ leftC (cntC codes lensF') j)
    (hwb : ∀ j, wF j < 65536) (hplaced : Placed lensF' wF codes codes)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs (cntC codes lensF') lensF' s j < 65536)
    (hcodes : codes ≤ 288) (hcap : 852 ≤ cap) (hb032 : b0 < 4294967296) :
    Triple ge (FunctionEntry2 ge) f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_match, .Vint (Integers.Int.repr 257))
          :: (_extra, .Vptr L.lxB Integers.Ptrofs.zero)
          :: (_base, .Vptr L.lbB Integers.Ptrofs.zero)
          :: TsortL L ((1 : _root_.Int)) codes b0 M Mn
               (leftC (cntC codes lensF') 15))
        (HLoopAt bh bc bo L codes cap b0 lensF' wF L.lxB L.lbB 31 31 lextF
          lbaseF (arrayU16 L.pg L.dbB 0 32 dbaseF
                  ∗ arrayU16 L.pg L.dxB 0 32 dextF)))
      postSwitch
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := RetSpec L ((1 : _root_.Int)) codes cap b0 lensF' workF' } := by
  have hmaxdef : M = maxLen lensF' codes :=
    maxLen_char lensF' codes M (fun i hi => hcom.hlens15 i) hM15 hzM hnM
  have hmndef : Mn = minLen lensF' codes :=
    minLen_char lensF' codes Mn M hMn1 (by omega) hmaxdef hM0 hzMn hnMn
  refine postSwitch_triple ge L ((1 : _root_.Int)) codes cap b0 lensF'
    workF' bh bc bo hd1 hd2 hd3 M Mn (Nat.max (Nat.min b0 M) Mn) 257 wF
    (leftC (cntC codes lensF') 15) L.lxB L.lbB
    (.Vptr L.lxB Integers.Ptrofs.zero) (.Vptr L.lbB Integers.Ptrofs.zero)
    31 31 lextF lbaseF _ 1 _
    (TsetupL L ((1 : _root_.Int)) codes M Mn
      (Nat.max (Nat.min b0 M) Mn) (leftC (cntC codes lensF') 15))
    (by temps_mem)
    hcom.hcenv hcom.hpt hcom.hptW hcom.hpb hcom.hpr hcom.hpw hcom.hpl hcom.hpg
    hwb (fun j => by have := hcom.hlens15 j; omega)
    (fun j => lextF_lt j) (fun j => lbaseF_lt j)
    hcom.hc31 hcom.hnoW hcom.hnoL (by decide) (by decide) (by decide)
    hcom.hcap31 hcom.hnoC hcom.htO4
    (fun i _ => hcom.hlens15 i) hplaced
    (fun l hl => by rw [← leftC_eq_leftAt lensF' codes l]; exact hnn l hl)
    hmaxdef hM0 hM15
    (by rw [← hmndef]; exact (root_bounds b0 M Mn hMn1 hMnM hM15).2.2.2)
    (root_bounds b0 M Mn hMn1 hMnM hM15).1
    (root_bounds b0 M Mn hMn1 hMnM hM15).2.1
    (root_bounds b0 M Mn hMn1 hMnM hM15).2.2.1
    hcom.hc16 (nlive_le_codes lensF' codes)
    (fun j => by rw [hmaxdef]; exact lensmax_of codes lensF' hcom.hlensz j)
    hcom.hlens15
    (fun i hi h => by omega) (fun i hi h => by omega)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (Or.inr (Or.inl rfl)) rfl (fun _ => hcap)
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (glob_LENS L)
    (fun h => ⟨by decide, by
      rcases hchk with hc | hc
      · rw [leftC_eq_leftAt lensF' codes 15] at hc; omega
      · exact hc.2⟩)
    (fun h => absurd h (by decide)) (fun j => hgb codes (Nat.le_refl _) j)
    (by rw [← hmndef]; temps_mem) (by temps_mem) (by temps_mem)
    -- nine-way conjunction: split it, `temps_ne`'s single `decide` gives up
    (by intro p hp
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (revert hp; revert p; temps_ne))
    (by rw [← hmndef]; simp only [entrySt]; temps_mem)
    -- `TLoop` is `Tmut ++ Tfix`, so the `++` has to be flattened before
    -- `List.forall_mem_cons` can split it
    (by intro q hq
        simp only [entrySt] at hq
        refine ⟨?_, ?_⟩ <;>
          (revert hq; revert q
           simp only [TLoop, Tmut, Tfix, List.cons_append, List.nil_append,
             List.forall_mem_cons]
           decide))

/-- **CODES.**  The `switch` sets only `match = 20`, so `base`/`extra` keep the
    prologue's `nullv` — which is statable only because `Tfix` carries them as
    `Val`s.  Neither table is chosen: `nx = nb = 0` makes
    `arrayU16 … 0 …` empty and all four ride in `Hrest`.  A3-CODES
    (`codes ≤ 20 = match`) makes the branch that would read them unreachable,
    which is what discharges `hvx`/`hvb` and `ha3x`/`ha3b` vacuously. -/
theorem inst_CODES (lensF' workF' : Nat → Nat) (hcom : Common ge L codes cap lensF')
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hM15 : M ≤ 15) (hM0 : M ≠ 0) (hMn1 : 1 ≤ Mn) (hMnM : Mn ≤ M)
    (hzM : ∀ l, M < l → l ≤ 15 → cntC codes lensF' l = 0)
    (hnM : M = 0 ∨ cntC codes lensF' M ≠ 0)
    (hzMn : ∀ j, 1 ≤ j → j < Mn → cntC codes lensF' j = 0)
    (hnMn : Mn = M ∨ cntC codes lensF' Mn ≠ 0)
    (hchk : leftC (cntC codes lensF') 15 ≤ 0
              ∨ ((0 : _root_.Int) ≠ 0 ∧ M = 1))
    (hnn : ∀ j, j ≤ 15 → 0 ≤ leftC (cntC codes lensF') j)
    (hwb : ∀ j, wF j < 65536) (hplaced : Placed lensF' wF codes codes)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs (cntC codes lensF') lensF' s j < 65536)
    (hcodes : codes ≤ 20) (hA5c : 2 ^ (Nat.max (Nat.min b0 M) Mn) ≤ cap)
    (hA5m : M ≤ Nat.max (Nat.min b0 M) Mn) (hb032 : b0 < 4294967296) :
    Triple ge (FunctionEntry2 ge) f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_match, .Vint (Integers.Int.repr 20))
          :: TsortC L ((0 : _root_.Int)) codes b0 M Mn
               (leftC (cntC codes lensF') 15))
        (HLoopAt bh bc bo L codes cap b0 lensF' wF L.lbB L.lbB 0 0 lextF
          lbaseF (Cglob L)))
      postSwitch
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := RetSpec L ((0 : _root_.Int)) codes cap b0 lensF' workF' } := by
  have hmaxdef : M = maxLen lensF' codes :=
    maxLen_char lensF' codes M (fun i hi => hcom.hlens15 i) hM15 hzM hnM
  have hmndef : Mn = minLen lensF' codes :=
    minLen_char lensF' codes Mn M hMn1 (by omega) hmaxdef hM0 hzMn hnMn
  refine postSwitch_triple ge L ((0 : _root_.Int)) codes cap b0 lensF'
    workF' bh bc bo hd1 hd2 hd3 M Mn (Nat.max (Nat.min b0 M) Mn) 20 wF
    (leftC (cntC codes lensF') 15) L.lbB L.lbB nullv nullv
    0 0 lextF lbaseF _ 0 _
    (TsetupC L ((0 : _root_.Int)) codes M Mn
      (Nat.max (Nat.min b0 M) Mn) (leftC (cntC codes lensF') 15))
    (by temps_mem)
    hcom.hcenv hcom.hpt hcom.hptW hcom.hpb hcom.hpr hcom.hpw hcom.hpl hcom.hpg
    hwb (fun j => by have := hcom.hlens15 j; omega)
    (fun j => lextF_lt j) (fun j => lbaseF_lt j)
    hcom.hc31 hcom.hnoW hcom.hnoL (by decide) (by decide) (by decide)
    hcom.hcap31 hcom.hnoC hcom.htO4
    (fun i _ => hcom.hlens15 i) hplaced
    (fun l hl => by rw [← leftC_eq_leftAt lensF' codes l]; exact hnn l hl)
    hmaxdef hM0 hM15
    (by rw [← hmndef]; exact (root_bounds b0 M Mn hMn1 hMnM hM15).2.2.2)
    (root_bounds b0 M Mn hMn1 hMnM hM15).1
    (root_bounds b0 M Mn hMn1 hMnM hM15).2.1
    (root_bounds b0 M Mn hMn1 hMnM hM15).2.2.1
    hcom.hc16 (nlive_le_codes lensF' codes)
    (fun j => by rw [hmaxdef]; exact lensmax_of codes lensF' hcom.hlensz j)
    hcom.hlens15
    (fun i hi h => by omega) (fun i hi h => by omega)
    -- A3-CODES makes the reading branch unreachable: `20 ≤ i < codes ≤ 20`
    (fun i hi h => absurd h (by omega)) (fun i hi h => absurd h (by omega))
    (Or.inl rfl) rfl (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun _ => hA5m)
    (glob_CODES L)
    -- for CODES the check *must* have found a complete code: `chk6` returns
    -- `-1` otherwise, so this branch is where that is consumed
    (fun h => absurd h (by
      rcases hchk with hc | hc
      · rw [leftC_eq_leftAt lensF' codes 15] at hc; omega
      · exact absurd rfl hc.1))
    (fun _ => hA5c) (fun j => hgb codes (Nat.le_refl _) j)
    (by rw [← hmndef]; temps_mem) (by temps_mem) (by temps_mem)
    -- nine-way conjunction: split it, `temps_ne`'s single `decide` gives up
    (by intro p hp
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (revert hp; revert p; temps_ne))
    (by rw [← hmndef]; simp only [entrySt]; temps_mem)
    -- `TLoop` is `Tmut ++ Tfix`, so the `++` has to be flattened before
    -- `List.forall_mem_cons` can split it
    (by intro q hq
        simp only [entrySt] at hq
        refine ⟨?_, ?_⟩ <;>
          (revert hq; revert q
           simp only [TLoop, Tmut, Tfix, List.cons_append, List.nil_append,
             List.forall_mem_cons]
           decide))

/-- **DISTS.**  `base = dbase`, `extra = dext`, both 32 entries; `match` keeps
    the prologue's `0`, which is the `mtch` the loop wants.  `lbase`/`lext` ride
    in `Hrest`. -/
theorem inst_DISTS (lensF' workF' : Nat → Nat) (hcom : Common ge L codes cap lensF')
    (hd1 : bh ≠ bc) (hd2 : bh ≠ bo) (hd3 : bc ≠ bo)
    (hM15 : M ≤ 15) (hM0 : M ≠ 0) (hMn1 : 1 ≤ Mn) (hMnM : Mn ≤ M)
    (hzM : ∀ l, M < l → l ≤ 15 → cntC codes lensF' l = 0)
    (hnM : M = 0 ∨ cntC codes lensF' M ≠ 0)
    (hzMn : ∀ j, 1 ≤ j → j < Mn → cntC codes lensF' j = 0)
    (hnMn : Mn = M ∨ cntC codes lensF' Mn ≠ 0)
    (hchk : leftC (cntC codes lensF') 15 ≤ 0
              ∨ ((2 : _root_.Int) ≠ 0 ∧ M = 1))
    (hnn : ∀ j, j ≤ 15 → 0 ≤ leftC (cntC codes lensF') j)
    (hwb : ∀ j, wF j < 65536) (hplaced : Placed lensF' wF codes codes)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs (cntC codes lensF') lensF' s j < 65536)
    (hcodes : codes ≤ 32) (hcap : 592 ≤ cap) (hb032 : b0 < 4294967296) :
    Triple ge (FunctionEntry2 ge) f_inflate_table
      (LocalSt (envOf bh bc bo)
        ((_extra, .Vptr L.dxB Integers.Ptrofs.zero)
          :: (_base, .Vptr L.dbB Integers.Ptrofs.zero)
          :: TsortD L ((2 : _root_.Int)) codes b0 M Mn
               (leftC (cntC codes lensF') 15))
        (HLoopAt bh bc bo L codes cap b0 lensF' wF L.dxB L.dbB 32 32 dextF
          dbaseF (arrayU16 L.pg L.lbB 0 31 lbaseF
                  ∗ arrayU16 L.pg L.lxB 0 31 lextF)))
      postSwitch
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := RetSpec L ((2 : _root_.Int)) codes cap b0 lensF' workF' } := by
  have hmaxdef : M = maxLen lensF' codes :=
    maxLen_char lensF' codes M (fun i hi => hcom.hlens15 i) hM15 hzM hnM
  have hmndef : Mn = minLen lensF' codes :=
    minLen_char lensF' codes Mn M hMn1 (by omega) hmaxdef hM0 hzMn hnMn
  refine postSwitch_triple ge L ((2 : _root_.Int)) codes cap b0 lensF'
    workF' bh bc bo hd1 hd2 hd3 M Mn (Nat.max (Nat.min b0 M) Mn) 0 wF
    (leftC (cntC codes lensF') 15) L.dxB L.dbB
    (.Vptr L.dxB Integers.Ptrofs.zero) (.Vptr L.dbB Integers.Ptrofs.zero)
    32 32 dextF dbaseF _ 2 _
    (TsetupD L ((2 : _root_.Int)) codes M Mn
      (Nat.max (Nat.min b0 M) Mn) (leftC (cntC codes lensF') 15))
    (by temps_mem)
    hcom.hcenv hcom.hpt hcom.hptW hcom.hpb hcom.hpr hcom.hpw hcom.hpl hcom.hpg
    hwb (fun j => by have := hcom.hlens15 j; omega)
    (fun j => dextF_lt j) (fun j => dbaseF_lt j)
    hcom.hc31 hcom.hnoW hcom.hnoL (by decide) (by decide) (by decide)
    hcom.hcap31 hcom.hnoC hcom.htO4
    (fun i _ => hcom.hlens15 i) hplaced
    (fun l hl => by rw [← leftC_eq_leftAt lensF' codes l]; exact hnn l hl)
    hmaxdef hM0 hM15
    (by rw [← hmndef]; exact (root_bounds b0 M Mn hMn1 hMnM hM15).2.2.2)
    (root_bounds b0 M Mn hMn1 hMnM hM15).1
    (root_bounds b0 M Mn hMn1 hMnM hM15).2.1
    (root_bounds b0 M Mn hMn1 hMnM hM15).2.2.1
    hcom.hc16 (nlive_le_codes lensF' codes)
    (fun j => by rw [hmaxdef]; exact lensmax_of codes lensF' hcom.hlensz j)
    hcom.hlens15
    (fun i hi h => by omega) (fun i hi h => by omega)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (Or.inr (Or.inr rfl)) rfl (fun h => absurd h (by decide)) (fun _ => hcap)
    (fun h => absurd h (by decide))
    (glob_DISTS L)
    (fun h => ⟨by decide, by
      rcases hchk with hc | hc
      · rw [leftC_eq_leftAt lensF' codes 15] at hc; omega
      · exact hc.2⟩)
    (fun h => absurd h (by decide)) (fun j => hgb codes (Nat.le_refl _) j)
    (by rw [← hmndef]; temps_mem) (by temps_mem) (by temps_mem)
    -- nine-way conjunction: split it, `temps_ne`'s single `decide` gives up
    (by intro p hp
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          (revert hp; revert p; temps_ne))
    (by rw [← hmndef]; simp only [entrySt]; temps_mem)
    -- `TLoop` is `Tmut ++ Tfix`, so the `++` has to be flattened before
    -- `List.forall_mem_cons` can split it
    (by intro q hq
        simp only [entrySt] at hq
        refine ⟨?_, ?_⟩ <;>
          (revert hq; revert q
           simp only [TLoop, Tmut, Tfix, List.cons_append, List.nil_append,
             List.forall_mem_cons]
           decide))

end Inst

/-! ## Reducing the body triple to the tail

With the spine done, `Entry.BodyTriple` — and so `inflate_table_safe` — reduces
to a triple for `fullBodyTail` alone, one per code type; `inst_CODES`,
`inst_LENS` and `inst_DISTS` above discharge those. -/

theorem body_of_tail (k : Nat) (hcap : cap = 2 + k)
    (hc16 : codes < 65536) (hb032 : b0 < 4294967296)
    (hty0 : 0 ≤ ty) (hty3 : ty < 3)
    (hcenv : ge.genv_cenv = Inftrees.prog.prog_comp_env)
    (hpl : permOrder L.pl .Readable = true)
    (hpw : permOrder L.pw .Writable = true)
    (hpbR : permOrder L.pb .Readable = true)
    (hpbW : permOrder L.pb .Writable = true)
    (hptR : permOrder L.pt .Readable = true)
    (hptW : permOrder L.pt .Writable = true)
    (hpr : permOrder L.pr .Writable = true)
    (hb : ∀ j, lensF j < 65536) (hwb : ∀ j, workF j < 65536)
    -- `s ≤ codes`: without it this is false at `j = 0`, where the count
    -- grows with `s`
    (hgb : ∀ s, s ≤ codes → ∀ j, sortOffs (cntC codes lensF) lensF s j < 65536)
    (hos : ∀ j, offsC (cntC codes lensF) j < 65536)
    (hlens15 : ∀ i, i < codes → lensF i ≤ 15)
    (hnoL : Integers.Ptrofs.unsigned L.lensO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hnoW : Integers.Ptrofs.unsigned L.workO + 2 * (codes : _root_.Int)
              < 18446744073709551616)
    (hal : Integers.Ptrofs.unsigned L.tO % 4 = 0)
    (haddr1 : Integers.Ptrofs.unsigned
      (idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed L.tO
        (Integers.Int.repr 1)) = Integers.Ptrofs.unsigned L.tO + 4)
    (hsymLb : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hsymLx : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hsymDb : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hsymDx : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hty : ty = 0 ∨ ty = 1 ∨ ty = 2)
    -- per code type: the loop setup, the loop, the epilogue
    (hC : ∀ (bh bc bo : Block), bh ≠ bc → bh ≠ bo → bc ≠ bo →
      ∀ (M Mn : Nat) (wF : Nat → Nat), M ≤ 15 → M ≠ 0 → 1 ≤ Mn → Mn ≤ M →
      (∀ l, M < l → l ≤ 15 → cntC codes lensF l = 0) →
      (M = 0 ∨ cntC codes lensF M ≠ 0) →
      (∀ j, 1 ≤ j → j < Mn → cntC codes lensF j = 0) →
      (Mn = M ∨ cntC codes lensF Mn ≠ 0) →
      (leftC (cntC codes lensF) 15 ≤ 0 ∨ (ty ≠ 0 ∧ M = 1)) →
      (∀ j, j ≤ 15 → 0 ≤ leftC (cntC codes lensF) j) →
      (∀ j, wF j < 65536) → Placed lensF wF codes codes → ty = 0 →
      Triple ge (FunctionEntry2 ge) f_inflate_table
        (LocalSt (envOf bh bc bo)
          ((_match, .Vint (Integers.Int.repr 20))
            :: TsortC L ty codes b0 M Mn (leftC (cntC codes lensF) 15))
          (HLoopAt bh bc bo L codes cap b0 lensF wF L.lbB L.lbB 0 0 lextF
            lbaseF (Cglob L))) postSwitch
        { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
          ret := RetSpec L ty codes cap b0 lensF workF })
    (hL : ∀ (bh bc bo : Block), bh ≠ bc → bh ≠ bo → bc ≠ bo →
      ∀ (M Mn : Nat) (wF : Nat → Nat), M ≤ 15 → M ≠ 0 → 1 ≤ Mn → Mn ≤ M →
      (∀ l, M < l → l ≤ 15 → cntC codes lensF l = 0) →
      (M = 0 ∨ cntC codes lensF M ≠ 0) →
      (∀ j, 1 ≤ j → j < Mn → cntC codes lensF j = 0) →
      (Mn = M ∨ cntC codes lensF Mn ≠ 0) →
      (leftC (cntC codes lensF) 15 ≤ 0 ∨ (ty ≠ 0 ∧ M = 1)) →
      (∀ j, j ≤ 15 → 0 ≤ leftC (cntC codes lensF) j) →
      (∀ j, wF j < 65536) → Placed lensF wF codes codes → ty = 1 →
      Triple ge (FunctionEntry2 ge) f_inflate_table
        (LocalSt (envOf bh bc bo)
          ((_match, .Vint (Integers.Int.repr 257))
            :: (_extra, .Vptr L.lxB Integers.Ptrofs.zero)
            :: (_base, .Vptr L.lbB Integers.Ptrofs.zero)
            :: TsortL L ty codes b0 M Mn (leftC (cntC codes lensF) 15))
          (HLoopAt bh bc bo L codes cap b0 lensF wF L.lxB L.lbB 31 31 lextF
            lbaseF (arrayU16 L.pg L.dbB 0 32 dbaseF
                    ∗ arrayU16 L.pg L.dxB 0 32 dextF))) postSwitch
        { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
          ret := RetSpec L ty codes cap b0 lensF workF })
    (hD : ∀ (bh bc bo : Block), bh ≠ bc → bh ≠ bo → bc ≠ bo →
      ∀ (M Mn : Nat) (wF : Nat → Nat), M ≤ 15 → M ≠ 0 → 1 ≤ Mn → Mn ≤ M →
      (∀ l, M < l → l ≤ 15 → cntC codes lensF l = 0) →
      (M = 0 ∨ cntC codes lensF M ≠ 0) →
      (∀ j, 1 ≤ j → j < Mn → cntC codes lensF j = 0) →
      (Mn = M ∨ cntC codes lensF Mn ≠ 0) →
      (leftC (cntC codes lensF) 15 ≤ 0 ∨ (ty ≠ 0 ∧ M = 1)) →
      (∀ j, j ≤ 15 → 0 ≤ leftC (cntC codes lensF) j) →
      (∀ j, wF j < 65536) → Placed lensF wF codes codes → ty = 2 →
      Triple ge (FunctionEntry2 ge) f_inflate_table
        (LocalSt (envOf bh bc bo)
          ((_extra, .Vptr L.dxB Integers.Ptrofs.zero)
            :: (_base, .Vptr L.dbB Integers.Ptrofs.zero)
            :: TsortD L ty codes b0 M Mn (leftC (cntC codes lensF) 15))
          (HLoopAt bh bc bo L codes cap b0 lensF wF L.dxB L.dbB 32 32 dextF
            dbaseF (arrayU16 L.pg L.lbB 0 31 lbaseF
                    ∗ arrayU16 L.pg L.lxB 0 31 lextF))) postSwitch
        { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
          ret := RetSpec L ty codes cap b0 lensF workF }) :
    Entry.BodyTriple ge L ty codes cap b0 lensF workF := by
  show Sep.Triple ge (FunctionEntry2 ge) f_inflate_table _
    f_inflate_table.fn_body _
  rw [spine_matches]
  refine triple_exists ge _ f_inflate_table _ _ _ (fun (bh : Block) => ?_)
  refine triple_exists ge _ f_inflate_table _ _ _ (fun (bc : Block) => ?_)
  refine triple_exists ge _ f_inflate_table _ _ _ (fun (bo : Block) => ?_)
  refine triple_exists ge _ f_inflate_table _ _ _ (fun (hd1 : bh ≠ bc) => ?_)
  refine triple_exists ge _ f_inflate_table _ _ _ (fun (hd2 : bh ≠ bo) => ?_)
  refine triple_exists ge _ f_inflate_table _ _ _ (fun (hd3 : bc ≠ bo) => ?_)
  exact spine_prefix ge (FunctionEntry2 ge) bh bc bo L ty codes cap b0 lensF
    workF fullBodyTail _ k hcap hc16 hb032 hty0 hty3 hcenv hd1 hd2 hd3
    hpl hpw hpbR hpbW hptR hptW hpr hb hwb hgb hos hlens15 hnoL hnoW hal
    haddr1 rfl
    (fun M Mn wF hM15 hM0 hMn1 hMnM hzM hnM hzMn hnMn hchk hnn hwF hplc =>
      ty_split ge (FunctionEntry2 ge) bh bc bo L ty codes cap b0 lensF _
        M Mn _ wF (envOf_lbase bh bc bo) (envOf_lext bh bc bo)
        (envOf_dbase bh bc bo) (envOf_dext bh bc bo)
        hsymLb hsymLx hsymDb hsymDx hty
        (fun h => hC bh bc bo hd1 hd2 hd3 M Mn wF hM15 hM0 hMn1 hMnM hzM hnM
          hzMn hnMn hchk hnn hwF hplc h)
        (fun h => hL bh bc bo hd1 hd2 hd3 M Mn wF hM15 hM0 hMn1 hMnM hzM hnM
          hzMn hnMn hchk hnn hwF hplc h)
        (fun h => hD bh bc bo hd1 hd2 hd3 M Mn wF hM15 hM0 hMn1 hMnM hzM hnM
          hzMn hnMn hchk hnn hwF hplc h))

end Chain

end InflateTable.Chain
