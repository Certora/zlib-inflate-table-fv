/-
  The memory-safety theorem for `inflate_table` (inftrees.c:46-311).

  Per fv/memory-safety.md: in the CCLib port of CompCert's Clight semantics,
  `Mem.load`/`store`/`free` are partial — a spatial or temporal violation makes
  the semantics STUCK, not wrong.  `Sep.SatisfiesAt` is total-correctness: it
  exhibits a `Steps` execution from call to return.  Therefore proving the
  theorem below at the (weak, safety-only) spec of InflateTableSpec.lean is
  exactly the statement that `inflate_table` commits no out-of-bounds access,
  no misaligned access, no permission violation, and consumes no `Vundef` in a
  control decision — for EVERY input satisfying A1-A5, with the frame rule
  additionally guaranteeing it touches nothing outside the declared footprint.

  Proof status: **COMPLETE — no `sorry`.**  Axioms are Lean's standard three
  (`propext`, `Classical.choice`, `Quot.sound`) plus CCLib's two semantics
  axioms (`CC.externalFunctionsSem`, `CC.inlineAssemblySem`), which every
  Clight-level result in the export repo carries.

  Two `rfl` guards tie the proof to the actual compiled program:
  `Body.body_matches` (every named statement chunk is at its real position in
  `f_inflate_table.fn_body`) and `Chain.spine_matches` (the seventeen slots the
  phase chain threads are that body's first seventeen, in order).

  `Sep.SatisfiesAt` exhibits a finite `Steps` execution to a `Returnstate`.
  That implies stuck-freedom — hence memory safety — modulo determinism of
  the Clight step relation, which CCLib proves (`CC.step_determ`).
  `inflate_table_no_stuck` at the bottom of this file makes the `∃`-run →
  `∀`-run step explicit: **every** state reachable from the call — at any
  trace — either steps or is the return state, and the run emits no observable
  event.  That corollary carries two extra axioms
  (`externalFunctionsSemDeterm`, `inlineAssemblySemDeterm`), inherited from
  `step_determ`'s external-call case even though this function contains no
  `Scall`; `inflate_table_safe` itself is unaffected.

  Statement-design notes for the reviewer
  ---------------------------------------
  * `ge` is universally quantified; the four `findSymbol` hypotheses pin only
    what the body's `Evar _lbase` (etc.) lookups need.  The CONTENTS of those
    globals are not trusted from `ge` — they are owned resources in the
    precondition (`preHeap`), so the theorem composes with any `init_mem`
    story that establishes them once.
  * `hdisj` requires the four global blocks to be pairwise distinct and
    distinct from the caller's blocks only where aliasing would break the
    `∗`-chain; unique ownership already forces all of that, so no explicit
    distinctness hypotheses appear — `preHeap`'s satisfiability carries them.
  * No identifier-distinctness hypothesis appears in the statement:
    `FunctionEntry2`'s no-repetition side conditions over the 6 parameters +
    54 temporaries + 3 locals all `decide` on the concrete AST
    (`Entry.entry_facts`).
  * `hcenv : ge.genv_cenv = Layout.cenv` IS a hypothesis, and is unavoidable:
    `sizeof`, `fieldOffset`, and `accessMode` for `struct code` are read out of
    `ge.genv_cenv`, so a `ge` with a different composite environment describes
    a different program.  It is the weakest form of "this is the genv of the
    compiled `Inftrees.prog`" the proof actually uses — strictly weaker than
    `ge = globalenv Inftrees.prog`, which would additionally fix the symbol
    table that the four `findSymbol` hypotheses leave open.
-/
import InflateTableSpec
import InflateTableInvariants
import InflateTableEntry
import InflateTableChain

open CC CC.HProp
open Inftrees

namespace InflateTable

/-! ## The body triple

`InflateTableEntry.lean` reduces memory safety to a single `Triple` over
`f_inflate_table.fn_body`; `InflateTableChain.lean` proves it, and this is
where its hypotheses are supplied from `SideConds`/`Assumptions`.
-/

/-- The body triple, assembled.  `Entry.BodyTriple` unfolds to

      Triple ge (FunctionEntry2 ge) f_inflate_table
        (Entry.Pbody …) f_inflate_table.fn_body
        { normal := no, brk := no, cont := no,
          ret := (inflateTableSpec …).post }

    and `Body.body_matches : f_inflate_table.fn_body = Body.fullBody` names the
    statement it has to be chained over. -/
theorem inflate_table_body
    (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat)
    (hlb : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hlx : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hdb : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hdx : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hsc : SideConds L ty codes cap b0 workF)
    (ha : Assumptions ty codes cap b0 lensF) :
    Entry.BodyTriple ge L ty codes cap b0 lensF workF := by
  -- run everything at the normalised `lens`/`work`:
  -- `LoopEnv` wants bounds at *every* index, and A2 / `SideConds.work_repr`
  -- only bound them inside the array
  refine Chain.BodyTriple_normLens ge L ty codes cap b0 lensF workF ?_
  obtain ⟨k, hk⟩ : ∃ k, cap = 2 + k := ⟨cap - 2, by have := ha.cap_min; omega⟩
  -- A3 bounds `codes` by 288 whichever type it is — and 288, not 65536, is
  -- what the `offs`/`sortOffs` bounds need (they are sums of two counts)
  have hc288 : codes ≤ 288 := by
    rcases ha.ty_valid with h | h | h
    · have := ha.codes_codes h; omega
    · have := ha.codes_lens h; omega
    · have := ha.codes_dists h; omega
  have hc16 : codes < 65536 := by omega
  have hlens15 : ∀ j, normLens lensF codes j ≤ 15 :=
    fun j => normLens_le lensF codes ha.lens_le_MAXBITS j
  have hlensz : ∀ j, ¬ (j < codes) → normLens lensF codes j = 0 :=
    fun j hj => by simp [normLens, hj]
  have hwork : ∀ j, normLens workF codes j < 65536 :=
    normWork_lt workF codes hsc.work_repr
  -- `Writable` implies `Readable`
  have hpbR : permOrder L.pb .Readable = true :=
    Mem.permOrder_trans hsc.perm_bits (by decide)
  have hptR : permOrder L.pt .Readable = true :=
    Mem.permOrder_trans hsc.perm_tbl (by decide)
  have hpwR : permOrder L.pw .Readable = true :=
    Mem.permOrder_trans hsc.perm_work (by decide)
  have hcom : Chain.Common ge L codes cap (normLens lensF codes) :=
    { hcenv := hcenv, hpt := hptR, hptW := hsc.perm_tbl, hpb := hsc.perm_bits
      hpr := hsc.perm_reg, hpw := hpwR, hpl := hsc.perm_lens
      hpg := hsc.perm_glob
      hc31 := by omega
      hnoW := hsc.no_wrap_work, hnoL := hsc.no_wrap_lens
      hcap31 := hsc.cap_repr
      hnoC := hsc.no_wrap_tbl
      htO4 := hsc.tbl_align
      hc16 := hc16
      hlens15 := hlens15, hlensz := hlensz }
  -- `offs`/`sortOffs` are partial sums of counts, so bounded by `2 * codes`
  have hnl : ∀ l, Model.offs (normLens lensF codes) codes l ≤ codes :=
    fun l => Nat.le_trans
      (Model.offs_le_nlive (normLens lensF codes) codes l
        (fun i _ => hlens15 i))
      (Model.nlive_le_codes _ _)
  have hos : ∀ j, Body.offsC (Chain.cntC codes (normLens lensF codes)) j < 65536 := by
    intro j
    have := hnl j
    rw [Body.offsC_count_eq (normLens lensF codes) codes j]
    omega
  have hgb : ∀ s, s ≤ codes → ∀ j,
      Body.sortOffs (Chain.cntC codes (normLens lensF codes))
        (normLens lensF codes) s j < 65536 := by
    intro s hs j
    have h1 := hnl j
    have h2 := Model.count_le (normLens lensF codes) s j
    show Body.offsC (Chain.cntC codes (normLens lensF codes)) j
           + Model.count (normLens lensF codes) s j < 65536
    rw [Body.offsC_count_eq (normLens lensF codes) codes j]
    omega
  -- `*table + 1` is `t + 4`
  have haddr1 : Integers.Ptrofs.unsigned
      (Sep.idxOfs ge.genv_cenv (Ty.Tstruct __1353 noattr) .Signed L.tO
        (Integers.Int.repr 1)) = Integers.Ptrofs.unsigned L.tO + 4 := by
    obtain ⟨T, hT⟩ : ∃ T : _root_.Int,
      Integers.Ptrofs.unsigned L.tO = T := ⟨_, rfl⟩
    have hnw : T + 4 * ((cap : Nat) : _root_.Int)
        < (18446744073709551616 : _root_.Int) := by
      rw [← hT]; exact hsc.no_wrap_tbl
    have h2 : 2 ≤ cap := ha.cap_min
    have h := Sep.idxOfs_unsigned ge.genv_cenv (Ty.Tstruct __1353 noattr)
      .Signed L.tO 1 4
      (by rw [hcenv]; exact Layout.code_sizeof) (by decide) (by decide)
      (by rw [hT]
          show T + ((4 : Nat) : _root_.Int) * ((1 : Nat) : _root_.Int)
            < (18446744073709551616 : _root_.Int)
          omega)
    -- `repr 1` vs `repr ↑(1 : Nat)`: defeq, so `refine h.trans` bridges them
    -- where `rw` will not
    refine h.trans ?_
    rw [hT]
    show T + ((4 : Nat) : _root_.Int) * ((1 : Nat) : _root_.Int) = T + 4
    omega
  have hty0 : (0 : _root_.Int) ≤ ty := by
    rcases ha.ty_valid with h | h | h <;> rw [h] <;> decide
  have hty3 : ty < 3 := by
    rcases ha.ty_valid with h | h | h <;> rw [h] <;> decide
  refine Chain.body_of_tail ge L ty codes cap b0 (normLens lensF codes)
    (normLens workF codes) k hk hc16
    (by have h := hsc.b0_repr
        obtain ⟨B, hB⟩ : ∃ B : _root_.Int, ((b0 : Nat) : _root_.Int) = B :=
          ⟨_, rfl⟩
        have h' : B < (4294967296 : _root_.Int) := by rw [← hB]; exact h
        omega)
    hty0 hty3 hcenv
    hsc.perm_lens hsc.perm_work hpbR hsc.perm_bits hptR hsc.perm_tbl
    hsc.perm_reg (fun j => by have := hlens15 j; omega) hwork hgb hos
    (fun i _ => hlens15 i) hsc.no_wrap_lens hsc.no_wrap_work hsc.tbl_align
    haddr1 hlb hlx hdb hdx ha.ty_valid ?_ ?_ ?_
  · -- CODES.  A5 supplies what the missing ENOUGH check would have: every
    -- length is ≤ Lc ≤ b0, so `root = max` and `2 ^ root ≤ cap`.
    intro bh bc bo hd1 hd2 hd3 M Mn wF hM15 hM0 hMn1 hMnM hzM hnM hzMn hnMn
      hchk hnn hwF hplc hty
    obtain ⟨Lc, hLc, hLcb, hLcc⟩ := ha.codes_cap hty
    subst hty
    -- `M` is *attained*, so it is one of the lengths A5 bounds
    have hMLc : M ≤ Lc := by
      have hpos : 0 < Model.count (normLens lensF codes) codes M := by
        rcases hnM with h | h
        · exact absurd h hM0
        · exact Nat.pos_of_ne_zero h
      obtain ⟨i, hi, he⟩ :=
        Model.exists_of_count_pos (normLens lensF codes) codes M hpos
      rw [← he, normLens_eq lensF codes i hi]
      exact hLc i hi
    -- so `root = max = M ≤ Lc`, and A5's `2 ^ Lc ≤ cap` covers the table
    have hrootM : Nat.max (Nat.min b0 M) Mn = M := by
      have h1 : Nat.min b0 M = M := Nat.min_eq_right (by omega)
      rw [h1]; exact Nat.max_eq_left hMnM
    exact Chain.inst_CODES ge L codes cap b0 bh bc bo M Mn wF
      (normLens lensF codes) (normLens workF codes) hcom hd1 hd2 hd3 hM15 hM0 hMn1 hMnM hzM hnM hzMn
      hnMn hchk hnn hwF hplc hgb
      (ha.codes_codes rfl)
      (by rw [hrootM]
          exact Nat.le_trans (Nat.pow_le_pow_right (by omega) hMLc) hLcc)
      (by rw [hrootM]; exact Nat.le_refl M)
      (by have h := hsc.b0_repr
          obtain ⟨B, hB⟩ : ∃ B : _root_.Int, ((b0 : Nat) : _root_.Int) = B :=
            ⟨_, rfl⟩
          have h' : B < (4294967296 : _root_.Int) := by rw [← hB]; exact h
          omega)
  · -- LENS
    intro bh bc bo hd1 hd2 hd3 M Mn wF hM15 hM0 hMn1 hMnM hzM hnM hzMn hnMn
      hchk hnn hwF hplc hty
    subst hty
    exact Chain.inst_LENS ge L codes cap b0 bh bc bo M Mn wF
      (normLens lensF codes) (normLens workF codes) hcom hd1 hd2 hd3 hM15 hM0 hMn1 hMnM hzM hnM hzMn
      hnMn hchk hnn hwF hplc hgb
      (ha.codes_lens rfl) (ha.cap_lens rfl)
      (by have h := hsc.b0_repr
          obtain ⟨B, hB⟩ : ∃ B : _root_.Int, ((b0 : Nat) : _root_.Int) = B :=
            ⟨_, rfl⟩
          have h' : B < (4294967296 : _root_.Int) := by rw [← hB]; exact h
          omega)
  · -- DISTS
    intro bh bc bo hd1 hd2 hd3 M Mn wF hM15 hM0 hMn1 hMnM hzM hnM hzMn hnMn
      hchk hnn hwF hplc hty
    subst hty
    exact Chain.inst_DISTS ge L codes cap b0 bh bc bo M Mn wF
      (normLens lensF codes) (normLens workF codes) hcom hd1 hd2 hd3 hM15 hM0 hMn1 hMnM hzM hnM hzMn
      hnMn hchk hnn hwF hplc hgb
      (ha.codes_dists rfl) (ha.cap_dists rfl)
      (by have h := hsc.b0_repr
          obtain ⟨B, hB⟩ : ∃ B : _root_.Int, ((b0 : Nat) : _root_.Int) = B :=
            ⟨_, rfl⟩
          have h' : B < (4294967296 : _root_.Int) := by rw [← hB]; exact h
          omega)

/-- **Memory safety of `inflate_table`** (statement).

    Under the footprint A1 (= `preHeap`), the side conditions of the memory
    model, and the minimal assumptions A2-A5, a call to the compiled
    `f_inflate_table` runs — without a single faulting step — to a return
    state, hands back the footprint, and leaves every disjoint frame
    untouched. -/
theorem inflate_table_safe
    (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat)
    (hlb : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hlx : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hdb : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hdx : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hsc : SideConds L ty codes cap b0 workF)
    (ha : Assumptions ty codes cap b0 lensF) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_inflate_table)
      (inflateTableSpec L ty codes cap b0 lensF workF)
      (argVals L ty codes) :=
  Entry.safe_of_body ge hcenv L ty codes cap b0 lensF workF
    (inflate_table_body ge hcenv L ty codes cap b0 lensF workF hlb hlx hdb hdx
      hsc ha)

/-! ## Instantiations at the three call sites (inflate.c, TABLE state)

Each corollary discharges the type-specific fields of `Assumptions` at the
values the real caller uses, so a reviewer can check the assumption set is
neither vacuous nor stronger than what inflate.c provides. -/

/-- CODES: 19 code-length codes, each length from a 3-bit field (≤ 7),
    root request 7, capacity ENOUGH = ENOUGH_LENS + ENOUGH_DISTS = 1444. -/
theorem inflate_table_safe_CODES
    (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (codes cap b0 : Nat) (lensF workF : Nat → Nat)
    (hlb : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hlx : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hdb : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hdx : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hsc : SideConds L CODES codes cap b0 workF)
    (hcodes : codes ≤ 19) (hlens : ∀ i, i < codes → lensF i ≤ 7)
    (hb0 : b0 = 7) (hcap : 1444 ≤ cap) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_inflate_table)
      (inflateTableSpec L CODES codes cap b0 lensF workF)
      (argVals L CODES codes) := by
  refine inflate_table_safe ge hcenv L CODES codes cap b0 lensF workF hlb hlx hdb hdx hsc ?_
  exact {
    ty_valid := Or.inl rfl
    lens_le_MAXBITS := fun i hi => Nat.le_trans (hlens i hi) (by decide)
    codes_lens := fun h => by simp [LENS, CODES] at h
    codes_dists := fun h => by simp [DISTS, CODES] at h
    codes_codes := fun _ => Nat.le_trans hcodes (by decide)
    cap_min := by omega
    cap_lens := fun h => by simp [LENS, CODES] at h
    cap_dists := fun h => by simp [DISTS, CODES] at h
    codes_cap := fun _ => ⟨7, hlens, by omega, by omega⟩
  }

/-- LENS: up to 288 literal/length code lengths, capacity ENOUGH_LENS = 852. -/
theorem inflate_table_safe_LENS
    (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (codes cap b0 : Nat) (lensF workF : Nat → Nat)
    (hlb : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hlx : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hdb : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hdx : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hsc : SideConds L LENS codes cap b0 workF)
    (hcodes : codes ≤ 288) (hlens : ∀ i, i < codes → lensF i ≤ 15)
    (hcap : 852 ≤ cap) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_inflate_table)
      (inflateTableSpec L LENS codes cap b0 lensF workF)
      (argVals L LENS codes) := by
  refine inflate_table_safe ge hcenv L LENS codes cap b0 lensF workF hlb hlx hdb hdx hsc ?_
  exact {
    ty_valid := Or.inr (Or.inl rfl)
    lens_le_MAXBITS := hlens
    codes_lens := fun _ => hcodes
    codes_dists := fun h => by simp [LENS, DISTS] at h
    codes_codes := fun h => by simp [LENS, CODES] at h
    cap_min := by omega
    cap_lens := fun _ => hcap
    cap_dists := fun h => by simp [LENS, DISTS] at h
    codes_cap := fun h => by simp [LENS, CODES] at h
  }

/-- DISTS: up to 32 distance code lengths, capacity ENOUGH_DISTS = 592. -/
theorem inflate_table_safe_DISTS
    (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (codes cap b0 : Nat) (lensF workF : Nat → Nat)
    (hlb : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hlx : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hdb : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hdx : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hsc : SideConds L DISTS codes cap b0 workF)
    (hcodes : codes ≤ 32) (hlens : ∀ i, i < codes → lensF i ≤ 15)
    (hcap : 592 ≤ cap) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_inflate_table)
      (inflateTableSpec L DISTS codes cap b0 lensF workF)
      (argVals L DISTS codes) := by
  refine inflate_table_safe ge hcenv L DISTS codes cap b0 lensF workF hlb hlx hdb hdx hsc ?_
  exact {
    ty_valid := Or.inr (Or.inr rfl)
    lens_le_MAXBITS := hlens
    codes_lens := fun h => by simp [LENS, DISTS] at h
    codes_dists := fun _ => hcodes
    codes_codes := fun h => by simp [DISTS, CODES] at h
    cap_min := by omega
    cap_lens := fun h => by simp [LENS, DISTS] at h
    cap_dists := fun _ => hcap
    codes_cap := fun h => by simp [DISTS, CODES] at h
  }

/-! ## The raw-execution corollary

The `Star Step` form, for comparison with the `MemSafe` definition of
fv/memory-safety.md — an explicit fault-free execution from `Callstate` to
`Returnstate` under CompCert's own step relation. -/

theorem inflate_table_runs
    (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat)
    (hlb : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hlx : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hdb : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hdx : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hsc : SideConds L ty codes cap b0 workF)
    (ha : Assumptions ty codes cap b0 lensF)
    (k : Cont) (hk : isCallCont k = true) (m : Mem) (hp hf : Heap)
    (hpre : preHeap L codes cap b0 lensF workF hp)
    (hdj : Heap.disjoint hp hf) (hag : Heap.Agrees (Heap.union hp hf) m) :
    ∃ r m' hp',
      Star (Step ge (FunctionEntry2 ge))
        (.Callstate (.Internal f_inflate_table) (argVals L ty codes) k m) E0
        (.Returnstate (.Vint (Integers.Int.repr r)) k m')
      ∧ (r = -1 ∨ r = 0 ∨ r = 1)
      ∧ postHeap L codes cap lensF hp'
      ∧ Heap.disjoint hp' hf ∧ Heap.Agrees (Heap.union hp' hf) m' := by
  obtain ⟨v, m', hp', hsteps, ⟨⟨r, hv, hr⟩, hpost⟩, hdj', hag'⟩ :=
    inflate_table_safe ge hcenv L ty codes cap b0 lensF workF hlb hlx hdb hdx hsc ha
      k m hp hf hk ⟨rfl, hpre⟩ hdj hag
  subst hv
  exact ⟨r, m', hp', Steps.toStar hsteps, hr, hpost, hdj', hag'⟩

/-! ## Stuck-freedom

`SatisfiesAt` exhibits **one** execution reaching a `Returnstate`.  Memory safety
is the stronger "**no** execution gets stuck", and the two coincide because the
step relation is deterministic (`CC.step_determ`, `CC.starE0_prefix`).

The continuation is `Kstop`: that makes the return state *final*
(`CC.FinalState`), hence stuck, which is what `starE0_prefix` needs — and it is
the right reading anyway, since what happens after `inflate_table` returns is the
caller's business, not this function's.

**Reading the single reachability clause.**  It carries both termination and
stuck-freedom (a stuck-freedom `∀` on its own would be satisfied vacuously by
a diverging function):

* `t := E0`, `s' := ` the call state, `Star.refl` ⟹ `Star … start E0 return`,
  i.e. **termination**;
* any other `s'` ⟹ `Star … s' E0 return`, which is either `refl` (so `s'` *is*
  the return) or a `step` (so `s'` steps).  That is **stuck-freedom**, and since
  `Mem.load`/`store`/`free` are partial it is exactly "no out-of-bounds,
  misaligned or permission-violating access, and no `Vundef` consumed in a
  control decision".

`t = E0` is the trace-side counterpart: the function emits no observable event.

`hinj` is the only new hypothesis.  It is discharged by
`CC.program_symbolsInjective p` for any real program's genv, so it costs nothing
at a call site; it appears here only because `ge` is universally quantified. -/

/-! ### Silent reachability is *all* reachability

`starE0_prefix` speaks about `StarE0` — runs made of `E0` steps.  For the `∀`
below to cover **every** reachable state, not just the silently-reachable ones,
we need that no reachable state can take a non-silent step.  It cannot:
`MatchTraces`' only constructor with an empty left trace is `nil`, so a state
that can step silently can step *only* silently.

These three are general facts about the CCLib semantics rather than about
`inflate_table`; they belong upstream, and are here only because CCLib does not
state them yet. -/

/-- `nil` is `MatchTraces`' only constructor with an empty left trace — every
    other puts a one-event trace on *both* sides. -/
theorem matchTraces_E0_left {gs : Senv} {t : Trace}
    (h : MatchTraces gs E0 t) : t = E0 := by
  cases h; rfl

/-- **A state that can step silently can step only silently.**  Determinism
    forces the traces to match, and matching `E0` forces `E0`. -/
theorem step_E0_forced {ge : CGenv}
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop}
    (hfe : EntryDeterm fe)
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective) {s s1 t s2}
    (h1 : Step ge fe s E0 s1) (h2 : Step ge fe s t s2) : t = E0 ∧ s2 = s1 := by
  obtain ⟨hm, he⟩ := step_determ hfe hinj h1 h2
  have ht : t = E0 := matchTraces_E0_left hm
  exact ⟨ht, (he ht.symm).symm⟩

/-- **The closure.**  Given a silent run to a stuck state, *every* run from the
    start — at any trace — is silent and lands on that run.  So quantifying over
    `StarE0` loses nothing. -/
theorem star_is_starE0 {ge : CGenv}
    {fe : Function → List Val → Mem → Env → TempEnv → Mem → Prop}
    (hfe : EntryDeterm fe)
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective) :
    ∀ {s sa}, StarE0 (Step ge fe) s sa → (∀ t s', ¬ Step ge fe sa t s') →
      ∀ {t sb}, Star (Step ge fe) s t sb →
        t = E0 ∧ StarE0 (Step ge fe) s sb := by
  intro s sa hrun
  induction hrun with
  | refl s =>
      intro hstuck t sb hstar
      cases hstar with
      | refl _ => exact ⟨rfl, StarE0.refl _⟩
      | step _ _ _ _ _ _ hr _ _ => exact absurd hr (hstuck _ _)
  | step s s2 sa hstep hrest ih =>
      intro hstuck t sb hstar
      cases hstar with
      | refl _ => exact ⟨rfl, StarE0.refl _⟩
      | step _ t1 s' t2 _ _ hr hst hteq =>
          obtain ⟨ht1, hs'⟩ := step_E0_forced hfe hinj hstep hr
          subst hs'
          obtain ⟨ht2, hse⟩ := ih hstuck hst
          refine ⟨?_, StarE0.step _ _ _ hstep hse⟩
          rw [hteq, ht1, ht2]; rfl

theorem inflate_table_no_stuck
    (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat)
    (hlb : Genv.findSymbol ge.genv_genv _lbase = some L.lbB)
    (hlx : Genv.findSymbol ge.genv_genv _lext = some L.lxB)
    (hdb : Genv.findSymbol ge.genv_genv _dbase = some L.dbB)
    (hdx : Genv.findSymbol ge.genv_genv _dext = some L.dxB)
    (hsc : SideConds L ty codes cap b0 workF)
    (ha : Assumptions ty codes cap b0 lensF)
    (hinj : (Genv.toSenv ge.genv_genv).SymbolsInjective)
    (m : Mem) (hp hf : Heap)
    (hpre : preHeap L codes cap b0 lensF workF hp)
    (hdj : Heap.disjoint hp hf) (hag : Heap.Agrees (Heap.union hp hf) m) :
    ∃ r m' hp',
      (r = -1 ∨ r = 0 ∨ r = 1)
      ∧ postHeap L codes cap lensF hp'
      ∧ Heap.disjoint hp' hf ∧ Heap.Agrees (Heap.union hp' hf) m'
      -- **The whole safety claim, in one clause.**  Every state reachable from
      -- the call — at any trace — was reached silently, and can still reach the
      -- return.  Instantiating at the call state itself (`Star.refl`) gives
      -- termination; instantiating anywhere else gives stuck-freedom, since a
      -- state that still reaches the return either *is* it or steps toward it.
      ∧ ∀ t s', Star (Step ge (FunctionEntry2 ge))
          (.Callstate (.Internal f_inflate_table) (argVals L ty codes) .Kstop m)
          t s' →
          t = E0
            ∧ Star (Step ge (FunctionEntry2 ge)) s' E0
                (.Returnstate (.Vint (Integers.Int.repr r)) .Kstop m') := by
  obtain ⟨r, m', hp', hstar, hr3, hpost, hdj', hag'⟩ :=
    inflate_table_runs ge hcenv L ty codes cap b0 lensF workF hlb hlx hdb hdx
      hsc ha .Kstop rfl m hp hf hpre hdj hag
  refine ⟨r, m', hp', hr3, hpost, hdj', hag', ?_⟩
  -- the exhibited run, as a silent run
  have hse : StarE0 (Step ge (FunctionEntry2 ge)) _ _ := starE0_of_star hstar rfl
  -- the return state is final, hence stuck
  have hstuck : ∀ t s', ¬ Step ge (FunctionEntry2 ge)
      (.Returnstate (.Vint (Integers.Int.repr r)) .Kstop m') t s' :=
    fun _ _ => finalState_nostep (FinalState.intro _ _)
  -- so every silent run from the call is a *prefix* of it
  have hpfx := starE0_prefix (entryDeterm_functionEntry2 ge) hinj hse hstuck
  intro t s' hs'
  -- every run — at *any* trace — is silent and lands on the exhibited one
  obtain ⟨ht, hse'⟩ :=
    star_is_starE0 (entryDeterm_functionEntry2 ge) hinj hse hstuck hs'
  exact ⟨ht, star_of_starE0 (hpfx s' hse')⟩

end InflateTable
