/-
  The function entry.

  `Sep.satisfies_internal` (CCLib/Funspec.lean:169) splits the memory-safety
  theorem in two along a shared assertion `Pbody`:

    * `hentry` — running `FunctionEntry2` yields an environment, temporaries, a
      memory, and a heap fragment for the freshly allocated locals, with
      `Pbody` holding of the caller's resources *plus* the locals.  **That is
      this file.**
    * `body : Triple … Pbody f_inflate_table.fn_body { ret := S.post, … }` —
      the phase chain over the 33 segments of `InflateTable.Body.fullBody`.
      That is InflateTableChain.lean.

  So `Pbody` (below) is the D/E interface.  Note the `ret` condition of `body`
  is `S.post` *alone*, with no locals: `Sep.triple_return` frees them (its
  `Mem.freeList` hypothesis is what consumes the `Freeable` ownership), so the
  locals are gone by the time the postcondition is stated.

  Everything here is `decide`/`rfl` plus one `hexists` peel — there is no
  arithmetic and no Clight execution reasoning.  The only genuine content is
  `entry_resources`, which threads `CC.allocVariables_resources`' disjointness
  and `Agrees` conclusions into the shape `satisfies_internal` asks for.
-/
import InflateTableBody

open CC CC.Sep CC.HProp
open Inftrees

namespace InflateTable.Entry

open InflateTable.Body

/-! ## §D1 The entry step

`FunctionEntry2` (CCLib/Clight.lean:584) wants five things.  Three are
`decide`, one is `rfl`, and one is the three-step `AllocVariables` chain.

The chain has to name its intermediate memories explicitly: `refine
AllocVariables.cons _ _ _ _ _ ?_ ?_ …` cannot infer them from the goal, since
`Mem.alloc`'s result appears only in the *hypothesis* of `cons`.  So the six
definitions below spell out the three fresh blocks and the three memories as
functions of the caller's memory `m`. -/

/-- Memory after allocating `here` (4 bytes). -/
def m1 (m : Mem) : Mem := (Mem.alloc m 0 4).1
/-- The block of `here`. -/
def bhOf (m : Mem) : Block := (Mem.alloc m 0 4).2
/-- Memory after additionally allocating `count` (32 bytes). -/
def m2 (m : Mem) : Mem := (Mem.alloc (m1 m) 0 32).1
/-- The block of `count`. -/
def bcOf (m : Mem) : Block := (Mem.alloc (m1 m) 0 32).2
/-- Memory after additionally allocating `offs` (32 bytes) — the memory the
    body starts in. -/
def m3 (m : Mem) : Mem := (Mem.alloc (m2 m) 0 32).1
/-- The block of `offs`. -/
def boOf (m : Mem) : Block := (Mem.alloc (m2 m) 0 32).2

/-- The three locals are allocated in `fn_vars` order, so the environment the
    body runs in is exactly `Body.envOf` of three successive `nextblock`s. -/
theorem alloc_vars (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv) (m : Mem) :
    AllocVariables ge.genv_cenv emptyEnv m f_inflate_table.fn_vars
      (envOf (bhOf m) (bcOf m) (boOf m)) (m3 m) := by
  rw [hcenv]
  show AllocVariables Layout.cenv emptyEnv m
    [(_here, Ty.Tstruct __1353 noattr), (_count, tarray tushort 16),
     (_offs, tarray tushort 16)] _ _
  refine AllocVariables.cons _ _ _ _ _ (m1 m) (bhOf m) _ _ ?_ ?_
  · rw [show sizeof Layout.cenv (Ty.Tstruct __1353 noattr) = 4 from by decide]
    rfl
  refine AllocVariables.cons _ _ _ _ _ (m2 m) (bcOf m) _ _ ?_ ?_
  · rw [show sizeof Layout.cenv (tarray tushort 16) = 32 from by decide]
    rfl
  refine AllocVariables.cons _ _ _ _ _ (m3 m) (boOf m) _ _ ?_ ?_
  · rw [show sizeof Layout.cenv (tarray tushort 16) = 32 from by decide]
    rfl
  exact AllocVariables.nil _ _

/-- **D1.**  The entry relation holds, at the environment `Body.envOf` and a
    temporary environment binding the six parameters.

    The `TempsHold` conclusion is six `rfl`s through the 54-node
    `createUndefTemps` tree.  The same computation makes every *unbound*
    temporary `.Vundef` — which is why `Body.LoopSt`'s `vi`/`vf` fields (the
    stale `incr`/`fill`) are arbitrary `Val`s rather than numbers. -/
theorem entry_facts (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (ty : _root_.Int) (codes : Nat) (m : Mem) :
    ∃ le : TempEnv,
      FunctionEntry2 ge f_inflate_table (argVals L ty codes) m
        (envOf (bhOf m) (bcOf m) (boOf m)) le (m3 m)
      ∧ TempsHold (entryTemps L ty codes) le := by
  refine ⟨_, FunctionEntry2.intro (by decide) (by decide) (by decide)
    (alloc_vars ge hcenv m) rfl, ?_⟩
  intro p hp
  -- eight `rfl`s through the 54-node `createUndefTemps` tree: the six
  -- parameters, and `_incr`/`_fill` at the `.Vundef` it left them
  rcases List.mem_cons.mp hp with rfl | hp
  · rfl
  rcases List.mem_cons.mp hp with rfl | hp
  · rfl
  rcases List.mem_cons.mp hp with rfl | hp
  · rfl
  rcases List.mem_cons.mp hp with rfl | hp
  · rfl
  rcases List.mem_cons.mp hp with rfl | hp
  · rfl
  rcases List.mem_cons.mp hp with rfl | hp
  · rfl
  rcases List.mem_cons.mp hp with rfl | hp
  · rfl
  rcases List.mem_cons.mp hp with rfl | hp
  · rfl
  simp at hp

/-! ## §D2 The locals' footprint

`CC.allocVariables_resources` hands back `localsAt ce e fn_vars hl`, a chain of
`hexists (fun b => ⌜e.get id = some (b, ty)⌝ ∗ undefBytes …)`.  The environment
pins each `b`, so the existential is not really one: it collapses. -/

/-- One local peels off `localsAt` when the environment pins its block.  The
    pure conjunct is what does the pinning — this is the only place the
    `⌜…⌝` inside `localsAt` is used. -/
theorem localsAt_pin {ce : CompositeEnv} {e : Env} {id : Ident} {ty : Ty}
    {b : Block} {rest : List (Ident × Ty)} (hb : e.get id = some (b, ty)) :
    localsAt ce e ((id, ty) :: rest)
      = undefBytes .Freeable b 0 (sizeof ce ty).toNat ∗ localsAt ce e rest := by
  show (hexists _ ∗ _) = _
  congr 1
  funext h
  refine propext ⟨fun hx => ?_, fun hu => ⟨b, pure_sep_intro hb hu⟩⟩
  obtain ⟨b', hb'⟩ := hx
  obtain ⟨he, hu⟩ := pure_sep_elim hb'
  rw [hb] at he
  have hbb : b = b' := congrArg Prod.fst (Option.some.inj he)
  rw [hbb]; exact hu

/-- **D2.**  `inflate_table`'s locals are exactly `here`'s 4 bytes and
    `count`/`offs`' 32 bytes each, all `Freeable` and all undefined — which is
    what §3's zeroing loop and §13's `here_carve` consume. -/
theorem locals_carve (bh bc bo : Block) :
    localsAt Layout.cenv (envOf bh bc bo) f_inflate_table.fn_vars
      = undefBytes .Freeable bh 0 4
        ∗ (undefBytes .Freeable bc 0 32 ∗ undefBytes .Freeable bo 0 32) := by
  show localsAt Layout.cenv (envOf bh bc bo)
    [(_here, Ty.Tstruct __1353 noattr), (_count, tarray tushort 16),
     (_offs, tarray tushort 16)] = _
  rw [localsAt_pin (envOf_here bh bc bo), localsAt_pin (envOf_count bh bc bo),
      localsAt_pin (envOf_offs bh bc bo),
      show localsAt Layout.cenv (envOf bh bc bo) [] = emp from rfl, sep_emp_eq,
      show (sizeof Layout.cenv (Ty.Tstruct __1353 noattr)).toNat = 4 from by
        decide,
      show (sizeof Layout.cenv (tarray tushort 16)).toNat = 32 from by decide]

/-! ### The three locals are distinct blocks

They are three *successive* `nextblock`s, so this is `toNat` arithmetic.  The
body needs it as a hypothesis at statement level (`Body.here_carve`, the return's
`freeList`, and every `HLoop` bridge take `bh ≠ bc` etc.), which is why `Pbody`
carries it rather than leaving it to be re-derived from heap disjointness. -/

theorem succ_ne (p : Positive) : p ≠ p.succ := by
  intro h
  have h' := congrArg Positive.toNat h
  rw [Positive.toNat_succ] at h'
  omega

theorem succ_ne2 (p : Positive) : p ≠ p.succ.succ := by
  intro h
  have h' := congrArg Positive.toNat h
  rw [Positive.toNat_succ, Positive.toNat_succ] at h'
  omega

theorem block_ne1 (m : Mem) : bhOf m ≠ bcOf m := succ_ne _
theorem block_ne2 (m : Mem) : bhOf m ≠ boOf m := succ_ne2 _
theorem block_ne3 (m : Mem) : bcOf m ≠ boOf m := succ_ne _

/-! ## §D3 The D/E interface -/

/-- The body's precondition: the caller's footprint `preHeap`, plus the three
    freshly allocated locals, in the environment and temporaries the entry
    produced.

    The three blocks are existentially quantified because `hentry` knows them
    only as successive `nextblock`s of the caller's memory; E peels them once
    at the top with `Sep.triple_exists`.

    Conjunct order is the order the entry *produces* — locals first, then
    `preHeap` verbatim.  E reassociates from here (§3's first segment wants
    `count` at the head); doing it there rather than here keeps this file free
    of any commitment about how the body is chained. -/
def Pbody (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat) : Sep.Assn :=
  fun e le hp => ∃ bh bc bo : Block,
    ∃ _ : bh ≠ bc, ∃ _ : bh ≠ bo, ∃ _ : bc ≠ bo,
    LocalSt (envOf bh bc bo) (entryTemps L ty codes)
      (undefBytes .Freeable bh 0 4
        ∗ (undefBytes .Freeable bc 0 32
           ∗ (undefBytes .Freeable bo 0 32
              ∗ preHeap L codes cap b0 lensF workF))) e le hp

/-- **D3 — `hentry`.**  The obligation `Sep.satisfies_internal` poses, at the
    `Pbody` above.

    The two heap conclusions are pure bookkeeping: `allocVariables_resources`
    is applied to the *whole* ambient fragment `hp ∪ hf`, so it returns
    `disjoint (hp ∪ hf) hl`, from which both halves follow; the `Agrees`
    conclusion needs only that `(hp ∪ hl) ∪ hf` and `(hp ∪ hf) ∪ hl` are the
    same heap, which they are because all three are pairwise disjoint. -/
theorem inflate_table_entry (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat) :
    ∀ (m : Mem) (hp hf : Heap),
      (inflateTableSpec L ty codes cap b0 lensF workF).pre (argVals L ty codes) hp →
      Heap.disjoint hp hf → Heap.Agrees (Heap.union hp hf) m →
      ∃ (e : Env) (le : TempEnv) (m1 : Mem) (hl : Heap),
        FunctionEntry2 ge f_inflate_table (argVals L ty codes) m e le m1
        ∧ Heap.disjoint (Heap.union hp hl) hf
        ∧ Heap.Agrees (Heap.union (Heap.union hp hl) hf) m1
        ∧ Pbody L ty codes cap b0 lensF workF e le (Heap.union hp hl) := by
  intro m hp hf hpre hd hag
  obtain ⟨-, hpreH⟩ := hpre
  obtain ⟨le, hent, hT⟩ := entry_facts ge hcenv L ty codes m
  obtain ⟨hl, hdl, hagl, hloc⟩ :=
    allocVariables_resources (alloc_vars ge hcenv m) (by decide)
      (by rw [hcenv]; decide) (Heap.union hp hf) hag
  -- split `disjoint (hp ∪ hf) hl` into its two halves
  obtain ⟨hdpl, hdfl⟩ := Heap.disjoint_union_left.mp hdl
  have hdlf : Heap.disjoint hl hf := Heap.disjoint_comm hdfl
  have hkey : Heap.union (Heap.union hp hl) hf = Heap.union (Heap.union hp hf) hl := by
    rw [Heap.union_assoc, Heap.union_comm hdlf, ← Heap.union_assoc]
  refine ⟨_, le, m3 m, hl, hent, Heap.disjoint_union_left.mpr ⟨hd, hdlf⟩, ?_, ?_⟩
  · rw [hkey]; exact hagl
  -- the fragment: locals ∗ preHeap, reassociated to the right
  refine ⟨bhOf m, bcOf m, boOf m, block_ne1 m, block_ne2 m, block_ne3 m,
    rfl, hT, ?_⟩
  have hsep : ((undefBytes .Freeable (bhOf m) 0 4
      ∗ (undefBytes .Freeable (bcOf m) 0 32
         ∗ undefBytes .Freeable (boOf m) 0 32))
      ∗ preHeap L codes cap b0 lensF workF) (Heap.union hp hl) := by
    refine ⟨hl, hp, Heap.disjoint_comm hdpl, Heap.union_comm hdpl, ?_, hpreH⟩
    rw [← locals_carve (bhOf m) (bcOf m) (boOf m), ← hcenv]
    exact hloc
  rw [sep_assoc_eq, sep_assoc_eq] at hsep
  exact hsep

/-! ## §D4 The body triple

With `hentry` discharged, the memory-safety theorem is *exactly* the body
triple, which InflateTableChain.lean proves. -/

/-- The body triple: `Pbody` in, the spec's postcondition out on
    `return`, and unreachable on every other exit (a function body cannot fall
    through, `break`, `continue`, or `goto` out of itself — `inflate_table`'s
    body ends in `return`, and it has no labels).

    `measure := 0` in the spec makes the leaf case trivial; the function
    contains no `Scall`, so no recursion obligation appears here. -/
abbrev BodyTriple (ge : CGenv) (L : Layout) (ty : _root_.Int)
    (codes cap b0 : Nat) (lensF workF : Nat → Nat) : Prop :=
  Triple ge (FunctionEntry2 ge) f_inflate_table
    (Pbody L ty codes cap b0 lensF workF) f_inflate_table.fn_body
    { normal := Assn.no, brk := Assn.no, cont := Assn.no,
      ret := (inflateTableSpec L ty codes cap b0 lensF workF).post }

/-- Memory safety follows from the body triple alone.

    Note what is *not* a hypothesis: nothing about the caller's memory `m`
    beyond `Agrees`, and no distinctness assumption about the three local
    blocks — `allocVariables_resources` derives their freshness from
    `Mem.alloc`, and `Agrees` forbids owning a byte of a not-yet-allocated
    block. -/
theorem safe_of_body (ge : CGenv) (hcenv : ge.genv_cenv = Layout.cenv)
    (L : Layout) (ty : _root_.Int) (codes cap b0 : Nat)
    (lensF workF : Nat → Nat)
    (body : BodyTriple ge L ty codes cap b0 lensF workF) :
    Sep.SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_inflate_table)
      (inflateTableSpec L ty codes cap b0 lensF workF)
      (argVals L ty codes) :=
  satisfies_internal ge (FunctionEntry2 ge) f_inflate_table _ _ _
    (inflate_table_entry ge hcenv L ty codes cap b0 lensF workF) body

end InflateTable.Entry
