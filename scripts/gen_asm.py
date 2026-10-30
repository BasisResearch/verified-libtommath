#!/usr/bin/env python3
"""The meet, a function's assembly from its annotation.

    python3 scripts/gen_asm.py experiments/asm/<f>.asm.json

Writes Tom/Machine/Fn/<Mod>.lean: the regions (the contract's, the stack cut into
the own frame's pieces and the callees' area, an allocation site), the entry state,
one cut per label (`Lbl`, Kit/Run.lean: parameters, measure, premise structure,
`At` from the segment rows' register list), one theorem per cut proving its edges,
and `correct` by `run`.

What the generator computes, so the annotation does not state it:
  * the segment applications: every row parameter from the register state the
    previous segment or call left (by name), loads from the kinds (a fact
    `DG M x (dp + 4 * i)` binds `x` to the digit function of the region at `dp`),
    every fact record by `cfacts`, every side condition by `side`;
  * the store rule from the row's log (`seq0`, `seqWs` over own-frame pieces, `seqD`
    on a digit array, `seqU` on a struct), the digit function after a store;
  * σ for every call by matching the callee's regions against ours (struct by its
    pointer, digits by their base, stack by containment, the site, the code);
    `hk`/`hsub`/`SepPres` checked by `rfl`/`iv_omega`/`decide` in Lean;
  * the `jal` word, offset and return address from the disassembly;
  * a cut's variables at a jump, by matching its register list with the state's;
  * the kinds at a cut (`congrK` by `rfl`), the snapshots of the own frame (`W(base,
    row)`: the row's write log).
The annotation holds: regions' pointers, the own frame's pieces, the cuts (pc,
register list, variables, kinds, value premise, measure), and per edge the steps
(segments by row name, calls with their parameters, branches, jumps with the value
premise's proof: the model-step lemmas of Tom/Spec).

Annotation syntax:
  callees      {"<Contract name>": {"ctor": "<region type>", "params": [<P fields in order>],
                "regions": [[name, ref], ...], "entry": "0x…", "heap": false, "site": region?}}: callee
               table entries besides the fixed `CALLEES`/`ENTRY` (an entry here wins).
               `ref`: 'stk', 'code', 'site', 'S <param>' (struct), 'D <param>' (digits).
  jump after a call
               ["call", C, params, res, {...}] then ["jump", cut, {...}]: the edge ends in
               the post-call state `At ret (C.rets ++ keep)`; the cut's register list
               (any; or the one named by the call's option "post") is reached by
               `At.subL` (`SubR` by `rfl`). Cut variables in the list are taken from the
               register state before the call, by name (give the call's results in "vars").
  seg overrides (rows mode as in Lean-segment mode)
               ["seg", row, how, {param: term, "_hL": proof, "_st": "pf1 pf2"}]: "_hL" is
               passed as `(hL := …)` (the `SubR` reshaping the current list to the row's
               pre), "_st" replaces the store rule's side proofs (`(by omega) (by omega)`);
               `_h` in either is the current `St` hypothesis.
               how = "o <region>": one digit store into an overlay `ovl g old i` by
               `St.seqOvl` (side proofs as "d", then `hgv` by `rfl`).
  "s" stores   how = "s <region>": a struct's sign by `St.seqS` (address `p + 8`) or, for any
               other spelling of the address, `St.seqS2` (its equation by `om`: through the
               projection `{ pa := sp - 56, … }.pa` a callee's `P` leaves in the kind).
  snapshots    `W(base, row)` of a row with an empty log is `base` itself (not `writeLog base []`).
  warning      an edge likely to overrun the heartbeat budget: see "budget".
  "d" stores   how = "d <region> [f]": one 4-byte store at `base + 4 * idx` (`St.seqD`) or at
               `base` itself (digit 0, `St.seqD0`); the digit function `f` becomes `Mont.upd`.
  "d8" stores how = "d8 <region> <f> [idx]": one 8-byte store (`sd`) of word `idx` into a digit
               array of 32-bit halves (`St.seqD8'`, Kit/W64.lean: an `mp_word` array); `idx` (annotation
               vocabulary) when the log's address is not `base + 8 * idx`; `f` becomes the halves' `Mont.upd`.
  tail call    ["tail", C, params, res, {"res": pf, "hq": name, "hra": pf, "K'": term,
                "flat": true | {"sound": pf, "stk": pf, "hF": pf, "kd": term, "ws": term}}]: `tail_seq` (Kit/Run.lean)
               from the callee's entry (the previous segment ends at the `j`); the rest
               of the edge (an exit) starts at `At ra (C.rets ++ keep) M' K'` with
               `_h`/`_M` the updated state; `K'` defaults to the cut's keep term.
               "flat": the callee runs on the whole stack: the state is first given back
               over the contract's layout by `St.flat` (sound `hS`, the stack's witness
               `⟨trivial, (hB .stk).2⟩`, pieces by `proj`/`sub3 (by omega)`, kinds `kind p`
               (or "kind_t"), written list `ws`), and σ maps
               into the contract's regions `R.r`. Needs the generated entry section.
  vocabulary   annotation text is Lean over the vocabulary: `ctx_vocab` words and the cut's
               variables are replaced, except named arguments/fields (`(a := …)`,
               `{ a := …`), names the text binds (`fun j hj =>`, `∀ j,`, `∃ j,`, `intro j`)
               and, in a cut's state, the record in `κ<cut> z x` (renamed `x_` when a
               variable is called `x`). Cut variables may not be called `z`, `xc`, `hc`.
               A row parameter with no register value, override or "rowdef" entry that
               would take a non-scalar context word (`p` = `z.p`, `m` = `z.m`) is an error.
  lay_rfl      true | {"<region>": "⟨base, len⟩"}: for a deep stack (a literal F ≳ 800, whose
               `⟨p.sp - F, F⟩` arm breaks `lay`'s equation lemmas): the entry section uses
               one `layE_<r> : lay p .r = … := rfl` per region instead of `simp [lay]`
               (intervals: stk `⟨p.sp - F, F⟩`, code `textIv`, "Rk" regions `⟨p.ptr, 24⟩` /
               `⟨p.dp, 4 * p.a.alloc⟩`, others given), and `heapEnd` is rewritten to its
               literal in `StkRes.lo` before `omega`.
  sites        "site": "<name>" | ["<name>", …]: allocation sites, `Site.lay` once per site over
               the pieces (`X = Option (… Y)`, outermost first); a call whose callee has a
               'site' region names ours by the option "site" when there are several. With
               style "pre", "site_lo" (Lean text over `z`, `hP`) proves `∀ y, 0x80000000 ≤ (ρ3 z.p y).base` (the
               sites' soundness side); the entry state is then over `ρX`.
  raw steps    ["tac", text, {"pc": "hex", "regs": list | "@call", "env": {word: term}, "lay": {site: n}}]: `@H`,
               (`@H'`, `@HP'`, `@M'` are fresh names the step binds, current from then on)
               `@M`, `@HP` in any step's text are the current `St` hypothesis, memory and
               heap checkpoint (a raw call rebinds them under the same names:
               `… @H (cd @H) … fun x @M hq @H => ?_`); the optional effect gives the pc and
               register list after the step (`@call`: the post-call state, as after "call")
               and new vocabulary words.
  isW          "isW": "<term : R → Bool>" (default `isW`): the contract's written names; the
               own frame's pieces are written on top (`Split.wr`, `Site.wr`). The entry
               section unfolds it by `simp [<term>]`.

  "Rk" kinds   besides "S p dp a" (struct) and "D dp a" (digits): "R ptr len", a written
               plain-RAM region (an out-parameter slot such as `*d`; kind `.ram` in the
               contract). The entry proves its RAM from the bundle; `lay_rfl` takes `⟨p.ptr, len⟩`.
               A ref "R <param>" in "refs" / a callee's "regions" matches it by pointer.
  "w" stores   how = "w <region>": a store into a written slot: `St.seqR` (kind "R": the slot
               becomes the snapshot `.frz (writeLog M log)` of the memory before) or `St.seqRD`
               (kind "D", a slot the contract models as a digit array exactly its region).
               Read back by `Dig.of_frz1` / `Kind.frz1W` (Kit/Run.lean) in the exits.
  "us" stores  how = "us <region>": a struct's `used` and `sign` in one segment (`St.seqUS`),
               rows and Lean-segment mode.
  slot step    ["slot", region, align]: a plain-RAM slot read as the one-digit array
               `slotInt (bytesT4 M p).toNat` (`St.slot1`), before a callee that models it so.
  heap tails   ["tail", C, …] with an allocating callee (`"heap": true`): `tail_heap`; the
               continuation also binds the callee's post `HPost …` (option "hpo", default
               `hpo`: its `place`/`foot`/`off` become the caller's) and the new checkpoint.
               With "flat": the checkpoint over the contract's layout by `HP.flatE` (option
               "hp"; it uses the generated `ramW`). Option "hsub": the callee's sub-layout proof.
  "flat" lay options "lay" (the layout given back: a region re-placed by an earlier
               call, `Iv.upd (lay p) R.aD J`) and "ins" (the pieces inside it), with "sound" and "hp" for it
               (`Kit/Replace.lean`: `Split.sound_upd`, `Split.sub_upd`, `HP.unsplit_upd`).
  entry_omega true: the entry section's frame-piece arithmetic closed by `omega` after `simp` (a
               stack depth over the operands, mred2klg.asm.json).
  jump "dec" a tactic proving the measure's decrease instead of `dec` (whose `omega` over a large
               context overran the budget at mred2klg.asm.json's back edge).
  "flat", pre  with style "pre" (one frame piece, no site): `St.flat1` (options "ws", "hf",
               "sound" default `hP.lay`, "ram" default `hP.rs`); with several frame pieces the `St.flat` path above, over `layG`.
  snapshots    the own frame's snapshots are tracked along an edge (from the cut's kinds
               `.frz X`, through every "ws" store, "forget" drops one): a jump gives a target
               cut variable that is a snapshot base (`"nL": ".frz Ml"`) its value; explicit
               "vars" win.
  raw rebinds  a raw step ending `fun … @M … @H => ?_` gets fresh names for `@M`/`@H`/`@HP`
               and the state follows them (no shadowing of a checkpoint's `Mk`).
  disj         "disj": [[r, t], …] (annotation: every edge; a cut: its edge): the disjointness of
               two regions hoisted once into the edge's prelude (`disj_hoist`, a `DisjH` fact kept
               out of `omega`'s sight); `cfacts` tries those before searching region pairs per fact.
  jump_mk      (default true) a jump builds the target's premise by `P<c>.mk'` (generated per cut:
               its fields over the cut's variables), so the field proofs see the values instead of
               record projections `⟨…⟩.i` (which `omega` takes for atoms; grow6 needed `by om`).
  reK          ["reK", region, k, e, hk?]: `St.reK` re-states the region's kind `k` as `k'` (`e : k' = k`);
               `hk : κ r = k` defaults to `rfl` (defeq): give it to re-kind from a kind equal only
               propositionally to the current one (grow6 used `redig … (show f' = _ by …)`).
  setmp        ["setmp", rS, rD, value, tactic?, {"used": pf, "alloc": pf, "sign": pf, "n": pf}?]: the
               header equations of `St.setMp` (default `rfl`) may be proved, so the value's fields
               need not be spelled as the old ones (grow6 passed `mx` explicitly for this).
  cases        ["cases", var, {"none": [...], "some ⟨q, c⟩": [...]}]: an alternative is its
               constructor and any rcases pattern; the pattern's names are bound as themselves
               (a pattern variable named like a vocabulary word is not replaced).
  rows         duplicate row names are rejected (`GR.check_names`).
  posts        Kit/Run.lean `HPost.keep` (nothing written), `HPost.inplace` (the site written in
               place, heap unchanged) for the exits; `cmp_lt`/`cmp_ge` for `mp_cmp_mag`'s word.
  cfacts       a struct field read at an address equal to the field's only by arithmetic
               (`sp - 40` for the `dp` of a struct at `sp - 56`, or through a projection
               `{ pa := sp - 56, … }.pa`) is closed by `omega`; the "s" rule's equation by `om`.

  Snap step    ["snap", region]: an untracked RAM region (kind `.ram`) re-read as the snapshot
               `.frz M` of the current memory (`St.snapK`, Kit/ByteBuf.lean); its snapshot is
               tracked from there on (the stores "ws" into it, a jump's snapshot variables).
  unslot step  ["unslot", region]: a callee's one-word out slot (kind `.mpD pd 1 f`, e.g.
               `mp_div_d`'s `*d`) given back to untracked RAM (`St.unslotK`; the slot inside the
               region by `iv_omega`), e.g. before a back edge to a cut where the region is `.ram`.
  layouts      every allocating call puts one more layer `Iv.upd ρ site J` on the layout. The layers
               per site are counted along an edge from the cut's `St` layout (through "defs":
               `def ρt … := Iv.upd (ρX p) nS …` is one layer on `nS`); at a jump to a cut with one
               layer fewer per extra placement the state and the checkpoint are normalised by
               `St.congrL`/`HP.congrL (Iv.upd_upd _ _ _ _)` (Kit/ByteBuf.lean), once per extra layer.
               One layer fewer than the target (the site left where the target cut places it,
               `ρ s = J` by `rfl`): `Iv.upd_eq_self _ _ rfl`. Explicit "st"/"hp" proofs win; a mismatch it cannot repair is a warning.
  "Rk" "F"     "F ptr len snap": a contract region of kind `.frz snap` (a byte buffer the contract
               states as the snapshot `snap` of its bytes, e.g. `p.m0`; `ToRadixPost`'s buffer before):
               the entry state holds it as that snapshot (no "snap" step, no read of the entry
               memory), its RAM from the bundle's witness (`(hB .r).2.1`), `lay_rfl` `⟨p.ptr, len⟩`;
               its stores by "ws", its snapshot tracked from the entry (`snap` in the vocabulary).
  no site      a heap function with no allocation site ("site" absent: its callees re-place a
               contract region, e.g. `mp_grow` the digits) gets the entry section over the pieces
               themselves (`X = Y`, `HP.entry hH offY …`); no dummy site.
               A heap call names the callee's site region by the call option "site".
  pos          optional: without "pos" the entry's `pos3` takes each contract region's `Off` (`Off.pos`:
               nonempty, or by `Off.edge` outside the arena), so a possibly empty region (a byte
               buffer of length `maxlen`) needs no `0 < …` premise; the frame pieces and the callees'
               area by their lengths. With "pos" (facts `0 < len`) as before.
  cfacts       (Kit/Run.lean) a digit array's word read at its base spelled `dp` (a callee's one-word
               out slot: `bytesT4 M (sp - 108)`, not `sp - 108 + 4 * 0`; `Dig.arr0`); a struct field
               or digit word at `a ± k` over the kind's base atom spelled otherwise (`sp - 96` for the
               sign of a struct at `sp - 104`) by its offset and one `omega`, before the region search
               (whose failing attempts overran the budget of an edge near it: r7a's `t.sign`); a
               snapshot's word (`St.frz4`) by a fact about the snapshot.
  budget       an edge theorem holds all its paths: weight = segments + 2 · calls + 5 · allocating
               calls (raw steps by the rule they apply). A warning at weight ≥ 48 or ≥ 5 allocating
               calls (calibrated: mp_gcd's largest edge 43 built, r6h's 4 allocating calls built;
               r6g's 5 overran):
               add a cut. It replaces gen6's "four calls on one path" (it fired on 6 built edges).

`--expand <f>`
prints the annotation as the generator reads it).
  let          {"W": text | list}: `{W}` in keys and texts; a list element "{W}" splices a list word.
  families     {"o": {"1": {words}, "2": {words}}}: a key with `{o}` is one copy per member (cut
               families `G{o}`, `L1{o}`, exits `mem{o}`; consecutive keys member by member).
  blocks       {"name": [steps]} and the step ["use", "name"]: a shared step list (in a family:
               `E{o}` gives `E1`, `E2`), e.g. the two operand orders' grow branches of s_mp_add.
  extends      "base.asm.json" (+ "subst" {token: token}): an aliasing variant is the base with its
               words restated and the destination renamed (`c` → `a`, `cS` → `aS`, …; texts and the
               region/vocabulary keys, not the callee table). A base with "abstract": true is a
               fragment (grow3.asm.json: the growing three-operand frame of s_mp_add/s_mp_sub).
  temps        heap temporaries in the own frame (`live_pass`; ksqr.asm.json): {"names": [t…] (the
               layout's argument order), "S"/"D": region names over `{t}`, "addr", "N" (sizes), "zero"
               (a fresh value over `{N}`), "lay" (`{IV}` the temporaries' intervals, `{IB}`), "IB",
               "base" (the heap tail, `hin`), "kinds_pre", "state" (over `{LAY}`, `{HEAP}`, `{cut}`),
               "recon", "clear" {callee, args, perm, res}, "jst", "jhp", "jhp_perm", "jvars_all", "afresh"
               (the fact of a block just re-placed, `{t}`), "perm_style": "chain"}; a live entry's 6th element overrides the clear's positivity proof,
               "dk" "S<t>" a struct's kind.
  live         a cut's live temporaries, heap order front first: [[t, q, n, T, A?], …] (block `(q, 4 n)`,
               value `T`, alloc fact `A` : `T.alloc = n ∧ 0 < n`, by default `⟨rfl, by om⟩` for a closed
               value, `⟨rfl, hq.pos⟩` when `n` is `T.alloc`, else the premise `a<t>`), with "dk" (digit
               kinds), "tail", "bI"; the cut's kinds and state are generated. "live": "auto": the set
               from the first incoming jump, each temporary named by the cut's variables q<t>/n<t>/t<t>.
               A cut with its own "state" (the entry, "live": []) is only tracked.
  heap steps   along an edge the live set is tracked: ["alloc", t, q] (an init call's block placed in
               front, the layout re-stated by "recon"), ["clear", t] (mp_clear: the block moved to the
               front by `List.perm_middle`, the call generated), ["live", {t: entry | null}, {tail, bI,
               order}?] (a value re-stated, a block dropped); a call option "front": t moves t's block to
               the front (option "perm" from `{PM}` or `{CHAIN}`, `{Q}`/`{N}`/`{T}` its entry, the heap behind
               it `{REST}`); `{HEAP}`/`{ENTS}` in a
               call are the current heap list / its entries, `{RESTE:t}` / `{CHAINTO:t}` the entries behind t / the
               perm moving t to the front.
  jumps        to a cut with a live set: its live variables and alloc facts from the tracked set (texts may
               use `{TGTL}` the target's heap list, `{ENTS}`, `{CHAIN}` the perm to its order); with
               "norm": true the layout and checkpoint are normalised ("jst", "jhp"; a block moved behind
               the next k by `HP.perm ((List.perm_middle …).symm)`). Tsqr.asm.json is the model.
  blocks       a block may use blocks to any depth (`_resolve_uses`; a cycle is an error), and a let word may hold
               `["use", b]` steps (resolved where it is spliced): a call chain as one block per call, each ending in
               `["use", "{NEXT}"]` (a family member's word), the skeleton a let list word.
  temps        "heap_form": "append" (heap lists always `[e, …] ++ tail`, also on the base tail); "front_perm": a
               call option "front" on a temporary whose size is not yet `T.alloc` gets this perm (words `{Q}`, `{T}`,
               `{REST}`, `{PM}`, `{RW}` = `rw [show (T).alloc = n from A1]`, `{A1}`/`{A2}` the alloc fact's proofs);
               "back" (default `have @HP := @HP.perm ({PERM}).symm`): the step ["back", t] undoes the last front
               move of t (its block behind the entries it had in front of it; nothing when there were none).
  clear        words `{A1}`, `{A2}` (the alloc fact's two proofs: the components of `⟨x, y⟩`, else `A.1`, `A.2`).
  tac/have     `{ENTS}`, `{HEAP}`, `{LAY}` in a raw step or a "have" are the live entries, heap list and layout there
               (a destination's block kept as the heap tail: ["live", {}, {"tail": …, "bI": …}] after a call into it).
  static       a block may be a list of lines.
  Region       {"api": "Api.MpDiv", "temps": [t…], "lay": "SqrAlg.lay p" | {r: arm, "_": "lay p"}, "kind": "kind p",
               "eqs": true, "gpre": {"res", "lay", "isW", "kind", "hin", "extra": [[field, type]…]},
               "eqsC": {name: {"lay": "lay p", "regions": [r…]}}}: the region type of a style-"pre" assembly with
               heap temporaries, generated at the head (it was a block of `Fn/<F>G5K.lean`): `R` (the annotation's
               "R", the temporaries last), `layG` (temporaries at `Iv.nil`; `layG_<r>` by `rfl` unless "eqs": false),
               `kindG`, the written flags (named by "isW", from "written"), `emb` (the temporaries as `Site.lay`s),
               `soundG` (`Site.soundN`, Kit/Sites.lean, over `Bundle.lo`), `GPre`. "eqsC": a layout's arm
               equations `name_<r> : lay p .r = arm := rfl` (also without "temps": `Api.MpSqrS.lay`'s deep stack).
  chunking     an assembly whose edge theorems pass CHUNK_MIN lines (annotation key "chunk_min") is written as `Fn/<Mod>/Defs.lean` (everything
               before the edges), `Fn/<Mod>/C<k>.lean` (consecutive cuts' edges, about CHUNK_LINES lines each) and the
               umbrella `Fn/<Mod>.lean` (`edges`, `correct`); `--chunk-lines N` or the key "chunk_lines" (0: one file),
               `--out-dir D`.
  Multi-site   a callee with "heapN": true (built in: `mpInitMulti<k>`, `mpClearMulti<k>`, k = 2..15,
               `_multi8_callees`) is called by `call_heapN` (`Gen.call_heapN`, `Gen.sigmaN`): σ maps the
               callee's `MR k` regions (`st ⟨i, _⟩`, `dg ⟨i, _⟩`; a default arm for indices out of range),
               refs 'S ps[i]' (an element of a list parameter), 'S xs[i]#0' / 'D xs[i]#1' (a tuple
               component), 'site i' (the call option "sites": [our site regions, in argument order]);
               `hsub`/`hk` by `mr_split <;> mr_iv` / `mr_split <;> rfl` (options "hsub"/"hk" override);
               one layout layer per callee site ("sites") on its image. Parameters: `mpInitMulti<k>`
               ⟨sp, [p₀, …], H, m0⟩, `mpClearMulti<k>` ⟨sp, [(p₀, dp₀, a₀), …], H, m0⟩ (heap `blocks xs ++ H`;
               `m0` the caller's memory its stack arguments are read from). For k ≥ 8 the stack
               arguments' words `sa ⟨j, _⟩` map to the regions of the call option "sargs".
  Callee refs 'to <our region>': the callee region is ours by name (`to nR .ks`).
  call opts    "sig" {callee region: our region text} (σ for a family member `nR (.tS x)`, no ref search), "hk", "hw",
               "with" (a named option set of the annotation's "call_opts", the call's own keys on top), "named"
               {arg: proof} (further named arguments of `call_heap`/`call_heapR`, e.g. `hrs`, `hal`),
               "hsep" (proofs passed to `call_heap`/`call_std` when the kind/separation checks do not reduce:
               two members of one family), "hsub" also for `call_std`, "C" (the contract as a Lean term, e.g.
               `(Std.reduxH md)`; the callee name still selects the registry entry for σ), "jalr" (the source
               register number of `jalr ra, 0(rs1)`: `call_heapR`, Kit/CallR.lean) with "htgt" (the register's
               value is the contract's entry; default `by decide`).
  seg facts a row fact by its name in the seg override (`{"XS": proof}`, `_h` the state): a word
               of a snapshot piece whose snapshot is a cut variable, read by a premise about it.
  call opts "hrs", "hal": `call_heapR`'s register-list and entry-alignment checks when they are not closed
               (`redux`'s entry by the mode, `Std.reduxS md`).
  fam          style "pre": [[ctor, fits, wit], …] the region type's indexed constructors (after the fixed names,
               not in "R" so not in `Names`): one bullet each in the entry bundle's `cases`.
  Grow step    ["grow", callee, t, args, hq, {"res", "fail": row, "tail"?}]: an in-place `mp_add`/`mp_sub` on the
               live temporary t that may re-place its block (`Std.mpAddHAv`/`mpSubHAc`, result `(ok, q', t')`):
               the call (option "front": t, site temps "D"), `ok<t>`/`q<t>1`/`t<t>1`, the new entry; on failure
               `["back", t]` + temps "grow" "fail" (`{SEG}` the row, an element "{TAIL}" the steps "tail" of the
               step or of temps "grow"), on success `["back", t]`, `["bind", {q<t>: q<t>1}]`, temps "grow" "ok",
               then the rest of the edge (`grow_pass`, before `live_pass`).
  {VALS}       in a raw step or a "have": the live values in temps "names" order (a compound one parenthesised),
               e.g. the kinds re-stated after a call, `….congrK (κ' := κT z qX … {VALS})`.
"""
import copy, importlib.util, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
_spec = importlib.util.spec_from_file_location('gen_rows', os.path.join(ROOT, 'scripts/gen_rows.py'))
GR = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(GR)


def die(msg):
    sys.exit(f'gen_asm: {msg}')


# ---- annotation templates: "extends"/"subst", "let", "families", "use"
_IDC = r"[A-Za-z0-9_'Ͱ-Ͽᴀ-ᶿ⁰-₟]"


def subst_text(s, sub):
    """Simultaneous whole-token renaming: a key matches where it is not inside a longer
    identifier (a `.` on either side is a boundary: `nR .cS`, `hres.cpos`, `Api.SAddG.F`)."""
    if not sub or not isinstance(s, str):
        return s
    keys = sorted(sub, key=len, reverse=True)
    pat = re.compile(r'(?<!' + _IDC + r')(?:' + '|'.join(re.escape(k) for k in keys) + r')(?!' + _IDC + r')')
    return pat.sub(lambda m: sub[m.group(0)], s)


_RENAME_KEYS = ('Rk', 'refs', 'kinds', 'ctx_vocab')      # dicts keyed by region names / words


def subst_tree(t, sub, up=(), keep=frozenset()):
    """Every text renamed; keys only of the dicts keyed by region names or vocabulary words (`Rk`,
    `refs`, a cut's `kinds`, a `kindsets` entry, `ctx_vocab`): annotation fields, row parameters
    (`rowdef`, a segment's overrides) and cut variables keep their names; `callees` (the callees'
    vocabulary) is not renamed, nor the keys `keep` (the variant's own `Rk`/`refs`/`ctx_vocab` keys)."""
    if isinstance(t, str):
        return subst_text(t, sub)
    if isinstance(t, list):
        return [subst_tree(x, sub) for x in t]
    if isinstance(t, dict):
        ren = (up[-1:] and up[-1] in _RENAME_KEYS) or up[-2:-1] == ('kindsets',)
        out = {}
        for k, v in t.items():
            if not up and k == 'callees':      # the callees' own vocabulary: never renamed
                out[k] = v
                continue
            nk = subst_text(k, sub) if ren and (up + (k,)) not in keep else k
            out[nk] = subst_tree(v, sub, up + (k,), keep)   # a renamed key colliding: the later wins
        return out
    return t


def merge_tree(base, over):
    """`over` on top of `base`: dicts merged key by key (a `null` deletes), anything else replaced."""
    if not (isinstance(base, dict) and isinstance(over, dict)):
        return over
    out = dict(base)
    for k, v in over.items():
        if v is None:
            out.pop(k, None)
        elif k in out:
            out[k] = merge_tree(out[k], v)
        else:
            out[k] = v
    return out


def load_raw(path):
    """An annotation with its `"extends"` chain merged (this file's keys on top of the base's), templates
    not yet expanded; and the renamings (`"subst"`) to apply after expansion, innermost first."""
    a = json.load(open(path))
    subs = []
    if 'extends' in a:
        bp = os.path.join(os.path.dirname(path), a.pop('extends'))
        base, subs = load_raw(bp)
        base.pop('abstract', None)
        sub = a.pop('subst', None)
        keep = frozenset((d, k) for d in ('Rk', 'refs', 'ctx_vocab') for k in a.get(d, {}))
        a = merge_tree(base, a)
        if sub:
            subs = subs + [(sub, keep)]
    return a, subs


_WORD = re.compile(r'\{([A-Za-z_][\w]*)\}')


def _ex_str(s, env):
    for _ in range(8):
        t = _WORD.sub(lambda m: env[m.group(1)] if isinstance(env.get(m.group(1)), str) else m.group(0), s)
        if t == s:
            break
        s = t
    for m in _WORD.finditer(s):
        if isinstance(env.get(m.group(1)), list):
            die(f'template word {{{m.group(1)}}} is a list: only a whole list element may name it ({s[:60]}…)')
    return s


def expand_tree(t, env, fams, blocks):
    if isinstance(t, str):
        m = _WORD.fullmatch(t)
        if m and isinstance(env.get(m.group(1)), (list, dict)):    # a whole text naming a list/dict word
            return expand_tree(env[m.group(1)], env, fams, blocks)
        return _ex_str(t, env)
    if isinstance(t, list):
        out = []
        for x in t:
            if isinstance(x, str):
                m = _WORD.fullmatch(x)
                if m and isinstance(env.get(m.group(1)), list):
                    out += expand_tree(env[m.group(1)], env, fams, blocks)
                    continue
                v, seen = x, 0                 # a word naming a list word (an alias): spliced
                while m and isinstance(env.get(m.group(1)), str) and seen < 8:
                    v, seen = env[m.group(1)], seen + 1
                    m = _WORD.fullmatch(v)
                if seen and m and isinstance(env.get(m.group(1)), list):
                    out += expand_tree(env[m.group(1)], env, fams, blocks)
                    continue
            if isinstance(x, list) and len(x) == 2 and x[0] == 'use' and isinstance(x[1], str):
                nm = _ex_str(x[1], env)
                if blocks is None:             # blocks being defined: resolved in the second pass
                    out.append(['use', nm])
                    continue
                if nm not in blocks:
                    die(f'["use", "{nm}"]: no such block')
                out += blocks[nm]
                continue
            out.append(expand_tree(x, env, fams, blocks))
        return out
    if isinstance(t, dict):
        out = {}
        items = [(k, v) for k, v in t.items() if k != '#']     # `#`: a comment
        i = 0
        while i < len(items):
            k, v = items[i]
            fs = [f for f in _WORD.findall(k) if f in fams and f not in env]
            if not fs:
                out[_ex_str(k, env)] = expand_tree(v, env, fams, blocks)
                i += 1
                continue
            f = fs[0]
            j = i                              # a run of keys in one family: member by member
            while j < len(items) and f in _WORD.findall(items[j][0]):
                j += 1
            for mem, words in fams[f].items():
                e2 = dict(env)
                e2.update(words)
                e2[f] = mem
                out.update(expand_tree(dict(items[i:j]), e2, fams, blocks))
            i = j
        return out
    return t


# ---- heap temporaries: "temps", a cut's "live", steps alloc/clear/live, call "front"
class Live:
    """The live temporaries at a point: `t -> [q, n, T, A]` (block `(q, 4 * n)`, value `T`, `A` a proof of
    `T.alloc = n ∧ 0 < n`), in heap order (front first), over the heap tail and the destination's interval."""

    def __init__(self, tm, ents, order, tail, bI, undo=None):
        self.tm, self.d, self.order, self.tail, self.bI = tm, {t: list(e) for t, e in ents.items()}, list(order), tail, bI
        self.undo = dict(undo or {})            # t -> the order before a call moved t to the front ("back")

    def copy(self):
        return Live(self.tm, self.d, self.order, self.tail, self.bI, self.undo)

    @staticmethod
    def parts(A):
        """An alloc fact's two proofs (`T.alloc = n`, `0 < n`): the components of `⟨x, y⟩`, else `A.1`, `A.2`."""
        a = A.strip()
        if a.startswith('⟨') and a.endswith('⟩'):
            inner, d = a[1:-1], 0
            for j, ch in enumerate(inner):
                d += ch in '([{⟨'
                d -= ch in ')]}⟩'
                if ch == ',' and d == 0:
                    return inner[:j].strip(), inner[j + 1:].strip()
        return f'{a}.1', f'{a}.2'

    @staticmethod
    def afact(t, q, n, T, tm=None):
        """The default alloc fact: a closed value (a parenthesised term) by `rfl`, a value just re-placed by
        a call (`n` = `T.alloc`) by its post (temps "afresh", default `⟨rfl, hq.pos⟩`), else the cut
        premise `a<t>`."""
        if T.startswith('('):
            return '⟨rfl, by om⟩'
        if n == f'{T}.alloc':
            return ((tm or {}).get('afresh', '⟨rfl, hq.pos⟩')).replace('{t}', t)
        return f'a{t}'

    def chain(self, dst, tail=None):
        """A `List.Perm` from the heap in this order to `dst` (temporaries), over the tail (cons form):
        position by position, `dst[j]` moved to `j` by `List.perm_middle` under the first `j` entries
        (`List.Perm.append_left`), every step with its two sides."""
        tl = self.tail if tail is None else tail
        def cons(es):
            return ' :: '.join(es + [tl]) if es else tl
        cur, steps = self.ents(), []
        for j, e in enumerate(self.ents(dst)):
            i = cur.index(e)
            if i == j:
                continue
            new = cur[:j] + [e] + cur[j:i] + cur[i + 1:]
            pm = f'List.perm_middle (l₁ := [{", ".join(cur[j:i])}])'
            if j:
                pm = f'List.Perm.append_left [{", ".join(cur[:j])}] ({pm})'
            steps.append(f'(show List.Perm ({cons(cur)}) ({cons(new)}) from {pm})')
            cur = new
        if not steps:
            return 'List.Perm.refl _'
        t = steps[0]
        for s_ in steps[1:]:
            t = f'({t}).trans {s_}'
        return t

    def ent(self, t):
        q, n = self.d[t][0], self.d[t][1]
        return f'({q}, 4 * {n})'

    def ents(self, order=None):
        return [self.ent(t) for t in (self.order if order is None else order)]

    def heap(self, order=None):
        """On the base tail (`hin`) the cons form `e :: … :: hin`, on another tail `[e, …] ++ tail`."""
        e = self.ents(order)
        if self.tm.get('heap_form') == 'append':
            return ('[' + ', '.join(e) + '] ++ ' + self.tail) if e else self.tail
        if self.tail == self.tm.get('base', 'hin'):
            return ' :: '.join(e + [self.tail])
        return ('[' + ', '.join(e) + '] ++ ' + self.tail) if e else self.tail

    def lay(self):
        iv = [f'⟨{self.d[t][0]}, 4 * {self.d[t][1]}⟩' if t in self.d else 'Iv.nil' for t in self.tm['names']]
        return self.tm['lay'].replace('{IV}', ' '.join(iv)).replace('{IB}', self.bI)

    def front(self, t):
        """`t` moved to the front: the perm term (`List.perm_middle`, or None) and the new order."""
        i = self.order.index(t)
        pm = None if i == 0 else f"List.perm_middle (l₁ := [{', '.join(self.ents(self.order[:i]))}])"
        self.undo[t] = list(self.order)
        self.order = [t] + [x for x in self.order if x != t]
        return pm


def _tm_word(s, w):
    for k, v in w.items():
        s = s.replace('{' + k + '}', v)
    return s


def live_of(tm, c, cu):
    ents, order = {}, []
    for e in cu['live']:
        t, q, n, T = e[:4]
        A = e[4] if len(e) > 4 else Live.afact(t, q, n, T, tm)
        ents[t] = [q, n, T, A] + list(e[5:6])
        order.append(t)
    return Live(tm, ents, order, cu.get('tail', tm.get('base', 'hin')), cu.get('bI', tm['IB']))


def live_kinds(tm, L, cu):
    k = dict(tm.get('kinds_pre', {}))
    dk = cu.get('dk', {})
    if isinstance(dk, list):                   # several dicts, merged in order
        dk = {k: v for d in dk for k, v in d.items()}
    for t in tm['names']:
        S, D = _tm_word(tm['S'], {'t': t}), _tm_word(tm['D'], {'t': t})
        if t in L.d:
            q, n, T = L.d[t][:3]
            k[S] = dk.get('S' + t, f'.mpS ({tm["addr"][t]}) {q} {T}')
            k[D] = dk.get(t, f'.mpD {q} ({T}).alloc ({T}).digit')
        else:
            k[S] = '.ram'
            k[D] = '.ram'
    k.update(cu.get('kinds', {}))
    return k


FROM_FIELDS = ('vars', 'kinds', 'state', 'prem', 'prelude', 'regs_over')


def parse_vars(s):
    """A cut's variables `"M Mk : Mem; q : Nat"` as (name, type) pairs in order."""
    out = []
    for grp in (s or '').split(';'):
        grp = grp.strip()
        if grp:
            names, _, ty = grp.partition(':')
            out += [(n, ty.strip()) for n in names.split()]
    return out


def render_vars(ps):
    """Pairs back to text, consecutive names of one type grouped (only the pairs reach the Lean)."""
    out = []
    for n, t in ps:
        if out and out[-1][1] == t:
            out[-1][0].append(n)
        else:
            out.append(([n], t))
    return '; '.join(f'{" ".join(ns)} : {t}' for ns, t in out)


def from_merge(c, b, cu, base):
    """ The cut's "vars" pairs inserted after the base's last
                 variable of the same type (else appended);
      prem/state base entries minus "-prem"/"-state" (field names); an own entry of a base field's name
                 replaces it in place, a new one is appended; the state's `κ<b>` becomes `κ<c>`;
      kinds,     base dict minus "-kinds"/"-regs_over" (keys), own keys on top (in place, or appended);
      regs_over
      prelude    the base's lines, then the cut's own;
    "<field>!" gives the field outright (no inheritance; `null`: absent)."""
    out = {k: v for k, v in cu.items() if k not in FROM_FIELDS and not k.startswith('-') and not k.endswith('!')
           and k != 'from'}
    for f in FROM_FIELDS:
        if f + '!' in cu:                      # outright; `null`: the field absent
            if cu[f + '!'] is not None:
                out[f] = cu[f + '!']
            continue
        bv, own, drop = base.get(f), cu.get(f), cu.get('-' + f, [])
        if isinstance(drop, str):
            drop = drop.split()
        if f == 'vars':
            ps = [(n, t) for n, t in parse_vars(bv) if n not in drop]
            for n, t in parse_vars(own):
                if n in [x for x, _ in ps]:
                    die(f'cut {c} ("from": {b}): variable {n} is already the base\'s')
                idx = max([i for i, (_, t2) in enumerate(ps) if t2 == t], default=len(ps) - 1)
                ps.insert(idx + 1, (n, t))
            if ps:
                out[f] = render_vars(ps)
        elif f in ('prem', 'state'):
            if isinstance(own, str) or (own is None and isinstance(bv, str)):
                if own is not None or bv is not None:
                    out[f] = own if own is not None else bv
                continue
            es = [[e[0]] + [t.replace(f'κ{b} ', f'κ{c} ') if f == 'state' and isinstance(t, str) else t for t in e[1:]]
                  for e in (bv or []) if e[0] not in drop]
            names = [e[0] for e in es]
            for e in own or []:
                if e[0] in names:
                    es[names.index(e[0])] = e
                else:
                    es.append(e); names.append(e[0])
            if es or own is not None or bv is not None:
                out[f] = es
        elif f in ('kinds', 'regs_over'):
            if isinstance(own, str) or (own is None and not isinstance(bv, dict)):
                if own is not None or bv is not None:
                    out[f] = own if own is not None else bv
                continue
            d = {k: v for k, v in (bv or {}).items() if k not in drop}
            for k, v in (own or {}).items():
                d[k] = v
            if d or own is not None or bv is not None:
                out[f] = d
        elif f == 'prelude':
            ls = [l for i, l in enumerate(bv or []) if i not in drop] + list(own or [])
            if ls or own is not None or bv is not None:
                out[f] = ls
    return out


def from_pass(a):
    """Resolve the cuts' `"from"` (`from_merge`), bases first; a cycle is an error."""
    cuts = a.get('cuts')
    if not isinstance(cuts, dict) or not any(isinstance(cu, dict) and 'from' in cu for cu in cuts.values()):
        return a
    done = set()

    def res(c, stack):
        cu = cuts[c]
        if c in done or not isinstance(cu, dict) or 'from' not in cu:
            return
        b = cu['from']
        if b not in cuts or not isinstance(cuts[b], dict):
            die(f'cut {c}: "from": no cut {b}')
        if b in stack:
            die(f'cut {c}: "from" cycle {stack + (c,)}')
        res(b, stack + (c,))
        cuts[c] = from_merge(c, b, cu, cuts[b])
        done.add(c)
    for c in list(cuts):
        res(c, ())
    return a


def _tm_tree(t, w):
    if isinstance(t, str):
        return _tm_word(t, w)
    if isinstance(t, list):
        return [_tm_tree(x, w) for x in t]
    if isinstance(t, dict):
        return {k: _tm_tree(v, w) for k, v in t.items()}
    return t


def grow_pass(a):
    """`["grow", callee, t, args, hq, {"res": …, "fail": seg}]`: an in-place call that may grow the live
    temporary `t` (`Std.mpAddHAv`/`mpSubHAc`: `(ok, q', t')`) — the call with `t`'s block in front, the
    result unpacked to `ok<t>`, `q<t>1`, `t<t>1` (alloc fact `⟨rfl, hq.pos⟩`), on failure the block put
    back, then temps "grow" "fail" (`{SEG}` the row of the failing branch, an element "{TAIL}" the steps
    "tail" of the step's options or else of temps "grow": the jump to the error exit), on success the block put back
    and re-bound (`q<t>` names `q<t>1`), then temps "grow" "ok", then the rest of the edge."""
    tm = a.get('temps')
    if not tm or 'cuts' not in a:
        return a
    g = tm.get('grow', {})

    def steps(ss):
        out = []
        for i, s in enumerate(ss):
            if isinstance(s, list) and s and s[0] == 'grow':
                _, callee, t, args, hq = s[:5]
                o = dict(s[5]) if len(s) > 5 else {}
                x, ok = f'x{t}', f'ok{t}'
                co = {'front': t, 'hq': hq, 'site': _tm_word(tm['D'], {'t': t}), 'res': o['res']}
                tail = copy.deepcopy(o.get('tail', g.get('tail', [])))
                fail = [['back', t]]
                for st in _tm_tree(copy.deepcopy(g.get('fail', [])), {'SEG': o['fail']}):
                    fail += tail if st == '{TAIL}' else [st]
                good = [['back', t], ['bind', {f'q{t}': f'q{t}1'}]] + copy.deepcopy(g.get('ok', [])) + steps(ss[i + 1:])
                return out + [['call', callee, args, x, co], ['tac', f'obtain ⟨{ok}, q{t}1, t{t}1⟩ := {x}'],
                              ['live', {t: [f'q{t}1', f't{t}1.alloc', f't{t}1', f'⟨rfl, {hq}.pos⟩']}],
                              ['cases', ok, {'false': fail, 'true': good}]]
            if isinstance(s, list) and s and s[0] == 'if':
                s = list(s)
                s[2], s[3] = steps(s[2]), steps(s[3])
            elif isinstance(s, list) and s and s[0] == 'cases':
                s = [s[0], s[1], {k: steps(v) for k, v in s[2].items()}] + s[3:]
            out.append(s)
        return out
    for cu in a['cuts'].values():
        if 'edge' in cu:
            cu['edge'] = steps(cu['edge'])
    return a


def live_pass(a):
    """Cuts with `"live"` get their kinds and state; along every edge the live set is tracked (from the
    cut's, through `alloc`/`clear`/`live` steps and calls with `"front"`), the heap lists, perms and the
    jumps' live variables and alloc facts computed (annotation syntax: the gen_asm docstring)."""
    tm = a.get('temps')
    if not tm:
        return a
    a.pop('temps')
    cuts = a['cuts']
    lives = {c: live_of(tm, c, cu) for c, cu in cuts.items() if 'live' in cu and cu['live'] != 'auto'}
    auto = [c for c, cu in cuts.items() if cu.get('live') == 'auto']
    # "live": "auto": the cut's live set from its first incoming jump (walked in cut order, to a fixpoint):
    # each temporary's block and value named by the cut's variables q<t>/n<t>/t<t> where it has them
    while auto:
        seen = {}
        for c, cu in cuts.items():
            if c in lives and 'edge' in cu:
                _live_steps(tm, a, lives, copy.deepcopy(cu['edge']), lives[c].copy(), seen)
        new = [c for c in auto if c in seen]
        if not new:
            die(f'"live": "auto" at {auto}: no incoming jump from a cut with a live set')
        for c in new:
            L, cu = seen[c], cuts[c]
            cv = {n for grp in cu.get('vars', '').split(';') for n in grp.partition(':')[0].split()}
            ents = {}
            for t in L.order:
                q, n, T, _ = L.d[t][:4]
                q, n, T = (f'q{t}' if f'q{t}' in cv else q), (f'n{t}' if f'n{t}' in cv else n), (f't{t}' if f't{t}' in cv else T)
                ents[t] = [q, n, T, Live.afact(t, q, n, T, tm)]
            lives[c] = Live(tm, ents, L.order, cu.get('tail', L.tail), cu.get('bI', L.bI))
        auto = [c for c in auto if c not in new]
    for c, L in lives.items():
        cu = cuts[c]
        if 'state' in cu:                      # a cut with its own state (the entry): tracking only
            continue
        cu['kinds'] = live_kinds(tm, L, cu)
        w = {'LAY': L.lay(), 'HEAP': L.heap(), 'cut': c}
        cu['state'] = [[f, _tm_word(t, w)] for f, t in tm['state']]
    for c, cu in cuts.items():
        L = lives[c].copy() if c in lives else None
        if 'edge' in cu:
            cu['edge'] = _live_steps(tm, a, lives, cu['edge'], L)
    for c in lives:
        for f in ('live', 'dk', 'tail', 'bI'):
            cuts[c].pop(f, None)
    return a


def _live_steps(tm, a, lives, steps, L, seen=None):
    out = []
    for i, s in enumerate(steps):
        if not isinstance(s, list) or not s:
            out.append(s)
            continue
        op = s[0]
        if op in ('if', 'cases'):            # branches end the edge: each continues with its own copy
            if op == 'if':
                s = list(s)
                s[2] = _live_steps(tm, a, lives, s[2], L.copy() if L else None, seen)
                s[3] = _live_steps(tm, a, lives, s[3], L.copy() if L else None, seen)
                out.append(s)
            else:
                alts = {k: _live_steps(tm, a, lives, v, L.copy() if L else None, seen) for k, v in s[2].items()}
                out.append([s[0], s[1], alts] + s[3:])
            return out + steps[i + 1:]
        if L is None:
            out.append(s)
            continue
        if op == 'alloc':
            # ["alloc", t, q]: the init call's block placed (front), the layout re-stated (`recon`)
            t, q = s[1], s[2]
            n = tm['N'][t]
            T = _tm_word(tm['zero'], {'N': n})
            L.d[t] = [q, n, T, Live.afact(t, q, n, T, tm)]
            L.order = [t] + [x for x in L.order if x != t]
            for line in tm.get('recon', []):
                out.append(['tac', _tm_word(line, {'LAY': L.lay()})])
            continue
        if op == 'live':
            # ["live", {t: [q, n, T, A?] | null}, {"tail": …, "bI": …, "order": [...]}?]: entries re-stated
            for t, e in s[1].items():
                if e is None:
                    L.d.pop(t, None)
                    L.order = [x for x in L.order if x != t]
                else:
                    q, n, T = e[:3]
                    L.d[t] = [q, n, T, e[3] if len(e) > 3 else Live.afact(t, q, n, T, tm)] + list(e[4:5])
                    if t not in L.order:       # a new block is in front; a live one keeps its place
                        L.order = [t] + L.order
            o = s[2] if len(s) > 2 else {}
            if 'tail' in o:
                L.tail = o['tail']
            if 'bI' in o:
                L.bI = o['bI']
            if 'order' in o:
                L.order = list(o['order'])
            continue
        if op == 'clear':
            # ["clear", t]: mp_clear of a live temporary, its block moved to the front first
            t = s[1]
            q, n, T, A = L.d[t][:4]
            if tm.get('perm_style') == 'chain':
                pm = L.chain([t] + [x for x in L.order if x != t])
                L.order = [t] + [x for x in L.order if x != t]
            else:
                pm = L.front(t)
            L.order.remove(t)
            pos_over = L.d[t][4] if len(L.d[t]) > 4 else None
            del L.d[t]
            rest = L.heap()
            if A.startswith('⟨rfl,'):
                fr, pos = 'rfl', ('om' if A == '⟨rfl, by om⟩' else 'exact ' + A[len('⟨rfl, '):-1])
            else:
                fr, pos = f'{A}.1', f'rw [{A}.1]; exact {A}.2'
            pos = pos_over or pos
            w = {'Q': q, 'T': T, 'ADDR': tm['addr'][t], 'REST': rest, 'PM': pm or 'List.Perm.refl _',
                 'RW': f'rw [show ({T}).alloc = {n} from {fr}]', 'POS': pos}
            w['A1'], w['A2'] = Live.parts(A)
            cl = tm['clear']
            out.append(['call', cl['callee'], _tm_word(cl['args'], w), '_',
                        {'perm': _tm_word(cl['perm'], w), 'res': _tm_word(cl['res'], w)}])
            continue
        if op == 'call' and len(s) > 4 and isinstance(s[4], dict) and 'front' in s[4]:
            # a call on a live temporary's block: it is moved to the front; {REST} the heap behind it
            o = dict(s[4])
            t = o.pop('front')
            ch = L.chain([t] + [x for x in L.order if x != t])
            pm = L.front(t)
            rest = Live(tm, {x: L.d[x] for x in L.order[1:]}, L.order[1:], L.tail, L.bI).heap()
            q, n, T = L.d[t][:3]
            w = {'REST': rest, 'PM': pm or 'List.Perm.refl _', 'ENTS': ', '.join(L.ents()), 'CHAIN': ch,
                 'Q': q, 'N': n, 'T': T}
            w['A1'], w['A2'] = Live.parts(L.d[t][3])
            w['RW'] = f'rw [show ({T}).alloc = {n} from {w["A1"]}]'
            o = {k: (_tm_word(v, w) if isinstance(v, str) else v) for k, v in o.items()}
            if 'perm' not in o and 'front_perm' in tm and n not in (f'{T}.alloc', f'({T}).alloc'):
                o['perm'] = _tm_word(tm['front_perm'], w)     # the block's size restated first
            if 'perm' not in o and pm:
                o['perm'] = pm
            out.append([s[0], s[1], _tm_word(s[2], w), s[3], o] + s[5:])
            continue
        if op == 'call':
            w = {'HEAP': L.heap(), 'ENTS': ', '.join(L.ents())}
            for t in L.order:                  # `{RESTE:t}` the entries behind t, `{CHAINTO:t}` t to the front
                w[f'RESTE:{t}'] = ', '.join(L.ents([x for x in L.order if x != t]))
                w[f'CHAINTO:{t}'] = L.chain([t] + [x for x in L.order if x != t])
            out.append([s[0], s[1], _tm_word(s[2], w), s[3]] +
                       [({k: (_tm_word(v, w) if isinstance(v, str) else v) for k, v in x.items()} if isinstance(x, dict) else x)
                        for x in s[4:]])
            continue
        if op == 'back':
            # ["back", t]: the front move of t's block (a call option "front") undone, its block put back
            # behind the entries it had in front of it (`HP.perm (List.perm_middle …).symm`)
            t = s[1]
            if t not in L.undo:
                die(f'["back", "{t}"]: no call moved {t} to the front')
            prev = L.undo.pop(t)
            before = prev[:prev.index(t)]
            if before:
                pm = f"List.perm_middle (l₁ := [{', '.join(L.ents(before))}])"
                out.append(['tac', _tm_word(tm.get('back', 'have @HP := @HP.perm ({PERM}).symm'), {'PERM': pm})])
            L.order = [x for x in prev if x in L.d]
            continue
        if op in ('tac', 'have'):
            # `{ENTS}`/`{HEAP}`/`{LAY}`: the live entries / the heap list / the layout here
            # `{VALS}`: the live values in temps "names" order (a kind re-statement `κT z … {VALS}`)
            w = {'HEAP': L.heap(), 'ENTS': ', '.join(L.ents()), 'LAY': L.lay(),
                 'VALS': ' '.join(_paren(L.d[t][2]) for t in tm['names'] if t in L.d)}
            out.append([_tm_word(x, w) if isinstance(x, str) else x for x in s])
            continue
        if op == 'jump' and s[1] in lives:
            out.append(_live_jump(tm, a, lives, s, L))
            continue
        if op == 'jump' and seen is not None and a['cuts'].get(s[1], {}).get('live') == 'auto':
            seen.setdefault(s[1], L.copy())
            continue
        out.append(s)
    return out


def _paren(T):
    """A value as an application argument: an atom as is, else parenthesised."""
    return T if (' ' not in T or (T.startswith('(') and T.endswith(')'))) else f'({T})'


def _live_jump(tm, a, lives, s, L):
    c = s[1]
    pr = dict(s[2]) if len(s) > 2 else {}
    tgt = lives[c]
    cu = a['cuts'][c]
    cvars = {n for grp in cu.get('vars', '').split(';') for n in grp.partition(':')[0].split()}
    fields = {f for f, _ in cu.get('prem', [])}
    vs = dict(pr.get('vars', {}))
    for t in tgt.order:
        if t not in L.d:
            die(f'jump to {c}: the temporary {t} is not live here')
        tq, tn, tT, tA = tgt.d[t][:4]
        q, n, T, A = L.d[t][:4]
        for tv, v in ((tq, q), (tn, n), (tT, T)):
            if tv in cvars and tv not in vs and (tv != v or tm.get('jvars_all')):
                vs[tv] = v
        if tA in fields and tA not in pr:
            pr[tA] = A
    if set(L.order) != set(tgt.order):
        die(f'jump to {c}: live {L.order}, the cut {tgt.order}')
    if vs:
        pr['vars'] = vs
    w = {'TGTL': '[' + ', '.join(L.ents(tgt.order)) + '] ++ ' + L.tail, 'ENTS': ', '.join(L.ents()),
         'CHAIN': L.chain(tgt.order)}
    pr = {k: (_tm_word(v, w) if isinstance(v, str) else v) for k, v in pr.items()}
    if not pr.pop('norm', False):
        return [s[0], c, pr] + s[3:]
    if 'st' not in pr and 'jst' in tm:
        pr['st'] = tm['jst']
    if 'hp' not in pr and 'jhp' in tm:
        if L.order == tgt.order:
            pr['hp'] = tm['jhp']
        elif tm.get('perm_style') == 'chain':
            pr['hp'] = _tm_word(tm['jhp_chain'], {'TGT': ' :: '.join(L.ents(tgt.order) + [L.tail]),
                                                  'CHAIN': L.chain(tgt.order)})
        else:
            # the front block moved behind the next k: `(List.perm_middle (l₁ := next k)).symm`
            k = tgt.order.index(L.order[0])
            if [x for x in L.order if x != L.order[0]] != [x for x in tgt.order if x != L.order[0]]:
                die(f'jump to {c}: heap order {L.order} -> {tgt.order}: give "hp"')
            pm = f"(List.perm_middle (l₁ := [{', '.join(L.ents(L.order[1:k + 1]))}])).symm"
            pr['hp'] = _tm_word(tm['jhp_perm'], {'PERM': pm})
    return [s[0], c, pr] + s[3:]


def _resolve_uses(t, blocks, seen):
    """The steps `["use", b]` left inside a block (a block using a block that uses a block) replaced."""
    if isinstance(t, dict):
        return {k: _resolve_uses(v, blocks, seen) for k, v in t.items()}
    if not isinstance(t, list):
        return t
    out = []
    for x in t:
        if isinstance(x, list) and len(x) == 2 and x[0] == 'use' and isinstance(x[1], str):
            if x[1] not in blocks:
                die(f'["use", "{x[1]}"]: no such block')
            if x[1] in seen:
                die(f'["use", "{x[1]}"]: blocks use each other in a cycle ({" > ".join(seen)})')
            out += _resolve_uses(blocks[x[1]], blocks, seen + (x[1],))
        else:
            out.append(_resolve_uses(x, blocks, seen))
    return out


def load_annotation(path):
    """The annotation as the generator reads it: "extends" resolved, then the templates expanded.
      "let"       {W: text | list | dict}: `{W}` in any key or text is replaced (repeatedly: a word's text may
                  name other words); a list element that is exactly "{W}" with W a list is spliced (zero or
                  more elements: lines present in one variant only); a text that is exactly "{W}" with W a
                  list or dict is that value. Let words may be a family's (`"Z{t}": …`).
      "families"  {f: {member: {W: text | list}}}: a key naming `{f}` (a cut, an exit, a block, any dict
                  key) stands for one copy per member, with `{f}` the member's name and its words bound;
                  consecutive keys of one family are copied member by member (G1 L11 M1 G2 L12 M2: the
                  cut order is the `Lab` order).
      "blocks"    {name: [steps]}: a step ["use", name] is replaced by the block's steps (a block is
                  expanded where it is defined: with the let words and, in a family, the member's).
      "extends"   "<base>.asm.json": the base with this file's keys merged on top (dicts key by key, `null`
                  deletes, lists replaced: a variant restates a let word, a family member's word, a list).
                  A base marked "abstract": true is a fragment (no rows of its own), not generated by itself.
      "subst"     {token: token} (with "extends"): after expansion every text is renamed token by token
                  (whole identifiers; see `subst_tree` for the keys), the callee table excepted: an aliasing
                  variant `f(a, b, a)` of `f(a, b, c)` is `{"c": "a", "pc": "pa", "cS": "aS", …}` (saddga)."""
    a, subs = load_raw(path)
    fams = a.pop('families', {})
    # let words may come in families (`"Z{t}"`) and hold `["use", b]` steps (resolved where they are spliced)
    env = expand_tree(a.pop('let', {}), {}, fams, None)
    braw = a.pop('blocks', {})
    blocks = {}
    for k, v in expand_tree(braw, env, fams, None).items():
        blocks[k] = v
    # blocks may use other blocks (one level), and those others (to any depth, no cycles)
    blocks = {k: expand_tree(v, env, fams, blocks) for k, v in blocks.items()}
    blocks = {k: _resolve_uses(v, blocks, (k,)) for k, v in blocks.items()}
    a = expand_tree(a, env, fams, blocks)
    a = from_pass(a)
    a = grow_pass(a)
    a = live_pass(a)
    for sub, keep in subs:
        a = subst_tree(a, sub, keep=keep)
    return vocab_defaults(a)


CTX_WORDS = {'p': 'z.p', 'm': 'z.m', 'ra': 'z.ra', 's0': 'z.s0', 's': 'z.s', 'o': 'z.o', 'v': 'z.v'}
ROWDEF = dict([('ra', 'ra'), ('s0', 's0')] + [(f's{i}', f's.s{i}') for i in range(1, 12)])


def api_fields(api):
    """The fields of `structure P` in Tom/Machine/Api/<api>.lean, in order (None if not there)."""
    f = os.path.join(ROOT, 'Tom/Machine/Api', api + '.lean')
    if not os.path.exists(f):
        return None
    src = open(f).read()
    m = re.search(r'^structure P where\n((?:  .*\n)+)', src, re.M)
    if not m:
        # a contract over another's parameters (`open Tom.Machine.Api.SMpMulDigsA (R P …)`)
        o = re.search(r'^open Tom\.Machine\.Api\.(\w+) \(([^)]*)\)', src, re.M)
        if o and 'P' in o.group(2).split() and o.group(1) != api:
            return api_fields(o.group(1))
        return None
    return [l.split(':')[0].strip() for l in m.group(1).splitlines()
            if ':' in l and not l.strip().startswith('--') and not l.strip().startswith('/-')]


def vocab_defaults(a):
    """ The rows'
    callee-saved words `ra s0 s1 … s11` are `ra s0 s.s1 … s.s11`. An annotation's own entry wins."""
    if a.get('abstract') or 'ctx_vocab' not in a and 'ns' not in a:
        return a
    api = a.get('api') or a['ns'].split('.')[-1]
    cv = a.setdefault('ctx_vocab', {})
    fs = api_fields(api)
    if fs is not None:
        for f in fs:
            cv.setdefault(f, f'z.p.{f}')
        cv.setdefault('hin', f'Api.{api}.hin z.p')
    for w, t in CTX_WORDS.items():
        cv.setdefault(w, t)
    rd = a.setdefault('rowdef', {})
    for w, t in ROWDEF.items():
        rd.setdefault(w, t)
    return contract_defaults(a, api)


STD_CX = [['res', 'Res p'], ['sound', 'Sound (lay p) isW'], ['bund', 'Bundle (lay p) (kind p) m'],
          ['heap', 'AHeap m hin'], ['off', '∀ r, Off (lay p r) hin'], ['ra4', 'ra.toNat % 4 = 0']]
STD_OPENS = ['open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa Vsa.Sim Vsa.Logic',
             'open Tom.Machine Tom.Machine.Code Tom.Machine.Api Tom.Machine.Std Tom.Machine.Api.Alloc Tom.Machine.Api.Heap']
STD_OPEN = 'have hres := hc.res; have hS := hc.sound; have hB := hc.bund; have hoff := hc.off; have hra := hc.ra4'


def contract_defaults(a, api):
    """
      Opens    the machine layer's namespaces first (`LeanRV64DExecutable … Vsa.Logic`, `Tom.Machine … Api.Heap`;
               "opens_std": 1 for the first only, 0 for none);
      cx       absent (default style): the contract's hypotheses `Res p`, `Sound`, `Bundle`, `AHeap`, `Off`, `ra4`;
      prelude  with that context, opened first (`have hres := hc.res; …`; "prelude_open": false to keep it shut);
      post     absent: `∃ x M, At ra (rets) … ∧ Q p x ∧ HPost (lay p) ws .S (out) (site') hin (hout) m M`, `S` the
               written digit region ("Rk" `D …`, the only one) or "post_site";
      exits    the template "keep" (unless the annotation has its own): the `HPost` record of a site kept in place
               (`wit` per written region: `stk` by the bundle, a struct by `hdr`, the site absurd), words `_X`, `_Q`,
               `_WS` (default `_h.dig (nR .S) rfl`)."""
    k = a.get('opens_std', 2)
    if k:
        a['opens'] = STD_OPENS[:k] + list(a.get('opens', []))
    if a.get('style') == 'pre':
        return a
    if 'cx' not in a:
        a['cx'] = copy.deepcopy(STD_CX)
    std = a['cx'] == STD_CX
    if std and a.get('prelude_open', True):
        a['prelude'] = [STD_OPEN] + list(a.get('prelude', []))
    ds = [r for r in a.get('written', []) if a.get('Rk', {}).get(r, '').startswith('D ')]
    site = a.get('post_site') or (ds[0] if len(ds) == 1 else None)
    if 'post' not in a and site:
        A = f'Api.{api}'
        a['post'] = (f'fun cf => ∃ x M, At ra ({A}.rets p x ra) M v.keep o cf ∧ {A}.Q p x ∧ HPost (lay p) ws .{site} '
                     f"({A}.out p x) ({A}.site' p x) hin ({A}.hout p x) m M")
    if site and 'keep' not in a.get('exits', {}):
        wit = ['      | stk => exact ⟨trivial, (hB .stk).2⟩']
        for r in a.get('written', []):
            k = a.get('Rk', {}).get(r, '')
            if k.startswith('S '):
                wit.append(f'      | {r} => exact ⟨Iv.sub_self _, _h.hdr (nR .{r}) rfl⟩')
            elif r == site:
                wit.append(f'      | {r} => exact absurd rfl hrs')
        a.setdefault('exits', {})['keep'] = [
            'obtain ⟨hfr, hh⟩ := _hp.fin _h', 'exact Lbl.exit fun cf hat => ⟨_X, _M, hat.sub rfl rfl, _Q,',
            '  { wit := fun r hr hrs => by', '      cases r with'] + wit + [
            '      | _ => simp [ws] at hr', '    wsite := ⟨Iv.sub_self _, _WS⟩, place := .keep',
            f'    frame := hfr, heap := hh, foot := fun _ h => .inl h, off := hoff .{site} }}⟩']
        a.setdefault('exit_defaults', {})['keep'] = {'_WS': f'_h.dig (nR .{site}) rfl'}
    return a


def region_ref(r, params):
    """ `S`/`D` (one struct) `S p`/`D dp`; `xS`/`xD` `S px`/`D xdp`; a region named like
    a parameter (a cutoff cell `kc`) `D <r>`; otherwise None (state the region list)."""
    if r in ('stk', 'code', 'site'):
        return r
    if r in ('S', 'D'):
        return {'S': 'S p', 'D': 'D dp'}[r]
    if len(r) == 2 and r[1] in 'SD':
        return f'S p{r[0]}' if r[1] == 'S' else f'D {r[0]}dp'
    if r in params:
        return f'D {r}'
    return None


def load_registry():
    """The callee registry: {"<Contract name>": entry} as in an annotation's "callees"; an entry
    without "regions" takes its region type's (`"ctors": {ctor: [region, …]}`) with `region_ref`."""
    p = os.path.join(ROOT, 'experiments/asm/callees.json')
    if not os.path.exists(p):
        return {}
    reg = json.load(open(p))
    out = {}
    for k, v in reg.items():
        if k.startswith('#') or k == 'ctors':
            continue
        out[k] = with_regions(v)
    return out


def with_regions(v):
    """A callee entry without "regions": its region type's list (the registry's "ctors") by `region_ref`."""
    if 'regions' in v:
        return v
    p = os.path.join(ROOT, 'experiments/asm/callees.json')
    ctors = json.load(open(p)).get('ctors', {}) if os.path.exists(p) else {}
    if v['ctor'] not in ctors:
        die(f'callee of region type {v["ctor"]}: give "regions" (or the type\'s list in callees.json "ctors")')
    return dict(v, regions=[[r, region_ref(r, v['params'])] for r in ctors[v['ctor']]])


# ---- callee contracts: parameters (`P` fields in order) and regions (name, ref)
#  ref: 'stk' (callee stack, inside our callees' area), 'code', 'site' (our site),
#       'S <param>' (a struct at that pointer), 'D <param>' (digits at that base)
CALLEES = {
    'mpInitSize': dict(heap=True, ctor='Is', params=['sp', 'pa', 'size', 'H'],
                       regions=[('stk', 'stk'), ('aS', 'S pa'), ('site', 'site'), ('code', 'code')]),
    'mpClear': dict(heap=True, ctor='Un.R', params=['sp', 'pa', 'adp', 'a', 'H'],
                    regions=[('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('code', 'code')]),
    'clamp': dict(heap=False, ctor='Ob', params=['p', 'dp', 'a'],
                  regions=[('S', 'S p'), ('D', 'D dp'), ('code', 'code')]),
    'mpZero': dict(heap=False, ctor='Ob', params=['p', 'dp', 'a'],
                   regions=[('S', 'S p'), ('D', 'D dp'), ('code', 'code')]),
    'mpExch': dict(heap=False, ctor='Two.R', params=['sp', 'pa', 'adp', 'pb', 'bdp', 'a', 'b'],
                   regions=[('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('bS', 'S pb'), ('bD', 'D bdp'),
                            ('code', 'code')]),
}
for _n in ('mulDA', 'addDA'):
    CALLEES[_n] = dict(heap=False, ctor='Un.R', params=['sp', 'pa', 'adp', 'a', 'b'],
                       regions=[('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('code', 'code')])
CALLEES['mpCopy'] = dict(heap=False, ctor='Two.R', params=['sp', 'pa', 'adp', 'pb', 'bdp', 'a', 'b'],
                         regions=[('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('bS', 'S pb'), ('bD', 'D bdp'),
                                  ('code', 'code')])
CALLEES['mpLshd'] = dict(heap=False, ctor='Un.R', params=['sp', 'pa', 'adp', 'a', 'k'],
                         regions=[('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('code', 'code')])
for _n in ('divdi3', 'moddi3'):
    CALLEES[_n] = dict(heap=False, ctor='Cd', params=['n', 'd'], regions=[('code', 'code')])
CALLEES['mpInit'] = dict(heap=True, ctor='Is', params=['sp', 'pa', 'H'],
                         regions=[('stk', 'stk'), ('aS', 'S pa'), ('site', 'site'), ('code', 'code')])
CALLEES['cntBits'] = dict(heap=False, ctor='Ob', params=['p', 'dp', 'a'],
                          regions=[('S', 'S p'), ('D', 'D dp'), ('code', 'code')])
CALLEES['mp2expt'] = dict(heap=False, ctor='Un.R', params=['sp', 'pa', 'adp', 'a', 'k'],
                          regions=[('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('code', 'code')])
CALLEES['sSubA'] = dict(heap=False, ctor='BinA.R', params=['sp', 'pa', 'adp', 'pb', 'bdp', 'a', 'b'],
                        regions=[('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('bS', 'S pb'), ('bD', 'D bdp'),
                                 ('code', 'code')])
_BIN = [('stk', 'stk'), ('cS', 'S pc'), ('cD', 'D cdp'), ('aS', 'S pa'), ('aD', 'D adp'), ('bS', 'S pb'),
        ('bD', 'D bdp'), ('code', 'code')]
CALLEES['sSubD'] = dict(heap=False, ctor='Bin.R', params=['sp', 'pa', 'adp', 'pb', 'bdp', 'pc', 'cdp', 'a', 'b', 'c'],
                        regions=_BIN)
CALLEES['mulFast'] = dict(heap=False, ctor='Bin.R',
                          params=['sp', 'pa', 'adp', 'pb', 'bdp', 'pc', 'cdp', 'dg', 'a', 'b', 'c'], regions=_BIN)
_UN = [('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('code', 'code')]
_TWO = [('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('bS', 'S pb'), ('bD', 'D bdp'), ('code', 'code')]
CALLEES['cntLsbG'] = dict(heap=False, ctor='Ob', params=['p', 'dp', 'a'],
                          regions=[('S', 'S p'), ('D', 'D dp'), ('code', 'code')])
CALLEES['div2dG'] = dict(heap=False, ctor='Un.R', params=['sp', 'pa', 'adp', 'a', 'b'], regions=_UN)
CALLEES['mul2dG'] = dict(heap=False, ctor='Two.R', params=['sp', 'pa', 'adp', 'pc', 'cdp', 'a', 'b', 'c'],
                         regions=[('stk', 'stk'), ('aS', 'S pa'), ('aD', 'D adp'), ('bS', 'S pc'), ('bD', 'D cdp'),
                                  ('code', 'code')])
CALLEES['mpAbsG'] = dict(heap=False, ctor='Two.R', params=['sp', 'pa', 'adp', 'pb', 'bdp', 'a', 'b'], regions=_TWO)
CALLEES['sSubCA'] = dict(heap=False, ctor='BinA.R', params=['sp', 'pa', 'adp', 'pb', 'bdp', 'a', 'b'], regions=_TWO)
CALLEES['cmpMagG'] = dict(heap=False, ctor='Cm', params=['pa', 'adp', 'pb', 'bdp', 'a', 'b'],
                          regions=[('aS', 'S pa'), ('aD', 'D adp'), ('bS', 'S pb'), ('bD', 'D bdp'), ('code', 'code')])
CALLEES['mpClearNullG'] = dict(heap=False, ctor='CnG', params=['pa'], regions=[('S', 'S pa'), ('code', 'code')])
CALLEES['mpInitCopyG'] = dict(heap=True, ctor='Ic', params=['sp', 'pa', 'pb', 'bdp', 'b', 'H'],
                              regions=[('stk', 'stk'), ('aS', 'S pa'), ('bS', 'S pb'), ('bD', 'D bdp'), ('site', 'site'),
                                       ('code', 'code')])
_ENTRY_R6C = ({'cntLsbG': 0x80005054, 'div2dG': 0x8000520c, 'mul2dG': 0x80001758, 'mpAbsG': 0x800005cc,
              'sSubCA': 0x80004564, 'cmpMagG': 0x80000764, 'mpClearNullG': 0x80005018, 'mpInitCopyG': 0x8000134c})

ENTRY = {'mpInit': 0x800012fc, 'cntBits': 0x800050f0, 'mp2expt': 0x800076d4, 'sSubA': 0x80004564,
         'sSubD': 0x80004564, 'mulFast': 0x800042f0,
         'mpCopy': 0x800007e0, 'mpLshd': 0x800015b8, 'divdi3': 0x800175a4, 'moddi3': 0x80017628, 'mpZero': 0x80002178, 'mulDA': 0x800019fc, 'addDA': 0x80004e30,'mpInitSize': 0x80001498, 'mpClear': 0x80005018, 'clamp': 0x80004fd8, 'mpExch': 0x80000e60,
         'muldi3': 0x80017540}
ENTRY.update(_ENTRY_R6C)


def _multi8_callees():
    """ Regions per argument
    `i`: the struct `st ⟨i, _⟩` and the digits `dg ⟨i, _⟩` (the callee's sites, `"sites"`); per stack
    argument `j < k - 7` (arguments 8 on, the `NULL` included) its word `sa ⟨j, _⟩`. Refs:
    'S ps[i]' (the i-th element of the list parameter `ps`), 'S xs[i]#0' / 'D xs[i]#1' (a component
    of the i-th tuple of `xs`), 'site i' (the call option "sites": our i-th site), 'sarg j' (the call
    option "sargs": our region holding the j-th stack word). The last parameter `m0` is the caller's
    memory the stack words are read from (its snapshot of that region; any memory for k ≤ 7)."""
    out, ent = {}, {}
    for k in range(2, 16):
        st = [f'st ⟨{i}, _⟩' for i in range(k)]
        dg = [f'dg ⟨{i}, _⟩' for i in range(k)]
        sa = [(f'sa ⟨{j}, _⟩', f'sarg {j}') for j in range(max(0, k - 7))]
        out[f'mpInitMulti{k}'] = dict(heap=True, heapN=True, ctor=f'Std.MR {k}', params=['sp', 'ps', 'H', 'm0'],
                                      regions=[('stk', 'stk'), ('code', 'code')] +
                                      [(st[i], f'S ps[{i}]') for i in range(k)] + [(dg[i], f'site {i}') for i in range(k)] + sa,
                                      sites=dg)
        out[f'mpClearMulti{k}'] = dict(heap=True, heapN=True, ctor=f'Std.MR {k}', params=['sp', 'xs', 'H', 'm0'],
                                       regions=[('stk', 'stk'), ('code', 'code')] +
                                       [(st[i], f'S xs[{i}]#0') for i in range(k)] +
                                       [(dg[i], f'D xs[{i}]#1') for i in range(k)] + sa,
                                       sites=dg)
        ent[f'mpInitMulti{k}'] = 0x800013c8
        ent[f'mpClearMulti{k}'] = 0x80000698
    return out, ent


_M8C, _M8E = _multi8_callees()
CALLEES.update(_M8C)
ENTRY.update(_M8E)


# ---- segment lemmas written in Lean: parsed from their statements
def top_split(s):
    """Split on spaces outside brackets."""
    out, cur, d = [], '', 0
    for ch in s:
        if ch == ' ' and d == 0:
            if cur:
                out.append(cur)
            cur = ''
            continue
        d += ch in '([{⟨'
        d -= ch in ')]}⟩'
        cur += ch
    if cur:
        out.append(cur)
    return out


def unparen(s):
    s = s.strip()
    while s.startswith('(') and s.endswith(')') and GR.balanced(s[1:-1]):
        s = s[1:-1].strip()
    return s


def parse_binders(s):
    """`(a b : T) {c : U} …` -> [(name, type)] (explicit only)."""
    out = []
    for tok in top_split(s):
        if not tok.startswith('('):
            continue
        body = tok[1:-1]
        names, _, ty = body.partition(' : ')
        for n in names.split():
            out.append((n, ty.strip()))
    return out


def parse_lean_segs(path):
    txt = open(os.path.join(ROOT, path)).read()
    defs = {}
    for m in re.finditer(r'^def (\w+) (.*?) : GRegs :=', txt, re.M):
        defs[m.group(1)] = [n for n, _ in parse_binders(m.group(2))]
    facts = set(re.findall(r'^structure (\w+)', txt, re.M))
    segs = {}
    for m in re.finditer(r'^theorem (\w+)_step (.*?) :\s*\n\s*Triple \(At (\S+) (.*?) (\w+) (\S+) outp\)\s*\n\s*\(At (\S+) (.*?)\) := by',
                         txt, re.M | re.S):
        nm, binders, pc0, pre, mem, keep, pc1, rest = m.groups()
        rest = ' '.join(rest.split())
        toks = top_split(rest)
        post, postmem = toks[0], toks[1]
        pm = unparen(postmem)
        log = None
        if pm.startswith('writeLog '):
            log = unparen(pm[len('writeLog '):].split(' ', 1)[1])
        pre_t = top_split(unparen(pre))
        post_t = top_split(unparen(post))
        segs[nm] = dict(params=parse_binders(' '.join(binders.split())), pre=(pre_t[0], pre_t[1:]),
                        post=(post_t[0], post_t[1:]), log=log, pc0=int(pc0.split('#')[0], 16) if pc0.startswith('0x') else None,
                        end=int(pc1.split('#')[0], 16) if pc1.startswith('0x') else 'ret', mem=mem)
    return segs, defs, facts


def norm(s):
    return re.sub(r'\s+', '', s)


class Gen:
    def __init__(self, path):
        self.path = path
        self.a = load_annotation(path)
        a = self.a
        if a.get('abstract'):
            print(f'gen_asm: {os.path.relpath(path, ROOT)} is a fragment ("abstract"): nothing to generate')
            sys.exit(0)
        self.lsegs = None
        if a.get('segs_lean'):
            self.lsegs, self.ldefs, self.lfacts = parse_lean_segs(a['segs_lean'])
            self.ann = {'segs': [], 'bv': '', 'nat': ''}
            self.F = None
            self.rows = {}
            self.W = GR.load_disasm()
        else:
            self.rows_path = os.path.join(ROOT, a['rows'])
            self.ann = GR.load_rows(self.rows_path)
            self.F = GR.Fn(self.ann)
            GR.check_names(self.ann)
            self.rows = {r['n']: r for r in self.ann['segs']}
            self.W = self.F.W
        self.out = []
        # callee table: the fixed entries plus the annotation's `callees`
        self.callees, self.entry = dict(CALLEES), dict(ENTRY)
        # experiments/asm/callees.json; an annotation's own entry wins
        reg = [(k, v) for k, v in load_registry().items() if k not in CALLEES]
        for name, c in reg + [(k, with_regions(v)) for k, v in a.get('callees', {}).items()]:
            self.callees[name] = dict(heap=c.get('heap', False), ctor=c['ctor'], params=c['params'],
                                      regions=[tuple(r) for r in c['regions']], site=c.get('site'))
            self.entry[name] = int(c['entry'], 16)
        self.ctx = a['ctx_vocab']
        a.setdefault('api', a['ns'].split('.')[-1])           # vocabulary -> Lean (context)
        self._sargs = None
        self.nh = 0
        for c, cu in a['cuts'].items():
            if isinstance(cu.get('kinds'), str):
                cu['kinds'] = a['kindsets'][cu['kinds'][1:]]
            if isinstance(cu.get('state'), str):
                cu['state'] = [[f, t.replace('κ@', 'κ' + c)] for f, t in a['statesets'][cu['state'][1:]]]
        self.rowinfo = {}
        for n in self.rows:
            self.rowinfo[n] = self.row_meta(n)
        self.ctx = a['ctx_vocab']

    # ---------------- rows
    def row_meta(self, nm):
        F, row = self.F, self.rows[nm]
        if row.get('alu'):
            pre_t, _ = F.apply(row['pre'], 'regs')
            post_t, _ = F.apply(row['post'], 'regs')
            hyps = []
            for h in row.get('h', []):
                t, head = F.apply(h, 'facts')
                hyps.append((t, head, h))
            ps = F.params([pre_t, post_t] + [t for t, _, _ in hyps])
            at = row['at'].split()[0]
            pc0 = GR.pc_of(at)
            return dict(bvs=[x for x in ps if x in F.bv], nats=[x for x in ps if x in F.nat], hyps=hyps, log=[],
                        pre=row['pre'], post=row['post'], end=pc0 + 4, pc0=pc0, alu=True)
        blocks, end, path_ = F.walk(row)
        pre = F.reg_values(row['pre'])
        lds, log, keys = F.evaluate(row, pre, path_)
        pre_t, _ = F.apply(row['pre'], 'regs')
        post_t, _ = F.apply(row['post'], 'regs')
        hyps = []
        for h in self.ann.get('h0', []) + row.get('h', []):
            t, head = F.apply(h, 'facts')
            hyps.append((t, head, h))
        post = F.reg_values(row['post'])
        if end == 'jr':
            pc1 = F.pin(post[1])
            hyps.append((f'{GR.paren(pc1)}.toNat % 4 = 0', None, 'hra'))
        else:
            pc1 = f'0x{end:x}#64'
        logt = '[' + ', '.join(log) + ']'
        texts = [pre_t, post_t, logt, pc1] + [t for t, _, _ in hyps] + lds
        ps = F.params(texts)
        bvs = [x for x in ps if x in F.bv]
        nats = [x for x in ps if x in F.nat]
        at = row['at'].split()[0]
        pc0 = GR.pc_of(at)
        return dict(bvs=bvs, nats=nats, hyps=hyps, log=log, pre=row['pre'], post=row['post'],
                    end=end, pc0=pc0)

    def list_params(self, name):
        if self.lsegs is not None:
            return self.ldefs[name]
        return self.F.reg_params(name)

    # ---------------- vocabulary
    BINDER = re.compile(r"(?:\bfun|λ|∀|∃|\bintro)\s+((?:[(]?[A-Za-z_][\w']*\s*)+?)(?=:|=>|,|$|\)|;)")

    def lean(self, s, env):
        """Annotation text -> Lean text: identifiers by `env` (then the context). Not
        replaced: a named argument or field (`(x := …)`, `{ x := …`, `, x := …`), a name the text binds itself
        (`fun x y =>`, `∀ x,`, `∃ x,`, `intro x y`): those are Lean's, not the vocabulary's."""
        st = getattr(self, '_st', None)
        if st is not None and '@' in s:
            # the current state's names: `@H` the `St` hypothesis, `@M` the memory, `@HP` the
            # heap checkpoint (a raw step rebinding them reuses the names: `fun x @M hq @H => ?_`)
            s = re.sub(r"@(HP|H|M)(?![\w'])", lambda m: {'HP': st.get('hp', 'hp'), 'H': st['h'], 'M': st['M']}[m.group(1)], s)
        bound = set()
        for m in self.BINDER.finditer(s):
            bound.update(re.findall(r"[A-Za-z_][\w']*", m.group(1)))
        def rep(m):
            t = m.group(1)
            if t in bound or (re.match(r"\s*:=", s[m.end():]) and re.search(r"[({,]\s*$", s[:m.start()])):
                return t
            if t in env:
                return GR.paren(env[t])
            if t in self.ctx:
                return GR.paren(self.ctx[t])
            return t
        return re.sub(r"(?<![\w.'])([A-Za-z_][\w']*)(?![\w'])", rep, s)

    def fresh(self, base='h'):
        self.nh += 1
        return f'{base}{self.nh}'

    # ---------------- regions
    def region_names(self):
        """Our region names as Lean terms, with refs."""
        a = self.a
        nest = len(a['frame'])
        names = self.sites() + [p[0] for p in a['frame']]
        return names

    def sites(self):
        """The allocation sites' names (`"site"`: a name or a list), outermost first."""
        st = self.a.get('site')
        return [] if not st else [st] if isinstance(st, str) else list(st)

    def so(self):
        return len(self.sites())

    def emit_region(self):
        """The region type of a style-"pre" assembly with heap temporaries (it was a per-function
        block in `Fn/<F>G5K.lean`): `R` (the contract's regions, then the temporaries' digit arrays), `layG`
        (the temporaries at `Iv.nil`), `kindG`, the written flags, `emb` (the temporaries as `Site.lay`s
        over the contract's names), one `layG_<r>` equation per region (`rfl`; a deep stack's literal arm
        breaks `simp [layG]`), `soundG` (`Site.soundN` over `Bundle.lo`) and `GPre` (the contract's
        hypotheses and the sites' soundness, then the named premises). "eqsC" {name: {"lay", "regions"}}:
        a layout's arm equations `name_<r>` (also without temporaries: `Api.MpSqrS.lay`'s deep stack)."""
        a = self.a
        g = a.get('region')
        if not g:
            return
        if 'temps' not in g:               # only the layout's arm equations ("eqsC")
            lay = g['lay']
            for nm, cfg in g.get('eqsC', {}).items():
                self.out += [f'theorem {nm}_{r} (p : P) : {cfg["lay"]} .{r} = '
                             f'{lay[r] if r in lay else lay["_"] + " ." + r} := rfl' for r in cfg['regions']] + ['']
            return
        R, T = a['R'], g['temps']
        C = [r for r in R if r not in T]
        api = g['api']
        n = len(T)
        lay = g['lay']
        def arm(r):
            if isinstance(lay, dict) and r in lay:
                return lay[r]
            if r == 'code':
                return 'textIv'
            if isinstance(lay, dict) and '_' not in lay:
                die(f'region: no layout arm for {r}')
            return f'{lay["_"] if isinstance(lay, dict) else lay} .{r}'
        wr = a.get('isW', 'isW')
        L = ['/-- The contract\'s regions and the temporaries\' digit arrays. -/',
             f'inductive R | {" | ".join(C)}', f'  | {" | ".join(T)}', '  deriving DecidableEq', '',
             'def layG (p : P) : R → Iv']
        L += [f'  | .{r} => {arm(r)}' for r in C] + [f'  | {" | ".join("." + t for t in T)} => Iv.nil', '']
        if g.get('eqs', True):
            L += [f'theorem layG_{r} (p : P) : layG p .{r} = {arm(r)} := rfl' for r in C]
            L += [f'theorem layG_{t} (p : P) : layG p .{t} = Iv.nil := rfl' for t in T] + ['']
        kd = g.get('kind', 'kind p')
        L += ['def kindG (p : P) (_ : Mem) : R → Kind']
        L += [f'  | .{r} => {".ram" if r == "stk" else ".code" if r == "code" else f"{kd} .{r}"}' for r in C]
        L += [f'  | {" | ".join("." + t for t in T)} => .ram', '']
        L += [f'def {wr} : R → Bool', f'  | {" | ".join("." + r for r in a["written"])} => true', '  | _ => false', '']
        ty = f'{api}.R'
        for _ in range(n):
            ty = f'Option ({ty})'
        L += ['/-- The temporaries first, as `Site.lay`s over the contract\'s layout. -/', f'def emb : R → {ty}']
        L += [f'  | .{t} => {self.some_pat(i)}' for i, t in enumerate(T)]
        L += [f'  | .{r} => {self.some_pat(n, "." + r)}' for r in C] + ['']
        gp = g['gpre']
        cl, cw, ck, ch = gp['lay'], gp['isW'], gp['kind'], gp['hin']
        L += ['/-- The temporaries\' sites are sound beside the contract\'s regions. -/',
              f'theorem soundG {{p : P}} {{m : Mem}} (hS : Sound ({cl} p) {cw}) (hB : Bundle ({cl} p) ({ck} p) m) :',
              f'    Sound (layG p) {wr} :=',
              f'  Site.soundN {n} hS (Bundle.lo hB (by bundle_exact)) emb [{", ".join("." + r for r in R)}]',
              '    (by intro r; cases r <;> simp) (by intro r; cases r <;> exact Iv.sub_self _)', '',
              '/-- The contract\'s hypotheses, the sites\' soundness and the named premises. -/',
              'structure GPre (p : P) (m : Mem) (ra : BitVec 64) : Prop where',
              '  ra4 : ra.toNat % 4 = 0', f'  res : {gp["res"]}', f'  sound : Sound ({cl} p) {cw}',
              f'  bund : Bundle ({cl} p) ({ck} p) m', f'  heap : AHeap m ({ch} p)', f'  off : ∀ r, Off ({cl} p r) ({ch} p)',
              f'  lay : Sound (layG p) {wr}']
        L += [f'  {f} : {t}' for f, t in gp.get('extra', [])] + ['']
        for nm, cfg in g.get('eqsC', {}).items():
            L += [f'theorem {nm}_{r} (p : P) : {cfg["lay"]} .{r} = {arm(r)} := rfl' for r in cfg['regions']]
            L.append('')
        self.out += L

    def emit_static(self):
        a = self.a
        R = a['R']
        k = len(a['frame'])
        so = self.so()
        self.emit_region()
        L = list(a.get('head_defs', []))
        if L:
            L.append('')
        Y = 'R'
        for _ in range(k):
            Y = f'Option ({Y})' if Y != 'R' else 'Option R'
        L.append(f'instance : Names R := ⟨[{", ".join("." + r for r in R)}]⟩')
        L.append('')
        L.append(f'abbrev Y := {Y}')
        X = 'Y'
        for _ in range(so):
            X = f'Option ({X})' if X != 'Y' else 'Option Y'
        L.append(f'abbrev X := {X}')
        # Split chain
        lay = a.get('lay_t', 'lay') + ' p'
        kd = a.get('kind_t', 'kind p')
        wr = a.get('isW', 'isW')
        stk = '.stk'
        for i, (nm, sz) in enumerate(a['frame']):
            lay = f'Split.lay ({lay}) {stk} {sz}'
            kd = f'Split.kind ({kd}) m' if i or not a.get('style') == 'pre' else f'Split.kind ({kd}) m'
            wr = f'Split.wr ({wr})'
            stk = f'(some {stk})'
        L.append(f'/-- The contract\'s layout with the stack cut into the own frame\'s pieces and the callees\' area. -/')
        L.append(f'def ρ3 (p : P) : Y → Iv := {lay}')
        L.append(f'def w3 : Y → Bool := {wr}')
        L.append(f'def κ3 (p : P) (m : Mem) : Y → Kind := {kd}')
        for i, sn in enumerate(self.sites()):
            L.append(f'abbrev {sn} : X := {self.some_pat(i)}')
        for i, (nm, sz) in enumerate(a['frame']):
            L.append(f'abbrev {nm} : X := {self.some_pat(k - 1 - i + so)}')
        L.append(f'abbrev nR (r : R) : X := {self.some_pat(k + so, "r")}')
        ws = self.sites() + [p[0] for p in a['frame']] + [f'nR .{r}' for r in a['written']]
        L.append(f'abbrev WX : List X := [{", ".join(ws)}]')
        L.append('/-- The contract region a piece lies in. -/')
        L.append('def proj : Y → R')
        pieces = ['none'] + [self.some_pat(i) for i in range(1, k)]
        L.append(f'  | {" | ".join(pieces)} => .stk')
        L.append(f'  | {self.some_pat(k, "r")} => r')
        if so:
            r_, w_, k_ = 'ρ3 p', 'w3', 'κ3 p m'
            for _ in range(so):
                r_, w_, k_ = f'Site.lay ({r_})', f'Site.wr {w_}' if w_ == 'w3' else f'Site.wr ({w_})', f'Site.kind ({k_})'
            L.append(f'abbrev ρX (p : P) : X → Iv := {r_}')
            L.append(f'abbrev wX : X → Bool := {w_}')
            L.append(f'abbrev κX (p : P) (m : Mem) : X → Kind := {k_}')
        else:
            L.append('abbrev ρX (p : P) : X → Iv := ρ3 p')
            L.append('abbrev wX : X → Bool := w3')
            L.append('abbrev κX (p : P) (m : Mem) : X → Kind := κ3 p m')
        L.append('')
        L.append(f'theorem cd {{ρ : X → Iv}} {{W : List X}} {{κ : X → Kind}} {{m M : Mem}} (h : St ρ wX W κ m M)')
        L.append(f'    (hk : κ (nR .code) = .code := by rfl) : CodeAt M {a["code"]}Base {a["code"]}Code :=')
        L.append(f'  (h.img (nR .code) hk).{a["code"]}')
        L.append('')
        self.out += L

    def some_pat(self, i, inner='none'):
        t = inner
        for _ in range(i):
            t = f'some ({t})' if (t not in ('none', 'r')) else f'some {t}'
        return t

    def rcases_pat(self):
        k = len(self.a['frame'])
        return ' | '.join(['_'] * (k + self.so()) + ['r'])

    # ---------------- the cut machinery
    def emit_cuts(self):
        a = self.a
        L = []
        cuts = a['cuts']
        L.append('/-- The fixed data of a run. -/')
        L.append('structure Fx where')
        for f, t in a.get('fx', [['p', 'P'], ['m', 'Mem'], ['tp', 'BitVec 64'], ['s0', 'BitVec 64'],
                                 ['s', 'Vsa.Sim.SRegs'], ['o', 'Array String'], ['ra', 'BitVec 64']]):
            L.append(f'  {f} : {t}')
        L.append('')
        if 'fx' not in a:
            L.append(f'def Fx.v (z : Fx) : Abi := ⟨BitVec.ofNat 64 z.p.sp, {a.get("gp", "gpV")}, z.tp, z.s0, z.s⟩')
            L.append('')
        L.append('/-- What the context gives every edge. -/')
        L.append('structure Cx (z : Fx) : Prop where')
        for f, t in a['cx']:
            L.append(f'  {f} : {self.lean(t, {})}')
        L.append('')
        for d in a.get('defs', []):
            L.append(d)
            L.append('')
        if a.get('style') == 'pre':
            L += self.emit_entry_pre()
        # snapshots: inlined through the vocabulary
        for nm, spec in a.get('snaps', {}).items():
            self.ctx[nm] = self.snap(spec)
        L.append('inductive Lab | ' + ' | '.join(cuts.keys()))
        L.append('')
        for c, cu in cuts.items():
            vs = self.cut_vars(cu)
            L.append(f'structure X{c} where')
            if not vs:
                L.append('  u : Unit := ()')
            for v, t in vs:
                L.append(f'  {v} : {t}')
            L.append('')
            xr = self.rec(cu)
            env = {v: f'{xr}.{v}' for v, _ in vs}
            if cu.get('kinds'):
                L.append(f'def κ{c} (z : Fx) ({xr} : X{c}) : X → Kind')
                for r, k in cu['kinds'].items():
                    L.append(f'  | {self.region_pat(r)} => {self.lean(k, env)}')
                L.append(f'  | {self.some_pat(len(a["frame"]) + self.so(), "r")} => {a.get("kind_rest", "kind z.p r")}')
                L.append('')
            L.append(f'structure P{c} (z : Fx) ({xr} : X{c}) : Prop where')
            for f, t in self.cut_fields(c, cu):
                # `κ… z x`: the cut's record, whatever the cut's variables are called
                t = re.sub(r"(κ[\w@]*) z x(?![\w'])", lambda m: f'{m.group(1)} z \u27eaREC\u27eb', t)
                L.append(f'  {f} : {self.lean(t, env).replace(chr(0x27ea) + "REC" + chr(0x27eb), xr)}')
            L.append('')
            if vs and self.a.get('jump_mk', True):
                # the premise from the cut's variables: a jump's field proofs see the values, not
                # projections of the record (`⟨…⟩.i`, which `omega` takes for atoms)
                venv = {v: v for v, _ in vs}
                names = {v for v, _ in vs} | {'z'}
                rec = '⟨' + ', '.join(v for v, _ in vs) + '⟩'
                bs = ' '.join(f'({v} : {t})' for v, t in vs)
                fs, fn = [], []
                for f, t in self.cut_fields(c, cu):
                    t = re.sub(r"(κ[\w@]*) z x(?![\w'])", lambda m: f'{m.group(1)} z \u27eaREC\u27eb', t)
                    b = f
                    while b in names:
                        b += "'"
                    names.add(b)
                    fn.append(b)
                    fs.append(f'({b} : {self.lean(t, venv).replace(chr(0x27ea) + "REC" + chr(0x27eb), f"({rec} : X{c})")})')
                L.append(f'theorem P{c}.mk\' (z : Fx) {bs}')
                L.append(f'    {" ".join(fs)} :')
                L.append(f'    P{c} z {rec} := ⟨{", ".join(fn)}⟩')
                L.append('')
        L.append('/-- The cuts. -/')
        L.append('def LL (z : Fx) : Lab → Lbl')
        for c, cu in cuts.items():
            xr = self.rec(cu)
            env = {v: f'{xr}.{v}' for v, _ in self.cut_vars(cu)}
            mu = self.lean(cu['mu'], env)
            L.append(f'  | .{c} => ⟨X{c}, fun {xr} => ({mu}), P{c} z, fun {xr} => At {self.pc(cu["pc"])} ({self.cut_regs(cu, env)}) {env.get("M", "z.m")} {a.get("keep", "(kp z.v)")} z.o⟩')
        L.append('')
        L.append('/-- The contract\'s post. -/')
        L.append(f'def Post (z : Fx) : Vsa.Machine.Config → Prop := {self.lean(a["post"], {})}')
        L.append('')
        L.append('macro "dec" : tactic => `(tactic| (simp only [Lt3, LL, true_and, and_true, true_or, or_true]; try omega))')
        if a.get('fam'):
            L.append(f'macro "krfl" : tactic => `(tactic| (intro r; rcases r with {self.rcases_pat()} <;> (try cases r) <;> rfl))')
        else:
            L.append(f'macro "krfl" : tactic => `(tactic| (intro r; rcases r with {self.rcases_pat()} <;> first | rfl | (cases r <;> rfl)))')
        L.append('')
        self.out += L

    def snap(self, spec):
        m = re.match(r'^W\((\w+),\s*(\w+)(?:,\s*(.*))?\)$', spec)
        if not m:
            return self.lean(spec, {})
        base, row, subs = m.group(1), m.group(2), m.group(3)
        sub = {}
        if subs:
            for part in GR.split_top(subs, ','):
                x, _, e = part.partition(':=')
                sub[x.strip()] = e.strip()
        base_t = 'z.m' if base == 'm' else GR.paren(self.ctx[base])
        if self.lsegs is not None:
            info = self.lsegs[row]
            args = {n: self.lean(sub.get(n, self.a['rowdef'].get(n, n)), {}) for n, t in info['params']
                    if t in ('Nat', 'BitVec 64')}
            if norm(info['log']) == '[]':
                return base_t
            return f'writeLog {base_t} {GR.paren(GR.substitute(info["log"], args))}'
        info = self.rowinfo[row]
        args = {}
        for p in info['bvs'] + info['nats']:
            args[p] = self.lean(sub.get(p, self.a['rowdef'].get(p, p)), {})
        if not info['log']:
            return base_t                   # `writeLog m []` is `m` (no `rfl` through writeLog)
        log = '[' + ', '.join(GR.substitute(e, args) for e in info['log']) + ']'
        return f'writeLog {base_t} {log}'

    def region_pat(self, r):
        a = self.a
        if r in self.sites():
            return self.some_pat(self.sites().index(r))
        for i, (nm, _) in enumerate(a['frame']):
            if nm == r:
                return self.some_pat(len(a['frame']) - 1 - i + self.so())
        m = re.match(r'^nR \.(\w+)$', r)
        if m:
            return self.some_pat(len(a['frame']) + self.so(), '.' + m.group(1))
        die(f'region {r}?')

    def nonscalar(self):
        """The fixed data's fields that are not `Nat`/`BitVec 64` (`z.p`, `z.m`, …)."""
        fx = self.a.get('fx', [['p', 'P'], ['m', 'Mem'], ['tp', 'BitVec 64'], ['s0', 'BitVec 64'],
                                ['s', 'Vsa.Sim.SRegs'], ['o', 'Array String'], ['ra', 'BitVec 64']])
        return {f'z.{f}' for f, t in fx if t not in ('Nat', 'BitVec 64')}

    def rec(self, cu):
        """The name of a cut's record in its definitions: `x`, unless a variable is so named."""
        names = {v for v, _ in self.cut_vars(cu)}
        for bad in ('z', 'xc', 'hc'):
            if bad in names:
                die(f'cut variable {bad!r} clashes with the generated binder of that name')
        for xr in ('x', 'x_', 'x__'):
            if xr not in names and xr not in self.ctx:
                return xr
        die('no name for the cut record')

    def cut_vars(self, cu):
        out = []
        for grp in cu.get('vars', '').split(';'):
            grp = grp.strip()
            if not grp:
                continue
            names, _, ty = grp.partition(':')
            for n in names.split():
                out.append((n, ty.strip()))
        return out

    def cut_fields(self, c, cu):
        out = []
        for f, t in cu.get('state', []):
            out.append((f, t))
        for f, t in cu.get('prem', []):
            out.append((f, t))
        return out

    def pc(self, s):
        v = GR.pc_of(s)
        return f'0x{v:x}#64'

    def cut_regs(self, cu, env):
        name = cu['regs']
        over = cu.get('regs_over', {})
        ps = self.list_params(name)
        args = []
        for p in ps:
            if p in over:
                args.append(GR.paren(self.lean(over[p], env)))
            elif p in env:
                args.append(env[p])
            else:
                args.append(GR.paren(self.lean(self.a['rowdef'].get(p, p), env)))
        return ' '.join([name] + args)

    # ---------------- edges
    def emit_edges(self):
        a = self.a
        for c, cu in a['cuts'].items():
            self.nh = 0
            vs = self.cut_vars(cu)
            env = {v: f'xc.{v}' for v, _ in vs}
            L = []
            L.append(f'theorem e{c} (z : Fx) (hc : Cx z) (xc : X{c}) : Lbl.Edge (LL z) (Post z) .{c} xc := by')
            fields = [f for f, _ in self.cut_fields(c, cu)]
            L.append(f'  refine Lbl.enter fun ⟨{", ".join(fields)}⟩ => ?_')
            L.append(f'  show Triple (At _ _ _ _ _) _')
            for line in a['prelude']:
                L.append('  ' + self.lean(line, env))
            if 'pr' in fields and a.get('hdig', True):
                L.append('  have hdig := pr.dig')
            if 'fr' in fields and a.get('hdig', True):
                L.append('  have := fr.lo; have := fr.hi')
            for line in cu.get('prelude', []):
                L.append('  ' + self.lean(line, env))
            # region pairs whose disjointness the edge's facts need, hoisted once (`DisjH`)
            for i, (r, t) in enumerate(self.a.get('disj', []) + cu.get('disj', [])):
                L.append(f'  disj_hoist hdj{i + 1} st {self.reg(r)} {self.reg(t)}')
            # register state: the cut's list, by row parameter names
            regs = {}
            over = cu.get('regs_over', {})
            for p in self.list_params(cu['regs']):
                if p in over:
                    regs[p] = self.lean(over[p], env)
                elif p in env:
                    regs[p] = env[p]
                else:
                    regs[p] = self.lean(self.a['rowdef'].get(p, p), env)
            st = dict(h='st', hp='hp', cut=c, M=env.get('M', 'z.m'), regs=regs, env=env, pc=int(self.pc(cu['pc'])[2:-3], 16),
                      cur=cu['regs'], mu=f'(LL z .{c}).μ xc', locals=fields, snap=self.snaps_at(cu, env),
                      lay=self.lay_layers(cu))
            self.budget(c, cu['edge'])
            self.steps(cu['edge'], st, L, 1)
            self._st = None
            self.out += L
            self.out.append('')
            self.edge_blocks.append((c, L + ['']))

    def steps(self, steps, st, L, ind):
        sp = '  ' * ind
        for i, s in enumerate(steps):
            self._st = st
            op = s[0]
            if op == 'seg':
                self.seg(s, st, L, sp)
            elif op == 'have':
                L.append(f'{sp}have {self.lean(s[1], st["env"])} := {self.lean(s[2], st["env"])}')
                st.setdefault('named', set()).add(re.match(r"\s*([^\s:]+)", s[1]).group(1))
            elif op == 'tac':
                txt = s[1]
                # step itself), the current one from then on (a later `cases` cannot resurrect a shadowed one)
                fresh_new = {}
                def fr2(m_):
                    k = m_.group(1)
                    if k not in fresh_new:
                        fresh_new[k] = self.fresh({'HP': 'hp', 'H': 'h', 'M': 'M'}[k])
                    return fresh_new[k]
                txt = re.sub(r"@(HP|H|M)'", fr2, txt)
                mm = re.search(r'fun ((?:[^=]|=(?!>))*)=> \?_\s*$', txt)
                if mm and re.search(r'@(HP|H|M)(?![\w\'])', mm.group(1)):
                    # a rebind (`fun x @M hq @H => ?_`): fresh names, the state updated after
                    new = {}
                    def fr(m_):
                        k = m_.group(1)
                        if k not in new:
                            new[k] = self.fresh({'HP': 'hp', 'H': 'h', 'M': 'M'}[k])
                        return new[k]
                    binder = re.sub(r"@(HP|H|M)(?![\w'])", fr, mm.group(1))
                    L.append(f'{sp}{self.lean(txt[:mm.start(1)], st["env"])}{binder}=> ?_')
                    for k, v in new.items():
                        st[{'HP': 'hp', 'H': 'h', 'M': 'M'}[k]] = v
                else:
                    L.append(f'{sp}{self.lean(txt, st["env"])}')
                st.setdefault('named', set()).update(re.findall(r"\bhave ([A-Za-z_][\w']*)\s*:", txt))
                for k, v in fresh_new.items():
                    st[{'HP': 'hp', 'H': 'h', 'M': 'M'}[k]] = v
                # a raw step's effect on the state: {"pc": "hex", "regs": list | "@call", "env": {...}}
                eff = s[2] if len(s) > 2 else {}
                if 'pc' in eff:
                    st['pc'] = int(self.pc(eff['pc'])[2:-3], 16)
                if 'regs' in eff:
                    st['cur'] = eff['regs']
                    st['postcall'] = eff['regs'] == '@call'
                for k, v in eff.get('env', {}).items():
                    st['env'][k] = self.lean(v, st['env'])
                if 'lay' in eff:
                    st['lay'] = dict(eff['lay'])
            elif op == 'set':
                for k, v in s[1].items():
                    st['regs'][k] = self.lean(v, st['env'])
            elif op == 'bind':
                for k, v in s[1].items():
                    st['env'][k] = self.lean(v, st['env'])
            elif op == 'forget':
                st.get('snap', {}).pop(s[1], None)
                h2 = self.fresh()
                L.append(f'{sp}have {h2} := {st["h"]}.forget {s[1]} rfl')
                st['h'] = h2
            elif op == 'setmp':
                rS, rD, val = s[1], s[2], s[3]
                # optional: the digit tactic (text) and/or the header equations {"used", "alloc",
                # "sign", "n"} (`a'.used = a.used`, …, `a.alloc = n`; default `rfl`: a result whose
                # fields are spelled otherwise proves them, e.g. "by om")
                tx = [x for x in s[4:] if isinstance(x, str)]
                eqs = next((x for x in s[4:] if isinstance(x, dict)), {})
                tac = self.lean(tx[0], st['env']) if tx else self.a['setmp_tac']
                h2 = self.fresh()
                v = self.lean(val, st['env'])
                pf = ' '.join(GR.paren(self.lean(eqs[k], st['env'])) if k in eqs else 'rfl'
                              for k in ('used', 'alloc', 'sign', 'n'))
                L.append(f'{sp}have {h2} := {st["h"]}.setMp ({rS}) ({rD}) rfl rfl ({v}) {pf} (by {tac})')
                st['h'] = h2
            elif op == 'reK':
                # ["reK", region, k, e : k' = k, hk?]: the region's kind `k` (by `rfl`, or the proof
                # `hk : κ r = k` given: a propositional re-kind) re-stated as `k'`
                h2 = self.fresh()
                hk = GR.paren(self.lean(s[4], st['env'])) if len(s) > 4 else 'rfl'
                L.append(f'{sp}have {h2} := {st["h"]}.reK ({s[1]}) {hk} (k := {self.lean(s[2], st["env"])}) ({self.lean(s[3], st["env"])})')
                st['h'] = h2
            elif op == 'slot':
                # ["slot", region, alignment proof]: a plain-RAM slot as a one-digit array
                h2 = self.fresh()
                L.append(f'{sp}have {h2} := {st["h"]}.slot1 ({s[1]}) rfl rfl ({self.lean(s[2], st["env"])})')
                st['h'] = h2
            elif op == 'snap':
                # ["snap", region]: an untracked RAM region re-read as the snapshot `.frz M` of the
                # current memory (`St.snapK`, Kit/ByteBuf.lean); the snapshot is tracked from here
                h2 = self.fresh()
                L.append(f'{sp}refine St.snapK {st["h"]} {self.reg(s[1])} rfl fun {h2} => ?_')
                st['h'] = h2
                st.setdefault('snap', {})[self.unreg(s[1])] = st['M']
            elif op == 'unslot':
                # ["unslot", region]: a callee's one-word out slot `.mpD pd 1 f` given back to RAM
                # (`St.unslotK`; the slot inside the region by `iv_omega`)
                h2 = self.fresh()
                L.append(f'{sp}refine St.unslotK {st["h"]} {self.reg(s[1])} rfl (by iv_omega) fun {h2} => ?_')
                st['h'] = h2
                st.get('snap', {}).pop(self.unreg(s[1]), None)
            elif op == 'redig':
                h2 = self.fresh()
                L.append(f'{sp}have {h2} := {st["h"]}.reD ({s[1]}) rfl {self.lean(s[2], st["env"])} {self.lean(s[3], st["env"])}')
                st['h'] = h2
            elif op == 'call':
                self.call(s, st, L, sp)
            elif op == 'mul':
                self.mul(s, st, L, sp)
            elif op == 'tail':
                self.tail(s, st, L, sp)
            elif op == 'if':
                _, cond, th, el = s[:4]
                hb = s[4] if len(s) > 4 else 'hb'
                cl = self.lean(cond, st['env'])
                L.append(f'{sp}by_cases {hb} : {cl}')
                st.setdefault('named', set()).add(hb)
                st1 = self.copy(st)
                L.append(f'{sp}· ' + '')
                L.pop()
                sub = []
                self.steps(th, st1, sub, ind + 1)
                L.append(f'{sp}· {sub[0].strip()}')
                L += sub[1:]
                st2 = self.copy(st)
                sub = []
                self.steps(el, st2, sub, ind + 1)
                L.append(f'{sp}· {sub[0].strip()}')
                L += sub[1:]
                return
            elif op == 'cases':
                _, var, alts = s
                # an alternative: its constructor, then any rcases pattern (`some ⟨q, c⟩`); the
                # pattern's names are bound as themselves (not vocabulary words)
                def pat(alt):
                    ws = alt.split(None, 1)
                    return ws[1].strip() if len(ws) > 1 else '_'
                pats = ' | '.join(pat(alt) for alt in alts)
                L.append(f'{sp}rcases {var} with {pats}')
                for alt, body in alts.items():
                    st1 = self.copy(st)
                    ws = alt.split(None, 1)
                    if len(ws) > 1:
                        for nm_ in re.findall(r"(?<![\w.'])[A-Za-z_][\w']*", ws[1]):
                            if nm_ != '_':
                                st1['env'][nm_] = nm_
                    st1['alt'] = ws[0]
                    sub = []
                    self.steps(body, st1, sub, ind + 1)
                    L.append(f'{sp}· {sub[0].strip()}')
                    L += sub[1:]
                return
            elif op == 'jump':
                self.jump(s, st, L, sp)
                return
            elif op == 'exit':
                self.exit(s, st, L, sp)
                return
            else:
                die(f'unknown step {op}')

    @staticmethod
    def unreg(r):
        """A region name without its parentheses (`(nR .str)` -> `nR .str`)."""
        r = r.strip()
        while r.startswith('(') and r.endswith(')') and GR.balanced(r[1:-1]):
            r = r[1:-1].strip()
        return r

    def reg(self, r):
        """A region name as an argument: parenthesised when it is an application."""
        r = self.unreg(r)
        return f'({r})' if ' ' in r else r

    # the elaboration budget of one edge theorem (all its paths are one declaration)
    W_SEG, W_CALL, W_HEAP = 1, 2, 5
    MAX_WEIGHT, MAX_HEAP = 48, 5

    def edge_cost(self, steps):
        """(segments, plain calls, allocating calls) over all paths of an edge; raw steps count
        as calls by the rule they apply (`call_heap`/`tail_heap`; `call_std`/`tail_seq`/`call_mul`)."""
        n = [0, 0, 0]
        def walk(xs):
            for x in xs:
                op = x[0]
                if op == 'seg':
                    n[0] += 1
                elif op in ('call', 'tail'):
                    n[2 if self.callees.get(x[1], {}).get('heap') else 1] += 1
                elif op == 'mul':
                    n[1] += 1
                elif op == 'tac':
                    if re.search(r'\b(call_heap|call_heapR|tail_heap)\b', x[1]):
                        n[2] += 1
                    elif re.search(r'\b(call_std|tail_seq|call_mul)\b', x[1]):
                        n[1] += 1
                elif op == 'if':
                    walk(x[2]); walk(x[3])
                elif op == 'cases':
                    for b in x[2].values():
                        walk(b)
        walk(steps)
        return tuple(n)

    def budget(self, c, steps):
        """Warn when an edge likely overruns the heartbeat budget. Calibrated on the built
        annotations: the largest edge is mp_gcd's L0/L1 (15 segments, 9 calls, 2 allocating: weight
        43); r6g's mp_mul edge with 5 allocating calls overran, 4 (r6h's Karatsuba I2/I4) did not."""
        sg, ca, he = self.edge_cost(steps)
        w = self.W_SEG * sg + self.W_CALL * ca + self.W_HEAP * he
        if w >= self.MAX_WEIGHT or he >= self.MAX_HEAP:
            print(f'gen_asm: warning: {os.path.basename(self.path)} cut {c}: the edge has {sg} segments, {ca} calls and '
                  f'{he} allocating calls (weight {w}; the budget is about {self.MAX_WEIGHT}, {self.MAX_HEAP - 1} allocating '
                  f'calls): elaboration may overrun the heartbeat budget, add a cut', file=sys.stderr)

    def copy(self, st):
        return dict(st, regs=dict(st['regs']), env=dict(st['env']), snap=dict(st.get('snap', {})),
                    lay=dict(st.get('lay', {})), named=set(st.get('named', ())))

    def lay_layers(self, cu):
        """How often each allocation site is placed (`Iv.upd … site …`) in a cut's layout: the
        first argument of its `St` field, through the annotation's "defs" (`def ρt … := Iv.upd
        (ρX p) nS …`). The entry layout `ρX` has none."""
        t = dict(cu.get('state', [])).get('st', '')
        toks = top_split(t)
        if len(toks) < 2 or toks[0] != 'St':
            return {}
        defs = {}
        for d in self.a.get('defs', []) + self.a.get('head_defs', []):
            mm = re.match(r"^(?:def|abbrev)\s+([^\s(:]+)(.*?):=(.*)$", d.strip(), re.S)
            if mm:
                defs[mm.group(1)] = mm.group(3)
        out = {}
        def count(txt, depth):
            # the site argument of every `Iv.upd ρ site J` (a site or a contract region `nR .aD`)
            for mm in re.finditer(r"(?<![\w.'])Iv\.upd\s", txt):
                args = top_split(txt[mm.end():])
                if len(args) >= 2:
                    sn = self.unreg(args[1])
                    out[sn] = out.get(sn, 0) + 1
            if depth < 3:
                for w in re.findall(r"[^\s()⟨⟩,]+", txt):
                    if w in defs:
                        count(defs[w], depth + 1)
        count(unparen(toks[1]), 0)
        return {k: v for k, v in out.items() if v}

    def snaps_at(self, cu, env):
        """The own frame's snapshots at a cut (region -> memory term): from its kinds (`.frz X`),
        else the entry's (`Split.kind … m`). Tracked through the edge's stores (`ws`), so a jump
        gives a cut variable that is a snapshot base (`"nL": ".frz Ml"`) its value (r6d, r6e)."""
        out = {}
        kinds = cu.get('kinds')
        if isinstance(kinds, dict):
            for r, k in kinds.items():
                mm = re.match(r'^\.frz (.*)$', k.strip())
                if mm:
                    out[r] = self.lean(mm.group(1), env)
        else:
            for nm, _ in self.a['frame']:
                out[nm] = 'z.m'
            # contract regions of kind `.frz` ("Rk" "F ptr len snap"): their snapshot
            for r, kd in self.a.get('Rk', {}).items():
                kd = kd.split(None, 3)
                if kd[0] == 'F' and len(kd) > 3:
                    out[f'nR .{r}'] = self.lean(kd[3], env)
        return out

    # a segment
    def seg(self, s, st, L, sp):
        if self.lsegs is not None:
            return self.seg_lean(s, st, L, sp)
        nm, how = s[1], s[2]
        over = s[3] if len(s) > 3 else {}
        info = self.rowinfo[nm]
        row = self.rows[nm]
        env = st['env']
        args = {}
        # loads from facts: DG-like `name{a:=base + 4 * i, x:=v}`
        for t, head, src in info['hyps']:
            m = re.match(r'^(\w+)\{(.*)\}$', src)
            if not m or m.group(1) not in self.a.get('loads', {}):
                continue
            sub = {}
            for part in GR.split_top(m.group(2), ','):
                x, _, e = part.partition(':=')
                sub[x.strip()] = GR.spaced(e.strip())
            ld = self.a['loads'][m.group(1)]     # {"addr": "a", "val": "x", "stride": 4}
            addr = sub.get(ld['addr'], ld['addr'])
            val = sub.get(ld['val'], ld['val'])
            if ld.get('stride', 4) == 4:
                mm = re.match(r'^(\w+) \+ 4 \* (.*)$', addr)
            else:
                mm = re.match(r'^(\w+)(?: \+ (.*))?$', addr)
            if not mm:
                if val in over:
                    continue
                die(f'{nm}: load address {addr}')
            base, idx = mm.group(1), (mm.group(2) or '0')
            if base not in self.a['digits'] and val in over:
                continue
            if val in over or val in args:
                continue
            bt = st['regs'].get(base, self.lean(self.a['rowdef'].get(base, base), env))
            fnm = None
            for b, fn in self.a['digits'].items():
                if norm(self.lean(b, env)) == norm(bt):
                    fnm = fn
            if fnm is None:
                die(f'{nm}: no digit array at {bt}')
            idx_t = GR.substitute(idx, {k: v for k, v in st['regs'].items()})
            fl = self.lean(fnm, env)
            args[val] = fl.replace('#', GR.paren(idx_t)) if '#' in fl else f'{GR.paren(fl)} {GR.paren(idx_t)}'
        for p in info['bvs'] + info['nats']:
            if p in over:
                args[p] = self.lean(over[p], env)
            elif p in args:
                pass
            elif p in st['regs']:
                args[p] = st['regs'][p]
            else:
                if p not in self.a['rowdef'] and p not in env and self.ctx.get(p) in self.nonscalar():
                    die(f'{nm}: row parameter {p!r} would take the context word {p} = {self.ctx[p]} '
                        f'(not a scalar): give its value in "rowdef" or the seg override')
                args[p] = self.lean(self.a['rowdef'].get(p, p), env)
        h = st['h']
        hy = []
        for t, head, src in info['hyps']:
            if src == 'hra':
                hy.append('hra')
            elif src in over:
                hy.append(GR.paren(self.lean(over[src], env).replace('_h', h)))
            elif head is not None:
                hy.append(f'(by cfacts {h})')
            else:
                hy.append(f'(by side {h})')
        call = (f'{nm}_step ' + ' '.join(GR.paren(args[p]) for p in info['bvs']) + ' z.v z.o ' +
                ' '.join(GR.paren(args[p]) for p in info['nats']) + f' {st["M"]} (cd {h}) ' + ' '.join(hy))
        M2, h2 = self.fresh('M'), self.fresh()
        kind = how.split()
        if len(kind) > 2 and kind[1] == 'nR':
            kind = [kind[0], f'(nR {kind[2]})'] + kind[3:]
        def ov(k):
            return GR.paren(self.lean(over[k], env).replace('_h', h))
        hl = f' (hL := {ov("_hL")})' if '_hL' in over else ''
        sa = ov('_st')[1:-1] if '_st' in over else '(by omega) (by omega)'
        if kind[0] == '0':
            L.append(f'{sp}refine St.seq0{hl} ({call}) ?_')
            M2, h2 = st['M'], h
        elif kind[0] == 'ws':
            L.append(f'{sp}refine {h}.seqWs [{", ".join(kind[1:])}]{hl} ({call}) fun {M2} {h2} => ?_')
            logt = '[' + ', '.join(GR.substitute(e, args) for e in info['log']) + ']'
            for r in kind[1:]:
                r_ = re.sub(r'^\((.*)\)$', r'\1', r)
                if r_ in st.get('snap', {}) and info['log']:
                    st['snap'][r_] = f'writeLog {GR.paren(st["snap"][r_])} {logt}'
        elif kind[0] == 'w':
            # a written slot: a snapshot of the memory before, with the log
            L.append(f'{sp}refine {h}.{self.wrule(kind[1])}{hl} ({call}) fun {M2} {h2} => ?_')
        elif kind[0] == 'us':
            L.append(f'{sp}refine {h}.seqUS {kind[1]} rfl{hl} ({call}) (by om) (by om) fun {M2} {h2} => ?_')
        elif kind[0] == 'o':
            L.append(f'{sp}refine {h}.seqOvl {kind[1]} rfl{hl} ({call}) {sa} rfl fun {M2} {h2} => ?_')
        elif kind[0] == 'd':
            # one digit store: the digit function of that region
            ent = info['log'][0]
            mm = re.match(r'^\((\w+) \+ 4 \* (.*), 4, BitVec\.ofNat 64 (.*)\)$', ent)
            if mm:
                idx = GR.substitute(mm.group(2), args)
                val = GR.substitute(mm.group(3), args)
                L.append(f'{sp}refine {h}.seqD {kind[1]} rfl{hl} ({call}) {sa} fun {M2} {h2} => ?_')
            else:
                # digit 0 stored at the array's base itself (`dp`, not `dp + 4 * 0`)
                mm = re.match(r'^\(([\w.]+), 4, BitVec\.ofNat 64 (.*)\)$', ent)
                if not mm:
                    die(f'{nm}: store rule "d" needs one 4-byte store at `base + 4 * idx` or `base`: {ent}')
                idx, val = '0', GR.substitute(mm.group(2), args)
                L.append(f'{sp}refine {h}.seqD0 {kind[1]} rfl{hl} ({call}) {sa} fun {M2} {h2} => ?_')
            fv = kind[2] if len(kind) > 2 else 'f'
            st['env'][fv] = f'Mont.upd {GR.paren(st["env"][fv])} {GR.paren(idx)} {GR.paren(val)}'
        elif kind[0] == 'd8':
            # Kit/W64.lean): `St.seqD8'`, the word's index from "d8 <region> <f> <idx>" (or the log's
            # `base + 8 * idx`), the digit function `f` becomes the two halves' `Mont.upd`
            ent = info['log'][0]
            mm = re.match(r'^\((.*), 8, BitVec\.ofNat 64 (.*)\)$', ent)
            if not mm:
                die(f'{nm}: store rule "d8" needs one 8-byte store: {ent}')
            val = GR.substitute(mm.group(2), args)
            fv = kind[2] if len(kind) > 2 else 'f'
            if len(kind) > 3:
                idx = self.lean(' '.join(kind[3:]), env)
            else:
                m2 = re.match(r'^\w[\w ()+*-]* \+ 8 \* (.*)$', mm.group(1))
                if not m2:
                    die(f'{nm}: store rule "d8": give the word index ("d8 <region> <f> <idx>")')
                idx = GR.substitute(m2.group(1), args)
            sa1 = ov('_st')[1:-1] if '_st' in over else '(by omega)'
            L.append(f"{sp}refine {h}.seqD8' {kind[1]} ({idx}) rfl (by omega){hl} ({call}) {sa1} fun {M2} {h2} => ?_")
            pi, pv = GR.paren(idx), GR.paren(val)
            st['env'][fv] = (f'Mont.upd (Mont.upd {GR.paren(st["env"][fv])} (2 * {pi}) ({pv} % 4294967296)) '
                             f'(2 * {pi} + 1) ({pv} / 4294967296 % 4294967296)')
        elif kind[0] == 's':
            ent = info['log'][0] if len(info['log']) == 1 else ''
            if re.match(r'^\(.* \+ 8, 4, ', ent):
                L.append(f'{sp}refine {h}.seqS {kind[1]} rfl{hl} ({call}) (by omega) fun {M2} {h2} => ?_')
            else:
                # the sign's address as another term (`sp - 48` for a struct at `sp - 56`)
                L.append(f'{sp}refine {h}.seqS2 {kind[1]} rfl (by om){hl} ({call}) (by omega) fun {M2} {h2} => ?_')
        elif kind[0] == 'u':
            L.append(f'{sp}refine {h}.seqU {kind[1]} rfl{hl} ({call}) (by omega) fun {M2} {h2} => ?_')
        else:
            die(f'{nm}: store rule {how}')
        st['h'], st['M'] = h2, M2
        # the register state after
        post = row['post']
        mm = re.match(r'^(\w+)(\{(.*)\})?$', post.strip())
        lname = mm.group(1)
        sub = {}
        if mm.group(3):
            for part in GR.split_top(mm.group(3), ','):
                x, _, e = part.partition(':=')
                sub[x.strip()] = GR.spaced(e.strip())
        newregs = dict(st['regs'])
        for p in self.list_params(lname):
            if p in sub:
                newregs[p] = GR.substitute(sub[p], args)
            else:
                newregs[p] = args.get(p, st['regs'].get(p, p))
        st['regs'] = newregs
        st['cur'] = lname
        st['pc'] = info['end']
        st['last'] = nm
        st['postcall'] = False

    def seg_lean(self, s, st, L, sp):
        nm, how = s[1], s[2]
        over = s[3] if len(s) > 3 else {}
        info = self.lsegs[nm]
        env = st['env']
        bind = {}
        pl, pargs = info['pre']
        dps = self.ldefs[pl]
        pnames = [n for n, _ in info['params']]
        for i, tok in enumerate(pargs):
            if tok in pnames and dps[i] in st['regs']:
                bind[tok] = st['regs'][dps[i]]
        for n, t in info['params']:
            if t not in ('Nat', 'BitVec 64'):
                continue
            if n in over:
                bind[n] = self.lean(over[n], env)
            elif n not in bind:
                if n in st['regs']:
                    bind[n] = st['regs'][n]
                else:
                    bind[n] = self.lean(self.a['rowdef'].get(n, n), env)
        h = st['h']
        out = []
        def ov(k):
            return GR.paren(self.lean(over[k], env).replace('_h', h))
        for n, t in info['params']:
            if t in ('Nat', 'BitVec 64'):
                out.append(GR.paren(bind[n]))
            elif n in over:
                out.append(ov(n))
            elif t == 'Abi':
                out.append('z.v')
            elif t == 'Array String':
                out.append('z.o')
            elif t == 'Mem':
                out.append(st['M'])
            elif t.startswith('CodeAt'):
                out.append(f'(cd {h})')
            elif t.split()[0] in self.lfacts:
                out.append(f'(by cfacts {h})')
            elif n == 'hra':
                out.append('hra')
            else:
                out.append(f'(by side {h})')
        call = f'{nm}_step ' + ' '.join(out)
        M2, h2 = self.fresh('M'), self.fresh()
        kind = how.split()
        if len(kind) > 2 and kind[1] == 'nR':
            kind = [kind[0], f'(nR {kind[2]})'] + kind[3:]
        hl = f' (hL := {ov("_hL")})' if '_hL' in over else ''
        sa = ov('_st')[1:-1] if '_st' in over else '(by om) (by om)'
        if kind[0] == '0':
            L.append(f'{sp}refine St.seq0{hl} ({call}) ?_')
            M2, h2 = st['M'], h
        elif kind[0] == 'ws':
            L.append(f'{sp}refine {h}.seqWs [{", ".join(kind[1:])}]{hl} ({call}) fun {M2} {h2} => ?_')
        elif kind[0] == 'w':
            L.append(f'{sp}refine {h}.{self.wrule(kind[1])}{hl} ({call}) fun {M2} {h2} => ?_')
        elif kind[0] == 'us':
            L.append(f'{sp}refine {h}.seqUS {kind[1]} rfl{hl} ({call}) (by om) (by om) fun {M2} {h2} => ?_')
        elif kind[0] == 'o':
            L.append(f'{sp}refine {h}.seqOvl {kind[1]} rfl{hl} ({call}) {sa} rfl fun {M2} {h2} => ?_')
        elif kind[0] == 'd':
            L.append(f'{sp}refine {h}.seqD {kind[1]} rfl{hl} ({call}) {sa} fun {M2} {h2} => ?_')
        elif kind[0] == 'u':
            L.append(f'{sp}refine {h}.seqU {kind[1]} rfl ({call}) (by om) fun {M2} {h2} => ?_')
        else:
            die(f'{nm}: store rule {how}')
        st['h'], st['M'] = h2, M2
        ql, qargs = info['post']
        newregs = dict(st['regs'])
        for i, a in enumerate(qargs):
            newregs[self.ldefs[ql][i]] = GR.substitute(unparen(a), bind)
        st['regs'] = newregs
        st['cur'] = ql
        st['pc'] = info['end']
        st['postcall'] = False

    def wrule(self, reg):
        """The store rule "w" on a written slot: `St.seqR` for plain RAM (`Rk` "R"), `St.seqRD` for
        a slot modelled as a digit array exactly its region (`Rk` "D")."""
        m = re.match(r'^\(?nR \.(\w+)\)?$', reg)
        k = self.a.get('Rk', {}).get(m.group(1), '') if m else ''
        if k.startswith('D'):
            return f'seqRD {reg} rfl rfl'
        if k.startswith('R'):
            return f'seqR {reg} rfl'
        if k.startswith('F'):
            die(f'store rule "w {reg}": a snapshot region ("Rk" "F") takes its stores by "ws"')
        die(f'store rule "w {reg}": the region needs an "Rk" kind "R" or "D"')

    def callsite(self, st, callee):
        pc = st['pc']
        if pc not in self.W:
            die(f'call at {pc}?')
        w, txt = self.W[pc]
        tgt = self.entry[callee]
        imm = (tgt - pc) & 0x1fffff
        return f'0x{w:08x}#32 0x{imm:x}#21 0x{pc + 4:x}#64', pc + 4

    def sigma(self, callee, params, env, site=None, over=None):
        C = self.callees[callee]
        pv = dict(zip(C['params'], params))
        refs = self.a['refs']
        out = []
        for r, ref in C['regions']:
            if over and r in over:
                out.append((r, self.lean(over[r], env)))
                continue
            if ref == 'stk':
                tgt = 'nR .stk'
            elif ref == 'code':
                tgt = 'nR .code'
            elif ref.startswith('to '):
                tgt = ref[3:]
            elif ref == 'site':
                # the call option "site" names it when the function has several
                tgt = site if site is not None else (self.sites()[0] if len(self.sites()) == 1 else None)
                if tgt is None:
                    die(f'σ for {callee}.{r}: which site? give the call option "site"')
            else:
                kind, par = ref.split()
                val = norm(self.lean(pv[par], env))
                tgt = None
                for ours, oref in refs.items():
                    ok, ov = oref.split(None, 1)
                    if ok == kind and norm(self.lean(ov, env)) == val:
                        tgt = ours
                if tgt is None:
                    die(f'σ for {callee}.{r}: no region {kind} at {val}')
            out.append((r, tgt))
        return out

    def call(self, s, st, L, sp):
        """A call. Options besides "res", "hq", "perm", "hsub", "site", "post" (region families and
        calls through a register): "sig" {callee region: our region} (σ for a table entry, `nR (.tS x)`),
        "hk", "hsep" (proofs of `call_heap`'s/`call_std`'s kind and separation checks when they do not
        reduce by `rfl`/`decide`: two entries of one family), "C" (the contract as a Lean term, default
        `Std.<callee>`; the callee name still selects the registry entry for σ), "jalr" (the source register
        of a `jalr ra, 0(rs1)`: `call_heapR`, Kit/CallR.lean) with "htgt" (its target is the contract's
        entry; default `by decide`)."""
        _, callee, params, res = s[:4]
        opts = s[4] if len(s) > 4 else {}
        if 'with' in opts:
            opts = {**self.a.get('call_opts', {})[opts['with']], **{k: v for k, v in opts.items() if k != 'with'}}
        C = self.callees[callee]
        if C.get('heapN') or self.a.get('callees', {}).get(callee, {}).get('heapN'):
            return self.call_heapN(s, st, L, sp)
        env = st['env']
        ps = [self.lean(p, env) for p in GR.split_top(params, ',')]
        sig = self.sigma(callee, [p for p in GR.split_top(params, ',')], env, opts.get('site'), opts.get('sig'))
        ctor = C['ctor']
        sgm = f'(fun r : {ctor} => match r with ' + ' '.join(f'| .{r} => ({t} : X)' for r, t in sig) + ')'
        cterm = self.lean(opts['C'], env) if 'C' in opts else f'Std.{callee}'
        if 'jalr' in opts:
            pc = st['pc']
            if pc not in self.W:
                die(f'call at {pc}?')
            w, txt = self.W[pc]
            if not txt.startswith('jalr'):
                die(f'call option "jalr" at {pc:x}: the word is `{txt}`')
            site, ret = f'0x{w:08x}#32 {opts["jalr"]} 0x{pc + 4:x}#64', pc + 4
        else:
            site, ret = self.callsite(st, callee)
        h = st['h']
        rp = f"({self.lean(opts['res'], env)})" if 'res' in opts else f'(by res_tac {h})'
        M2, h2, hq = self.fresh('M'), self.fresh(), opts.get('hq', self.fresh('hq'))
        if 'hq' in opts:
            st.setdefault('named', set()).add(opts['hq'])
        pp = '⟨' + ', '.join(ps) + '⟩'
        extra = ''
        for k in ('hk', 'hsep', 'hw', 'hrs', 'hal'):
            if k in opts:
                extra += f' ({k} := {self.lean(opts[k], env)})'
        for k, v in opts.get('named', {}).items():
            extra += f' ({k} := {self.lean(v, env)})'
        if C['heap']:
            hp = st['hp']
            if 'perm' in opts:
                hp1 = self.fresh('hp')
                L.append(f'{sp}have {hp1} := {hp}.perm ({self.lean(opts["perm"], env)})')
                hp = hp1
            hp2 = self.fresh('hp')
            hs = f" (hsub := {self.lean(opts['hsub'], env)})" if 'hsub' in opts else ''
            if 'jalr' in opts:
                ht = self.lean(opts.get('htgt', 'by decide'), env)
                L.append(f'{sp}refine call_heapR {cterm} {pp} {sgm} {h} {hp} (cd {h}) {site} {rp} (htgt := {ht}){hs}{extra} '
                         f'fun {res} {M2} {hq} {h2} {hp2} => ?_')
            else:
                L.append(f'{sp}refine call_heap {cterm} {pp} {sgm} {h} {hp} (cd {h}) {site} {rp}{hs}{extra} fun {res} {M2} {hq} {h2} {hp2} => ?_')
            st['hp'] = hp2
            # the layout after: `Iv.upd ρ (σ C.site) …` (one more layer on that site: the callee's
            # "site" region, else its region with ref 'site'; unknown: no normalisation on this path)
            sr = C.get('site') or next((r for r, ref in C['regions'] if ref == 'site'), None)
            if sr is None:
                st['lay_unknown'] = True
            else:
                t = self.unreg(dict(sig)[sr])
                st.setdefault('lay', {})[t] = st.get('lay', {}).get(t, 0) + 1
            st['env']['Mk'] = M2
        else:
            if 'jalr' in opts:
                die('call option "jalr": an allocating contract only (`call_heapR`)')
            hs = f" (hsub := {self.lean(opts['hsub'], env)})" if 'hsub' in opts else ''
            L.append(f'{sp}refine call_std {cterm} {pp} {sgm} {h} (cd {h}) {site} {rp}{hs}{extra} fun {res} {M2} {hq} {h2} => ?_')
        if self.a.get('dsimp_q'):
            L.append(f'{sp}try dsimp only at {hq}')
        st['h'], st['M'] = h2, M2
        st['pc'] = ret
        # the post-call state `At ret (C.rets ++ keep)`: a jump may end here (`subL`)
        st['cur'] = opts.get('post', '@call')
        st['postcall'] = True
        if res != '_':
            st['env'][res] = res

    def sigmaN(self, callee, params, env, sites):
        """σ for a multi-site callee: refs 'stk', 'code', 'site i' (our i-th site of
        the call option "sites"), 'S|D <param>[i]' (the i-th element of a list parameter) and
        'S|D <param>[i]#j' (component j of that tuple), else as `sigma`."""
        C = self.callees[callee]
        pv = dict(zip(C['params'], params))
        refs = self.a['refs']
        out = []
        for r, ref in C['regions']:
            if ref == 'stk':
                tgt = 'nR .stk'
            elif ref == 'code':
                tgt = 'nR .code'
            elif ref.startswith('site'):
                i = int(ref.split()[1])
                if sites is None or i >= len(sites):
                    die(f'σ for {callee}.{r}: give our sites in the call option "sites"')
                tgt = sites[i]
            elif ref.startswith('sarg'):
                j = int(ref.split()[1])
                sargs = (self._sargs or [])
                if j >= len(sargs):
                    die(f'σ for {callee}.{r}: give our regions holding the stack arguments in the call option "sargs"')
                tgt = sargs[j]
            else:
                kind, par = ref.split(None, 1)
                m = re.match(r'^(\w+)\[(\d+)\](?:#(\d+))?$', par)
                if m:
                    lst = self.lean(pv[m.group(1)], env).strip()
                    if not (lst.startswith('[') and lst.endswith(']')):
                        die(f'σ for {callee}.{r}: parameter {m.group(1)} is not a list literal: {lst}')
                    x = GR.split_top(lst[1:-1], ',')[int(m.group(2))].strip()
                    if m.group(3) is not None:
                        if not (x.startswith('(') and x.endswith(')')):
                            die(f'σ for {callee}.{r}: {x} is not a tuple')
                        x = GR.split_top(x[1:-1], ',')[int(m.group(3))].strip()
                    val = norm(x)
                else:
                    val = norm(self.lean(pv[par], env))
                tgt = None
                for ours, oref in refs.items():
                    ok, ov = oref.split(None, 1)
                    if ok == kind and norm(self.lean(ov, env)) == val:
                        tgt = ours
                if tgt is None:
                    die(f'σ for {callee}.{r}: no region {kind} at {val}')
            out.append((r, tgt))
        return out

    def call_heapN(self, s, st, L, sp):
        """["call", C, params, res, {"sites": [our site regions], "perm": …, "res": …}] for a
        multi-site callee (`"heapN": true`): `call_heapN` (Kit/MeetHeapN.lean) with σ by
        `sigmaN` (a default arm for the `Fin` indices out of range), `hsub`/`hk` by `mr_split`
        (Api/Std_multi8.lean); one layout layer per callee site on its image."""
        _, callee, params, res = s[:4]
        opts = s[4] if len(s) > 4 else {}
        C = dict(self.callees[callee])
        C.update({k: v for k, v in self.a.get('callees', {}).get(callee, {}).items() if k in ('heapN', 'sites')})
        env = st['env']
        ps = [self.lean(p, env) for p in GR.split_top(params, ',')]
        self._sargs = opts.get('sargs')
        sig = self.sigmaN(callee, GR.split_top(params, ','), env, opts.get('sites'))
        dflt = dict(sig).get('stk', 'nR .stk')
        sgm = (f'(fun r : {C["ctor"]} => match r with ' + ' '.join(f'| .{r} => ({t} : X)' for r, t in sig) +
               f' | _ => ({dflt} : X))')
        site, ret = self.callsite(st, callee)
        h = st['h']
        rp = f"({self.lean(opts['res'], env)})" if 'res' in opts else f'(by res_tac {h})'
        M2, h2, hq = self.fresh('M'), self.fresh(), opts.get('hq', self.fresh('hq'))
        if 'hq' in opts:
            st.setdefault('named', set()).add(opts['hq'])
        pp = '⟨' + ', '.join(ps) + '⟩'
        hp = st['hp']
        if 'perm' in opts:
            hp1 = self.fresh('hp')
            L.append(f'{sp}have {hp1} := {hp}.perm ({self.lean(opts["perm"], env)})')
            hp = hp1
        hp2 = self.fresh('hp')
        hsub = opts.get('hsub', 'by mr_split <;> mr_iv')
        hk = opts.get('hk', 'by mr_split <;> rfl')
        L.append(f'{sp}refine call_heapN Std.{callee} {pp} {sgm} {h} {hp} (cd {h}) {site} {rp} '
                 f'(hsub := {hsub}) (hk := {hk}) fun {res} {M2} {hq} {h2} {hp2} => ?_')
        st['hp'] = hp2
        lay = st.setdefault('lay', {})
        for r in C.get('sites', []):
            t = self.unreg(dict(sig)[r])
            lay[t] = lay.get(t, 0) + 1
        st['env']['Mk'] = M2
        if self.a.get('dsimp_q'):
            L.append(f'{sp}try dsimp only at {hq}')
        st['h'], st['M'] = h2, M2
        st['pc'] = ret
        st['cur'] = opts.get('post', '@call')
        st['postcall'] = True
        if res != '_':
            st['env'][res] = res

    def tail(self, s, st, L, sp):
        """A tail call (`tail_seq`; `tail_heap` for an allocating callee): the rest of the edge
        starts at the return to `ra`."""
        _, callee, params, res = s[:4]
        opts = s[4] if len(s) > 4 else {}
        C = self.callees[callee]
        env = st['env']
        ps = [self.lean(p, env) for p in GR.split_top(params, ',')]
        # piece, made RAM by "forget", as a tail callee's stack)
        sig = self.sigma(callee, GR.split_top(params, ','), env, opts.get('site'), opts.get('sig'))
        h = st['h']
        flat = opts.get('flat')
        hp = st.get('hp', 'hp')
        if flat is not None and self.a.get('style') == 'pre' and len(self.a['frame']) == 1 and not self.so():
            # style "pre" (one frame piece): `St.flat1`, the stack plain RAM again
            fo = flat if isinstance(flat, dict) else {}
            if C['heap']:
                die(f'tail call to {callee}: "flat" with style "pre" and a heap callee')
            hf = self.fresh()
            fl = self.lean(fo.get('hf', f'by exact (by decide : {self.a["frame"][0][1]} ≤ {self.a.get("F", "_")})'), env)
            L.append(f'{sp}have {hf} := {h}.flat1 (ws := {self.lean(fo.get("ws", "ws"), env)}) ({fl}) '
                     f'({self.lean(fo.get("sound", "hP.lay"), env)}) ({self.lean(fo.get("ram", "hP.rs"), env)})')
            h = hf
            out = []
            for r, t in sig:
                mm = re.match(r'^nR \.(\w+)$', t)
                if not mm:
                    die(f'tail call to {callee}: region {r} maps to {t}, not a contract region')
                out.append((r, 'R.' + mm.group(1)))
            sgm = f'(fun r : {C["ctor"]} => match r with ' + ' '.join(f'| .{r} => {t}' for r, t in out) + ')'
        elif flat is not None:
            # the own frame given back: the state over the contract's layout
            fo = flat if isinstance(flat, dict) else {}
            if self.so() > 1:
                die(f'tail call to {callee}: "flat" with several sites')
            ins = 'InAny.site' if self.so() else 'InAny.push'
            hf = self.fresh()
            hF = self.lean(fo.get('hF', 'by omega'), env)
            kd = self.lean(fo.get('kd', self.a.get('kind_t', 'kind p')), env)
            wsl = self.lean(fo.get('ws', 'ws'), env)
            # call, `Iv.upd (lay p) R.aD J`) and "ins" (the pieces inside it) override the contract's
            lay = f' (lay := {self.lean(fo["lay"], env)})' if 'lay' in fo else ''
            insp = self.lean(fo['ins'], env) if 'ins' in fo else f'{ins} proj (sub3 ({hF}))'
            L.append(f'{sp}have {hf} := {h}.flat{lay} (kd := {kd}) (ws := {wsl}) R.stk (fun r => {self.some_pat(len(self.a["frame"]) + self.so(), "r")}) '
                     f'({self.lean(fo.get("sound", "hS"), env)}) ({self.lean(fo.get("stk", "⟨trivial, (hB .stk).2⟩"), env)}) '
                     f'({insp})')
            h = hf
            if C['heap']:
                # the heap checkpoint over the contract's layout, at the entry
                hp = self.fresh('hp')
                wsimp = self.a.get('isW', 'isW')
                hpF = fo.get('hp', f'HP.flatE (ws := {fo.get("ws", "ws")}) hc.heap hoff (ramW hB) (by intro r hr; cases r <;> first | exact absurd hr (by decide) | decide)')
                L.append(f'{sp}have {hp} := {self.lean(hpF, env)}')
            out = []
            for r, t in sig:
                mm = re.match(r'^nR \.(\w+)$', t)
                if not mm:
                    die(f'tail call to {callee}: region {r} maps to {t}, not a contract region')
                out.append((r, 'R.' + mm.group(1)))
            sgm = f'(fun r : {C["ctor"]} => match r with ' + ' '.join(f'| .{r} => {t}' for r, t in out) + ')'
        else:
            sgm = f'(fun r : {C["ctor"]} => match r with ' + ' '.join(f'| .{r} => ({t} : X)' for r, t in sig) + ')'
        rp = f"({self.lean(opts['res'], env)})" if 'res' in opts else f'(by res_tac {h})'
        hra = self.lean(opts.get('hra', 'hra'), env)
        kk = f" (K' := {self.lean(opts[chr(75) + chr(39)], env)})" if "K'" in opts else f" (K' := {self.a.get('keep', '(kp z.v)')})"
        hs = f" (hsub := {self.lean(opts['hsub'], env)})" if 'hsub' in opts else ''
        M2, h2, hq = self.fresh('M'), self.fresh(), opts.get('hq', self.fresh('hq'))
        if 'hq' in opts:
            st.setdefault('named', set()).add(opts['hq'])
        pp = '⟨' + ', '.join(ps) + '⟩'
        if C['heap']:
            hp2, hpo = self.fresh('hp'), opts.get('hpo', 'hpo')
            L.append(f'{sp}refine tail_heap Std.{callee} {pp} {sgm} {h} {hp} {rp} {hra}{kk}{hs} fun {res} {M2} {hq} {h2} {hp2} {hpo} => ?_')
            st['hp'] = hp2
        else:
            L.append(f'{sp}refine tail_seq Std.{callee} {pp} {sgm} {h} {rp} {hra}{kk}{hs} fun {res} {M2} {hq} {h2} => ?_')
        if self.a.get('dsimp_q'):
            L.append(f'{sp}try dsimp only at {hq}')
        st['h'], st['M'] = h2, M2
        st['pc'] = None
        st['cur'] = '@tail'
        st['postcall'] = False
        if res != '_':
            st['env'][res] = res

    def mul(self, s, st, L, sp):
        _, l2 = s[:2]
        cur = st['cur']
        rl = self.F.regs[cur]
        x = GR.substitute(rl[10], st['regs'])
        y = GR.substitute(rl[11], st['regs'])
        site, ret = self.callsite(st, 'muldi3')
        w, imm, r = site.split()
        args = ' '.join(GR.paren(st['regs'][p]) for p in self.list_params(l2))
        L.append(f'{sp}refine call_mul ({l2} {args}) {GR.paren(x)} {GR.paren(y)} ({st["h"]}.img (nR .code)) (cd {st["h"]}) {r} (pc := 0x{st["pc"]:x}#64) (w := {w}) (imm := {imm}) ?_')
        st['pc'] = ret
        st['cur'] = l2
        st['postcall'] = False

    def jump(self, s, st, L, sp):
        _, c = s[:2]
        proofs = s[2] if len(s) > 2 else {}
        cu = self.a['cuts'][c]
        env = st['env']
        vs = self.cut_vars(cu)
        # cut variables from the register state
        val = {}
        if st['cur'] != cu['regs'] and not (st.get('postcall') and st['cur'] == '@call'):
            die(f'jump to {c}: register list {st["cur"]} is not {cu["regs"]}')
        over = cu.get('regs_over', {})
        for p in self.list_params(cu['regs']):
            if p in [v for v, _ in vs] and p not in over:
                val[p] = st['regs'][p]
        snapv = {}
        if isinstance(cu.get('kinds'), dict):
            for r, k in cu['kinds'].items():
                mm = re.match(r'^\.frz (\w+)$', k.strip())
                if mm and mm.group(1) in [x for x, _ in vs] and r in st.get('snap', {}):
                    snapv[mm.group(1)] = st['snap'][r]
        for v, _ in vs:
            if v in proofs.get('vars', {}):
                val[v] = self.lean(proofs['vars'][v], env)
            elif v in snapv:
                val[v] = snapv[v]
            elif v == 'M':
                val[v] = st['M']
            elif v not in val:
                if v in env:
                    val[v] = env[v]
                else:
                    die(f'jump to {c}: no value for {v}')
        xs = '⟨' + ', '.join(val[v] for v, _ in vs) + '⟩' if vs else '⟨()⟩'
        # the layout normalised: a site placed again on the path (`Iv.upd (Iv.upd ρ s I) s J`)
        # collapses to the target cut's one layer by `Iv.upd_upd` (`St.congrL`, `HP.congrL`)
        tl_ = self.lay_layers(cu)
        cur_ = st.get('lay', {})
        extra = {sn: cur_.get(sn, 0) - tl_.get(sn, 0) for sn in set(cur_) | set(tl_)
                 if cur_.get(sn, 0) != tl_.get(sn, 0)}
        hS_, hP_ = st['h'], st.get('hp', 'hp')
        if extra and not st.get('lay_unknown'):
            bad = [sn for sn, k in extra.items() if k < 0 or tl_.get(sn, 0) < 1]
            # one layer fewer than the target: the site kept where the target places it
            #: `Iv.upd_eq_self`
            keep = [sn for sn, k in extra.items() if k == -1 and tl_.get(sn, 0) == 1]
            if len(extra) == 1 and keep:
                hS_ = f'({hS_}.congrL (Iv.upd_eq_self _ _ rfl))'
                hP_ = f'{hP_}.congrL (Iv.upd_eq_self _ _ rfl)'
            elif len(extra) == 1 and not bad:
                (sn, k), = extra.items()
                for _ in range(k):
                    hS_ = f'({hS_}.congrL (Iv.upd_upd _ _ _ _))'
                    hP_ = f'{hP_}.congrL (Iv.upd_upd _ _ _ _)' if _ == 0 else f'({hP_}).congrL (Iv.upd_upd _ _ _ _)'
            elif 'st' not in proofs:
                print(f'gen_asm: warning: {os.path.basename(self.path)} jump to {c}: the layout has sites placed '
                      f'{dict(st.get("lay", {}))}, the cut {tl_}: give "st"/"hp"', file=sys.stderr)
        hS_ = f'{hS_}.congrK (by krfl)'
        # premise fields
        fl = []
        for f, t in self.cut_fields(c, cu):
            if f in proofs:
                fl.append(self.lean(proofs[f], env))
            elif f == 'st':
                fl.append(hS_)
            elif f == 'hp':
                fl.append(hP_)
            elif f in env:
                fl.append(env[f])
            elif f in st.get('locals', ()) and all(val.get(v) == f'xc.{v}' for v in
                                                 re.findall(r"[A-Za-z_][\w']*", t) if v in val):
                fl.append(f)
            elif f in st.get('named', ()):
                fl.append(f)
            else:
                fl.append(f'(by side {st["h"]})')
        dec_ = f"(by {self.lean(proofs['dec'], env)})" if 'dec' in proofs else '(by dec)'
        L.append(f'{sp}exact Lbl.jump (L := LL z) .{c} {xs} {dec_}')
        tl = 'h.subL (by exact rfl)' if st.get('postcall') else 'h'
        if vs and self.a.get('jump_mk', True):
            args = ' '.join(GR.paren(val[v]) for v, _ in vs) + ' ' + ' '.join(GR.paren(x) for x in fl)
            L.append(f"{sp}  (P{c}.mk' z {args}) fun _ h => {tl}")
        else:
            L.append(f'{sp}  ⟨{", ".join(fl)}⟩ fun _ h => {tl}')

    def exit(self, s, st, L, sp):
        _, tmpl = s[:2]
        args = s[2] if len(s) > 2 else {}
        env = dict(st['env'])
        env['_h'] = st['h']
        env['_hp'] = st['hp']
        env['_M'] = st['M']
        for k, v in list(self.a.get('exit_defaults', {}).get(tmpl, {}).items()) + list(args.items()):
            env[k] = self.lean(v, env)
        t = self.a['exits'][tmpl]
        for line in t:
            out = line
            for k in ('_hp', '_M', '_h'):
                out = out.replace(k, env[k])
            L.append(sp + self.lean(out, env))

    def ram_line(self, r, simps):
        """The RAM of written region `r` from the entry bundle, by its `Rk` kind: a struct's 24
        bytes (`S p dp a`), a digit array (`D dp a`), plain RAM (`R`, an out-parameter slot)."""
        kd = self.a['Rk'][r].split()
        if kd[0] == 'S':
            return f'simpa [{simps}, Layout.sizeofMpInt] using (Hdr.geom (show Hdr m p.{kd[1]} p.{kd[2]} p.{kd[3]} from (hB .{r}).2)).st'
        if kd[0] == 'R':
            return f'first | exact (hB .{r}).2 | simpa [{simps}] using (hB .{r}).2'
        if kd[0] == 'F':
            # a snapshot region: its witness is RAM and the agreement with the snapshot
            return f'first | exact (hB .{r}).2.1 | simpa [{simps}] using (hB .{r}).2.1'
        return f'simpa [{simps}] using (show Dig m p.{kd[1]} p.{kd[2]}.alloc p.{kd[2]}.digit from (hB .{r}).2).ram'

    def heap_flat(self):
        """Some edge tail-calls an allocating callee over the contract's layout (`ramW` needed)."""
        def walk(x):
            if isinstance(x, list):
                if len(x) >= 5 and x[0] == 'tail' and isinstance(x[1], str) and self.callees.get(x[1], {}).get('heap') \
                        and isinstance(x[4], dict) and x[4].get('flat') is not None:
                    return True
                return any(walk(y) for y in x)
            if isinstance(x, dict):
                return any(walk(y) for y in x.values())
            return False
        return walk([cu.get('edge', []) for cu in self.a['cuts'].values()])

    def emit_entry(self):
        a = self.a
        if a.get('style') == 'pre':
            return
        k = len(a['frame'])
        F = a['F']
        pat = ' | '.join(['_'] * k + ['r'])
        L = []
        lay_ = lay_s = 'lay'
        hlo = 'have := hres.stk.lo; have e : heapEnd = 0x87800000 := rfl; omega'
        if a.get('lay_rfl'):
            # a deep stack (F ≳ 800): no equation lemmas of `lay` (its `⟨p.sp - F, F⟩` arm
            # overflows), one `rfl` lemma per region instead; `heapEnd` as a literal
            ov = a['lay_rfl'] if isinstance(a['lay_rfl'], dict) else {}
            names = []
            for r in a['R']:
                if r in ov:
                    rhs = ov[r]
                elif r == 'stk':
                    rhs = f'⟨p.sp - {F}, {F}⟩'
                elif r == 'code':
                    rhs = 'textIv'
                elif r in a.get('Rk', {}) and (a['Rk'][r].split()[0] != 'R' or len(a['Rk'][r].split()) > 2):
                    kd = a['Rk'][r].split()
                    rhs = (f'⟨p.{kd[1]}, 24⟩' if kd[0] == 'S' else f'⟨p.{kd[1]}, {kd[2]}⟩' if kd[0] in ('R', 'F')
                           else f'⟨p.{kd[1]}, 4 * p.{kd[2]}.alloc⟩')
                else:
                    die(f'lay_rfl: give the interval of region {r} ("lay_rfl": {{"{r}": "⟨…⟩"}})')
                L.append(f'theorem layE_{r} (p : P) : lay p .{r} = {rhs} := rfl')
                names.append(f'layE_{r}')
            L.append('')
            lay_ = ', '.join(names)
            lay_s = 'layE_stk'
            hlo = 'have h := hres.stk.lo; rw [show heapEnd = 0x87800000 from rfl] at h; omega'
        L.append('section Entry')
        L.append('variable {p : P}')
        L.append('')
        L.append(f'theorem sub3 (hF : {F} ≤ p.sp) (y : Y) : (ρ3 p y).Sub (lay p (proj y)) := by')
        L.append(f'  have eF : Api.{a["api"]}.F = {F} := rfl')
        L.append(f'  rcases y with {pat}')
        eo = ' <;> omega' if a.get('entry_omega') else ''
        for _ in range(k):
            L.append(f'  · simp [ρ3, Split.lay, {lay_s}, proj, Iv.Sub, eF]{eo}')
        L.append(f'  · cases r <;> simp [ρ3, Split.lay, {lay_}, proj, Iv.Sub, eF] <;> omega')
        L.append('')
        edge = 'pos' not in a
        if edge:
            # no "pos": a contract region is nonempty or outside the arena by its own `Off` (`Off.pos`,
            # its `edge` field when empty); only the frame pieces and the callees' area by length
            L.append(f'theorem pos3 (hoff : ∀ r, Off (lay p r) (Api.{a["api"]}.hin p)) (y : Y) : 0 < (ρ3 p y).len ∨ (ρ3 p y).base < heapStart ∨ heapEnd ≤ (ρ3 p y).base := by')
        else:
            L.append('theorem pos3 (hres : Res p) (y : Y) : 0 < (ρ3 p y).len ∨ (ρ3 p y).base < heapStart ∨ heapEnd ≤ (ρ3 p y).base := by')
        L.append(f'  have eF : Api.{a["api"]}.F = {F} := rfl')
        for f in a.get('pos', []):
            L.append(f'  have := {f}')
        L.append(f'  rcases y with {pat}')
        for _ in range(k):
            L.append(f'  · left; simp [ρ3, Split.lay, {lay_s}, eF]{eo}')
        if edge:
            L.append('  · cases r with')
            for r in a['R']:
                if r == 'stk':
                    L.append(f'    | stk => left; simp [ρ3, Split.lay, {lay_s}, eF]')
                else:
                    L.append(f'    | {r} => exact Off.pos (hoff .{r})')
        else:
            L.append(f'  · cases r <;> (left; simp [ρ3, Split.lay, {lay_}, eF, textIv, textLen]; try omega)')
        L.append('')
        wsimp = a.get('isW', 'isW')
        L.append('/-- The entry state and the heap checkpoint. -/')
        L.append('theorem entry_state {m : Mem} (hres : Res p) (hS : Sound (lay p) isW) (hB : Bundle (lay p) (kind p) m)')
        L.append(f'    (hH : AHeap m (Api.{a["api"]}.hin p)) (hoff : ∀ r, Off (lay p r) (Api.{a["api"]}.hin p)) :')
        L.append('    St (ρX p) wX WX (κX p m) m m ∧')
        L.append(f'      HP (ρX p) wX (Api.{a["api"]}.hin p) (Api.{a["api"]}.hin p) (InAny (lay p) ws) m m := by')
        if a.get('entry_omega') and a.get('lay_rfl'):
            hlo = f'have h := hres.stk.lo; rw [show heapEnd = 0x87800000 from rfl, show Api.{a["api"]}.F = {F} from rfl] at h; omega'
        L.append(f'  have hF : {F} ≤ p.sp := by {hlo}')
        L.append(f'  have eF : Api.{a["api"]}.F = {F} := rfl')
        lay = 'lay p'
        stk = '.stk'
        hs = []
        for i, (nm, sz) in enumerate(a['frame']):
            L.append(f'  have h{i + 1} : {sz} ≤ ({lay} {stk}).len := by simp [Split.lay, {lay_s}, eF]{eo}')
            hs.append(f'h{i + 1}')
            lay = f'Split.lay ({lay}) {stk} {sz}'
            stk = f'(some {stk})'
        L.append(f'  have offY : ∀ y, Off (ρ3 p y) (Api.{a["api"]}.hin p) := fun y => (hoff (proj y)).sub (sub3 hF y) (pos3 {"hoff" if "pos" not in a else "hres"} y)')
        snd, bnd = 'hS', 'hB'
        for hh in hs:
            snd = f'Split.sound ({snd}) rfl {hh}'
            bnd = f'Split.bundle ({bnd}) rfl {hh}'
        L.append(f'  have S3 : Sound (ρ3 p) w3 := {snd}')
        L.append(f'  have B3 : Bundle (ρ3 p) (κ3 p m) m := {bnd}')
        if self.so() > 1 and self.heap_flat():
            die('a heap tail call over the contract\'s layout with several sites')
        if self.so() != 1:
            # several sites: peel them by Site.*_all, then the pieces as with one; no site (a heap
            # function whose callees re-place a contract region): the pieces themselves
            n = self.so()
            snd, lo = 'S3', 'fun y => (offY y).lo'
            for _ in range(n):
                snd, lo = f'Site.sound ({snd}) ({lo})', f'Site.lo_all ({lo})'
            bnd, off, cov, ram = 'B3', 'offY', '?_', '?_'
            for _ in range(n):
                bnd, off, cov, ram = f'Site.bundle ({bnd})', f'Site.off_all ({off})', f'Site.cov_all ({cov})', f'Site.ram_all ({ram})'
            L.append(f'  refine ⟨⟨{snd}, {bnd}, Frm.refl _ _⟩, HP.entry hH ({off}) ({cov}) ({ram})⟩')
            L.append('  · intro y hx a ha')
            L.append('    have hs := sub3 hF y')
            # no site: the goals are over `ρX`/`wX` (abbreviations of `ρ3`/`w3`)
            ux, wx, rx = ('', '', '') if n else (' dsimp only [ρX] at ha;', 'wX, ', 'ρX, ')
            L.append(f"    have ha' : (lay p (proj y)).In a := by unfold Iv.Sub Iv.In at *;{ux} omega")
            L.append(f'    rcases y with {pat}')
            for _ in range(k):
                L.append("    · exact InAny.of_mem (w := R.stk) (by decide) ha'")
            L.append(f"    · cases r <;> simp [{wx}w3, Split.wr, {wsimp}] at hx <;> exact InAny.of_mem (by decide) ha'")
            L.append('  · intro y hx')
            L.append('    have hs := sub3 hF y')
            L.append('    have hstk : Ram (lay p .stk).base (lay p .stk).len := (hB .stk).2')
            L.append(f'    rcases y with {pat}')
            for _ in range(k):
                L.append('    · exact Ram.sub hstk hs.1 hs.2')
            L.append(f'    · cases r <;> simp [{wx}w3, Split.wr, {wsimp}] at hx')
            for r in a['written']:
                if r == 'stk':
                    L.append('      · exact Ram.sub hstk hs.1 hs.2')
                    continue
                L.append('      · ' + self.ram_line(r, f'{rx}ρ3, Split.lay, {lay_}'))
            if self.heap_flat():
                L += self.ramW_lines(lay_)
            L.append('')
            L.append('end Entry')
            L.append('')
            self.out += L
            return
        L.append('  refine ⟨⟨Site.sound S3 fun y => (offY y).lo, Site.bundle B3, Frm.refl _ _⟩, HP.entry hH ?_ ?_ ?_⟩')
        L.append('  · intro x; cases x with')
        L.append('    | none => exact Off.nil _')
        L.append('    | some y => exact offY y')
        L.append('  · intro x hx a ha')
        L.append('    cases x with')
        L.append('    | none => simp [Site.lay, Iv.nil, Iv.In] at ha; omega')
        L.append('    | some y =>')
        L.append('      have hs := sub3 hF y')
        L.append('      have ha\' : (lay p (proj y)).In a := by unfold Iv.Sub Iv.In at *; simp only [Site.lay] at ha; omega')
        L.append(f'      rcases y with {pat}')
        for _ in range(k):
            L.append('      · exact InAny.of_mem (w := R.stk) (by decide) ha\'')
        L.append(f'      · cases r <;> simp [wX, Site.wr, w3, Split.wr, {wsimp}] at hx <;> exact InAny.of_mem (by decide) ha\'')
        L.append('  · intro x hx')
        L.append('    cases x with')
        L.append('    | none => exact Ram.nil')
        L.append('    | some y =>')
        L.append('      have hs := sub3 hF y')
        L.append('      have hstk : Ram (lay p .stk).base (lay p .stk).len := (hB .stk).2')
        L.append(f'      rcases y with {pat}')
        for _ in range(k):
            L.append('      · exact Ram.sub hstk hs.1 hs.2')
        L.append(f'      · cases r <;> simp [wX, Site.wr, w3, Split.wr, {wsimp}] at hx')
        for r in a['written']:
            if r == 'stk':
                L.append('        · exact Ram.sub hstk hs.1 hs.2')
                continue
            L.append('        · ' + self.ram_line(r, f'Site.lay, ρ3, Split.lay, {lay_}'))
        if self.heap_flat():
            L += self.ramW_lines(lay_)
        L.append('')
        L.append('end Entry')
        L.append('')
        self.out += L

    def ramW_lines(self, lay_):
        """The written regions' RAM over the contract's layout (`HP.flatE` before a heap tail call)."""
        a, wsimp = self.a, self.a.get('isW', 'isW')
        L = ['', '/-- The written regions are RAM (the heap checkpoint over the contract\'s layout). -/',
             f'theorem ramW {{m : Mem}} (hB : Bundle (lay p) (kind p) m) (r : R) (hr : {wsimp} r = true) :',
             '    Ram (lay p r).base (lay p r).len := by', f'  cases r <;> simp [{wsimp}] at hr']
        for r in [r for r in a['R'] if r in a['written']]:
            L.append('  · ' + ('exact (hB .stk).2' if r == 'stk' else self.ram_line(r, lay_)))
        return L

    def emit_entry_pre(self):
        a = self.a
        L = ['/-- The entry state, from the contract\'s Pre. -/',
             'theorem entry_state {z : Fx} (hc : Cx z) : St (ρX z.p) wX WX (κX z.p z.m) z.m z.m := by',
             '  have hP := hc.pre']
        lay = f'{a["lay_t"]} z.p'
        bnd = 'hB'
        snd = 'hP.lay'
        stk = '.stk'
        L.append(f'  have hB : Bundle ({a["lay_t"]} z.p) ({a["kind_t"].replace(" p m", " z.p z.m")}) z.m := fun r => by')
        L.append('    cases r')
        for r in a['R']:
            L.append(f'    · exact ⟨{a["fits"].get(r, "Iv.sub_self _")}, {a["wit"][r]}⟩')
        # Not in `Names`)
        for r, fits, wit in a.get('fam', []):
            L.append(f'    · exact ⟨{fits}, {wit}⟩')
        for i, (nm, sz) in enumerate(a['frame']):
            L.append(f'  have h{i + 1} : {sz} ≤ ({lay} {stk}).len := by {a["frame_len_tac"][i]}')
            snd = f'Split.sound ({snd}) rfl h{i + 1}'
            bnd = f'Split.bundle ({bnd}) rfl h{i + 1}'
            lay = f'Split.lay ({lay}) {stk} {sz}'
            stk = f'(some {stk})'
        if self.so():
            # sites over the pieces: their bases from the annotation's "site_lo"
            if 'site_lo' not in a:
                die('style "pre" with a site: give "site_lo", a proof of ∀ y, 0x80000000 ≤ (ρ3 z.p y).base')
            lo = a['site_lo']
            for _ in range(self.so()):
                snd, bnd, lo = f'Site.sound ({snd}) ({lo})', f'Site.bundle ({bnd})', f'Site.lo_all ({lo})'
        L.append(f'  exact ⟨{snd}, {bnd}, Frm.refl _ _⟩')
        L.append('')
        return L

    def emit_correct(self):
        a = self.a
        cuts = list(a['cuts'].keys())
        if a.get('style') == 'pre':
            L = ['theorem edges (z : Fx) (hc : Cx z) : ∀ l x, Lbl.Edge (LL z) (Post z) l x']
            for c in cuts:
                L.append(f'  | .{c}, x => e{c} z hc x')
            L += ['', f'/-- **`{a["fn"]}` on the machine.** -/', f'theorem correct : Api.{a["api"]}.Statement := by',
                  f'  {a["intro"]}', f'  have hc : Cx {a["fxmk"]} := ⟨hP⟩',
                  f'  exact Lbl.start (L := LL _ .{cuts[0]}) (x := ⟨()⟩) (run (LL _) _ (edges _ hc) .{cuts[0]} ⟨()⟩)',
                  '    ⟨entry_state hc⟩ (fun cf hat => hat.sub rfl rfl)']
            self.out += L
            return
        L = ['theorem edges (z : Fx) (hc : Cx z) : ∀ l x, Lbl.Edge (LL z) (Post z) l x']
        for c in cuts:
            L.append(f'  | .{c}, x => e{c} z hc x')
        L.append('')
        L.append(f'/-- **`{a["fn"]}` on the machine.** -/')
        L.append(f'theorem correct : Api.{a["api"]}.Statement := by')
        L.append('  intro p m v outp ra hra hres hS hB hH hoff c hc')
        L.append('  obtain ⟨vsp, gp, tp, s0, s⟩ := v')
        L.append('  have hsp := At.sp_eq hc (x := BitVec.ofNat 64 p.sp) rfl')
        L.append('  have hgp := At.gp_eq hc (x := gpV) rfl')
        L.append('  simp only at hsp hgp; subst hsp hgp')
        L.append('  revert c hc')
        L.append('  have hst := entry_state hres hS hB hH hoff')
        L.append(f'  exact Lbl.start (L := LL ⟨p, m, tp, s0, s, outp, ra⟩ .{cuts[0]}) (x := ⟨()⟩)')
        L.append(f'    (run (LL ⟨p, m, tp, s0, s, outp, ra⟩) _ (edges _ ⟨hres, hS, hB, hH, hoff, hra⟩) .{cuts[0]} ⟨()⟩)')
        L.append('    ⟨hst.1, hst.2⟩ (fun cf hat => hat.sub rfl rfl)')
        self.out += L

    # Chunking: an assembly whose edge theorems exceed CHUNK_MIN lines is written as
    # `Fn/<Mod>/Defs.lean` (everything before the edges), `Fn/<Mod>/C<k>.lean` (consecutive cuts'
    # edge theorems, about CHUNK_LINES lines each) and the umbrella `Fn/<Mod>.lean` (`edges`,
    # `correct`): Lake builds the chunks in parallel, each in a fraction of the memory, and a
    # re-check of one edge re-checks only its chunk. Names and statements are those of the
    # one-file form. `--chunk-lines N` sets CHUNK_LINES (0: always one file).
    CHUNK_LINES = 350
    CHUNK_MIN = 600

    def header(self, what):
        a = self.a
        rel = os.path.relpath(self.path, ROOT)
        return ['', f'/-! Generated by scripts/gen_asm.py from {rel}: `{a["fn"]}`\'s assembly{what}.',
                'Do not edit: change the annotation and regenerate. -/', '',
                f'namespace {a["ns"]}', ''] + a['opens'] + ['']

    def write_chunked(self, i_edges, i_correct):
        a = self.a
        base = os.path.join(self.out_dir, a['mod'])
        if os.path.isdir(base):
            for f_ in os.listdir(base):
                if f_.endswith('.lean'):
                    os.remove(os.path.join(base, f_))
        n_edge = i_correct - i_edges
        mod = f'Tom.Machine.Fn.{a["mod"]}'
        if self.chunk_lines <= 0 or n_edge <= a.get('chunk_min', self.CHUNK_MIN):
            return False
        os.makedirs(base, exist_ok=True)
        tail = ['', f'end {a["ns"]}', '']
        n_hdr = len(a['imports']) + len(self.header(''))
        defs = [f'import {i}' for i in a['imports']] + self.header(' (definitions)') + self.out[n_hdr:i_edges] + tail
        open(os.path.join(base, 'Defs.lean'), 'w').write('\n'.join(defs))
        groups, cur, n = [], [], 0
        for c, blk in self.edge_blocks:
            if cur and n + len(blk) > self.chunk_lines:
                groups.append(cur); cur, n = [], 0
            cur.append((c, blk)); n += len(blk)
        if cur:
            groups.append(cur)
        parts = []
        for k, g in enumerate(groups):
            pn = f'C{k + 1}'
            parts.append(f'{mod}.{pn}')
            body = [l for _, blk in g for l in blk]
            what = f' (cut{"s" if len(g) > 1 else ""} {", ".join(c for c, _ in g)})'
            open(os.path.join(base, f'{pn}.lean'), 'w').write(
                '\n'.join([f'import {mod}.Defs'] + self.header(what) + body + tail))
        umb = [f'import {mod}.Defs'] + [f'import {p_}' for p_ in parts] + self.header(' (umbrella)') + \
            self.out[i_correct:] + tail
        open(os.path.join(self.out_dir, f'{a["mod"]}.lean'), 'w').write('\n'.join(umb))
        print(f'gen_asm: {len(a["cuts"])} cuts -> {os.path.relpath(os.path.join(self.out_dir, a["mod"] + ".lean"), ROOT)} '
              f'+ Defs + {len(groups)} chunks')
        return True

    def run(self):
        a = self.a
        hdr = [f'import {i}' for i in a['imports']]
        self.edge_blocks = []
        self.out += hdr + self.header('')
        self.emit_static()
        self.emit_entry()
        for blk in a.get('static', []):
            if isinstance(blk, list):          # a block as its lines
                blk = '\n'.join(blk)
            self.out.append(self.lean(blk, {}))
            self.out.append('')
        self.emit_cuts()
        i_edges = len(self.out)
        self.emit_edges()
        i_correct = len(self.out)
        self.emit_correct()
        if self.write_chunked(i_edges, i_correct):
            return
        self.out += ['', f'end {a["ns"]}', '']
        fo = os.path.join(self.out_dir, f'{a["mod"]}.lean')
        open(fo, 'w').write('\n'.join(self.out))
        print(f'gen_asm: {len(a["cuts"])} cuts -> {os.path.relpath(fo, ROOT)}')


if __name__ == '__main__':
    if sys.argv[1] == '--expand':      # the annotation as the generator reads it (templates expanded)
        json.dump(load_annotation(sys.argv[2]), sys.stdout, ensure_ascii=False, indent=1)
        print()
    else:
        args = sys.argv[1:]
        out_dir, chunk = os.path.join(ROOT, 'Tom/Machine/Fn'), Gen.CHUNK_LINES
        if '--out-dir' in args:            # write elsewhere (a scratch comparison)
            i = args.index('--out-dir'); out_dir = os.path.abspath(args[i + 1]); del args[i:i + 2]
        if '--chunk-lines' in args:
            i = args.index('--chunk-lines'); chunk = int(args[i + 1]); del args[i:i + 2]
        g = Gen(args[0])
        g.out_dir, g.chunk_lines = out_dir, g.a.get('chunk_lines', chunk) if '--chunk-lines' not in sys.argv else chunk
        g.run()
