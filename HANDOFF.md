# Handoff — sorry-elimination state (as of 2026-06-04)

**50 live (non-commented) sorries remain.** Full build is green (`lake build` exit 0). Every solve this far is compiler-verified and statement-audited (no theorem statement was ever weakened). See `CHEATSHEET.md` for the full bug catalog, lemma-name tips, and the sub-sorry attack maps referenced below.

## Workflow that works
Per-file fan-out, one agent per file (never two agents on one file — write races). Standard protocol baked into each agent prompt:
1. Edit ONLY the assigned file. Never alter/weaken a theorem STATEMENT (maxHeartbeats / noncomputable / imports / private helpers are fine).
2. Verify every change: `lake env lean Analysis/<F>.lean 2>&1 | grep -vE "uses .sorry.|deprecated" | grep -E "error"` must be empty.
3. Orchestrator (not agents) commits, one file per commit, trailer `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`.
4. Audit before commit: `git diff -U0` for altered signatures + `comm -23` of HEAD-vs-current decl names for dropped/renamed (note: `git show HEAD:` path is `analysis/Analysis/<F>.lean`, repo root is the parent dir).
Live-sorry count (ignores commented ones): strip `/- -/` then count `sorry` left of `--` per line. The `sorries_over_time.csv` figure is inflated by commented sorries.

## The remaining 53, classified

### Hard-but-TRUE (worth another attempt) — ~15
- **Section_8_2 (7)** — Riemann rearrangement. ALL SIX inner sorries reduce to ONE *greedy-exhaustion lemma* (greedy `Nat.min` selection eventually captures any finite subset of A₊/A₋, ≈ `Nat.monotone_enum_of_infinite` surjectivity). Full attack recipe + enabling scaffolding (hnep/hnem, hsign_pos/neg, hbridge) is in CHEATSHEET.md under "8_2 greedy-selection core". This is the single highest-leverage target: cracking that one lemma collapses the whole file.
- **Section_7_4 (2)** — ex_7_4_4'_conv / '_sum: the 1-positive-then-2-negative rearrangement (per block j: +1/(2j+2) −1/(4j+3) −1/(4j+5)); needs from-scratch block/triple partial-sum Cauchy analysis (not abs-convergent, not simple alternating).
- **Appendix_B_2 (1)**, **Section_5_epilogue (1)** — decimal surjectivity / equivR chain.
- (DONE this wave: Section_7_5 fully cleared; Appendix_B_2 inj_nonterminating.)
- (RECLASSIFIED BUGGED this wave: all 4 of Section_9_8, and Section_11_10:517 reflection — see CHEATSHEET.)

### BUGGED (false as stated — DO NOT attempt without authorization to edit statements) — ~37
Catalogued with counterexamples in CHEATSHEET.md. Summary: 10_2(3), 10_4(3), 11_1(2), 11_2(2), 11_3(2), 11_5(2), 11_6(2 — incl. the reclassified 11_6:220 integral test, same Summable-over-ℝ defect), 11_8(2), 11_9(2 — boundary one-sided-derivative defect), 9_3(7), 9_8(2), 9_9(1), 8_5(2 — IsMin/IsMax uniqueness on general PartialOrder), 6_4(4).

## Recommended next move
Single dedicated agent on Section_8_2's greedy-exhaustion lemma (deep, multi-session-grade). If/when statement corrections are authorized, the bugged ~38 become addressable — produce a read-only corrected-statement proposal first.
