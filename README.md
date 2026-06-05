# Analysis I — Lean formalization (exercise solutions fork)

A fork of **[teorth/analysis](https://github.com/teorth/analysis)** (Terence Tao's *Analysis I*, formalized in Lean 4) in which the exercises — rendered upstream as `sorry`s — are being filled in with compiler-verified proofs.

The upstream repository deliberately leaves exercises as `sorry` and does not host solutions; this fork is an independent solving effort. `lake build` is green at every commit.

**Progress: 1580 / 2083 exercises solved (76%).** Counts are *live* `sorry`s (proof-term `sorry`, excluding any in comments); “Total” is the number upstream leaves open in that section.

## Chapter 2 — Natural numbers

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 2.epilogue | epilogue: Isomorphism with the Mathlib natural numbers | 18/18 | 0 | ✅ |
| 2.2 | Addition | 20/20 | 0 | ✅ |
| 2.3 | Multiplication | 11/11 | 0 | ✅ |

## Chapter 3 — Set theory

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 3.1 | Fundamentals (of set theory) | 72/72 | 0 | ✅ |
| 3.2 | Russell's paradox | 10/10 | 0 | ✅ |
| 3.3 | Functions | 35/35 | 0 | ✅ |
| 3.4 | Images and inverse images | 30/30 | 0 | ✅ |
| 3.5 | Cartesian products | 64/64 | 0 | ✅ |
| 3.6 | Cardinality of sets | 54/54 | 0 | ✅ |

## Chapter 4 — Integers and rationals

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 4.1 | The integers | 48/48 | 0 | ✅ |
| 4.2 |  | 65/65 | 0 | ✅ |
| 4.3 | Absolute value and exponentiation | 43/43 | 0 | ✅ |
| 4.4 | gaps in the rational numbers | 9/9 | 0 | ✅ |

## Chapter 5 — Real numbers

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 5.epilogue | epilogue: Isomorphism with the Mathlib real numbers | 33/34 | 1 | 🟡 |
| 5.1 | Cauchy sequences | 11/11 | 0 | ✅ |
| 5.2 | Equivalent Cauchy sequences | 10/10 | 0 | ✅ |
| 5.3 | The construction of the real numbers | 51/51 | 0 | ✅ |
| 5.4 | Ordering the reals | 59/59 | 0 | ✅ |
| 5.5 | The least upper bound property | 19/19 | 0 | ✅ |
| 5.6 | Real exponentiation, part I | 48/48 | 0 | ✅ |

## Chapter 6 — Limits of sequences

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 6.epilogue | epilogue: Connections with Mathlib limits | 10/10 | 0 | ✅ |
| 6.1 | Convergence and limit laws | 37/37 | 0 | ✅ |
| 6.2 | The extended real number system | 24/24 | 0 | ✅ |
| 6.3 | Suprema and infima of sequences | 28/28 | 0 | ✅ |
| 6.4 | Limsup, liminf, and limit points | 56/56 | 0 | ✅ |
| 6.5 | Some standard limits | 7/7 | 0 | ✅ |
| 6.6 | Subsequences | 10/10 | 0 | ✅ |
| 6.7 | Real exponentiation, part II | 9/9 | 0 | ✅ |

## Chapter 7 — Series

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 7.1 | Finite series | 28/28 | 0 | ✅ |
| 7.2 | Infinite series | 31/31 | 0 | ✅ |
| 7.3 | Sums of non-negative numbers | 8/8 | 0 | ✅ |
| 7.4 | Rearrangement of series | 12/12 | 0 | ✅ |
| 7.5 | The root and ratio tests | 9/9 | 0 | ✅ |

## Chapter 8 — Infinite sets

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 8.1 | Countability | 32/32 | 0 | ✅ |
| 8.2 | Summation on infinite sets | 27/27 | 0 | ✅ |
| 8.3 | Uncountable sets | 9/9 | 0 | ✅ |
| 8.4 | The axiom of choice | 6/6 | 0 | ✅ |
| 8.5 | Ordered sets | 73/75 | 2 | 🟡 |

## Chapter 9 — Continuous functions on ℝ

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 9.1 | Subsets of the real line | 72/72 | 0 | ✅ |
| 9.2 | The algebra of real-valued functions | 4/4 | 0 | ✅ |
| 9.3 | Limiting values of functions | 30/32 | 2 | 🟡 |
| 9.4 | Continuous functions | 22/22 | 0 | ✅ |
| 9.5 | Left and right limits | 10/10 | 0 | ✅ |
| 9.6 | The maximum principle | 22/22 | 0 | ✅ |
| 9.7 | The intermediate value theorem | 11/11 | 0 | ✅ |
| 9.8 | Monotonic functions | 26/28 | 2 | 🟡 |
| 9.9 | Uniform continuity | 31/31 | 0 | ✅ |
| 9.10 | Limits at infinity | 2/2 | 0 | ✅ |

## Chapter 10 — Differentiation

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 10.1 | Basic definitions | 26/26 | 0 | ✅ |
| 10.2 | Local maxima, local minima, and derivatives | 15/18 | 3 | 🟡 |
| 10.3 | Monotone functions and derivatives | 7/7 | 0 | ✅ |
| 10.4 | Inverse functions and derivatives | 8/8 | 0 | ✅ |
| 10.5 | L'Hôpital's rule | 1/1 | 0 | ✅ |

## Chapter 11 — The Riemann integral

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| 11.1 | Partitions | 28/30 | 2 | 🟡 |
| 11.2 | Piecewise constant functions | 30/32 | 2 | 🟡 |
| 11.3 | Upper and lower Riemann integrals | 10/12 | 2 | 🟡 |
| 11.4 | Basic properties of the Riemann integral | 16/16 | 0 | ✅ |
| 11.5 | Riemann integrability of continuous functions | 8/10 | 2 | 🟡 |
| 11.6 | Riemann integrability of monotone functions | 3/5 | 2 | 🟡 |
| 11.8 | The Riemann-Stieltjes integral | 24/26 | 2 | 🟡 |
| 11.9 | The two fundamental theorems of calculus | 8/10 | 2 | 🟡 |
| 11.10 | Consequences of the fundamental theorems | 11/12 | 1 | 🟡 |

## Appendices

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| A.1 | Mathematical Statements | 8/8 | 0 | ✅ |
| A.5 | Nested quantifiers | 5/5 | 0 | ✅ |
| A.6 | Some examples of proofs and quantifiers | 1/1 | 0 | ✅ |
| A.7 | Equality | 1/1 | 0 | ✅ |
| B.1 | The decimal representation of natural numbers | 8/8 | 0 | ✅ |
| B.2 | The decimal representation of real numbers | 5/5 | 0 | ✅ |

## Measure Theory (Chapter 1, draft)

| Section | Title | Solved | Remaining | Status |
|---|---|---:|---:|:--:|
| MT 1.1.1 |  | 1/13 | 12 | 🟡 |
| MT 1.1.2 |  | 0/43 | 43 | ⬜ |
| MT 1.1.3 |  | 0/25 | 25 | ⬜ |
| MT 1.2.0 |  | 0/3 | 3 | ⬜ |
| MT 1.2.1 |  | 0/6 | 6 | ⬜ |
| MT 1.2.2 |  | 0/46 | 46 | ⬜ |
| MT 1.2.3 |  | 0/2 | 2 | ⬜ |
| MT 1.3.1 |  | 0/28 | 28 | ⬜ |
| MT 1.3.2 |  | 0/31 | 31 | ⬜ |
| MT 1.3.3 |  | 0/30 | 30 | ⬜ |
| MT 1.3.4 |  | 0/21 | 21 | ⬜ |
| MT 1.3.5 |  | 0/20 | 20 | ⬜ |
| MT 1.4.1 |  | 0/80 | 80 | ⬜ |
| MT 1.4.2 |  | 0/51 | 51 | ⬜ |
| MT 1.4.3 |  | 0/80 | 80 | ⬜ |

---

*Legend: ✅ section complete · 🟡 partially solved · ⬜ untouched. Generated from a `lake build`-green tree; see `scripts/count_live_sorries.py`.*
