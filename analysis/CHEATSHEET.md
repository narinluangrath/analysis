# Sorry-solving cheat sheet (Tao Analysis in Lean)

Working notes for solving `sorry`s in `analysis/Analysis/*.lean`.

## Workflow
- Build a single file fast: `lake env lean Analysis/Section_X_Y.lean` (no `lake build` needed for a quick check). Exit 0 + no `declaration uses 'sorry'` warning = clean.
- Find easy targets: `grep -rc sorry --include=*.lean Analysis | grep -v :0 | sort -t: -k2 -n`.
- Commit after each net decrease in sorrys: `git commit -m "solve N sorrys in Section_X_Y.lean"`. End message with the Co-Authored-By trailer.
- `-Dwarn.sorry=false` is set for `lake build`, but `lake env lean <file>` DOES print sorry warnings — use that to confirm.

## Tips learned
- **Instance fields**: when filling an `instance ... where` field, `#print <ClassName>` to get the EXACT field signature and binder order. The `intro` order must match the field's argument order, NOT the standalone lemma's. Example: `MulPosMono.mul_le_mul_of_nonneg_right : ∀ ⦃c⦄, 0 ≤ c → ∀ ⦃a b⦄, a ≤ b → a*c ≤ b*c` → `intro c _ a b hab`.
- The Chapter 2 `Nat` defines `≤` as `∃ d, b = a + d`; `obtain ⟨d, hd⟩ := hab` then `rw [hd, add_mul/mul_add]`.
- Mirror a sibling proof in the same file when one direction (left/right) is already done.
- **Restricted-filter limits** `atTop ⊓ 𝓟 (range f)`: rewrite with `← Filter.map_comap` (gives `map f (comap f atTop) = atTop ⊓ 𝓟 (range f)`), then `Nat.comap_cast_atTop` (`comap cast atTop = atTop`) collapses it to `map cast atTop`, then `Filter.tendsto_map'_iff` turns `Tendsto g (map f l)` into `Tendsto (g∘f) l`. Great for "sequence vs function-on-ℝ-restricted-to-ℕ" equivalences.
- `tendsto_inv_atTop_zero : Tendsto (·⁻¹) atTop (nhds 0)`; combine with `Filter.Tendsto.mono_left _ inf_le_left` for restricted filters; `simpa [one_div]` to match `1/x`.
- **IVT / continuous image of Icc**: `ContinuousOn.image_Icc (hab : a ≤ b) : f '' Icc a b = Icc (sInf ..) (sSup ..)`. `intermediate_value_Icc (hab) (hf) : Icc (f a) (f b) ⊆ f '' Icc a b`; primed version `intermediate_value_Icc'` uses `Icc (f b) (f a)` (decreasing). Fixed-point: set `g = f x - x`, apply `intermediate_value_Icc'` to get `0 ∈ g '' Icc`.
- **Monotone deriv ≥ 0**: `hderiv.hasDerivWithinAt` then `rw [hasDerivWithinAt_iff_tendsto_slope]`; bound `slope f x₀ y ≥ 0` via `slope_def_field` + `div_nonneg`/`div_nonneg_iff` (no `div_nonneg_of_nonpos_of_nonpos` lemma — use `div_nonneg_iff` and pick `Or.inr`); finish with `ge_of_tendsto` (need `NeBot` from the `ClusterPt` hyp: `haveI : (nhdsWithin x₀ (X\{x₀})).NeBot := hx₀`).
- **derivWithin = deriv** on interior of Icc: `rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]` (after `rw [interior_Icc]`). Or `hf.derivWithin huniq` / `hderiv.hasDerivWithinAt.derivWithin huniq` where `huniq : UniqueDiffWithinAt`.
- **StrictMonoOn from positive deriv**: `strictMonoOn_of_deriv_pos (convex_Icc a b) hf.continuousOn`; the `hf'` arg needs `deriv` (global) on `interior D` — convert from `derivWithin`.
- **UniqueDiffWithinAt for a set union**: `(uniqueDiffOn_Icc (by norm_num) x hmem).mono Set.subset_union_left/right`. `UniqueDiffWithinAt.mono` is monotone in the set (s ⊆ t).
- **Counterexample to "positive derivWithin ⟹ strict mono"** needs a DISCONNECTED domain (the theorem holds on intervals). Use `f = x³-3x` on `[-2,-3/2] ∪ [3/2,2]`: globally differentiable (poly), `f'=3x²-3>0` since `|x|≥3/2`, but `f(-3/2)=9/8 > f(3/2)=-9/8`. Build deriv via `HasDerivAt`: `simpa using hasDerivAt_pow 3 x`, `(hasDerivAt_id x).const_mul 3`, `.sub`.
- `Set.mem_image_of_mem` (NOT bare `mem_image_of_mem`). `Set.mem_Icc` to unpack `x ∈ Icc a b` into `a ≤ x ∧ x ≤ b`.
- **Beta reduction is finicky**: after `refine ⟨fun x => …, …⟩`, sometimes the goal/hyp is auto-beta-reduced and `dsimp only` then ERRORS with "no progress"; other times it's NOT reduced and `split_ifs`/`rw` fails to match the lambda. Don't blanket-add `dsimp only`. For a goal use `show <reduced form>` to force it; for hyps from `h x hx`, try WITHOUT dsimp first (often already reduced) and only add `dsimp only at h` if a later `rw` fails to match. `nlinarith` ring-normalizes so it tolerates unreduced lambdas.
- **`IsMinOn`/`IsMaxOn`**: `rw [isMinOn_iff]`/`isMaxOn_iff` → `∀ x ∈ s, f a ≤ f x` / `∀ x ∈ s, f x ≤ f a`. To refute existence of a max on an OPEN interval, pick a witness strictly past the candidate toward the (excluded) endpoint, e.g. `3/2 + (|x₀-3/2|+1/2)/2`, and `nlinarith` with `sq_abs`, `abs_nonneg`, and an explicit `mul_pos` of the two positive factors.
- `max M 0 + 1` is the canonical "bigger than M and ≥ 1" gadget for unboundedness proofs; `le_max_left`/`le_max_right` give the two bounds (mind which!). `1/(max M 0+1)` lands in `(0,1]`.
- **Cardinality (Chapter 8)**: `EqualCard X Y := ∃ f, Bijective f`; `LeCard X Y := ∃ f, Injective f`; `LtCard X Y := LeCard X Y ∧ ¬ EqualCard X Y`. Schröder–Bernstein = `Function.Embedding.schroeder_bernstein (hf:Injective f) (hg:Injective g) : ∃ h, Bijective h` — exactly `LeCard X Y → LeCard Y X → EqualCard X Y`. From `EqualCard X Y` (a bijection `e`) get the reverse injection via `(Equiv.ofBijective e he).symm` + `.injective`. For `LtCard` transitivity/antisymmetry, reduce `¬EqualCard`/`¬LeCard` goals to a contradiction by building both injections and applying Schröder–Bernstein. `Preorder.lt_iff_le_not_ge` field goal is `a<b ↔ a≤b ∧ ¬b≤a`.
- **Custom `Function` (Chapter 3, SetTheory.Set)**: `Function.eq_iff f g : f = g ↔ ∀ x, f x = g x` (use `rw [eq_iff]; intro x`). `comp_eval` unfolds `(g ○ f) x = g (f x)`. `inverse_eval h y x : x = (f.inverse h) y ↔ f x = y`. Inverse facts: `inverse_comp_self h x : (f.inverse h)(f x)=x`, `self_comp_inverse h y : f ((f.inverse h) y)=y`. one_to_one via `rw [one_to_one_iff]` then push hyp through `f` with `by rw [hyp]` + `rwa [self_comp_inverse, self_comp_inverse]`.
- Defeq `if h:P then ... else ...` with a known proof: `rw [dif_pos hex]` substitutes your `hex` for the chooser; then `congr 1` + `Nat.cast_injective hex.choose_spec` to pin the witness.

## Conventions
- Proofs intentionally follow the textbook structure (comments say so); prefer faithful over golfed.
- Chapter namespaces: `Chapter9`, `Chapter10`, etc. Custom `Nat` lives in Section 2.
