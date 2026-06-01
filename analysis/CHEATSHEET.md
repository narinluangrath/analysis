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
- Defeq `if h:P then ... else ...` with a known proof: `rw [dif_pos hex]` substitutes your `hex` for the chooser; then `congr 1` + `Nat.cast_injective hex.choose_spec` to pin the witness.

## Conventions
- Proofs intentionally follow the textbook structure (comments say so); prefer faithful over golfed.
- Chapter namespaces: `Chapter9`, `Chapter10`, etc. Custom `Nat` lives in Section 2.
