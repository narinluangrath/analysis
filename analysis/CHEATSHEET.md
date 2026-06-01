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

## Conventions
- Proofs intentionally follow the textbook structure (comments say so); prefer faithful over golfed.
- Chapter namespaces: `Chapter9`, `Chapter10`, etc. Custom `Nat` lives in Section 2.
