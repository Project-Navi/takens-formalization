# Summary of changes
All three theorems in the ordinal pattern file have been proved:

1. **`ordPat_of_strictMono`** — If `f : Fin d → ℝ` is strictly monotone, then the identity permutation is its ordinal pattern. The proof simply observes that `f ∘ Equiv.refl = f`.

2. **`ordPat_of_strictAnti`** — If `f` is strictly antitone, then the reversal permutation `σ i = ⟨d-1-i, _⟩` is its ordinal pattern. Constructed via `Equiv.ofBijective` with the reversal map shown to be a bijection.

3. **`ordPat_eq_iff_order_eq`** — Two injective functions have the same ordinal pattern iff they induce the same ordering on indices. The backward direction is direct; the forward direction constructs a sorting permutation using `Finset.orderEmbOfFin`.

**Note:** The file was renamed from `batch1-ordinal-depth.lean` to `Batch1OrdinalDepth.lean` (and the lakefile updated) because the hyphenated module name caused Lake build errors. Both files are present in the project. The lakefile references `Batch1OrdinalDepth` as the build target.