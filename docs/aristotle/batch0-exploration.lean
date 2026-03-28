/-
Aristotle Batch 0 — Exploratory API Reconnaissance
====================================================
Probing Mathlib API surface before freezing definitions.
These are NOT project theorems — they test what API patterns exist
for period semantics, iterate arithmetic, finite orbit bounds,
and tuple sorting on Aristotle's Lean 4.24.0.

Goal: learn where the hard API boundaries are, not prove route theorems.

Submission: prove_file with wait=False
Target: Aristotle (Lean 4.24.0 — syntax may differ from our 4.28.0)
-/

import Mathlib.Dynamics.PeriodicPts
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Basic

set_option maxHeartbeats 200000

open Function Fintype

/-! ### Group 1: Minimal-period semantics

Probing how Mathlib's `minimalPeriod` behaves, especially on nonperiodic
points. In a finite type, every orbit is *eventually* periodic, but NOT
necessarily periodic from time 0 (counterexample: f(0)=1, f(1)=1 — then
0 is not periodic). `minimalPeriod f x = 0` for nonperiodic x in Mathlib. -/

/-- For a bijective map on a finite type, every point IS periodic
    (bijectivity prevents the "tail" of eventual periodicity). -/
theorem isPeriodicPt_of_bijective {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hf : Bijective f) (x : α) :
    IsPeriodicPt f (minimalPeriod f x) x := by
  sorry

/-- For a bijective map on a finite type, minimalPeriod is positive. -/
theorem minimalPeriod_pos_of_bijective {α : Type*} [Fintype α] [DecidableEq α]
    [Nonempty α] (f : α → α) (hf : Bijective f) (x : α) :
    0 < minimalPeriod f x := by
  sorry

/-- Under explicit periodicity, iteration is periodic with the minimal period. -/
theorem iterate_minimalPeriod_eq {α : Type*} [DecidableEq α]
    (f : α → α) (x : α) (hx : IsPeriodicPt f (minimalPeriod f x) x) :
    f^[minimalPeriod f x] x = x := by
  sorry

/-- Under periodicity, iterate by n mod period equals iterate by n. -/
theorem iterate_mod_minimalPeriod {α : Type*} [DecidableEq α]
    (f : α → α) (x : α) (n : ℕ)
    (hx : 0 < minimalPeriod f x) :
    f^[n % minimalPeriod f x] x = f^[n] x := by
  sorry

/-! ### Group 2: Iterate arithmetic

Probing what iterate composition/decomposition lemmas exist in Mathlib.
These inform how delay embedding shift proofs will work. -/

/-- Iterate addition decomposes as sequential iteration. -/
theorem iterate_add_apply {α : Type*} (f : α → α) (m n : ℕ) (x : α) :
    f^[m + n] x = f^[m] (f^[n] x) := by
  sorry

/-- Injectivity is preserved through iteration. -/
theorem injective_iterate {α : Type*}
    (f : α → α) (hf : Injective f) (n : ℕ) :
    Injective (f^[n]) := by
  sorry

/-- If f is bijective on a finite type and f^[i] x = f^[i] y for all
    i in range k where k ≥ minimalPeriod, then f^[0] x = f^[0] y.
    (Probes whether period-cycling + range coverage closes.) -/
theorem iterate_zero_eq_of_all_eq_of_bijective {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hf : Bijective f) (x y : α) (k : ℕ)
    (hk : minimalPeriod f x ≤ k)
    (h : ∀ i, i < k → f^[i] x = f^[i] y) :
    x = y := by
  sorry

/-! ### Group 3: Finite orbit bounding

Probing bounded-orbit constructions over explicit finite index sets.
NOT using `Finset.univ` over ℕ (ill-typed). -/

/-- The image of a bounded range under iteration has card ≤ type card. -/
theorem iterate_range_image_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (x : α) (m : ℕ) :
    ((Finset.range m).image (fun i => f^[i] x)).card ≤ Fintype.card α := by
  sorry

/-- For a bijective f, minimalPeriod is bounded by card. -/
theorem minimalPeriod_le_card_of_bijective {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hf : Bijective f) (x : α) :
    minimalPeriod f x ≤ Fintype.card α := by
  sorry

/-- For any f on a finite type, the orbit length (number of distinct
    iterates in range n) is at most card. Probes Finset.card_image_le. -/
theorem iterate_image_card_le_card {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (x : α) (n : ℕ) :
    ((Finset.range n).image (fun i => f^[i] x)).card ≤ Fintype.card α := by
  sorry

/-! ### Group 4: Tuple.sort reconnaissance

Probing what `Tuple.sort` exposes on 4.24.0. Highest risk of
version incompatibility. Deliberately low ambition — testing
what elaborates, not proving deep facts. -/

/-- Tuple.sort produces a monotone result. -/
theorem tuple_sort_monotone (n : ℕ) [NeZero n]
    (v : Fin n → ℝ) :
    Monotone (Tuple.sort v) := by
  sorry

/-- Tuple.sort is a permutation of the original tuple.
    Probes whether `Tuple.sort` API gives us a permutation witness. -/
theorem tuple_sort_perm (n : ℕ)
    (v : Fin n → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, Tuple.sort v i = v (σ i) := by
  sorry
