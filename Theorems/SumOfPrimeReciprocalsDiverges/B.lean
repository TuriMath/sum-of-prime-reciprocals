import Mathlib

/-!
# Divergence of the sum of prime reciprocals — statement B (Gauss)

Source (issue TuriMath/sum-of-prime-reciprocals#1, quoted exactly):
> The sum of the reciprocals of all prime numbers diverges; that is, ∑_{p prime} 1/p = ∞.

Elementary phrasing chosen: the partial sums over primes below `N` exceed every real bound.

Mapping, source → Lean:
* "prime numbers"                  → `p : ℕ` with `Nat.Prime p` (the natural primes 2, 3, 5, …)
* "the reciprocals"                → `(1 : ℝ) / p`, real division
* "the sum … of all prime numbers" → partial sums `∑ p ∈ (Finset.range N).filter Nat.Prime, 1 / p`
                                     over all primes `p < N`, for every cut-off `N`
* "diverges; … = ∞"                → for every real bound `M` some partial sum exceeds `M`
                                     (positive terms, so the partial sums are increasing and
                                     unbounded means they tend to `+∞`)
-/

namespace TuriMath.SumOfPrimeReciprocalsDiverges.B

/-- Partial sum of `1/p` over the primes `p < N`, as a real number. -/
noncomputable def primeRecipSum (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range N).filter Nat.Prime, (1 : ℝ) / p

/-- The sum of the reciprocals of the primes diverges: its partial sums are unbounded above. -/
def Statement : Prop :=
  ∀ M : ℝ, ∃ N : ℕ, M < primeRecipSum N

/-! ## Sanity section

The statement has no hypotheses, so there is nothing that must be simultaneously satisfiable.
Instead we check the partial sums on small concrete cases, to confirm `primeRecipSum`
is the sum we mean (only primes, reciprocals, cut-off strict).
-/

/-- Primes below 6 are 2, 3, 5. -/
example : (Finset.range 6).filter Nat.Prime = {2, 3, 5} := by decide

/-- For N = 6: 1/2 + 1/3 + 1/5 = 31/30. -/
example : primeRecipSum 6 = 31 / 30 := by
  have h : (Finset.range 6).filter Nat.Prime = {2, 3, 5} := by decide
  rw [primeRecipSum, h]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- For N = 0, 1, 2 there are no primes below N, so the sum is 0 (cut-off is strict). -/
example : primeRecipSum 2 = 0 := by
  have h : (Finset.range 2).filter Nat.Prime = ∅ := by decide
  rw [primeRecipSum, h, Finset.sum_empty]

/-- The bound M = 1 is beaten at N = 6, since 31/30 > 1: one instance of the statement. -/
example : ∃ N : ℕ, (1 : ℝ) < primeRecipSum N := by
  refine ⟨6, ?_⟩
  have h : (Finset.range 6).filter Nat.Prime = {2, 3, 5} := by decide
  rw [primeRecipSum, h]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

/-- Composites are excluded: 4 contributes nothing (primes below 5 are just 2 and 3). -/
example : primeRecipSum 5 = 5 / 6 := by
  have h : (Finset.range 5).filter Nat.Prime = {2, 3} := by decide
  rw [primeRecipSum, h]
  norm_num [Finset.sum_insert, Finset.sum_singleton]

end TuriMath.SumOfPrimeReciprocalsDiverges.B
