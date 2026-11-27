import Mathlib

/-!
# Divergence of the sum of prime reciprocals — statement A (Noether)

Source (issue #1): "The sum of the reciprocals of all prime numbers diverges;
that is, ∑_{p prime} 1/p = ∞."  (Euler 1737; Hardy & Wright Thm 19; Freek 100.)
-/

namespace TuriMath.SumOfPrimeReciprocalsDiverges.A

/-- The sum of the reciprocals of all primes diverges.

Mapping, source → Lean:
* "all prime numbers"       → index type `Nat.Primes` (the subtype `{p : ℕ // p.Prime}`):
                               the natural primes 2, 3, 5, …, each exactly once.
                               ℕ not ℤ: the source means the positive primes.
* "the reciprocals 1/p"     → `fun p : Nat.Primes => (1 : ℝ) / (p : ℝ)`, computed in ℝ
                               (not ℕ division, which would give 0).
* "the sum … diverges"      → `¬ Summable …`: the real series has no finite sum.
* "that is, ∑ 1/p = ∞"      → for nonnegative terms, not summable is the same as the
                               partial sums tending to +∞, so no separate clause is needed;
                               `Summable` is Mathlib's (unconditional) notion, which agrees
                               with ordinary convergence for nonnegative terms.
-/
def Statement : Prop :=
  ¬ Summable (fun p : Nat.Primes => (1 : ℝ) / (p : ℝ))

/-! ## Sanity section

`Statement` has no hypotheses, so there is nothing to show jointly satisfiable.
Instead we check that the summands really are the reciprocals of the primes
(not degenerate, e.g. not all zero from a bad cast). -/

example : (fun p : Nat.Primes => (1 : ℝ) / (p : ℝ)) ⟨2, Nat.prime_two⟩ = 1 / 2 := by
  norm_num

example (p : Nat.Primes) : 0 < (1 : ℝ) / (p : ℝ) := by
  have : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  positivity

end TuriMath.SumOfPrimeReciprocalsDiverges.A
