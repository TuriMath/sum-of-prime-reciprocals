import Theorems.SumOfPrimeReciprocalsDiverges.A
import Theorems.SumOfPrimeReciprocalsDiverges.B

/-!
# Equivalence of statements A and B

A: the series `1/p` over the subtype `Nat.Primes` is not summable.
B: the partial sums over primes `< N` are unbounded above.
Matched directly: for nonnegative terms, summable ⇔ finite partial sums bounded.
-/

namespace TuriMath.SumOfPrimeReciprocalsDiverges

/-- Partial sum over primes `< N` equals the finset sum over the subtype. -/
private lemma partial_eq (N : ℕ) :
    B.primeRecipSum N =
      ∑ p ∈ (Finset.range N).subtype Nat.Prime, (1 : ℝ) / ((p : ℕ) : ℝ) := by
  unfold B.primeRecipSum
  rw [Finset.sum_subtype_eq_sum_filter (fun n : ℕ => (1 : ℝ) / (n : ℝ))]

theorem equiv : A.Statement ↔ B.Statement := by
  constructor
  · intro hA M
    by_contra hM
    simp only [not_exists, not_lt] at hM
    apply hA
    refine summable_of_sum_le (c := max M 0)
      (fun p => by positivity) (fun s => ?_)
    -- bound by the partial sum at N = (sup of s) + 1
    set N := s.sup (fun p : Nat.Primes => (p : ℕ)) + 1 with hN
    have hsub : s ⊆ (Finset.range N).subtype Nat.Prime := by
      intro p hp
      refine Finset.mem_subtype.2 (Finset.mem_range.2 ?_)
      rw [hN]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp)
    calc ∑ p ∈ s, (1 : ℝ) / ((p : ℕ) : ℝ)
        ≤ ∑ p ∈ (Finset.range N).subtype Nat.Prime, (1 : ℝ) / ((p : ℕ) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by
            have : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
            positivity)
      _ = B.primeRecipSum N := (partial_eq N).symm
      _ ≤ M := hM N
      _ ≤ max M 0 := le_max_left _ _
  · intro hB hS
    obtain ⟨N, hN⟩ := hB (∑' p : Nat.Primes, (1 : ℝ) / ((p : ℕ) : ℝ))
    rw [partial_eq] at hN
    exact absurd (hS.sum_le_tsum _ (fun p _ => by
      have : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
      positivity)) (not_le.mpr hN)

end TuriMath.SumOfPrimeReciprocalsDiverges
