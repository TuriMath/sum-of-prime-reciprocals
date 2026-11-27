import Theorems.SumOfPrimeReciprocalsDiverges.A

/-!
# Proof: the sum of prime reciprocals diverges (Erdős's counting argument)

Not a citation of Mathlib's `not_summable_one_div_on_primes` / `Nat.Primes.not_summable_one_div`.
Built from the smooth/rough-number counting lemmas in `Mathlib.NumberTheory.SmoothNumbers`.
-/

open Set Nat Finset
open scoped Topology

namespace TuriMath.SumOfPrimeReciprocalsDiverges

/-- Rough numbers `≤ N` (all prime factors `≥ k`) number at most `N · ∑_{k ≤ p ≤ N} 1/p`. -/
private lemma rough_card_le (N k : ℕ) :
    (roughNumbersUpTo N k).card ≤
      N * (N.succ.primesBelow \ k.primesBelow).sum (fun p ↦ (1 : ℝ) / p) := by
  simp_rw [Finset.mul_sum, mul_one_div]
  exact (Nat.cast_le.mpr <| roughNumbersUpTo_card_le N k).trans <|
    Nat.cast_sum (R := ℝ) .. ▸ Finset.sum_le_sum fun n _ ↦ Nat.cast_div_le

/-- Tail of the prime reciprocal sum, `k ≤ p ≤ 4^(π(k-1)+1)`, is at least `1/2`. -/
private lemma tail_ge_half (k : ℕ) :
    1 / 2 ≤ ∑ p ∈ (4 ^ ((k.primesBelow).card + 1)).succ.primesBelow \ k.primesBelow,
      (1 / p : ℝ) := by
  set m : ℕ := 2 ^ (k.primesBelow).card
  set N₀ : ℕ := 2 * m ^ 2 with hN₀
  let S : ℝ := ((2 * N₀).succ.primesBelow \ k.primesBelow).sum (fun p ↦ (1 / p : ℝ))
  suffices 1 / 2 ≤ S by
    convert this using 5
    rw [show 4 = 2 ^ 2 by simp, pow_right_comm]
    ring
  suffices 2 * N₀ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S by
    rwa [hN₀, ← mul_assoc, ← pow_two 2, ← mul_pow, sqrt_eq', ← sub_le_iff_le_add',
      cast_mul, cast_mul, cast_pow, cast_two,
      show (2 * (2 * m ^ 2) - m * (2 * m) : ℝ) = 2 * (2 * m ^ 2) * (1 / 2) by ring,
      mul_le_mul_iff_right₀ <| by positivity] at this
  calc (2 * N₀ : ℝ)
    _ = ((2 * N₀).smoothNumbersUpTo k).card + ((2 * N₀).roughNumbersUpTo k).card := by
        exact mod_cast ((2 * N₀).smoothNumbersUpTo_card_add_roughNumbersUpTo_card k).symm
    _ ≤ m * (2 * N₀).sqrt + ((2 * N₀).roughNumbersUpTo k).card := by
        exact mod_cast Nat.add_le_add_right ((2 * N₀).smoothNumbersUpTo_card_le k) _
    _ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S := by grw [rough_card_le]; norm_cast

theorem main : A.Statement := by
  intro hS
  have h : Summable (fun n : ℕ ↦ if n.Prime then (1 : ℝ) / n else 0) :=
    (Nat.Primes.summable_iff_summable_ite (fun n : ℕ ↦ (1 : ℝ) / n)).1 hS
  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : ℝ) ∈ 𝓝 0)
  set T : Finset ℕ := (4 ^ ((k.primesBelow).card + 1)).succ.primesBelow \ k.primesBelow
  have hTk : ∀ n ∈ T, k ≤ n ∧ n.Prime := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hn
    have hp := prime_of_mem_primesBelow h1
    refine ⟨?_, hp⟩
    by_contra hlt
    exact h2 (by simpa [primesBelow, hp] using not_le.mp hlt)
  -- finite subset of the tail has sum < 1/2
  have hlt : ∑ n ∈ T, (1 / n : ℝ) < 1 / 2 := by
    have h1 := hk (T : Set ℕ) (fun n hn => (hTk n hn).1)
    rw [Set.mem_Iio] at h1
    rw [show (∑' n : ((T : Finset ℕ) : Set ℕ), if (n : ℕ).Prime then (1 : ℝ) / (n : ℕ) else 0)
        = ∑ n ∈ T, (if n.Prime then (1 : ℝ) / n else 0) from
      Finset.tsum_subtype T (fun n : ℕ ↦ if n.Prime then (1 : ℝ) / n else 0)] at h1
    calc ∑ n ∈ T, (1 / n : ℝ) = ∑ n ∈ T, (if n.Prime then (1 : ℝ) / n else 0) :=
          Finset.sum_congr rfl fun n hn => by rw [if_pos (hTk n hn).2]
      _ < 1 / 2 := h1
  exact absurd (tail_ge_half k) (not_le.mpr hlt)

end TuriMath.SumOfPrimeReciprocalsDiverges
