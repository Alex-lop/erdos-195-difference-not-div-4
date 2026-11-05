module

public import Mathlib.Order.OrderIsoNat
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Order.Ring.Abs

public section

/-!
# Advertised statement

Partial progress on Erdős Problem #195 (<https://www.erdosproblems.com/195>).

A *permutation of `ℤ`* is a bijection `f : ℕ ≃ ℤ`, read as the sequence `f 0, f 1, f 2, …`.
A *monotone 4-term arithmetic progression* in it is a choice of indices `i < j < k < l` with
`(f i, f j, f k, f l) = (a, a + d, a + 2d, a + 3d)` for some `d ≠ 0`; a negative `d` gives a
decreasing progression. The theorems below say that some permutation of `ℤ` has no such
progression whose common difference `d` is not divisible by 4 (such a `d` is automatically
nonzero). This covers all odd differences and all differences `≡ 2 (mod 4)`.

Erdős #195 asks for the largest `k` such that every permutation of `ℤ` has a monotone `k`-term
progression; the answer is known to be 3 or 4. These theorems do not decide it: they say
nothing about differences divisible by 4.
-/

/-- Some permutation of `ℤ` has no monotone 4-term arithmetic progression, increasing or
decreasing, whose common difference is not divisible by 4. -/
theorem Erdos195Depth2.main_result :
    ∃ f : ℕ ≃ ℤ, ∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ, ¬ (4 : ℤ) ∣ d →
      ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d) := by
  sorry

/-- The same statement in the shape of `HasMonotoneAP f 4` from google-deepmind/formal-conjectures
(`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`), restricted to common differences not
divisible by 4: no strictly increasing list of indices is mapped by `f` onto `a, a + d, a + 2d,
a + 3d`, in either order, with `4 ∤ d`. -/
theorem Erdos195Depth2.main_result_list :
    ∃ f : ℕ ≃ ℤ, ¬ ∃ l : List ℕ, ∃ a d : ℤ, ¬ (4 : ℤ) ∣ d ∧
      (l.map f = (List.range 4).map (fun n => a + n • d) ∨
        l.map f = (List.range 4).reverse.map (fun n => a + n • d)) ∧
      l.Pairwise (· < ·) := by
  sorry
