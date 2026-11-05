module

public import Solution
public import Mathlib.Logic.Equiv.Nat

/-!
# Independent fidelity audit of `Erdos195Depth2.main_result{,_list}` (audit file, not part of the formalization)

The three definitions in the public section below are verbatim copies (docstrings included) of
formal-conjectures commit 5d8b04d3d41b745cc3f2f3cdd5ed04b60c500983,
`FormalConjecturesForMathlib/Combinatorics/AP/Basic.lean`, pasted at the root namespace exactly as
there (formal-conjectures is not imported, so nothing clashes). `HasMonotoneAPNot4` is FC's
`HasMonotoneAP` with `IsAPOfLength` inlined and the single conjunct `¬ (4 : ℤ) ∣ d` added.
-/

@[expose] public section

variable {α : Type*} [AddCommMonoid α]

/--
A list version of `Set.IsAPOfLengthWith`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLengthWith (s : List α) (l : ℕ) (a d : α) : Prop :=
  s = (List.range l).map (fun n ↦ a + n • d) ∨ s = (List.range l).reverse.map (fun n ↦ a + n • d)

/--
A list version of `Set.IsAPOfLength`. Useful when order preservation is required, for example
when considering images under arbitrary functions.
-/
def List.IsAPOfLength (s : List α) (l : ℕ) : Prop :=
  ∃ a d : α, s.IsAPOfLengthWith l a d

/--
A function `f : β → α` has a monotone `k`-term arithmetic progression if there exists a choice
of indices `b 1 < b 2 < ... < b k` such that the subsequence `f (b i)` forms an increasing or
decreasing arithmetic progression of length `k`.
-/
def HasMonotoneAP {β : Type*} [Preorder β] (f : β → α) (k : ℕ) : Prop :=
  ∃ l : List β, (l.map f).IsAPOfLength k ∧ l.Pairwise (· < ·)

end

/-- FC's `HasMonotoneAP f k`, restricted to common differences not divisible by 4. -/
def HasMonotoneAPNot4 {β : Type*} [Preorder β] (f : β → ℤ) (k : ℕ) : Prop :=
  ∃ l : List β, (∃ a d : ℤ, ¬ (4 : ℤ) ∣ d ∧ (l.map f).IsAPOfLengthWith k a d) ∧ l.Pairwise (· < ·)

/-- (1) The advertised result in FC's vocabulary, from `main_result_list` in two lines: the FC
predicate is accepted by plain term-mode unfolding. -/
theorem fc_form : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAPNot4 f 4 := by
  obtain ⟨f, hf⟩ := Erdos195Depth2.main_result_list
  exact ⟨f, fun ⟨l, ⟨a, d, hd, hAP⟩, hl⟩ => hf ⟨l, a, d, hd, hAP, hl⟩⟩

/-- (2) For every `f`, the body of `main_result_list` is exactly `¬ HasMonotoneAPNot4 f 4`. -/
theorem list_iff (f : ℕ ≃ ℤ) :
    (¬ ∃ l : List ℕ, ∃ a d : ℤ, ¬ (4 : ℤ) ∣ d ∧
      (l.map f = (List.range 4).map (fun n => a + n • d) ∨
        l.map f = (List.range 4).reverse.map (fun n => a + n • d)) ∧
      l.Pairwise (· < ·)) ↔ ¬ HasMonotoneAPNot4 f 4 :=
  ⟨fun h ⟨l, ⟨a, d, hd, hAP⟩, hl⟩ => h ⟨l, a, d, hd, hAP, hl⟩,
   fun h ⟨l, a, d, hd, hAP, hl⟩ => h ⟨l, ⟨a, d, hd, hAP⟩, hl⟩⟩

/-- (3) For every `f`, the body of `main_result` (four indices) is also `¬ HasMonotoneAPNot4 f 4`. -/
theorem index_iff (f : ℕ → ℤ) :
    (∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ, ¬ (4 : ℤ) ∣ d →
      ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d)) ↔
    ¬ HasMonotoneAPNot4 f 4 := by
  constructor
  · rintro H ⟨l, ⟨a, d, hd, hAP⟩, hl⟩
    rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨m, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
      simp [List.IsAPOfLengthWith, List.range_succ] at hAP
    simp at hl
    rcases hAP with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact H i j k m hl.1.1 hl.2.1.1 hl.2.2 a d hd ⟨h1, h2, h3, h4⟩
    · refine H i j k m hl.1.1 hl.2.1.1 hl.2.2 _ (-d) (by omega) ⟨h1, ?_, ?_, ?_⟩ <;> omega
  · rintro H i j k l hij hjk hkl a d hd ⟨h1, h2, h3, h4⟩
    refine H ⟨[i, j, k, l], ⟨a, d, hd, Or.inl ?_⟩, ?_⟩
    · simp [List.range_succ, h1, h2, h3, h4]
    · simp
      omega

/-- (2') The same FC form, derived from the four-index `main_result` instead. -/
theorem fc_form' : ∃ f : ℕ ≃ ℤ, ¬ HasMonotoneAPNot4 f 4 := by
  obtain ⟨f, hf⟩ := Erdos195Depth2.main_result
  exact ⟨f, (index_iff f).mp hf⟩

/-- (4) It is a genuine restriction of FC's predicate, and the two pieces cover it. -/
theorem restrict_split {β : Type*} [Preorder β] (f : β → ℤ) (k : ℕ) :
    HasMonotoneAP f k ↔ HasMonotoneAPNot4 f k ∨
      ∃ l : List β, (∃ a d : ℤ, (4 : ℤ) ∣ d ∧ (l.map f).IsAPOfLengthWith k a d) ∧
        l.Pairwise (· < ·) := by
  constructor
  · rintro ⟨l, ⟨a, d, h⟩, hl⟩
    by_cases hd : (4 : ℤ) ∣ d
    · exact Or.inr ⟨l, ⟨a, d, hd, h⟩, hl⟩
    · exact Or.inl ⟨l, ⟨a, d, hd, h⟩, hl⟩
  · rintro (⟨l, ⟨a, d, _, h⟩, hl⟩ | ⟨l, ⟨a, d, _, h⟩, hl⟩) <;> exact ⟨l, ⟨a, d, h⟩, hl⟩

/-- (5) The restriction is well defined on the list: the difference is determined up to sign,
so `¬ 4 ∣ d` does not depend on which witness `(a, d)` is chosen. -/
theorem diff_determined (s : List ℤ) (a d a' d' : ℤ) (h : s.IsAPOfLengthWith 4 a d)
    (h' : s.IsAPOfLengthWith 4 a' d') : d' = d ∨ d' = -d := by
  unfold List.IsAPOfLengthWith at h h'
  rcases h with rfl | rfl <;> rcases h' with h' | h' <;> simp [List.range_succ] at h' <;> omega

/-- (6) Non-vacuity: some permutation of `ℤ` does have such a progression (Mathlib's
`intEquivNat.symm` sends `0, 2, 4, 6` to `0, 1, 2, 3`), so the theorem is not trivially true. -/
theorem nonvacuous : ∃ f : ℕ ≃ ℤ, HasMonotoneAPNot4 f 4 :=
  ⟨Equiv.intEquivNat.symm, [0, 2, 4, 6], ⟨0, 1, by omega, Or.inl (by decide)⟩, by decide⟩

#print axioms fc_form
#print axioms fc_form'
#print axioms list_iff
#print axioms index_iff
#print axioms restrict_split
#print axioms diff_determined
#print axioms nonvacuous
