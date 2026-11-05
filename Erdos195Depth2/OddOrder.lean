module

public import Mathlib.Order.OrderIsoNat
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

public section

/-!
# A permutation of `ℤ` with no monotone 4-term AP of odd common difference

Call `x : ℤ` *fast* if it is a positive even or a negative odd integer, and give it the key
`|x|` if it is fast and `4|x|` otherwise (four times the key `κ` of `docs/proof.md`). Listing `ℤ`
by key, ties broken by value, is an enumeration `enum : ℕ ≃ ℤ`. Keys are non-decreasing along it,
and keys can never be non-decreasing along a 4-term AP with odd difference (`key_not_monotone`).
-/

namespace Erdos195Odd

/-- `x` is *fast* if it is a positive even integer or a negative odd integer. -/
@[expose] def Fast (x : ℤ) : Prop := (0 < x ∧ x % 2 = 0) ∨ (x < 0 ∧ x % 2 = 1)

instance : DecidablePred Fast := fun x => by unfold Fast; infer_instance

/-- Four times the key `κ` of the write-up: `|x|` if `x` is fast and `4|x|` otherwise. -/
def key (x : ℤ) : ℤ := if Fast x then |x| else 4 * |x|

theorem key_spec (x : ℤ) :
    (x = 0 ∧ key x = 0) ∨ (0 < x ∧ x % 2 = 0 ∧ key x = x) ∨ (0 < x ∧ x % 2 = 1 ∧ key x = 4 * x) ∨
      (x < 0 ∧ x % 2 = 1 ∧ key x = -x) ∨ (x < 0 ∧ x % 2 = 0 ∧ key x = -(4 * x)) := by
  unfold key Fast
  rcases lt_trichotomy x 0 with h | h | h
  · have : |x| = -x := abs_of_neg h
    split_ifs <;> omega
  · subst h; simp
  · have : |x| = x := abs_of_pos h
    split_ifs <;> omega

/-- Lemma 1.2 of the write-up: keys cannot be non-decreasing along a 4-term AP with odd
difference. `omega` checks every sign/parity case of the hand proof. -/
theorem key_not_monotone (a d : ℤ) (hd : Odd d) :
    ¬ (key a ≤ key (a + d) ∧ key (a + d) ≤ key (a + 2 * d) ∧
        key (a + 2 * d) ≤ key (a + 3 * d)) := by
  obtain ⟨t, rfl⟩ := hd
  have h0 := key_spec a
  have h1 := key_spec (a + (2 * t + 1))
  have h2 := key_spec (a + 2 * (2 * t + 1))
  have h3 := key_spec (a + 3 * (2 * t + 1))
  omega

theorem key_bounds (x : ℤ) : 0 ≤ key x ∧ -key x ≤ x ∧ x ≤ key x := by
  have := key_spec x
  omega

/-- An injective code `ℤ → ℕ` that is monotone in `key`. Listing `ℤ` by increasing code is
listing it by `(key x, x)` in lexicographic order. -/
def code (x : ℤ) : ℕ := (key x * (key x + 1) + (x + key x)).toNat

theorem code_lt_of_key_lt {x y : ℤ} (h : key x < key y) : code x < code y := by
  obtain ⟨hx0, hx1, hx2⟩ := key_bounds x
  obtain ⟨hy0, hy1, hy2⟩ := key_bounds y
  have hm : key x * (key x + 1) + 2 * key x < key y * (key y + 1) := by nlinarith
  have hpos : 0 ≤ key x * (key x + 1) := by positivity
  unfold code
  omega

theorem code_injective : Function.Injective code := by
  intro x y h
  rcases lt_trichotomy (key x) (key y) with hk | hk | hk
  · exact absurd h (code_lt_of_key_lt hk).ne
  · obtain ⟨hx0, hx1, hx2⟩ := key_bounds x
    obtain ⟨hy0, hy1, hy2⟩ := key_bounds y
    have hpos : 0 ≤ key y * (key y + 1) := by positivity
    unfold code at h
    rw [hk] at h hx1
    omega
  · exact absurd h (code_lt_of_key_lt hk).ne'

instance : Infinite (Set.range code) :=
  (Set.infinite_range_of_injective code_injective).to_subtype

/-- The enumeration of `ℤ`: list the integers in increasing order of `code`. It begins
`0, -1, 2, -3, 1, 4, -5, 6, -7, -2, 8, -9, 10, -11, 3, 12, …`. -/
noncomputable def enum : ℕ ≃ ℤ :=
  (Nat.Subtype.orderIsoOfNat (Set.range code)).toEquiv.trans
    (Equiv.ofInjective code code_injective).symm

theorem code_enum (n : ℕ) :
    code (enum n) = (Nat.Subtype.orderIsoOfNat (Set.range code) n : ℕ) :=
  Equiv.apply_ofInjective_symm code_injective _

theorem key_enum_le {i j : ℕ} (h : i < j) : key (enum i) ≤ key (enum j) := by
  by_contra hc
  have h1 : code (enum j) < code (enum i) := code_lt_of_key_lt (lt_of_not_ge hc)
  have h2 : code (enum i) < code (enum j) := by
    rw [code_enum, code_enum]
    exact (Nat.Subtype.orderIsoOfNat (Set.range code)).strictMono h
  omega

theorem enum_no_odd_ap {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k < l) {a d : ℤ}
    (hd : Odd d) : ¬ (enum i = a ∧ enum j = a + d ∧ enum k = a + 2 * d ∧ enum l = a + 3 * d) := by
  rintro ⟨h1, h2, h3, h4⟩
  subst h1
  apply key_not_monotone _ d hd
  rw [← h2, ← h3, ← h4]
  exact ⟨key_enum_le hij, key_enum_le hjk, key_enum_le hkl⟩

theorem exists_enum_no_odd_ap :
    ∃ f : ℕ ≃ ℤ, ∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ, Odd d →
      ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d) :=
  ⟨enum, fun _ _ _ _ hij hjk hkl _ _ hd => enum_no_odd_ap hij hjk hkl hd⟩

theorem exists_enum_no_odd_ap_list :
    ∃ f : ℕ ≃ ℤ, ¬ ∃ l : List ℕ, ∃ a d : ℤ, Odd d ∧
      (l.map f = (List.range 4).map (fun n => a + n • d) ∨
        l.map f = (List.range 4).reverse.map (fun n => a + n • d)) ∧
      l.Pairwise (· < ·) := by
  refine ⟨enum, ?_⟩
  rintro ⟨l, a, d, hd, hAP, hl⟩
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨m, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
    simp [List.range_succ] at hAP
  simp at hl
  rcases hAP with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact enum_no_odd_ap hl.1.1 hl.2.1.1 hl.2.2 hd ⟨h1, h2, h3, h4⟩
  · refine enum_no_odd_ap hl.1.1 hl.2.1.1 hl.2.2 hd.neg ⟨h1, ?_, ?_, ?_⟩ <;> omega

end Erdos195Odd
