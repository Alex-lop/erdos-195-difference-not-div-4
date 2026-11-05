module

public import Erdos195Depth2

public section

/-!
# Proved solution

Comparator checks that each declaration below has exactly the statement of its counterpart in
`Challenge.lean` and uses only the permitted axioms. The proofs live in
`Erdos195Depth2/Basic.lean`, on top of the published odd-difference order copied in
`Erdos195Depth2/OddOrder.lean`.
-/

theorem Erdos195Depth2.main_result :
    ∃ f : ℕ ≃ ℤ, ∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ, ¬ (4 : ℤ) ∣ d →
      ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d) :=
  Erdos195Depth2.exists_enum_no_ap

theorem Erdos195Depth2.main_result_list :
    ∃ f : ℕ ≃ ℤ, ¬ ∃ l : List ℕ, ∃ a d : ℤ, ¬ (4 : ℤ) ∣ d ∧
      (l.map f = (List.range 4).map (fun n => a + n • d) ∨
        l.map f = (List.range 4).reverse.map (fun n => a + n • d)) ∧
      l.Pairwise (· < ·) :=
  Erdos195Depth2.exists_enum_no_ap_list
