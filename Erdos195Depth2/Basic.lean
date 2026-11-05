module

public import Erdos195Depth2.OddOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public section

/-!
# A permutation of `ℤ` with no monotone 4-term AP whose difference is not divisible by 4

This file follows `docs/proof.md`.

* `Erdos195Odd.enum` (the published order `P`, copied verbatim in `Erdos195Depth2.OddOrder`)
  has no monotone 4-term AP with odd difference, and `|P k| ≤ k` (`enum_bound`).
* The odd number `Y_k = 2 P(k) + 1` (`cen k`) is the centre of stage `k`. The key of `z` about
  `Y` is `ckey Y z`; it is symmetric about `Y / 2` and `4`-Lipschitz in `Y`.
* `z` enters at the first stage `k` with `ckey (cen k) z ≤ T_k`, where `T_k = 2048 * 2 ^ k`.
  The stages are nested (`nested`).
* The enumeration `E` lists, for `k = 0, 1, 2, …`, the even numbers `2z` of stage `k` by
  increasing key (ties by value), then the odd number `Y_k`. It is built by ranking `ℤ`
  injectively in `ℤ` (`rank`) and listing the integers by increasing rank.
* Odd differences are excluded by reflection: the evens placed before `Y_k` form a set that is
  symmetric about `Y_k` (`refl_rank`). Differences `≡ 2 (mod 4)` are excluded on the odd numbers
  by the published theorem and on the even numbers by `margin` (keys about `1/2` drop by at least
  `1/7` of the scale somewhere along an odd-difference AP), `even_step` (the centre drifts by
  `O(stage)`) and the stage bound (an element of stage `k ≥ 1` has size `≳ 2^k`).
-/

namespace Erdos195Depth2

open Erdos195Odd (enum key key_spec key_bounds key_enum_le enum_no_odd_ap)

/-! ### The published order moves slowly: `|enum k| ≤ k` -/

/-- The fast integer of magnitude `m`: `m` if `m` is even, `-m` if `m` is odd. -/
def fastOf (m : ℕ) : ℤ := if m % 2 = 0 then (m : ℤ) else -(m : ℤ)

theorem key_fastOf (m : ℕ) : key (fastOf m) = m := by
  have h := key_spec (fastOf m)
  unfold fastOf at h ⊢
  split_ifs at h ⊢ <;> omega

theorem symm_lt_of_key_lt {u v : ℤ} (h : key v < key u) : enum.symm v < enum.symm u := by
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with hlt | heq
  · have := key_enum_le hlt
    simp only [Equiv.apply_symm_apply] at this
    omega
  · rw [enum.symm.injective heq] at h
    omega

/-- The fast integers of magnitudes `0, …, |u| - 1` all come before `u`. -/
theorem natAbs_le_symm (u : ℤ) : u.natAbs ≤ enum.symm u := by
  have hu := key_bounds u
  have hlt : ∀ m : Fin u.natAbs, enum.symm (fastOf m) < enum.symm u := fun m =>
    symm_lt_of_key_lt (by rw [key_fastOf]; have := m.isLt; omega)
  have := Fintype.card_le_of_injective
    (fun m : Fin u.natAbs => (⟨enum.symm (fastOf m), hlt m⟩ : Fin (enum.symm u))) (by
      intro a b hab
      have h1 : fastOf a = fastOf b := enum.symm.injective (Fin.mk.inj_iff.mp hab)
      have h2 := key_fastOf a
      have h3 := key_fastOf b
      rw [h1] at h2
      exact Fin.ext (by omega))
  simpa using this

/-- (P1) of the write-up: `|P(k)| ≤ k`. -/
theorem enum_bound (k : ℕ) : -(k : ℤ) ≤ enum k ∧ enum k ≤ k := by
  have := natAbs_le_symm (enum k)
  rw [Equiv.symm_apply_apply] at this
  omega

/-! ### Keys about a moving centre -/

/-- The key `K_Y(z)` of `z` about the half-integer centre `Y / 2`: `|2z - Y|` if `z` is fast
(right of the centre and even, or left of it and odd) and `4|2z - Y|` otherwise. -/
def ckey (Y z : ℤ) : ℤ :=
  if (Y < 2 * z ∧ z % 2 = 0) ∨ (2 * z < Y ∧ z % 2 = 1) then |2 * z - Y| else 4 * |2 * z - Y|

theorem ckey_spec (Y z : ℤ) :
    (Y < 2 * z ∧ z % 2 = 0 ∧ ckey Y z = 2 * z - Y) ∨
    (Y < 2 * z ∧ z % 2 = 1 ∧ ckey Y z = 4 * (2 * z - Y)) ∨
    (2 * z < Y ∧ z % 2 = 1 ∧ ckey Y z = Y - 2 * z) ∨
    (2 * z < Y ∧ z % 2 = 0 ∧ ckey Y z = 4 * (Y - 2 * z)) ∨
    (2 * z = Y ∧ ckey Y z = 0) := by
  unfold ckey
  rcases lt_trichotomy (2 * z) Y with h | h | h
  · have : |2 * z - Y| = -(2 * z - Y) := abs_of_neg (by linarith)
    split_ifs <;> omega
  · have : |2 * z - Y| = 0 := by rw [h, sub_self, abs_zero]
    split_ifs <;> omega
  · have : |2 * z - Y| = 2 * z - Y := abs_of_pos (by linarith)
    split_ifs <;> omega

/-- Lemma 0(a): for odd `Y` the key is symmetric about `Y / 2`. -/
theorem ckey_symm (Y z : ℤ) (hY : Y % 2 = 1) : ckey Y (Y - z) = ckey Y z := by
  have h1 := ckey_spec Y z
  have h2 := ckey_spec Y (Y - z)
  omega

/-- Lemma 0(b): `|K_Y(z) - K_{Y'}(z)| ≤ 4 |Y - Y'|`. -/
theorem ckey_lip (Y Y' z D : ℤ) (h1 : Y - Y' ≤ D) (h2 : Y' - Y ≤ D) :
    ckey Y z ≤ ckey Y' z + 4 * D := by
  have := ckey_spec Y z
  have := ckey_spec Y' z
  omega

/-- Lemma 5 (margin): along a 4-term AP with odd difference `d`, the key `K* = K_1` about `1/2`
drops somewhere by at least `(|2z - 1| + 2|d|) / 7`. Checked by `omega` over all sign and parity
cases. -/
theorem margin (z d M : ℤ) (hd : d % 2 = 1)
    (h1 : ckey 1 z ≤ ckey 1 (z + d) + M) (h2 : ckey 1 (z + d) ≤ ckey 1 (z + 2 * d) + M)
    (h3 : ckey 1 (z + 2 * d) ≤ ckey 1 (z + 3 * d) + M) :
    (2 * z - 1) + 2 * d ≤ 7 * M ∧ (2 * z - 1) - 2 * d ≤ 7 * M ∧
      (1 - 2 * z) + 2 * d ≤ 7 * M ∧ (1 - 2 * z) - 2 * d ≤ 7 * M := by
  have s0 := ckey_spec 1 z
  have s1 := ckey_spec 1 (z + d)
  have s2 := ckey_spec 1 (z + 2 * d)
  have s3 := ckey_spec 1 (z + 3 * d)
  omega

/-! ### Centres, thresholds and stages -/

/-- The centre `Y_k = 2 P(k) + 1` of stage `k`. -/
noncomputable def cen (k : ℕ) : ℤ := 2 * enum k + 1

theorem cen_bound (k : ℕ) : -(2 * k : ℤ) ≤ cen k - 1 ∧ cen k - 1 ≤ 2 * k := by
  have := enum_bound k
  unfold cen
  omega

theorem cen_symm (u : ℤ) : cen (enum.symm u) = 2 * u + 1 := by
  unfold cen
  rw [Equiv.apply_symm_apply]

/-- The threshold `T_k = 2048 * 2 ^ k`. -/
def thr (k : ℕ) : ℤ := 2048 * 2 ^ k

theorem thr_succ (k : ℕ) : thr (k + 1) = 2 * thr k := by
  unfold thr
  ring

theorem thr_ge (k : ℕ) : 2048 * ((k : ℤ) + 1) ≤ thr k := by
  have h : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h' : ((k + 1 : ℕ) : ℤ) ≤ ((2 ^ k : ℕ) : ℤ) := by exact_mod_cast h
  push_cast at h'
  unfold thr
  linarith

theorem thr_mono {j k : ℕ} (h : j < k) : 2 * thr j ≤ thr k := by
  unfold thr
  have : (2 : ℤ) ^ (j + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) h
  rw [pow_succ] at this
  linarith

/-- Lemma 0(d): every `z` lies in some `S_k = {z | K_{Y_k}(z) ≤ T_k}`. -/
theorem exists_stage (z : ℤ) : ∃ k, ckey (cen k) z ≤ thr k := by
  refine ⟨z.natAbs, ?_⟩
  have h1 := cen_bound z.natAbs
  have h2 := thr_ge z.natAbs
  have h3 := ckey_spec (cen z.natAbs) z
  omega

/-- The stage `s(z)` of `z`: the least `k` with `z ∈ S_k`. -/
noncomputable def stage (z : ℤ) : ℕ := Nat.find (exists_stage z)

theorem stage_spec (z : ℤ) : ckey (cen (stage z)) z ≤ thr (stage z) :=
  Nat.find_spec (exists_stage z)

theorem lt_of_lt_stage {z : ℤ} {k : ℕ} (h : k < stage z) : thr k < ckey (cen k) z :=
  lt_of_not_ge (Nat.find_min (exists_stage z) h)

/-- Lemma 0(c): the sets `S_k` are nested. -/
theorem nested {j k : ℕ} (hjk : j ≤ k) {z : ℤ} (h : ckey (cen j) z ≤ thr j) :
    ckey (cen k) z ≤ thr k := by
  induction hjk with
  | refl => exact h
  | @step m _ ih =>
    show ckey (cen (m + 1)) z ≤ thr (m + 1)
    have h1 := cen_bound m
    have h2 := cen_bound (m + 1)
    have h3 := ckey_lip (cen (m + 1)) (cen m) z (4 * m + 2) (by omega) (by omega)
    have h4 := thr_succ m
    have h5 := thr_ge m
    omega

theorem stage_le_iff {z : ℤ} {k : ℕ} : stage z ≤ k ↔ ckey (cen k) z ≤ thr k :=
  ⟨fun h => nested h (stage_spec z), fun h => Nat.find_min' (exists_stage z) h⟩

/-! ### The rank of an integer in `E` -/

/-- The key of `z` about the centre of its own stage. -/
noncomputable def skey (z : ℤ) : ℤ := ckey (cen (stage z)) z

theorem skey_bounds (z : ℤ) : 0 ≤ skey z ∧ skey z ≤ thr (stage z) ∧
    2 * z - cen (stage z) ≤ skey z ∧ cen (stage z) - 2 * z ≤ skey z := by
  have h1 := stage_spec z
  have h2 := ckey_spec (cen (stage z)) z
  unfold skey
  omega

/-- The rank of the even number `2z`: stage first, then key, then `2z - Y_k`. -/
noncomputable def evenCode (z : ℤ) : ℤ :=
  thr (stage z) ^ 2 + skey z * (skey z + 1) + (2 * z - cen (stage z) + skey z)

/-- The rank of the odd number `Y_k`: after every even number of stage `k`. -/
def oddCodeAt (k : ℕ) : ℤ := 2 * thr k ^ 2 + 3 * thr k + 1

theorem evenCode_bounds (z : ℤ) : thr (stage z) ^ 2 ≤ evenCode z ∧
    evenCode z ≤ 2 * thr (stage z) ^ 2 + 3 * thr (stage z) := by
  obtain ⟨h0, h1, h2, h3⟩ := skey_bounds z
  have hm : skey z * (skey z + 1) ≤ thr (stage z) * (thr (stage z) + 1) :=
    mul_le_mul h1 (by linarith) (by linarith) (by linarith)
  have hp : 0 ≤ skey z * (skey z + 1) := mul_nonneg h0 (by linarith)
  unfold evenCode
  constructor <;> nlinarith

theorem sep {j k : ℕ} (h : j < k) : 2 * thr j ^ 2 + 3 * thr j + 1 < thr k ^ 2 := by
  have h1 := thr_mono h
  have h2 := thr_ge j
  have h3 : (2048 : ℤ) ≤ thr j := by
    have : (0 : ℤ) ≤ j := by positivity
    linarith
  have h4 : 2 * thr j * (2 * thr j) ≤ thr k * thr k :=
    mul_le_mul h1 h1 (by linarith) (by linarith)
  have h5 : 2048 * thr j ≤ thr j * thr j := mul_le_mul_of_nonneg_right h3 (by linarith)
  nlinarith

theorem oddCodeAt_lt {j k : ℕ} (h : j < k) : oddCodeAt j < oddCodeAt k := by
  have := sep h
  have := thr_ge k
  have : (0 : ℤ) ≤ k := by positivity
  unfold oddCodeAt
  nlinarith

theorem evenCode_lt_oddCodeAt_iff {z : ℤ} {k : ℕ} : evenCode z < oddCodeAt k ↔ stage z ≤ k := by
  have hb := evenCode_bounds z
  unfold oddCodeAt
  constructor
  · intro h
    by_contra hc
    have := sep (not_le.mp hc)
    linarith
  · intro h
    rcases h.lt_or_eq with h | h
    · have := sep h
      have := thr_ge k
      have : (0 : ℤ) ≤ k := by positivity
      nlinarith
    · rw [h] at hb
      linarith

theorem evenCode_ne_oddCodeAt (z : ℤ) (k : ℕ) : evenCode z ≠ oddCodeAt k := by
  intro h
  rcases le_or_gt (stage z) k with hk | hk
  · exact (evenCode_lt_oddCodeAt_iff.mpr hk).ne h
  · have := sep hk
    have := (evenCode_bounds z).1
    unfold oddCodeAt at h
    linarith

theorem inner_lt {K K' w w' : ℤ} (hK' : 0 ≤ K') (hw : -K ≤ w) (hw' : w' ≤ K') (h : K' < K) :
    K' * (K' + 1) + (w' + K') < K * (K + 1) + (w + K) := by
  have : (K' + 1) * (K' + 2) ≤ K * (K + 1) := mul_le_mul (by omega) (by omega) (by omega) (by omega)
  nlinarith

theorem evenCode_lt_of_stage_lt {z z' : ℤ} (h : stage z < stage z') : evenCode z < evenCode z' := by
  have := sep h
  have := (evenCode_bounds z).2
  have := (evenCode_bounds z').1
  linarith

theorem evenCode_lt_of_skey_lt {z z' : ℤ} (hs : stage z = stage z') (h : skey z < skey z') :
    evenCode z < evenCode z' := by
  have b := skey_bounds z
  have b' := skey_bounds z'
  have := inner_lt (w := 2 * z' - cen (stage z')) (w' := 2 * z - cen (stage z)) b.1
    (by linarith) (by linarith) h
  unfold evenCode
  rw [hs] at this ⊢
  linarith

theorem stage_le_of_evenCode_lt {z z' : ℤ} (h : evenCode z < evenCode z') :
    stage z ≤ stage z' :=
  not_lt.mp fun hs => lt_asymm h (evenCode_lt_of_stage_lt hs)

theorem skey_le_of_evenCode_lt {z z' : ℤ} (h : evenCode z < evenCode z')
    (hs : stage z = stage z') : skey z ≤ skey z' :=
  not_lt.mp fun hk => lt_asymm h (evenCode_lt_of_skey_lt hs.symm hk)

theorem evenCode_injective : Function.Injective evenCode := by
  intro z z' h
  rcases lt_trichotomy (stage z) (stage z') with hs | hs | hs
  · exact absurd h (evenCode_lt_of_stage_lt hs).ne
  · rcases lt_trichotomy (skey z) (skey z') with hk | hk | hk
    · exact absurd h (evenCode_lt_of_skey_lt hs hk).ne
    · unfold evenCode at h
      rw [hs, hk] at h
      linarith
    · exact absurd h (evenCode_lt_of_skey_lt hs.symm hk).ne'
  · exact absurd h (evenCode_lt_of_stage_lt hs).ne'

/-- The rank of `x` in `E`: `2u + 1` gets `oddCodeAt (P⁻¹ u)`, `2z` gets `evenCode z`. -/
noncomputable def rank (x : ℤ) : ℤ :=
  if x % 2 = 1 then oddCodeAt (enum.symm (x / 2)) else evenCode (x / 2)

theorem rank_odd (u : ℤ) : rank (2 * u + 1) = oddCodeAt (enum.symm u) := by
  have h1 : (2 * u + 1) % 2 = 1 := by omega
  have h2 : (2 * u + 1) / 2 = u := by omega
  rw [rank, h2]
  simp [h1]

theorem rank_even (z : ℤ) : rank (2 * z) = evenCode z := by
  have h2 : (2 * z) / 2 = z := by omega
  rw [rank, h2]
  simp

theorem rank_pos (x : ℤ) : 0 < rank x := by
  unfold rank
  split_ifs
  · have := thr_ge (enum.symm (x / 2))
    have : (0 : ℤ) ≤ (enum.symm (x / 2) : ℕ) := by positivity
    unfold oddCodeAt
    nlinarith
  · have := (evenCode_bounds (x / 2)).1
    have := thr_ge (stage (x / 2))
    have : (0 : ℤ) ≤ (stage (x / 2) : ℕ) := by positivity
    nlinarith

theorem rank_injective : Function.Injective rank := by
  intro x y h
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  · obtain ⟨z, rfl⟩ : ∃ z, x = 2 * z := ⟨x / 2, by omega⟩
    obtain ⟨z', rfl⟩ : ∃ z', y = 2 * z' := ⟨y / 2, by omega⟩
    rw [rank_even, rank_even] at h
    rw [evenCode_injective h]
  · obtain ⟨z, rfl⟩ : ∃ z, x = 2 * z := ⟨x / 2, by omega⟩
    obtain ⟨u, rfl⟩ : ∃ u, y = 2 * u + 1 := ⟨y / 2, by omega⟩
    rw [rank_even, rank_odd] at h
    exact absurd h (evenCode_ne_oddCodeAt _ _)
  · obtain ⟨u, rfl⟩ : ∃ u, x = 2 * u + 1 := ⟨x / 2, by omega⟩
    obtain ⟨z, rfl⟩ : ∃ z, y = 2 * z := ⟨y / 2, by omega⟩
    rw [rank_odd, rank_even] at h
    exact absurd h.symm (evenCode_ne_oddCodeAt _ _)
  · obtain ⟨u, rfl⟩ : ∃ u, x = 2 * u + 1 := ⟨x / 2, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, y = 2 * v + 1 := ⟨y / 2, by omega⟩
    rw [rank_odd, rank_odd] at h
    have : enum.symm u = enum.symm v := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · exact (oddCodeAt_lt hl).ne h
      · exact (oddCodeAt_lt hl).ne' h
    rw [enum.symm.injective this]

/-! ### The enumeration `E` -/

/-- The rank as a natural number. -/
noncomputable def rankN (x : ℤ) : ℕ := (rank x).toNat

theorem rankN_injective : Function.Injective rankN := by
  intro x y h
  have hx := rank_pos x
  have hy := rank_pos y
  unfold rankN at h
  exact rank_injective (by omega)

instance : Infinite (Set.range rankN) :=
  (Set.infinite_range_of_injective rankN_injective).to_subtype

/-- The enumeration `E` of `ℤ`: list the integers by increasing rank. -/
noncomputable def E : ℕ ≃ ℤ :=
  (Nat.Subtype.orderIsoOfNat (Set.range rankN)).toEquiv.trans
    (Equiv.ofInjective rankN rankN_injective).symm

theorem rankN_E (n : ℕ) :
    rankN (E n) = (Nat.Subtype.orderIsoOfNat (Set.range rankN) n : ℕ) :=
  Equiv.apply_ofInjective_symm rankN_injective _

theorem rank_E_lt {i j : ℕ} (h : i < j) : rank (E i) < rank (E j) := by
  have h2 : rankN (E i) < rankN (E j) := by
    rw [rankN_E, rankN_E]
    exact (Nat.Subtype.orderIsoOfNat (Set.range rankN)).strictMono h
  have := rank_pos (E i)
  have := rank_pos (E j)
  unfold rankN at h2
  omega

/-! ### The three cases of the proof -/

/-- Lemma 2(1), reflection: the even numbers placed before `Y_k = 2u + 1` form a set that is
symmetric about `Y_k`. -/
theorem refl_rank {u z : ℤ} (h : rank (2 * z) < rank (2 * u + 1)) :
    rank (2 * (2 * u + 1 - z)) < rank (2 * u + 1) := by
  rw [rank_even, rank_odd, evenCode_lt_oddCodeAt_iff, stage_le_iff, cen_symm] at h ⊢
  rwa [ckey_symm (2 * u + 1) z (by omega)]

/-- The odd numbers appear in the order `P`. -/
theorem odd_lt_of_rank_lt {u v : ℤ} (h : rank (2 * u + 1) < rank (2 * v + 1)) :
    enum.symm u < enum.symm v := by
  rw [rank_odd, rank_odd] at h
  by_contra hc
  rcases (not_lt.mp hc).lt_or_eq with hc | hc
  · exact lt_asymm h (oddCodeAt_lt hc)
  · rw [hc] at h
    exact lt_irrefl _ h

/-- Lemma 6 (comparison): if `2z` comes before `2z'`, then `stage z ≤ stage z'` and
`K*(z) ≤ K*(z') + 16 stage(z')`. -/
theorem even_step {z z' : ℤ} (h : rank (2 * z) < rank (2 * z')) :
    stage z ≤ stage z' ∧ ckey 1 z ≤ ckey 1 z' + 16 * stage z' := by
  rw [rank_even, rank_even] at h
  have hs := stage_le_of_evenCode_lt h
  refine ⟨hs, ?_⟩
  obtain ⟨j, hj, hjk⟩ : ∃ j, j ≤ stage z' ∧ ckey (cen j) z ≤ ckey (cen j) z' := by
    rcases hs.lt_or_eq with hlt | heq
    · obtain ⟨m, hm⟩ : ∃ m, stage z' = m + 1 := ⟨stage z' - 1, by omega⟩
      refine ⟨m, by omega, ?_⟩
      have h1 : ckey (cen m) z ≤ thr m := stage_le_iff.mp (by omega)
      have h2 : thr m < ckey (cen m) z' := lt_of_lt_stage (by omega)
      linarith
    · refine ⟨stage z', le_refl _, ?_⟩
      have := skey_le_of_evenCode_lt h heq
      unfold skey at this
      rwa [heq] at this
  have hb := cen_bound j
  have l1 := ckey_lip 1 (cen j) z (2 * j) (by omega) (by omega)
  have l2 := ckey_lip (cen j) 1 z' (2 * j) (by omega) (by omega)
  have : (j : ℤ) ≤ stage z' := by exact_mod_cast hj
  linarith

/-- Proposition 3 with Lemma 7: the even numbers contain no ordered 4-term AP `2z, 2z + 2d, …`
with `d` odd. -/
theorem even_no_ap {z d : ℤ} (hd : d % 2 = 1) (c1 : rank (2 * z) < rank (2 * (z + d)))
    (c2 : rank (2 * (z + d)) < rank (2 * (z + 2 * d)))
    (c3 : rank (2 * (z + 2 * d)) < rank (2 * (z + 3 * d))) : False := by
  have e1 := even_step c1
  have e2 := even_step c2
  have e3 := even_step c3
  have s1 : (stage (z + d) : ℤ) ≤ stage (z + 3 * d) := by exact_mod_cast e2.1.trans e3.1
  have s2 : (stage (z + 2 * d) : ℤ) ≤ stage (z + 3 * d) := by exact_mod_cast e3.1
  have m := margin z d (16 * stage (z + 3 * d)) hd (by linarith [e1.2]) (by linarith [e2.2])
    (by linarith [e3.2])
  obtain ⟨k, hk⟩ : ∃ k, stage (z + 3 * d) = k := ⟨_, rfl⟩
  rw [hk] at m
  rcases k with _ | m'
  · push_cast at m
    omega
  · have l7 := lt_of_lt_stage (z := z + 3 * d) (k := m') (by omega)
    have cb := cen_bound m'
    have sp := ckey_spec (cen m') (z + 3 * d)
    have tg := thr_ge m'
    push_cast at m
    omega

/-- No four indices `i < j < k < l` map to an AP whose difference is not divisible by 4. -/
theorem E_no_ap {i j k l : ℕ} (hij : i < j) (hjk : j < k) (hkl : k < l) {a d : ℤ}
    (hd : ¬ (4 : ℤ) ∣ d) : ¬ (E i = a ∧ E j = a + d ∧ E k = a + 2 * d ∧ E l = a + 3 * d) := by
  rintro ⟨h1, h2, h3, h4⟩
  have c1 := rank_E_lt hij
  have c2 := rank_E_lt hjk
  have c3 := rank_E_lt hkl
  rw [h1, h2] at c1
  rw [h2, h3] at c2
  rw [h3, h4] at c3
  rcases Int.emod_two_eq_zero_or_one d with hd2 | hd2
  · -- `d ≡ 2 (mod 4)`: all four terms have the same parity
    obtain ⟨d', rfl⟩ : ∃ d', d = 2 * d' := ⟨d / 2, by omega⟩
    have hd' : d' % 2 = 1 := by omega
    rcases Int.emod_two_eq_zero_or_one a with ha | ha
    · obtain ⟨z, rfl⟩ : ∃ z, a = 2 * z := ⟨a / 2, by omega⟩
      exact even_no_ap hd' (by convert c1 using 2; ring) (by convert c2 using 2 <;> ring)
        (by convert c3 using 2 <;> ring)
    · obtain ⟨u, rfl⟩ : ∃ u, a = 2 * u + 1 := ⟨a / 2, by omega⟩
      have o1 := odd_lt_of_rank_lt (u := u) (v := u + d') (by convert c1 using 2; ring)
      have o2 := odd_lt_of_rank_lt (u := u + d') (v := u + 2 * d')
        (by convert c2 using 2 <;> ring)
      have o3 := odd_lt_of_rank_lt (u := u + 2 * d') (v := u + 3 * d')
        (by convert c3 using 2 <;> ring)
      exact enum_no_odd_ap o1 o2 o3 (Int.odd_iff.mpr hd')
        ⟨Equiv.apply_symm_apply _ _, Equiv.apply_symm_apply _ _, Equiv.apply_symm_apply _ _,
          Equiv.apply_symm_apply _ _⟩
  · -- `d` odd: an even term, an odd term and the reflected even term would be in order
    rcases Int.emod_two_eq_zero_or_one a with ha | ha
    · obtain ⟨z, hz⟩ : ∃ z, a = 2 * z := ⟨a / 2, by omega⟩
      obtain ⟨u, hu⟩ : ∃ u, a + d = 2 * u + 1 := ⟨(a + d) / 2, by omega⟩
      have r := refl_rank (u := u) (z := z) (by rw [← hz, ← hu]; exact c1)
      rw [show 2 * (2 * u + 1 - z) = a + 2 * d by omega, ← hu] at r
      exact lt_asymm c2 r
    · obtain ⟨z, hz⟩ : ∃ z, a + d = 2 * z := ⟨(a + d) / 2, by omega⟩
      obtain ⟨u, hu⟩ : ∃ u, a + 2 * d = 2 * u + 1 := ⟨(a + 2 * d) / 2, by omega⟩
      have r := refl_rank (u := u) (z := z) (by rw [← hz, ← hu]; exact c2)
      rw [show 2 * (2 * u + 1 - z) = a + 3 * d by omega, ← hu] at r
      exact lt_asymm c3 r

theorem exists_enum_no_ap :
    ∃ f : ℕ ≃ ℤ, ∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ, ¬ (4 : ℤ) ∣ d →
      ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d) :=
  ⟨E, fun _ _ _ _ hij hjk hkl _ _ hd => E_no_ap hij hjk hkl hd⟩

theorem exists_enum_no_ap_list :
    ∃ f : ℕ ≃ ℤ, ¬ ∃ l : List ℕ, ∃ a d : ℤ, ¬ (4 : ℤ) ∣ d ∧
      (l.map f = (List.range 4).map (fun n => a + n • d) ∨
        l.map f = (List.range 4).reverse.map (fun n => a + n • d)) ∧
      l.Pairwise (· < ·) := by
  refine ⟨E, ?_⟩
  rintro ⟨l, a, d, hd, hAP, hl⟩
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | ⟨m, _ | ⟨_, _⟩⟩⟩⟩⟩ <;>
    simp [List.range_succ] at hAP
  simp at hl
  rcases hAP with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact E_no_ap hl.1.1 hl.2.1.1 hl.2.2 hd ⟨h1, h2, h3, h4⟩
  · refine E_no_ap hl.1.1 hl.2.1.1 hl.2.2 (d := -d) (by omega) ⟨h1, ?_, ?_, ?_⟩ <;> omega

end Erdos195Depth2
