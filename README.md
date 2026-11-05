# Erdős #195, depth 2: a permutation of ℤ with no monotone 4-term AP whose difference is not divisible by 4

> **Status: PARTIAL result. This is NOT a solution of [Erdős Problem #195](https://www.erdosproblems.com/195), which is still open.** The repository proves, and formally verifies in Lean 4, the case of common differences not divisible by 4. That covers every odd difference and every difference $\equiv 2 \pmod 4$. It extends the published odd-difference result [Alex-lop/erdos-195-odd-difference](https://github.com/Alex-lop/erdos-195-odd-difference).

## The result

**Theorem.** There is an explicit bijection $E:\mathbb N\to\mathbb Z$ with no indices $i<j<k<l$ such that $E(i),E(j),E(k),E(l)$ is an arithmetic progression, increasing or decreasing, whose common difference $d$ satisfies $4\nmid d$.

Monotone 4-APs with $4\mid d$ **do** occur in $E$. For example, $4,8,12,16$ appear in this order. So the theorem does not decide #195.

**Context.** Erdős #195 asks for the largest $k$ such that every permutation of ℤ contains a monotone $k$-term AP. The answer is 3 or 4 (Davis–Entringer–Graham–Simmons; Geneson; Adenwalla). For ℕ the question is settled (B. S. Ho, arXiv:2609.12780).

## The construction

Let $P$ be the published odd-difference order: list ℤ by the key $k_4(u)$, which is $|u|$ if $u>0$ is even or $u<0$ is odd and $4|u|$ otherwise, with ties broken by value. Put:

- $Y_k = 2P(k)+1$ (the odd numbers, in the order $P$);
- $T_k = 2048\cdot 2^k$;
- for odd $Y$, the key $K_Y(z) = |2z-Y|$ if ($2z>Y$ and $z$ even) or ($2z<Y$ and $z$ odd), and $4|2z-Y|$ otherwise;
- $S_k = \{z : K_{Y_k}(z)\le T_k\}$.

These sets are nested and exhaust ℤ. For $k=0,1,2,\dots$, the enumeration $E$ lists the even numbers $2z$ with $z\in S_k\setminus S_{k-1}$ by increasing $(K_{Y_k}(z), z)$, and then the odd number $Y_k$:

```
-2, 4, 0, 2, -6, 8, -10, 12, -14, 16, -18, 20, -4, 6, -22, 24, ...   (1280 evens, then Y_0 = 1, ...)
```

The proof has three parts.

1. **Odd $d$: reflection merge.** $S_k$ is symmetric about $Y_k/2$. So the even numbers placed before each odd $y$ form a set symmetric about $y$, and no triple even, odd, even with $e+e'=2y$ is in order.
2. **$d\equiv2\pmod 4$, odd terms.** These reduce to an odd-difference AP of $P$, which the published theorem excludes.
3. **$d\equiv2\pmod 4$, even terms.** The drifting-centre key order of the evens has no odd-difference AP. The argument uses an exact margin lemma (the key about $\tfrac12$ drops by at least $\tfrac17$ of the scale somewhere along such an AP), a drift bound and a stage bound. The margin lemma is a finite case analysis, checked by `omega` in Lean. With $T_0 = 2048 \ge 1352$ no finite check of progressions is needed.

The full human proof is in [`docs/proof.md`](docs/proof.md).

## Lean formalization

| File | Contents |
| --- | --- |
| [`Challenge.lean`](Challenge.lean) | The statements to audit (Mathlib-only, proofs `sorry`). |
| [`Solution.lean`](Solution.lean) | The same statements, proved. |
| [`Erdos195Depth2/OddOrder.lean`](Erdos195Depth2/OddOrder.lean) | Verbatim copy of `Erdos195Odd/Basic.lean` from the published odd-difference repository (the order $P$ and its theorem). |
| [`Erdos195Depth2/Basic.lean`](Erdos195Depth2/Basic.lean) | The construction (`E : ℕ ≃ ℤ`) and the new proofs. |

```lean
theorem Erdos195Depth2.main_result :
    ∃ f : ℕ ≃ ℤ, ∀ i j k l : ℕ, i < j → j < k → k < l → ∀ a d : ℤ, ¬ (4 : ℤ) ∣ d →
      ¬ (f i = a ∧ f j = a + d ∧ f k = a + 2 * d ∧ f l = a + 3 * d)
```

`Erdos195Depth2.main_result_list` states the same fact in the shape of `HasMonotoneAP f 4` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/a64e959c32c270df4dd0d96d2027481f15750534/FormalConjectures/ErdosProblems/195.lean), restricted to differences not divisible by 4.

Checks run on this repository:

- Lean `v4.35.0`, Mathlib `v4.35.0`. `lake build` succeeds. The only warnings are the two `sorry`s in `Challenge.lean`.
- No `sorry`, `admit`, `native_decide`, `decide`, `implemented_by` or `axiom` in the Lean files outside `Challenge.lean` (checked with `grep`).
- Both theorems depend only on `propext`, `Classical.choice` and `Quot.sound` (`#print axioms`).
- The statements in `Challenge.lean` and `Solution.lean` elaborate to byte-identical terms under `set_option pp.all true`.
- `scripts/check-lean-sources.py` and `scripts/validate-formalization.rb` from the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate) (commit `2891de4`) pass. The scripts are not vendored here; copy them from the template to rerun them.

The repository follows the Palomar layout, with `comparator.json` and `formalization.yaml`. It has **not** been submitted to the registry.

To build:

```sh
lake exe cache get   # download Mathlib build files
lake build
```

## Use of AI

This work was produced by **Claude Opus 5.5 and Fable 5.1 (Anthropic) in Claude Code, under the direction of Alex Lopez**. The AI agents found the construction, wrote the proof and this repository, and wrote the Lean formalization.

- The informal argument was checked by three adversarial AI referees. They checked the proof, the computations and the scope, in a version with $T_0=100$ and a finite computer check.
- The version here ($T_0 = 2048$, no finite check) is checked by the Lean kernel.
- It has **not** been refereed by a human.

## License

Apache-2.0; see [LICENSE](LICENSE).
