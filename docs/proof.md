# A permutation of ℤ with no monotone 4-term AP whose difference is not divisible by 4

*Partial progress on [Erdős Problem #195](https://www.erdosproblems.com/195). The problem itself remains open.*

## Background

A **permutation of ℤ** is a bijection $E:\mathbb N\to\mathbb Z$, read as the sequence $E(0),E(1),E(2),\dots$.
A **monotone 4-term arithmetic progression** in it is a choice of positions $i<j<k<l$ with
$(E(i),E(j),E(k),E(l))=(x,x+d,x+2d,x+3d)$ for some $d\ne0$. A negative $d$ gives a decreasing progression.

Erdős Problem #195 (Erdős–Graham) asks for the largest $k$ such that every permutation of ℤ contains a monotone $k$-term progression. The answer is 3 or 4:

- every permutation contains a monotone 3-AP (Davis–Entringer–Graham–Simmons, 1977);
- Adenwalla (2024) built a permutation with no monotone 5-AP.

For ℕ the question is settled: every permutation of ℕ has a monotone 3-AP (Davis–Entringer–Graham–Simmons 1977), and B. S. Ho (arXiv:2609.12780) constructed a permutation of ℕ with no monotone 4-AP. LeSaulnier–Vijay (2011) had earlier handled odd differences on ℕ.
For ℤ, the repository [Alex-lop/erdos-195-odd-difference](https://github.com/Alex-lop/erdos-195-odd-difference) gives a permutation with no monotone 4-AP of **odd** difference. This note goes one 2-adic level deeper.

**Theorem 1.** There is an explicit permutation $E$ of ℤ with no monotone 4-term arithmetic progression whose common difference $d$ is not divisible by 4.

Theorem 1 does **not** decide #195. Monotone 4-APs with $4\mid d$ do occur in $E$. For example, $4,8,12,16$ appear in this order (at positions 1, 5, 7, 9).

## 1. Ingredients

### 1.1 The published order $P$

Call $u\ne0$ *fast* if $u>0$ is even or $u<0$ is odd. Put $k_4(u)=|u|$ if $u$ is fast and $k_4(u)=4|u|$ otherwise, so $k_4(0)=0$. Let $P(0),P(1),\dots$ list ℤ in increasing order of $(k_4(u),u)$:
$$P=0,-1,2,-3,1,4,-5,6,-7,-2,8,\dots$$
This is the published enumeration ($k_4$ is four times the key $\kappa$ used there).

**Theorem P** (published, Lean-checked). $P$ has no monotone 4-AP with odd difference. In Lean this is `Erdos195Odd.enum_no_odd_ap` for the enumeration `Erdos195Odd.enum`, which lists ℤ by $(k_4(u),u)$ and so is exactly $P$.

**(P1)** $|P(k)|\le k$ for every $k$.

*Proof.* Let $u=P(k)$. For $0\le m<|u|$ let $f_m=m$ for even $m$ and $f_m=-m$ for odd $m$ (so $f_0=0$, and $f_m$ is the fast integer of magnitude $m$ for $m\ge1$; in every case $k_4(f_m)=m$). Then $k_4(f_m)=m<|u|\le k_4(u)$. Since $P$ lists by $k_4$ first, every $f_m$ comes before $u$. These are $|u|$ distinct integers, so $k\ge|u|$. $\square$

### 1.2 Keys about a moving centre

For odd $Y$ and $z\in\mathbb Z$ put
$$K_Y(z)=\begin{cases}|2z-Y| & \text{if }(2z>Y\text{ and }z\text{ even})\text{ or }(2z<Y\text{ and }z\text{ odd}),\\ 4\,|2z-Y| & \text{otherwise.}\end{cases}$$
So $K_Y$ is the key $k_4$ re-centred at the half-integer $Y/2$, measured in the units $|2z-Y|$. Write $K^*=K_1$ for the key centred at $\tfrac12$. Always $|2z-Y|\le K_Y(z)\le4|2z-Y|$.

**Lemma 0.** For odd $Y,Y'$ and all $z$:

- (a) **Symmetry:** $K_Y(Y-z)=K_Y(z)$.
- (b) **Lipschitz:** $K_Y(z)\le K_{Y'}(z)+4|Y-Y'|$.

*Proof.*
(a) We have $2(Y-z)-Y=-(2z-Y)$, so the absolute value is the same and the side of $Y/2$ flips. Since $Y$ is odd, $Y-z$ and $z$ have opposite parities, so the factor ($1$ or $4$) is the same.
(b) Suppose $z$ lies on the same side of $Y/2$ and of $Y'/2$. Then both keys use the same factor $f\in\{1,4\}$, and $f|2z-Y|\le f|2z-Y'|+f|Y-Y'|$. Otherwise $2z$ lies between $Y$ and $Y'$, so $K_Y(z)\le4|2z-Y|\le4|Y-Y'|$. $\square$

### 1.3 The construction

Put
$$Y_k=2P(k)+1,\qquad T_k=2048\cdot 2^k,\qquad S_k=\{z\in\mathbb Z: K_{Y_k}(z)\le T_k\}.$$
Then $k\mapsto Y_k$ is a bijection from ℕ onto the odd integers, and each $S_k$ is finite. By (P1), $|Y_k-1|=2|P(k)|\le2k$.

**Lemma 0 (continued).**

- (c) **Nested:** $S_{k-1}\subseteq S_k$ for $k\ge1$.
- (d) **Exhaustive:** $z\in S_{|z|}$ for every $z$.

*Proof.*
(c) Take $z\in S_{k-1}$. By (P1), $|Y_k-Y_{k-1}|\le |Y_k-1|+|Y_{k-1}-1|\le 2k+2(k-1)=4k-2$; then (b) moves the key from $Y_{k-1}$ to $Y_k$ at a cost of at most $4(4k-2)$, and $2^{k-1}\ge k$,
$$K_{Y_k}(z)\le T_{k-1}+4(4k-2)\le T_{k-1}+2048\cdot2^{k-1}=T_k .$$
(d) Put $k=|z|$. Then $K_{Y_k}(z)\le4|2z-Y_k|\le4(2|z|+2k+1)=16k+4\le2048\cdot2^k$. $\square$

Let $s(z)=\min\{k: z\in S_k\}$ be the *stage* of $z$. By (c), $z\in S_k$ iff $s(z)\le k$.

**Definition of $E$.** For $k=0,1,2,\dots$ in turn, append

1. the even numbers $2z$ with $s(z)=k$, in increasing order of $(K_{Y_k}(z),z)$;
2. then the odd number $Y_k$.

Each block is finite, and by (d) every even number lies in exactly one block. So $E$ is a permutation of ℤ.
It begins
$$-2,\ 4,\ 0,\ 2,\ -6,\ 8,\ -10,\ 12,\ -14,\ 16,\ -18,\ 20,\ -4,\ 6,\ -22,\ 24,\ \dots$$
Block 0 consists of the $1280$ even numbers $2z$ with $K^*(z)\le2048$. Next comes $Y_0=1$, then $1280$ new even numbers about the centre $Y_1=-1$, then $Y_1$, and so on.

This is the enumeration of this project's (unpublished) research note, with $T_k=2048\cdot2^k$ instead of $100\cdot2^k$. The larger constant removes the finite computer check that the note needed (its Lemma 8); see §3.

## 2. Odd differences: the reflection merge

**Lemma 2 (reflection).** Let $y=Y_k$ be odd, and let $e$ be an even number placed before $y$. Then $2y-e$ is also placed before $y$.

*Proof.* The even numbers placed before $Y_k$ are those of blocks $0,\dots,k$, i.e. the numbers $2z$ with $z\in S_k$. If $e=2z$ with $z\in S_k$, then by Lemma 0(a) $K_{Y_k}(Y_k-z)=K_{Y_k}(z)\le T_k$, so $Y_k-z\in S_k$, and $2y-e=2(Y_k-z)$ is placed before $y$. $\square$

**Corollary.** $E$ has no monotone 4-AP with odd difference.

*Proof.* If $d$ is odd, the parities along $x,x+d,x+2d,x+3d$ alternate. So three consecutive terms $e,y,e'$ are even, odd, even with $e+e'=2y$. These are the terms $0,1,2$ if $x$ is even and $1,2,3$ if $x$ is odd. If $e$ comes before $y$, Lemma 2 puts $e'=2y-e$ before $y$ as well. So $e,y,e'$ never appear in this order. $\square$

The mechanism does not depend on the internal orders of the two parity classes. Each odd number $y$ has its set of earlier even numbers symmetric about $y$, and that kills every odd-difference progression. Splitting a permutation by parity classes is classical (Davis–Entringer–Graham–Simmons; Adenwalla). We are not aware of this exact reflection condition in the literature.

## 3. Differences $\equiv2\pmod4$

Let $d=2d'$ with $d'$ odd. All four terms of $x,x+d,x+2d,x+3d$ have the same parity.

**Odd terms.** The odd numbers appear in $E$ in the order $Y_0,Y_1,Y_2,\dots$. If $x=2u+1$, the terms are $2(u+td')+1$, so $u,u+d',u+2d',u+3d'$ would be a monotone 4-AP of $P$ with odd difference $d'$. This contradicts Theorem P.

**Even terms.** If $x=2z$, the terms are $2z_t$ with $z_t=z+td'$. It remains to prove:

**Proposition 3.** There is no AP $z_0,z_1,z_2,z_3$ with odd difference $d$ such that $2z_0,2z_1,2z_2,2z_3$ appear in $E$ in this order.

The proof uses three lemmas.

**Lemma 5 (margin).** Let $d$ be odd and let $M$ be an integer with $K^*(z_i)\le K^*(z_{i+1})+M$ for $i=0,1,2$, where $z_i=z_0+id$. Then
$$|2z_0-1|+2|d|\le7M .$$

*Proof.* Put $v_i=2z_i-1$, which is odd, and $h=2d\equiv2\pmod4$. Then $K^*(z)=|v|$ if ($v>0$ and $v\equiv3$) or ($v<0$ and $v\equiv1\pmod4$), and $K^*(z)=4|v|$ otherwise. Along the AP the residues of $v_i$ mod 4 alternate between 1 and 3. Fix the residue of $v_0$ and the signs of $v_0,\dots,v_3$; there are finitely many such patterns. Within one pattern, each $K^*(z_i)$ is a fixed linear function of $(z_0,d)$, so the hypotheses are linear inequalities in $(z_0,d,M)$, and the negated conclusion is a disjunction of at most four linear inequalities (the sign of $d$ is not always fixed by the pattern). Each of the resulting finitely many linear systems has no integer solution. This is a finite exact case analysis. In Lean it is discharged by `omega`, a decision procedure for linear integer arithmetic (`Erdos195Depth2.margin`). Two independent exact rational computations in the research notes find the sharp constant $\tfrac17$; it is approached at $v_0/|h|=-17/11$. $\square$

**Lemma 6 (comparison).** If $2z$ comes before $2z'$ in $E$, then $s(z)\le s(z')$ and
$$K^*(z)\le K^*(z')+16\,s(z').$$

*Proof.* Let $k=s(z')$. The blocks come in stage order, so $s(z)\le k$. We find $j\le k$ with $K_{Y_j}(z)\le K_{Y_j}(z')$:

- if $s(z)=k$, take $j=k$; the block order gives $K_{Y_k}(z)\le K_{Y_k}(z')$;
- if $s(z)<k$, take $j=k-1$; then $z\in S_{k-1}$ and $z'\notin S_{k-1}$, so $K_{Y_{k-1}}(z)\le T_{k-1}<K_{Y_{k-1}}(z')$.

Lemma 0(b) and $|Y_j-1|\le2j\le2k$ give $K^*(z)\le K_{Y_j}(z)+8k\le K_{Y_j}(z')+8k\le K^*(z')+16k$. $\square$

**Lemma 7 (stage bound).** If $s(z)=k\ge1$, then $T_{k-1}<4|2z-1|+8(k-1)$.

*Proof.* Since $z\notin S_{k-1}$,
$$T_{k-1}<K_{Y_{k-1}}(z)\le4|2z-Y_{k-1}|\le4|2z-1|+4|Y_{k-1}-1|\le4|2z-1|+8(k-1).\ \square$$

*Proof of Proposition 3.* Suppose $2z_0,2z_1,2z_2,2z_3$ appear in this order. Put $k=s(z_3)$ and $S=|2z_0-1|+2|d|$.

1. By Lemma 6, $s(z_1)\le s(z_2)\le k$, and $K^*(z_i)\le K^*(z_{i+1})+16k$ for $i=0,1,2$.
2. By Lemma 5 with $M=16k$, $S\le112k$. Since $S\ge1+2=3$, we get $k\ge1$.
3. We have $|2z_3-1|=|2z_0-1+6d|\le3S$. Lemma 7 applied to $z_3$ gives
$$2048\cdot2^{k-1}=T_{k-1}<4\cdot3S+8(k-1)\le1344k+8k-8<1352k .$$
4. But $2^{k-1}\ge k$, so $2048\cdot2^{k-1}\ge2048k$. This is a contradiction. $\square$

This completes the proof of Theorem 1. $\blacksquare$

**Computer assistance.** One step is machine-checked rather than written out by hand: the finite case analysis of Lemma 5. It is checked by `omega` inside Lean, so the Lean kernel checks it like every other step. Everything else above is a complete hand proof.

**On the constant.** The argument needs $T_0\ge1352$ in step 4 (because $4\cdot3\cdot7\cdot16+8=1352$). Lemma 0(c) needs only $16k-8\le C\cdot2^{k-1}$ for all $k\ge1$ (true for $C\ge12$) and Lemma 0(d) needs $16|z|+4\le C\cdot 2^{|z|}$ (true for $C\ge10$). Any $T_k=C\cdot2^k$ with $C\ge1352$ works with the same proof. With the original $C=100$, step 4 leaves the stages $k\le7$, which the research note handled by a computer check on $[-1100,1100]$ (Lemma 8 there). With $C=2048$ no computation is needed.

## 4. Formal verification

Theorem 1 is formalized in Lean 4 with Mathlib (`Erdos195Depth2.main_result` and `Erdos195Depth2.main_result_list`; see the README). The library `Erdos195Depth2/OddOrder.lean` is a verbatim copy of the published `Erdos195Odd/Basic.lean` (Theorem P, the key $k_4$ and the order $P$). The new proof is `Erdos195Depth2/Basic.lean`:

| Here | Lean |
|---|---|
| (P1) | `enum_bound` (via `natAbs_le_symm`) |
| $K_Y$, Lemma 0(a), (b) | `ckey`, `ckey_symm`, `ckey_lip` |
| Lemma 5 | `margin` (by `omega`) |
| $Y_k$, $T_k$, Lemma 0(c), (d) | `cen`, `thr`, `nested`, `exists_stage` |
| stage $s(z)$ | `stage` (`Nat.find`) |
| $E$ | `E`, the integers listed by increasing `rank` |
| Lemma 2 | `refl_rank` |
| odd terms, $d\equiv2$ | `odd_lt_of_rank_lt` with the published `enum_no_odd_ap` |
| Lemma 6 | `even_step` |
| Lemma 7 and Proposition 3 | `even_no_ap` |
| Theorem 1 | `E_no_ap`, `exists_enum_no_ap`, `exists_enum_no_ap_list` |

The Lean proof does not count predecessors. It gives every integer an injective rank in ℤ: stage first; within a stage, the even numbers by $(K_{Y_k}(z),\,2z-Y_k)$, then the odd number $Y_k$. It then enumerates the image with `Nat.Subtype.orderIsoOfNat`, as in the published repository.

## 5. Remarks (not formalized)

1. **Why it stops at $4\mid d$.** Iterating Lemma 2 would need an even part that again has nested prefixes symmetric about moving centres. In any reflection merge every prefix $S_k$ has as many even as odd elements, since reflection about a half-integer swaps parity. An earlier counting argument of this project (unpublished) then rules out exact reflection at the root of the even part. So depth 3 ($8\nmid d$) needs a different, balanced mechanism.
2. **Even differences divisible by 4 occur**, as noted above.
3. **Margin sharpness and parameter freedom.** According to exact rational computations in the research notes, the constant $\tfrac17$ in Lemma 5 is sharp, and the factor 4 in the keys can be replaced by any $\lambda>3$ (with a different margin). Neither fact is used here; only Lemma 5 as stated is used and formalized.

## Credits

The reflection merge (Lemma 2) and the drifting-centre key order of §3 were found during an AI-driven research run on Erdős #195 directed by Alex Lopez. The odd order $P$ and Theorem P are those of the published repository [Alex-lop/erdos-195-odd-difference](https://github.com/Alex-lop/erdos-195-odd-difference). The write-up, the simplification with a large constant (which removes the finite check) and the Lean formalization were produced in the same run. All of it was done by Claude Opus 5.5 and Fable 5.1 (Anthropic) in Claude Code under the direction of Alex Lopez. The informal argument has been checked by AI referees and the formal one by the Lean kernel; no human has refereed it.
