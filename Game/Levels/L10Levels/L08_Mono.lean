import Game.Levels.L10Levels.L07_Order

World "Lecture10"
Level 3
Title "Subsequences"


Introduction "
# Level 3: Subsequence Theorem

A **subsequence** is what you get when you drop out some terms from a sequence and slide everyone left.

**Two Perspectives on Subsequences:**

Most textbooks write $a_{\\sigma(n)}$ and call this \"the subsequence of `a`.\" But we prefer to think of **`σ` itself as the subsequence**—it's the function `σ : ℕ → ℕ` that tells us which terms of `a` to keep. When people use the word \"of\" in mathematics, it implies multiplication, which in the case of functions means composition. So the words \"subsequence of a sequence\" should mean the composition `a ∘ σ` of a sequence `a` with a \"subsequence\" `σ`.

**The Geometric Picture:**

Imagine the graph of `a n`. To form a subsequence:
1. Drop out some terms (say, keep only positions 0, 2, 5, 7, 11, ...)
2. Slide everyone left so every index has a value
3. The new sequence is indexed 0, 1, 2, 3, 4, ...

The function `σ` encodes this relabeling:
- `σ(0) = 0` (keep term 0)
- `σ(1) = 2` (skip term 1, keep term 2)
- `σ(2) = 5` (skip terms 3,4, keep term 5)
- etc.

**Definition: `Subseq σ`**

A function `σ : ℕ → ℕ` is a subsequence if it's **strictly monotone increasing**:
```
∀ i j, i < j → σ(i) < σ(j)
```

This ensures we preserve the original ordering—we can't rearrange terms, only delete some!

**Key Lemma: `SubseqGe`**

If `σ` is a subsequence, then `n ≤ σ(n)` for all `n`.

Intuition: as you drop terms and relabel, indices can only \"spread out,\" never compress. The new index `n` corresponds to some original index `σ(n) ≥ n`. (You already proved this in Problem Set 8, Exercise 4.)

**The Theorem:** If `a n → L` and `σ` is a subsequence, then `(a ∘ σ) n → L`.

Translation: **every subsequence of a convergent sequence converges to the same limit**.

**Proof Strategy:**

This one is surprisingly simple! Given `ε > 0`:
- Use convergence of `a` to find `N` such that `|a m - L| < ε` for all `m ≥ N`
- For any `n ≥ N`, note that `σ(n) ≥ n ≥ N` (by `SubseqGe`)
- Therefore `|a(σ(n)) - L| < ε`

Done! The same `N` works for both the sequence and all its subsequences.

**Powerful Consequence:**

If a sequence has two subsequences converging to **different limits**, then the sequence itself **does not converge**! This gives us a new way to prove divergence. (See Lecture 10 Exercises.)

"

/-- `(σ : ℕ → ℕ) := ∀ i j, i < j → σ i < σ j`

A sequence `σ : ℕ → ℕ` is a *subsequence* if `∀ i j, i < j → σ (i) < σ (j)`. -/
DefinitionDoc Subseq as "Subseq"

NewDefinition Subseq

def Subseq (σ : ℕ → ℕ) : Prop :=
  ∀ i j, i < j → σ i < σ j

/--
If a sequence `a` converges to `L` and `σ` is a subsequence, then `a ∘ σ` also converges to `L`.
-/
TheoremDoc SubseqConv as "SubseqConv" in "Theorems"

/-- Prove this
-/
Statement SubseqConv (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (σ : ℕ → ℕ) (hσ : Subseq σ) :
    SeqLim (a ∘ σ) L := by
intro ε hε
choose N hN using ha ε hε
use N
intro n hn
have f1 : n ≤ σ n := by apply SubseqGe hσ n
have f2 : N ≤ σ n := by linarith [f1, hn]
specialize hN (σ n) f2
apply hN

Conclusion "
Beautiful! That was remarkably simple for such a powerful theorem.

**Why This Proof Works:**

The key insight is that subsequences can only \"spread out\" indices, never compress them. Since `σ(n) ≥ n` always, if `a` is eventually within `ε` of `L` (for all indices ≥ N), then `a ∘ σ` is too—because `σ` maps `n ≥ N` to even larger indices where `a` is still close to `L`.

The same `N` works for all subsequences!

**The Contrapositive: A Divergence Test**

The Subsequence Theorem says: *If `a n → L`, then every subsequence converges to `L`.*

By contrapositive: *If there exist two subsequences converging to different limits, then `a` does not converge.*

This is a powerful tool for proving divergence!

**Example Application:**

Consider `a n = (-1)^n`, which oscillates between -1 and 1:
- The even-indexed subsequence: `a(0), a(2), a(4), ... = 1, 1, 1, ...` converges to 1
- The odd-indexed subsequence: `a(1), a(3), a(5), ... = -1, -1, -1, ...` converges to -1

Since we have subsequences converging to different limits (1 and -1), the sequence `a n = (-1)^n` does not converge. We'll see this in the next level!

**Looking Ahead:**

Subsequences are fundamental in analysis:
- **Bolzano-Weierstrass Theorem:** Every bounded sequence has a convergent subsequence
- **Compactness:** Sequential compactness is defined using subsequences
- **Cauchy sequences:** Can be understood through subsequences
- **limsup and liminf:** Defined as limits of monotone subsequences

The concept generalizes to metric spaces and topological spaces, where it's crucial for understanding convergence and compactness.

**Exercise:** Prove that if a sequence has two subsequences converging to different limits, then the sequence diverges. (Hint: use proof by contradiction—assume the sequence converges and derive that the two limits must be equal.)
"
