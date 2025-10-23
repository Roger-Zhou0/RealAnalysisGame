import Game.Levels.L12Lecture

World "Lecture13"
Level 1
Title "Monotone Subsequence"


Introduction "
# Level 1 **Big Boss:**  Monotone Subsequence

## New definitions:

- `IsAPeak`: Standing at `a n`, you can look down at all future values.

`def IsAPeak {X : Type*} [LinearOrder X] (a : ℕ → X) (n : ℕ) : Prop := ∀ m > n, a m ≤ a n`

- A sequence `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) satisfies `UnBddPeaks` if there are arbitrarily large peaks.

`def UnBddPeaks {X : Type*} [LinearOrder X] (a : ℕ → X) : Prop := ∀ k, ∃ n > k, IsAPeak a n`

## The Goal

Assume your sequence `a : ℕ → X` does **not** have `UnBddPeaks`. Prove that it then has a `Monotone` subsequence. (In the homework, you will show the opposite: if the sequence *does* have `UnBddPeaks`, then it has an `Antitone` -- that is, non-increasing -- subsequence.)

## New tactics:

- `if` `then` `else`

## New theorems:

- `lt_of_not_ge`

It says: If `¬ (m ≤ n)`, then `n < m`.


"

/-- `(a : ℕ → X) (n : ℕ) := ∀ m > n, a m ≤ a n`

For a sequence `a : ℕ → X` (where `X` is `ℚ` or `ℝ`) and `n : ℕ`, we say that `IsAPeak a n` if: `∀ m > n, a m ≤ a n`. -/
DefinitionDoc IsAPeak as "IsAPeak"

def IsAPeak {X : Type*} [LinearOrder X] (a : ℕ → X) (n : ℕ) : Prop := ∀ m > n, a m ≤ a n

/-- `(a : ℕ → X) := ∀ k, ∃ n > k, IsAPeak a n`

We say that a sequence `a : ℕ → X` (where `X` is `ℚ` or `ℝ`)
satisfies `UnBddPeaks a`, if its set of peaks is unbounded.-/
DefinitionDoc UnBddPeaks as "UnBddPeaks"

def UnBddPeaks {X : Type*} [LinearOrder X] (a : ℕ → X) : Prop := ∀ k, ∃ n > k, IsAPeak a n

NewDefinition IsAPeak UnBddPeaks

/-- If `¬ (m ≤ n)`, then `n < m`. -/
TheoremDoc lt_of_not_ge as "lt_of_not_ge" in "Theorems"

NewTheorem lt_of_not_ge

/--
If a sequence `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) does not have unbounded peaks, then it has a `Monotone` subsequence.
-/
TheoremDoc MonotoneSubseq_of_BddPeaks as "MonotoneSubseq_of_BddPeaks" in "Theorems"

/-- Prove this
-/
Statement MonotoneSubseq_of_BddPeaks {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (ha : ¬ UnBddPeaks a) : ∃ σ, Subseq σ ∧ Monotone (a ∘ σ) := by
change ¬ (∀ k, ∃ n > k, ∀ m > n, a m ≤ a n) at ha
push_neg at ha
choose k hk using ha
choose τ τ_gt hτ using hk
let τ' : ℕ → ℕ := fun n => if h : n ≤ k then n + 1 else τ n (lt_of_not_ge h)
have τ'_eq : ∀ n, τ' n = if h : n ≤ k then n + 1 else τ n (lt_of_not_ge h) := by intro n; rfl
have τ'_gt : ∀ n, n < τ' n := by
  intro n;
  by_cases hn : n ≤ k;
  rewrite [τ'_eq];
  bound;
  rewrite [τ'_eq];
  bound
let σ : ℕ → ℕ := fun n ↦ τ'^[n] (k+1)
have σ_eq : ∀ n, σ n = τ'^[n] (k+1) := by intro n; rfl
have hσ : ∀ n, k < σ n := by
  intro n;
  induction' n with n hn;
  rewrite [σ_eq];
  bound;
  rewrite [σ_eq];
  rewrite [← show τ' (τ'^[n] (k + 1)) = τ'^[n + 1] (k + 1) by apply succ_iterate];
  rewrite [← σ_eq];
  specialize τ'_gt (σ n);
  linarith [τ'_gt, hn]
use σ
split_ands
apply Subseq_of_Iterate
apply τ'_gt
apply Monotone_of_succ
intro n
specialize hσ n
specialize hτ (σ n) hσ
change a (σ n) ≤ a (σ (n + 1))
rewrite [show σ (n + 1) = τ'^[n+1] (k + 1) by apply σ_eq]
rewrite [← show τ' (τ'^[n] (k + 1)) = τ'^[n + 1] (k + 1) by apply succ_iterate]
rewrite [← show σ (n) = τ'^[n] (k + 1) by apply σ_eq]
rewrite [τ'_eq]
bound

Conclusion ""
