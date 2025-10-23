import Game.Levels.L13Lecture

World "Lecture14"
Level 1
Title "Bolzano-Weierstass"


Introduction "
# Level 1 **Big Boss:**  Bolzano-Weierstass

## New theorems:

- `abs_le` -- just like `abs_lt` but for `|x| ≤ y` instead of `|x| < y`

- `IsCauchyOfAntitoneBdd` (from Pset 12)

- `AntitoneSubseq_of_UnBddPeaks` (to be proved in Pset 13)

"

/-- `|x| ≤ y ↔ -y ≤ x ≤ y`
-/
TheoremDoc abs_le as "abs_le" in "Theorems"

/--
If a sequence `a : ℕ → X` (where `X` can be `ℚ` or `ℝ`) is antitone and bounded, then it is Cauchy.
-/
TheoremDoc IsCauchyOfAntitoneBdd as "IsCauchyOfAntitoneBdd" in "Theorems"

theorem IsCauchyOfAntitoneBdd {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (M : X) (hM : ∀ n, M ≤ a n) (ha : Antitone a)
    : IsCauchy a := by
sorry

/--
If a sequence `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) is `Monotone` and grows along some subsequences by `ε`, then it eventually grows by `k * ε` for any `k`.
-/
TheoremDoc AntitoneSubseq_of_UnBddPeaks as "AntitoneSubseq_of_UnBddPeaks" in "Theorems"

theorem AntitoneSubseq_of_UnBddPeaks
{X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (ha : UnBddPeaks a) : ∃ σ, Subseq σ ∧ Antitone (a ∘ σ) := by
sorry

NewTheorem AntitoneSubseq_of_UnBddPeaks IsCauchyOfAntitoneBdd abs_le

/--
If a sequence `a : ℕ → X` (where `X` could be `ℚ` or `ℝ`) is bounded, then it has a subsequence which is Cauchy.
-/
TheoremDoc BolzanoWeierstrass as "BolzanoWeierstrass" in "Theorems"

/-- Prove this
-/
Statement BolzanoWeierstrass {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (ha : SeqBdd a) : ∃ σ, Subseq σ ∧ IsCauchy (a ∘ σ) := by
choose M Mpos hM using ha
have aBddAbove : ∀ n, a n ≤ M := by intro n; specialize hM n; rewrite [abs_le] at hM; apply hM.2
have aBddBelow : ∀ n, -M ≤ a n := by intro n; specialize hM n; rewrite [abs_le] at hM; apply hM.1
by_cases hPeaks : UnBddPeaks a
choose σ σsubseq σanti using AntitoneSubseq_of_UnBddPeaks a hPeaks
use σ
split_ands
exact σsubseq
apply IsCauchyOfAntitoneBdd (a ∘ σ) (-M)
intro n
change -M ≤ a (σ n)
apply aBddBelow
apply σanti
choose σ σsubseq σmono using MonotoneSubseq_of_BddPeaks a hPeaks
use σ
split_ands
apply σsubseq
apply IsCauchyOfMonotoneBdd (a ∘ σ) M
intro n
change a (σ n) ≤ M
apply aBddAbove
apply σmono

Conclusion ""
