import Game.Levels.L12PsetIntro
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

Statement IsCauchyOfAntitoneBdd {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (M : X) (hM : ∀ n, M ≤ a n) (ha : Antitone a)
    : IsCauchy a := by
let b := -a
have hb : Monotone b := by apply MonotoneNeg_of_Antitone a ha
have b_bdd : ∀ n, b n ≤ -M := by intro n; change -a n ≤ - M; linarith [hM n]
have bCauchy : IsCauchy b := IsCauchyOfMonotoneBdd b (-M) b_bdd hb
have negbCauchy : IsCauchy (-b) := IsCauchyNeg b bCauchy
change IsCauchy (- -a) at negbCauchy
rewrite [show - - a = a by ring_nf] at negbCauchy
apply negbCauchy

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
