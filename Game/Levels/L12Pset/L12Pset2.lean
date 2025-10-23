import Game.Levels.L12Pset.L12Pset1

World "L12Pset"
Level 2
Title "Problem 2"

Introduction "
# Problem 2:

More fun with Cauchy sequences. True or false: There exists a sequence of real numbers that is Cauchy but not Monotone.

Your solution to this problem **must** begin with either `left` or `right`

"

/-- Prove this
-/
Statement : (∃ (a : ℕ → ℝ), IsCauchy a ∧ ¬ Monotone a)
        ∨ ¬ (∃ (a : ℕ → ℝ), IsCauchy a ∧ ¬ Monotone a) := by
sorry

Conclusion ""
