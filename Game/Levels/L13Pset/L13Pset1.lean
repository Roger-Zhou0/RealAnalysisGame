import Game.Levels.L13Lecture

World "L13Pset"
Level 1
Title "Problem 1"

Introduction "
# Problem 1:

Prove `AntitoneSubseq_of_UnBddPeaks`

## New theorem: `Antitone_of_succ`

"

theorem Antitone_of_succ {X : Type*} [Preorder X] (a : ℕ → X) (ha : ∀ n, a (n+1) ≤ a n) : Antitone a := by
exact antitone_nat_of_succ_le ha

/-- If `a (n+1) ≤ a n` holds for all `n`, then `a` is `Monotone`. -/
TheoremDoc Antitone_of_succ as "Antitone_of_succ" in "Theorems"

NewTheorem Antitone_of_succ

DisabledTheorem AntitoneSubseq_of_UnBddPeaks

/-- Prove `AntitoneSubseq_of_UnBddPeaks`
-/
Statement {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (ha : UnBddPeaks a) : ∃ σ, Subseq σ ∧ Antitone (a ∘ σ) := by
sorry


Conclusion ""
