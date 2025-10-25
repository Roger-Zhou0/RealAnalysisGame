import Game.Levels.L12Pset.L12Pset1

World "L12Pset"
Level 2
Title "Problem 2"

Introduction "
# Problem 2:

More fun with Cauchy sequences. Show that `1/n` is Cauchy but is neither `Monotone` nor `Antitone`! (Because of how division by zero works in Lean...)

"

/-- Prove this
-/
Statement (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) : IsCauchy a ∧ ¬ Monotone a ∧ ¬ Antitone a := by
split_ands
apply IsCauchyOfLim
use 0
apply OneOverNLimZero a ha
intro h
specialize h (by bound : 1 ≤ 2)
rewrite [ha, ha] at h
norm_num at h
intro h
specialize h (by bound : 0 ≤ 1)
rewrite [ha, ha] at h
norm_num at h

Conclusion ""


#exit

"True or false: There exists a sequence of real numbers that is Cauchy but not Monotone.

Your solution to this problem **must** begin with either `left` or `right`"

/-- Prove this
-/
Statement : (∃ (a : ℕ → ℝ), IsCauchy a ∧ ¬ Monotone a)
        ∨ ¬ (∃ (a : ℕ → ℝ), IsCauchy a ∧ ¬ Monotone a) := by
left
let a : ℕ → ℝ := fun n ↦ (-1) ^ n / n
use a
split_ands
apply IsCauchyOfLim
use 0
intro ε hε
choose N hN using ArchProp hε
use N
intro n hn
change |(-1 : ℝ)^n / n - 0| < ε
rewrite [show (-1 : ℝ)^n / n - 0 = (-1 : ℝ)^n / n by ring_nf]
rewrite [abs_div]
have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
rewrite [show |(-1 : ℝ) ^ n| = 1 by norm_num]
rewrite [show |(n : ℝ)| = n by bound]
have εinv : 0 < 1 / ε := by bound
have Npos : (0 : ℝ) < N := by linarith [hN, εinv]
have npos : (0 : ℝ) < n := by linarith [Npos, hn']
have : N * ε ≤ n * ε := by bound
field_simp at hN ⊢
linarith [hN, this]
change ¬(∀ i j, i ≤ j → a i ≤ a j)
push_neg
use 0, 1
split_ands
norm_num
norm_num
