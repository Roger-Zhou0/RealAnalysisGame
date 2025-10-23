import Game.Levels.L12Levels.L00_SubseqIterate

World "Lecture12"
Level 2
Title "Enhanced Choose"

Introduction "
# Level 2: Enhanced `Choose`

Do you know the \"Twin Prime Conjecture\"?
A number `n : ℕ` is called a Twin Prime if both `n`
and `n+2` are prime numbers. Let's call this property
`p : ℕ → Prop`. So `p` is a function that takes a
natural number `n` and returns `p (n) = ` Yes/No, depending on whether `n` is a twin prime. The Twin Prime Conjecture says that there are infinitely many twin primes; that is, for any bound `N`, no matter how large,
there is always at least one `n > N` for which `p (n)` holds. We would state the conjecture like this:

`h : ∀ N, ∃ n > N, p n`

Now suppose that we have a hypothesis like this, for some abstract property `p` (if you like, you're welcome to keep thinking of `p n` as testing whether `n` is a twin prime). Given that there are arbitrarily large `n`'s for which `p n` holds, how do I get my hands on a subsequence `σ : ℕ → ℕ`, so that, along the subsequence, `p (σ n)` holds, for all `n`?

The idea is that you should interpret `h` as a collection of **functions**. Given a natural number `N`,  the hypothesis `h` will produce a `n` for you, but that `n` is a function of `N`, so we should really write `n = n (N)`. But that's not all! The hypothesis `h` also contains a *proof* that `n (N) > N` for all `N`. Do you see why the statement of `h` implies
the existence of such a function? And lastly, `h` also gives us a proof of the fact that, for all `N`,
`p (n (N))` holds. So `n (N)` is (almost) our desired sequence! (Since it's funny to write `n (N)`, let's rename `n` to `τ`, so we can write `τ (N)`.) The way in Lean to go from `h` to these sequences is to invoke a familiar tactic: `choose`! If you write:

`choose τ hτBnd hτP using h`

then Lean will add to your goal state:

`τ : ℕ → ℕ`

`hτBnd : ∀ N, τ (N) > N`

`hτP : ∀ N, p (N)`

Isn't that cool?! Now you should be able to use the idea from the last level to make the desired subsequence `σ`,
 but you'll need to think about how *exactly* to make it work...

"


/-- Prove this
-/
Statement (p : ℕ → Prop) (h : ∀ N, ∃ n > N, p n) :
  ∃ σ, Subseq σ ∧ ∀ n, p (σ n) := by
Hint (hidden := true) "Try starting your proof with `choose τ hτBnd hτP using h`."
choose τ hτBnd hτP using h
Hint (hidden := true) (strict := true) "You can make `σ` by taking an orbit of `τ`! You can start at any base point, as long as `p` is satisfied for that base point; since we don't *a priori* know of such a point, we can start with `τ 0`. Try writing `let σ : ℕ → ℕ := fun n ↦ τ^[n] (τ 0)`."
let σ : ℕ → ℕ := fun n ↦ τ^[n] (τ 0)
use σ
split_ands
apply Subseq_of_Iterate τ hτBnd (τ 0)
intro n
change p (τ^[n+1] 0)
rewrite [← show  τ (τ^[n] 0) = τ^[n+1] 0 by apply succ_iterate]
apply hτP (τ^[n] 0)

Conclusion "
## What You've Accomplished

You've mastered a crucial technique for extracting structured objects from existence statements. By using `choose` to convert the Twin Prime Conjecture into concrete functions, then applying orbit construction to make those functions monotonic, you've built a subsequence that is both strictly increasing and preserves the desired property.

## The Power of `choose`

This level revealed how existence statements like `∀ N, ∃ n > N, p n` are actually encoding:
- A **function** `τ : ℕ → ℕ` that produces witnesses
- **Proofs** that these witnesses satisfy the required properties
- The ability to **extract** these hidden structures for further use

The `choose` tactic transforms abstract existence into concrete tools you can manipulate.

## Bridging Existence and Structure

The key insight is the two-step process:
1. **Extract witnesses** using `choose` to get a function `τ` satisfying the property
2. **Add structure** using orbit construction to get a subsequence `σ` that's both monotonic and property-preserving

This pattern - *existence → extraction → structuring* - appears throughout advanced mathematics.

## Looking Ahead

You now have all the tools needed for the main theorem of this lecture. In the next level, you'll see this exact `choose` technique applied to extract subsequences from the negation of the Cauchy property. The orbit construction you've mastered will then be used to accumulate gaps and create the contradiction with boundedness.

The ability to extract functions from complex quantified statements, then transform them to have the structure you need, is a fundamental skill in formal mathematics. You've seen how abstract number theory (Twin Prime Conjecture) and concrete analysis (orbit construction) can work together seamlessly.
"
