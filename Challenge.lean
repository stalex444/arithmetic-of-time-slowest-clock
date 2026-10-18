module
public import Mathlib

@[expose] public section

/-!
# Challenge: the slowest settling clock on at most three letters

This module is the small, trusted surface to audit. It states the five compared theorems with
`sorry` placeholders; `Solution.lean` proves them, with identical statements.

Among all substitutions on at most three letters whose incidence matrix has a Pisot
eigenvalue `θ > 1`, the least such `θ` is the plastic number `ρ`, the real root of
`x³ = x + 1`. It is attained only by the Padovan substitution `a ↦ b, b ↦ c, c ↦ ab` and its
mirror `c ↦ ba`, up to renaming the letters, and both minimal rules are chiral, in opposite
directions. Statement 1 below gives the bound and the equality case; that `ρ` does occur, as a
Pisot eigenvalue of the Padovan incidence matrix, is `padovan_pisot_eigenvalue` in
`Supplement.lean` (proved, not compared).

Vocabulary. Letters are `Fin k`; on `Fin 3` the letters `0, 1, 2` stand for `a, b, c`, and
`s` is the Padovan substitution. A substitution `σ : Fin k → List (Fin k)` may have empty
images. `inc σ` is its incidence matrix (entry `(i, j)` counts the letter `i` in `σ j`),
`mir σ` reads every image block backwards, `sub σ` applies `σ` letterwise to a word, and
`u <:+: w` says that `u` is a factor (a contiguous sublist) of `w`.

The compared statements are exactly these five:

1. `padovan_minimal_unique` — for `σ` on `k ≤ 3` letters and a real eigenvalue `θ > 1` of
   `inc σ` that is a Pisot number (every complex root of `minpoly ℚ θ` other than `θ` has
   norm `< 1`): `ρ ≤ θ`, and `θ = ρ` exactly when, after renaming the letters, `σ` is `s`
   or `mir s`.
2. `padovan_eigenvalue_unique` — the equivalence of statement 1 for every real eigenvalue
   `θ` of `inc σ`, with no Pisot hypothesis and no `1 < θ`.
3. `padovan_matrix_unique` — a `3 × 3` matrix over `ℕ` with characteristic polynomial
   `x³ − x − 1` is the Padovan incidence matrix `!![0, 0, 1; 1, 0, 1; 0, 1, 0]` after one
   simultaneous permutation of its rows and columns.
4. `pisot_ge_plastic` — every Pisot number `θ` of degree at most `3` satisfies `ρ ≤ θ`.
5. `padovan_rules_chiral` — under `s`, the word `ca` (`[2, 0]`) is a factor of an iterate
   from the seed `a` and `ac` (`[0, 2]`) is a factor of no iterate from any seed; under
   `mir s`, the reverse.

Statement 1 is the headline and combines two others: its bound is statement 4 applied to
`θ` (a root of the monic degree-`k` polynomial `(inc σ).charpoly`, hence an algebraic
integer of degree at most `3`), and its equivalence is statement 2, which needs no Pisot
hypothesis. Statement 3 is the matrix classification on which statement 2 rests. In
statement 5 the Padovan half is the companion entry's compared chirality statement, restated
over `sub s`; the mirror half follows because mirroring reverses every iterate from a
one-letter seed.

In statements 1, 2 and 4 the plastic number enters as any real `ρ` with `ρ ^ 3 = ρ + 1` (the
equation has exactly one real solution). Neither primitivity nor the unit property is
assumed, every alphabet size `k ≤ 3` is allowed, and images may be empty. Renaming the
letters is an equivalence `e : Fin k ≃ Fin 3` applied letterwise, so the equality case
forces `k = 3`. In statement 1, `θ` is an algebraic integer because it is a root of the
monic integer polynomial `(inc σ).charpoly`; statement 4 assumes `IsIntegral ℤ θ`.

Prior art. The bound `ρ ≤ θ` is Siegel's theorem (Duke Math. J. 11 (1944), 597–602), which
holds in every degree, restricted here to degree at most `3`; it is not new. Here it is
obtained through the minimal Mahler measures of the registered entry
PALOMAR-2026-08-31-000004 (stalex444/mahler-measure-minima at `ca3df22`; modules
`PdtMahler*`, statements and proofs unchanged) and a short bridge: a Pisot number is the
Mahler measure of its minimal polynomial (`Time.Clock.mahler_eq_of_pisot` in
`SlowestClock.lean`). The uniqueness was observed without proof by Mercat (Experiment.
Math. 29 (2020), §1, doi:10.1080/10586458.2018.1446063): up to a permutation of the letters,
the Padovan substitution and its reversal are the only substitutions on three letters
associated with the smallest Pisot number. The abstract of his preprint adds that no
substitution on fewer letters is associated with it; statement 2 covers that case.

Contribution. A kernel-checked proof of the combined statement, which Mercat states without
proof. In statement 2, `θ` may be any real eigenvalue of the incidence matrix, not only the
dominant one; no statement assumes primitivity, the unit property or non-erasing images, and
every alphabet size `k ≤ 3` is allowed. In the equality case these are consequences, not
hypotheses: `θ = ρ` forces `k = 3` and characteristic polynomial `x³ − x − 1`. The entry adds
the chirality of both minimal rules (statement 5). No claim of a first formalization is made.

Companion entry. This entry is the companion of the registered entry
PALOMAR-2026-08-19-000006 (stalex444/arithmetic-of-time), whose compared statements concern
the Padovan substitution's factor language. The Padovan half of statement 5 is that entry's
compared chirality statement, restated here over `sub s`; the mirror half is not compared
there.

Imported definitions. The statements also use Mathlib's `Matrix.charpoly`,
`Polynomial.aeval`, `minpoly`, `Polynomial.aroots`, `Polynomial.natDegree`, `IsIntegral`,
the norm on `ℂ` and the iterate `f^[n]`, and core Lean's `List.IsInfix` (`<:+:`) and
`List.count`.
`MATHLIB_DEFINITIONS.md` quotes the pinned source of each verbatim, with paths, line
numbers and permalinks. `DefinitionAudit.lean` (a default build target, imports Mathlib
only, not compared) kernel-checks the facts about them that this account relies on.
-/

namespace ArithmeticOfTime

/-- The Padovan substitution: `0 ↦ [1]`, `1 ↦ [2]`, `2 ↦ [0, 1]`
(that is, `a ↦ b`, `b ↦ c`, `c ↦ ab`). -/
def s : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | 2 => [0, 1]

/-! ### Mirror and incidence matrix on an arbitrary alphabet -/

/-- The mirror of a substitution: every image block read backwards. -/
def mir {A : Type*} (σ : A → List A) : A → List A := fun x => (σ x).reverse

/-- The incidence matrix of a substitution `σ`: the entry at `(i, j)` counts the
occurrences of the letter `i` in the image block of `j`. -/
def inc {A : Type*} [DecidableEq A] (σ : A → List A) : Matrix A A ℤ :=
  fun i j => ((σ j).count i : ℤ)

/-! ### Minimality and uniqueness of the Padovan rule on at most three letters -/

/-- **Minimality and uniqueness of the Padovan rule.** Let `σ` be a substitution on
`k ≤ 3` letters (images may be empty) and `θ > 1` a real eigenvalue of its incidence matrix that is a
Pisot number: every other complex root of its minimal polynomial lies strictly
inside the unit circle. Then `ρ ≤ θ`, where `ρ³ = ρ + 1`; and `θ = ρ` exactly when,
after renaming the letters, `σ` is the Padovan substitution or its mirror. -/
theorem padovan_minimal_unique {k : ℕ} (hk : k ≤ 3) (σ : Fin k → List (Fin k)) (θ : ℝ)
    (hθ : Polynomial.aeval θ (inc σ).charpoly = 0) (h1 : 1 < θ)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1)
    (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) :
    ρ ≤ θ ∧ (θ = ρ ↔ ∃ e : Fin k ≃ Fin 3,
      (∀ x, (σ x).map e = s (e x)) ∨ (∀ x, (σ x).map e = mir s (e x))) := by
  sorry

/-- **The classification, for every real eigenvalue.** For a substitution `σ` on
`k ≤ 3` letters and any real eigenvalue `θ` of its incidence matrix, `θ = ρ`
exactly when, after renaming the letters, `σ` is the Padovan substitution or its
mirror. -/
theorem padovan_eigenvalue_unique {k : ℕ} (hk : k ≤ 3) (σ : Fin k → List (Fin k)) (θ : ℝ)
    (hθ : Polynomial.aeval θ (inc σ).charpoly = 0) (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) :
    θ = ρ ↔ ∃ e : Fin k ≃ Fin 3,
      (∀ x, (σ x).map e = s (e x)) ∨ (∀ x, (σ x).map e = mir s (e x)) := by
  sorry

/-- **The matrix classification.** A `3 × 3` matrix with entries in `ℕ` and
characteristic polynomial `x³ − x − 1` is the Padovan incidence matrix after one
simultaneous permutation of its rows and columns. -/
theorem padovan_matrix_unique (M : Matrix (Fin 3) (Fin 3) ℕ)
    (h : (M.map (Nat.cast : ℕ → ℤ)).charpoly = Polynomial.X ^ 3 - Polynomial.X - 1) :
    ∃ e : Fin 3 ≃ Fin 3, ∀ i j, M i j = !![0, 0, 1; 1, 0, 1; 0, 1, 0] (e i) (e j) := by
  sorry

/-- **Pisot numbers of degree at most three are at least `ρ`.** A real algebraic
integer `θ > 1` of degree at most `3`, every other complex conjugate of which lies
strictly inside the unit circle, satisfies `ρ ≤ θ`. -/
theorem pisot_ge_plastic (θ : ℝ) (h1 : 1 < θ) (hint : IsIntegral ℤ θ)
    (hdeg : (minpoly ℚ θ).natDegree ≤ 3)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1)
    (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) : ρ ≤ θ := by
  sorry

/-! ### Both minimal rules are chiral -/

/-- Letterwise application of a substitution `σ` on an arbitrary alphabet: the
concatenation of the image blocks. -/
def sub {A : Type*} (σ : A → List A) (w : List A) : List A := (w.map σ).flatten

/-- **Both minimal rules are chiral.** For the Padovan substitution, `[2, 0]` is a
factor of the fifth iterate from the seed `0` while `[0, 2]` is a factor of no iterate
from any seed; for its mirror, `[0, 2]` is a factor of the fifth iterate from the seed `0`
while `[2, 0]` is a factor of no iterate from any seed. -/
theorem padovan_rules_chiral :
    ((([2, 0] : List (Fin 3)) <:+: (sub s)^[5] [0]) ∧
      ∀ (n : ℕ) (x : Fin 3), ¬ ([0, 2] : List (Fin 3)) <:+: (sub s)^[n] [x]) ∧
    ((([0, 2] : List (Fin 3)) <:+: (sub (mir s))^[5] [0]) ∧
      ∀ (n : ℕ) (x : Fin 3), ¬ ([2, 0] : List (Fin 3)) <:+: (sub (mir s))^[n] [x]) := by
  sorry

end ArithmeticOfTime
