module
public import Solution
public import PdtPisotBoundary

@[expose] public section

/-!
# Supplement: the bound of statement 1 is attained (proved, not compared)

Compared statement 1 (`padovan_minimal_unique`) gives `ρ ≤ θ` for every Pisot eigenvalue
`θ > 1` of the incidence matrix of a substitution on at most three letters, with `θ = ρ`
exactly for the Padovan rule `s` and its mirror, up to renaming. It does not by itself say that
`ρ` occurs. `padovan_pisot_eigenvalue` below supplies that: the plastic number `ρ` is an
eigenvalue of `inc s` meeting every hypothesis of statement 1. So `ρ` is the least such
eigenvalue, and it is attained, exactly by `s` and `mir s` up to renaming the letters.

The proof uses `Time.Clock.aeval_charpoly_pad` and `Time.Clock.rho_bounds`
(`SlowestClock.lean`), the irreducibility of `x³ − x − 1` over `ℚ`
(`Time.cubicQ_irreducible`, `Irreducibility.lean`), the uniqueness of the real root
(`Time.Clock.cubic_root_unique`), and the bound `‖z‖ < 1` for the non-real roots of
`x³ − x − 1` (`PDT.cubic_conj_norm_lt_one`, `PdtPisotBoundary.lean`). This module is not
on the compared surface.
-/

namespace ArithmeticOfTime

open Polynomial

/-- **The bound is attained.** For the real `ρ` with `ρ ^ 3 = ρ + 1`: `ρ` is an eigenvalue of
the Padovan incidence matrix `inc s`, `1 < ρ`, and every complex root of `minpoly ℚ ρ` other
than `ρ` lies strictly inside the unit circle. -/
theorem padovan_pisot_eigenvalue (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) :
    Polynomial.aeval ρ (inc s).charpoly = 0 ∧ 1 < ρ ∧
      ∀ z ∈ (minpoly ℚ ρ).aroots ℂ, z ≠ (ρ : ℂ) → ‖z‖ < 1 := by
  have hinc : inc s = Time.Clock.inc Time.Clock.pad := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  refine ⟨?_, (Time.Clock.rho_bounds hρ).1, ?_⟩
  · rw [hinc, Time.Clock.aeval_charpoly_pad]
    linear_combination hρ
  · have hmin : minpoly ℚ ρ = X ^ 3 - X - 1 := by
      refine (minpoly.eq_of_irreducible_of_monic Time.cubicQ_irreducible ?_
        (by monicity!)).symm
      simp only [map_sub, map_pow, aeval_X, map_one]
      linear_combination hρ
    intro z hz hne
    rw [hmin, mem_aroots] at hz
    obtain ⟨-, hz⟩ := hz
    simp only [map_sub, map_pow, aeval_X, map_one] at hz
    have hz3 : z ^ 3 = z + 1 := by linear_combination hz
    by_cases him : z.im = 0
    · exfalso
      apply hne
      have hzre : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
      have hre : z.re ^ 3 = z.re + 1 := by
        have h3 : ((z.re : ℂ)) ^ 3 = (z.re : ℂ) + 1 := by rw [← hzre]; exact hz3
        exact_mod_cast h3
      rw [hzre, Time.Clock.cubic_root_unique hρ hre]
    · exact PDT.cubic_conj_norm_lt_one z hz3 him

end ArithmeticOfTime

/-! ### Axiom audit (in-module) -/

#print axioms ArithmeticOfTime.padovan_pisot_eigenvalue
