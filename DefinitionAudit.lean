module
public import Mathlib

@[expose] public section
/-!
# Audit of the imported definitions

The compared statements in `Challenge.lean` rest on definitions imported from Mathlib (pinned
revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`) and from core Lean (toolchain
`leanprover/lean4:v4.35.0-rc2`): `Matrix.charpoly` with `Matrix.charmatrix`, `Polynomial.aeval`,
`minpoly`, `Polynomial.roots` with `Polynomial.aroots`, `Polynomial.natDegree`, `IsIntegral`,
the norm on `ℂ`, the iterate `f^[n]` (`Nat.iterate`), `List.IsInfix` (`<:+:`) and `List.count`.
Their pinned source text is quoted verbatim, with permalinks, in `MATHLIB_DEFINITIONS.md`; the
remaining vocabulary (`List.map`, `List.reverse`, `List.flatten`, `Equiv`, `Matrix.map`, the
`!![…]` matrix notation) is standard and is not quoted, and the facts about the notation that the
account uses are checked below. This file is not part of the compared set and imports Mathlib
only. It records, as kernel-checked theorems, the facts about those definitions that the informal
account relies on, so that the correspondence can be audited from this repository alone:

* `charpoly_eq_det`, `charmatrix_eq`, `eval_charpoly` — `M.charpoly` is `det (X • 1 − M)`.
* `aeval_eq_eval₂` — `aeval θ p` is the evaluation sum `eval₂ (algebraMap ℤ ℝ) θ p`.
* `aeval_charpoly_eq_zero_iff` — for an integer matrix `M` and a real `θ`, the hypothesis
  `Polynomial.aeval θ M.charpoly = 0` holds exactly when `θ` is a real eigenvalue of `M`: some
  nonzero real vector `v` has `M v = θ v`.
* `isIntegral_iff`, `isIntegral_of_aeval_charpoly` — `IsIntegral ℤ θ` means that `θ` is a root of
  a monic integer polynomial, and every real eigenvalue of an integer matrix is one.
* `minpoly_eq_zero_of_not_isIntegral`, `minpoly_spec`, `minpoly_eq_map_minpoly_int`,
  `natDegree_minpoly_eq_finrank` — for an algebraic `θ`, `minpoly ℚ θ` is the monic irreducible
  rational polynomial that divides every rational polynomial vanishing at `θ`; for an algebraic
  integer it is the image of `minpoly ℤ θ`, so it has integer coefficients; its `natDegree` is the
  degree `[ℚ(θ) : ℚ]` of `θ`. For a non-algebraic `θ` it is `0` (Mathlib's convention).
* `mem_aroots_minpoly`, `self_mem_aroots_minpoly`, `aroots_minpoly_nodup`,
  `card_aroots_minpoly` — for an algebraic real `θ`, `(minpoly ℚ θ).aroots ℂ` is the multiset of
  complex roots of `minpoly ℚ θ`: it contains `θ`, has no repeated element, and has as many
  elements as the degree. So the Pisot hypothesis
  `∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1` says that every conjugate of `θ` other
  than `θ` itself lies strictly inside the unit circle.
* `complex_norm_eq`, `complex_norm_lt_one_iff` — `‖z‖` on `ℂ` is the modulus `√(re² + im²)`.
* `plastic_exists_unique`, `plastic_gt_one` — exactly one real `ρ` satisfies `ρ ^ 3 = ρ + 1`,
  and it exceeds `1`.
* `padovan_matrix_eq_count`, `padovan_matrix_charpoly` — `!![0, 0, 1; 1, 0, 1; 0, 1, 0]` lists its
  rows, it is the matrix whose entry `(i, j)` counts the letter `i` in the Padovan image of `j`
  (`[1]`, `[2]`, `[0, 1]`), and its characteristic polynomial is `X ^ 3 − X − 1`.
* `iterate_zero_apply`, `iterate_succ_apply'` — `f^[0] x = x` and `f^[n+1] x = f (f^[n] x)`.
* `isInfix_iff`, `count_eq_length_filter` — `u <:+: w` means `w = p ++ u ++ t` for some words
  `p, t` (a contiguous factor), and `l.count a` is the number of occurrences of `a` in `l`.
-/

namespace DefinitionAudit

open Polynomial

/-! ### The characteristic polynomial -/

/-- The characteristic polynomial is the determinant of the characteristic matrix. -/
theorem charpoly_eq_det {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (M : Matrix n n R) : M.charpoly = (Matrix.charmatrix M).det := rfl

/-- The characteristic matrix is `X • 1 − M`, with `M` read in `R[X]` through constants. -/
theorem charmatrix_eq {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (M : Matrix n n R) :
    Matrix.charmatrix M = Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M := rfl

/-- Evaluated at `t`, the characteristic polynomial is `det (t • 1 − M)`. -/
theorem eval_charpoly {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]
    (M : Matrix n n R) (t : R) : M.charpoly.eval t = (Matrix.scalar n t - M).det :=
  Matrix.eval_charpoly M t

/-- `aeval θ p` is the evaluation sum `eval₂ (algebraMap ℤ ℝ) θ p`. -/
theorem aeval_eq_eval₂ (p : ℤ[X]) (θ : ℝ) : aeval θ p = eval₂ (algebraMap ℤ ℝ) θ p :=
  aeval_def θ p

/-- For an integer matrix, `aeval θ M.charpoly = 0` says exactly that `θ` is a real eigenvalue. -/
theorem aeval_charpoly_eq_zero_iff {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix n n ℤ) (θ : ℝ) :
    aeval θ M.charpoly = 0 ↔
      ∃ v : n → ℝ, v ≠ 0 ∧ (M.map (Int.cast : ℤ → ℝ)).mulVec v = θ • v := by
  have h1 : aeval θ M.charpoly = (M.map (Int.cast : ℤ → ℝ)).charpoly.eval θ := by
    rw [aeval_def, eval₂_eq_eval_map, ← Matrix.charpoly_map]
    rfl
  rw [h1, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [Matrix.sub_mulVec, sub_eq_zero, eq_comm]
  simp [Matrix.scalar_apply, funext_iff, Pi.smul_apply, smul_eq_mul]

/-! ### Algebraic integers and the minimal polynomial -/

/-- `IsIntegral ℤ θ`: `θ` is a root of some monic integer polynomial. -/
theorem isIntegral_iff (θ : ℝ) :
    IsIntegral ℤ θ ↔ ∃ p : ℤ[X], p.Monic ∧ aeval θ p = 0 := by
  simp only [IsIntegral, RingHom.IsIntegralElem, aeval_def]

/-- A real eigenvalue of an integer matrix is an algebraic integer (the characteristic
polynomial is monic). -/
theorem isIntegral_of_aeval_charpoly {n : Type*} [DecidableEq n] [Fintype n]
    (M : Matrix n n ℤ) (θ : ℝ) (h : aeval θ M.charpoly = 0) : IsIntegral ℤ θ :=
  (isIntegral_iff θ).2 ⟨M.charpoly, Matrix.charpoly_monic M, h⟩

/-- Mathlib's convention: the minimal polynomial of a non-algebraic element is `0`. -/
theorem minpoly_eq_zero_of_not_isIntegral (θ : ℝ) (h : ¬ IsIntegral ℚ θ) :
    minpoly ℚ θ = 0 :=
  minpoly.eq_zero h

/-- For algebraic `θ`, `minpoly ℚ θ` is monic, irreducible, vanishes at `θ`, and divides every
rational polynomial that vanishes at `θ`. -/
theorem minpoly_spec (θ : ℝ) (h : IsIntegral ℚ θ) :
    (minpoly ℚ θ).Monic ∧ Irreducible (minpoly ℚ θ) ∧ aeval θ (minpoly ℚ θ) = 0 ∧
      ∀ q : ℚ[X], aeval θ q = 0 → minpoly ℚ θ ∣ q :=
  ⟨minpoly.monic h, minpoly.irreducible h, minpoly.aeval ℚ θ, fun _ hq => minpoly.dvd ℚ θ hq⟩

/-- For an algebraic integer, `minpoly ℚ θ` is the image of `minpoly ℤ θ`: its coefficients are
integers. -/
theorem minpoly_eq_map_minpoly_int (θ : ℝ) (h : IsIntegral ℤ θ) :
    minpoly ℚ θ = (minpoly ℤ θ).map (algebraMap ℤ ℚ) :=
  minpoly.isIntegrallyClosed_eq_field_fractions' ℚ h

/-- The `natDegree` of `minpoly ℚ θ` is the degree `[ℚ(θ) : ℚ]` of `θ`. -/
theorem natDegree_minpoly_eq_finrank (θ : ℝ) (h : IsIntegral ℚ θ) :
    (minpoly ℚ θ).natDegree = Module.finrank ℚ (IntermediateField.adjoin ℚ {θ}) :=
  (IntermediateField.adjoin.finrank h).symm

/-! ### The complex roots of the minimal polynomial -/

/-- For algebraic `θ`, `(minpoly ℚ θ).aroots ℂ` consists of the complex roots of
`minpoly ℚ θ`. -/
theorem mem_aroots_minpoly (θ : ℝ) (h : IsIntegral ℚ θ) (z : ℂ) :
    z ∈ (minpoly ℚ θ).aroots ℂ ↔ aeval z (minpoly ℚ θ) = 0 := by
  rw [mem_aroots]
  exact and_iff_right (minpoly.ne_zero h)

/-- `θ` itself is one of them. -/
theorem self_mem_aroots_minpoly (θ : ℝ) (h : IsIntegral ℚ θ) :
    (θ : ℂ) ∈ (minpoly ℚ θ).aroots ℂ := by
  rw [mem_aroots_minpoly θ h]
  have : ((θ : ℂ)) = algebraMap ℝ ℂ θ := rfl
  rw [this, aeval_algebraMap_apply, minpoly.aeval, map_zero]

/-- The complex roots of `minpoly ℚ θ` are simple. -/
theorem aroots_minpoly_nodup (θ : ℝ) (h : IsIntegral ℚ θ) :
    ((minpoly ℚ θ).aroots ℂ).Nodup :=
  nodup_roots (PerfectField.separable_of_irreducible (minpoly.irreducible h)).map

/-- There are as many of them as the degree of `θ`. -/
theorem card_aroots_minpoly (θ : ℝ) (h : IsIntegral ℚ θ) :
    Multiset.card ((minpoly ℚ θ).aroots ℂ) = (minpoly ℚ θ).natDegree := by
  rw [aroots_def, IsAlgClosed.card_roots_eq_natDegree, (minpoly.monic h).natDegree_map]

/-! ### The norm on `ℂ` -/

/-- The norm on `ℂ` is the modulus. -/
theorem complex_norm_eq (z : ℂ) : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) :=
  Complex.norm_eq_sqrt_sq_add_sq z

/-- `‖z‖ < 1`: `z` lies strictly inside the unit circle. -/
theorem complex_norm_lt_one_iff (z : ℂ) : ‖z‖ < 1 ↔ z.re ^ 2 + z.im ^ 2 < 1 := by
  rw [complex_norm_eq, Real.sqrt_lt' one_pos, one_pow]

/-! ### The plastic number -/

/-- Exactly one real number `ρ` satisfies `ρ ^ 3 = ρ + 1`. -/
theorem plastic_exists_unique : ∃! ρ : ℝ, ρ ^ 3 = ρ + 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) := by fun_prop
  obtain ⟨ρ, -, hρ⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont
    (show (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 1) 1) ((fun x : ℝ => x ^ 3 - x - 1) 2) by
      norm_num)
  have hρ' : ρ ^ 3 = ρ + 1 := by simp only at hρ; linarith
  refine ⟨ρ, hρ', fun θ hθ => ?_⟩
  have hρ1 : 1 < ρ := by nlinarith [sq_nonneg (ρ - 1), sq_nonneg (ρ + 1), sq_nonneg ρ]
  have hfac : (θ - ρ) * (θ ^ 2 + θ * ρ + ρ ^ 2 - 1) = 0 := by linear_combination hθ - hρ'
  have hpos : 0 < θ ^ 2 + θ * ρ + ρ ^ 2 - 1 := by nlinarith [sq_nonneg (2 * θ + ρ)]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith

/-- That number exceeds `1`. -/
theorem plastic_gt_one (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) : 1 < ρ := by
  nlinarith [sq_nonneg (ρ - 1), sq_nonneg (ρ + 1), sq_nonneg ρ]

/-! ### The Padovan incidence matrix -/

/-- `!![0, 0, 1; 1, 0, 1; 0, 1, 0]` lists its rows: its entry `(i, j)` is the number of
occurrences of the letter `i` in the Padovan image of `j` (`0 ↦ [1]`, `1 ↦ [2]`, `2 ↦ [0, 1]`). -/
theorem padovan_matrix_eq_count :
    (!![0, 0, 1; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℕ) =
      Matrix.of fun i j => ((![[1], [2], [0, 1]] : Fin 3 → List (Fin 3)) j).count i := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Its characteristic polynomial, over `ℤ`, is `X ^ 3 − X − 1`. -/
theorem padovan_matrix_charpoly :
    ((!![0, 0, 1; 1, 0, 1; 0, 1, 0] : Matrix (Fin 3) (Fin 3) ℕ).map (Nat.cast : ℕ → ℤ)).charpoly =
      X ^ 3 - X - 1 := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp
  ring

/-! ### Iterates, factors and counts -/

/-- `f^[0] x = x`. -/
theorem iterate_zero_apply {α : Type*} (f : α → α) (x : α) : f^[0] x = x := rfl

/-- `f^[n+1] x = f (f^[n] x)`. -/
theorem iterate_succ_apply' {α : Type*} (f : α → α) (n : ℕ) (x : α) :
    f^[n + 1] x = f (f^[n] x) :=
  Function.iterate_succ_apply' f n x

/-- `u <:+: w`: `w = p ++ u ++ t` for some words `p` and `t`. -/
theorem isInfix_iff {α : Type*} (u w : List α) : u <:+: w ↔ ∃ p t, p ++ u ++ t = w := Iff.rfl

/-- `l.count a` is the number of occurrences of `a` in `l`. -/
theorem count_eq_length_filter {α : Type*} [BEq α] (a : α) (l : List α) :
    l.count a = (l.filter (· == a)).length :=
  List.count_eq_length_filter

end DefinitionAudit
