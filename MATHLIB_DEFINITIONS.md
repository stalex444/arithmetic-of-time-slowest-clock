# Imported definitions

The compared statements in `Challenge.lean` rest on the definitions below: Mathlib's characteristic polynomial, polynomial evaluation, minimal polynomial, roots, degree, integrality, the norm on `ℂ` and the iterate `f^[n]`, and core Lean's `List.IsInfix` and `List.count`. The remaining vocabulary (`List.map`, `List.reverse`, `List.flatten`, `Equiv`, `Matrix.map`, `Fin`, the `!![…]` matrix notation) is standard and is not quoted; the facts about the `!![…]` notation that the account uses are kernel-checked in `DefinitionAudit.lean`. Each Mathlib excerpt is copied verbatim from Mathlib at the pinned revision `065356127b1dc0016f66b7283ce0ce2c4055aa55` (the revision required in `lakefile.toml` and recorded in `lake-manifest.json`); each core excerpt is copied verbatim from the Lean 4 repository at commit `11acb17ec6b07a8f9e9173e6845197929540936b` (tag `v4.35.0-rc2`, the toolchain pinned in `lean-toolchain`). Each comes with its file path, line numbers and a permalink. Mathlib and Lean 4 are released under the Apache 2.0 license; copyright of these excerpts remains with the authors named in each file's header.

The file `DefinitionAudit.lean` in this repository is built with the package (it is a default target) and checks, as theorems, the facts about these definitions that the informal account relies on. It is not part of the compared set and imports Mathlib only. All its theorems use only the standard axioms `propext`, `Classical.choice` and `Quot.sound` (see `BUILD.txt`).

## 1. `Matrix.charmatrix` and `Matrix.charpoly`

`Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`, lines 47–51: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean#L47-L51>

```lean
/-- The "characteristic matrix" of `M : Matrix n n R` is the matrix of polynomials $t I - M$.
The determinant of this matrix is the characteristic polynomial.
-/
def charmatrix (M : Matrix n n R) : Matrix n n R[X] :=
  Matrix.scalar n (X : R[X]) - (C : R →+* R[X]).mapMatrix M
```

`Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean`, lines 132–135: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean#L132-L135>

```lean
/-- The characteristic polynomial of a matrix `M` is given by $\det (t I - M)$. -/
@[wikidata Q849705]
def charpoly (M : Matrix n n R) : R[X] :=
  (charmatrix M).det
```

The characteristic polynomial of `M` is `det (X · 1 − M)`, the matrix `X · 1 − M` having `M`'s entries read as constant polynomials. Statements 1 and 2 use it through the hypothesis `Polynomial.aeval θ (inc σ).charpoly = 0`, and statement 3 through `(M.map (Nat.cast : ℕ → ℤ)).charpoly = X ^ 3 − X − 1`. Kernel-checked: `DefinitionAudit.charpoly_eq_det`, `DefinitionAudit.charmatrix_eq`, `DefinitionAudit.eval_charpoly` (`M.charpoly` evaluated at `t` is `det (t · 1 − M)`), and `DefinitionAudit.padovan_matrix_charpoly` (the Padovan matrix `!![0, 0, 1; 1, 0, 1; 0, 1, 0]` has characteristic polynomial `X ^ 3 − X − 1`, so the hypothesis of statement 3 is satisfiable).

## 2. `Polynomial.eval₂` and `Polynomial.aeval`

`Mathlib/Algebra/Polynomial/Eval/Defs.lean`, lines 55–58: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Eval/Defs.lean#L55-L58>

```lean
/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
irreducible_def eval₂ (p : R[X]) : S :=
  p.sum fun e a => f a * x ^ e
```

`Mathlib/Algebra/Polynomial/AlgebraMap.lean`, lines 243–258: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/AlgebraMap.lean#L243-L258>

```lean
variable (R A) in
/-- Given a valuation `x` of the variable in an `R`-algebra `A`, the bijection induced by the unique
`R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`. -/
@[simps! symm_apply]
def aevalEquiv : A ≃ (R[X] →ₐ[R] A) where
  toFun x := eval₂AlgHom (Algebra.ofId _ _) x (Algebra.commutes · _)
  invFun f := f X
  left_inv := eval₂_X _
  right_inv _ := algHom_ext' (Subsingleton.elim ..) <| eval₂_X ..

/-- Given a valuation `x` of the variable in an `R`-algebra `A`, `aeval R A x` is
the unique `R`-algebra homomorphism from `R[X]` to `A` sending `X` to `x`.

This is a stronger variant of the linear map `Polynomial.leval`. -/
def aeval : R[X] →ₐ[R] A :=
  aevalEquiv R A x
```

`aeval θ p` evaluates the polynomial `p` at `θ` through the algebra map (here `ℤ → ℝ`, `ℚ → ℝ` or `ℚ → ℂ`); `eval₂` is the evaluation sum `Σ f(aₑ) xᵉ`. Two names in the excerpts are section variables bound outside the quoted lines: in the `eval₂` excerpt, `f` and `x` come from `variable (f : R →+* S) (x : S)` (`Mathlib/Algebra/Polynomial/Eval/Defs.lean`, line 53: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Eval/Defs.lean#L53>), and in the `aeval` excerpt, `x` comes from `variable {p q : R[X]} (x : A)` (`Mathlib/Algebra/Polynomial/AlgebraMap.lean`, line 241: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/AlgebraMap.lean#L241>). `DefinitionAudit.aeval_eq_eval₂` kernel-checks that `aeval θ p` is `eval₂ (algebraMap ℤ ℝ) θ p`. The hypothesis `Polynomial.aeval θ (inc σ).charpoly = 0` of statements 1 and 2 says that the real number `θ` is a root of the integer characteristic polynomial of `inc σ`. Kernel-checked: `DefinitionAudit.aeval_charpoly_eq_zero_iff` — for an integer matrix `M` and a real `θ` this holds exactly when some nonzero real vector `v` has `M v = θ v`, so it says precisely that `θ` is a real eigenvalue of `M`.

## 3. `minpoly`

`Mathlib/FieldTheory/Minpoly/Basic.lean`, lines 30–42: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/FieldTheory/Minpoly/Basic.lean#L30-L42>

```lean
open scoped Classical in
/-- Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`IsIntegral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
@[stacks 09GM]
noncomputable def minpoly (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0
```

`minpoly ℚ θ` is the monic rational polynomial of least degree with root `θ` when `θ` is algebraic, and `0` otherwise. Kernel-checked: `DefinitionAudit.minpoly_spec` (for algebraic `θ` it is monic, irreducible, vanishes at `θ`, and divides every rational polynomial vanishing at `θ`), `DefinitionAudit.minpoly_eq_zero_of_not_isIntegral` (the convention `0`), `DefinitionAudit.minpoly_eq_map_minpoly_int` (for an algebraic integer it has integer coefficients) and `DefinitionAudit.natDegree_minpoly_eq_finrank` (its `natDegree` is the degree `[ℚ(θ) : ℚ]`). The convention `0` does not make the Pisot hypothesis vacuous in the compared statements: in statement 1, `θ` is a root of the monic integer polynomial `(inc σ).charpoly`, hence an algebraic integer (`DefinitionAudit.isIntegral_of_aeval_charpoly`), and statement 4 assumes `IsIntegral ℤ θ`.

## 4. `Polynomial.roots` and `Polynomial.aroots`

`Mathlib/Algebra/Polynomial/Roots.lean`, lines 56–61: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Roots.lean#L56-L61>

```lean
/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : R[X]) : Multiset R :=
  haveI := Classical.decEq R
  haveI := Classical.dec (p = 0)
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)
```

`Mathlib/Algebra/Polynomial/Roots.lean`, lines 479–482: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Roots.lean#L479-L482>

```lean
/-- Given a polynomial `p` with coefficients in a ring `T` and a `T`-algebra `S`, `aroots p S` is
the multiset of roots of `p` regarded as a polynomial over `S`. -/
noncomputable abbrev aroots (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Multiset S :=
  (p.map (algebraMap T S)).roots
```

`p.aroots ℂ` is the multiset of complex roots of `p`, with multiplicity (empty for the zero polynomial). The Pisot hypothesis of statements 1 and 4 is `∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1`. Kernel-checked, for algebraic real `θ`: `DefinitionAudit.mem_aroots_minpoly` (the members are exactly the complex roots of `minpoly ℚ θ`), `DefinitionAudit.self_mem_aroots_minpoly` (`θ` is one of them), `DefinitionAudit.aroots_minpoly_nodup` (no root is repeated, so `z ≠ θ` excludes exactly one member) and `DefinitionAudit.card_aroots_minpoly` (there are as many as the degree of `θ`). So the hypothesis says that every conjugate of `θ` other than `θ` lies strictly inside the unit circle: `θ` is a Pisot number when also `θ > 1` and `θ` is an algebraic integer.

## 5. `Polynomial.degree` and `Polynomial.natDegree`

`Mathlib/Algebra/Polynomial/Degree/Defs.lean`, lines 45–53: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Polynomial/Degree/Defs.lean#L45-L53>

```lean
/-- `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.
`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise
`degree 0 = ⊥`. -/
def degree (p : R[X]) : WithBot ℕ :=
  p.support.max

/-- `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`. -/
def natDegree (p : R[X]) : ℕ :=
  (degree p).unbotD 0
```

`natDegree` is the degree as a natural number, with `natDegree 0 = 0`. Statement 4's hypothesis `(minpoly ℚ θ).natDegree ≤ 3` says that `θ` has degree at most `3` (`DefinitionAudit.natDegree_minpoly_eq_finrank`).

## 6. `IsIntegral`

`Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean`, lines 37–40: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean#L37-L40>

```lean
/-- An element `x` of `A` is said to be integral over `R` with respect to `f`
if it is a root of a monic polynomial `p : R[X]` evaluated under `f` -/
def RingHom.IsIntegralElem (f : R →+* A) (x : A) :=
  ∃ p : R[X], Monic p ∧ eval₂ f x p = 0
```

`Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean`, lines 50–54: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/IntegralClosure/IsIntegral/Defs.lean#L50-L54>

```lean
/-- An element `x` of an algebra `A` over a commutative ring `R` is said to be *integral*,
if it is a root of some monic polynomial `p : R[X]`.
Equivalently, the element is integral over `R` with respect to the induced `algebraMap` -/
def IsIntegral (x : A) : Prop :=
  (algebraMap R A).IsIntegralElem x
```

`IsIntegral ℤ θ`: `θ` is a root of a monic integer polynomial (an algebraic integer). Kernel-checked: `DefinitionAudit.isIntegral_iff` and `DefinitionAudit.isIntegral_of_aeval_charpoly`.

## 7. The norm on `ℂ`

`Mathlib/Analysis/Complex/Norm.lean`, lines 27–31: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Complex/Norm.lean#L27-L31>

```lean
@[no_expose]
instance instNorm : Norm ℂ where
  norm z := √(normSq z)

theorem norm_def (z : ℂ) : ‖z‖ = √(normSq z) := (rfl)
```

`‖z‖ = √(normSq z)`, the modulus. The instance is marked `@[no_expose]` at this pin, so it does not unfold in importing modules; `Complex.norm_def` is the public statement. Kernel-checked: `DefinitionAudit.complex_norm_eq` (`‖z‖ = √(re² + im²)`) and `DefinitionAudit.complex_norm_lt_one_iff` (`‖z‖ < 1` exactly when `z` lies strictly inside the unit circle).

## 8. `Nat.iterate` and the notation `f^[n]`

`Mathlib/Logic/Function/Iterate.lean`, lines 40–46: <https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Logic/Function/Iterate.lean#L40-L46>

```lean
/-- Iterate a function. -/
def Nat.iterate {α : Sort u} (op : α → α) : ℕ → α → α
  | 0, a => a
  | succ k, a => iterate op k (op a)

@[inherit_doc Nat.iterate]
notation:max f "^[" n "]" => Nat.iterate f n
```

`f^[n]` is `f` composed with itself `n` times. In statement 5, `(sub s)^[n] [x]` is the `n`-th iterate of the word map from the one-letter seed `x`. Kernel-checked: `DefinitionAudit.iterate_zero_apply` and `DefinitionAudit.iterate_succ_apply'`.

## 9. `List.IsInfix` and the notation `<:+:` (core Lean)

`src/Init/Data/List/Basic.lean`, lines 1233–1242: <https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/List/Basic.lean#L1233-L1242>

```lean
/--
The first list is a contiguous sub-list of the second list. Typically written with the `<:+:`
operator.

In other words, `l₁ <:+: l₂` means that there exist lists `s : List α` and `t : List α` such that
`l₂` has the form `s ++ l₁ ++ t`.
-/
def IsInfix (l₁ : List α) (l₂ : List α) : Prop := Exists fun s => Exists fun t => s ++ l₁ ++ t = l₂

@[inherit_doc] infixl:50 " <:+: " => IsInfix
```

`u <:+: w`: `w = p ++ u ++ t` for some lists `p, t`, that is, `u` is a factor (a contiguous sublist) of `w`. Statement 5 uses it for factors of iterates. Kernel-checked: `DefinitionAudit.isInfix_iff`.

## 10. `List.countP` and `List.count` (core Lean)

`src/Init/Data/List/Basic.lean`, lines 1788–1812: <https://github.com/leanprover/lean4/blob/11acb17ec6b07a8f9e9173e6845197929540936b/src/Init/Data/List/Basic.lean#L1788-L1812>

```lean
/--
Counts the number of elements in the list `l` that satisfy the Boolean predicate `p`.

Examples:
 * `[1, 2, 3, 4, 5].countP (· % 2 == 0) = 2`
 * `[1, 2, 3, 4, 5].countP (· < 5) = 4`
 * `[1, 2, 3, 4, 5].countP (· > 5) = 0`
-/
@[inline] def countP (p : α → Bool) (l : List α) : Nat := go l 0 where
  /-- Auxiliary for `countP`: `countP.go p l acc = countP p l + acc`. -/
  @[specialize] go : List α → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => if p x then go xs (acc + 1) else go xs acc

/-! ### count -/

/--
Counts the number of times an element occurs in a list.

Examples:
 * `[1, 1, 2, 3, 5].count 1 = 2`
 * `[1, 1, 2, 3, 5].count 5 = 1`
 * `[1, 1, 2, 3, 5].count 4 = 0`
-/
@[inline] def count [BEq α] (a : α) : List α → Nat := countP (· == a)
```

`l.count a` is the number of occurrences of `a` in `l`; the Challenge's `inc σ i j` is `(σ j).count i`, cast to `ℤ`. Kernel-checked: `DefinitionAudit.count_eq_length_filter` and `DefinitionAudit.padovan_matrix_eq_count` (the matrix `!![0, 0, 1; 1, 0, 1; 0, 1, 0]` of statement 3 lists its rows, and its entry `(i, j)` counts the letter `i` in the Padovan image of `j`).
