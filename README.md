# The Arithmetic of Time: the slowest settling clock on three letters

Among all substitution rules on at most three letters whose incidence
matrix has a Pisot eigenvalue `θ > 1`, the least such `θ` is the plastic
number `ρ ≈ 1.3247`, the real root of `ρ³ = ρ + 1`, and only two rules
attain it: the Padovan rule `a ↦ b, b ↦ c, c ↦ ab` and its mirror
`c ↦ ba`, up to renaming the letters. The slowest settling clock on three
letters is unique up to mirror image. Both minimal rules are chiral, in
opposite directions: under the Padovan rule the word `ca` occurs in an
iterate and `ac` occurs in none; under its mirror, the reverse.

Here a substitution `σ` sends each letter to a word (possibly empty), its
incidence matrix `inc σ` has entry `(i, j)` equal to the number of letters
`i` in the image of `j`, and a Pisot eigenvalue is a real eigenvalue
`θ > 1` all of whose other conjugates lie strictly inside the unit circle.
Everything is kernel-checked in Lean 4 against Mathlib: five compared
theorems, each on the axioms `propext`, `Classical.choice` and
`Quot.sound` alone.

## The compared statements

All five are in namespace `ArithmeticOfTime`. Letters are `Fin k`; on
`Fin 3` the letters `0, 1, 2` stand for `a, b, c`, and `s` is the Padovan
substitution `0 ↦ [1], 1 ↦ [2], 2 ↦ [0, 1]`. `mir σ` reads every image
backwards, `sub σ` applies `σ` letterwise to a word, and `u <:+: w` says
that `u` is a factor (a contiguous sublist) of `w`.

1. `padovan_minimal_unique` — for `σ` on `k ≤ 3` letters and a real
   eigenvalue `θ > 1` of `inc σ` that is a Pisot number (every complex root
   of `minpoly ℚ θ` other than `θ` has norm `< 1`): `ρ ≤ θ`, and `θ = ρ`
   exactly when, after renaming the letters, `σ` is `s` or `mir s`.
2. `padovan_eigenvalue_unique` — the equivalence of statement 1 for every
   real eigenvalue `θ` of `inc σ`, with no Pisot hypothesis and no `1 < θ`.
3. `padovan_matrix_unique` — a `3 × 3` matrix over `ℕ` with characteristic
   polynomial `x³ − x − 1` is the Padovan incidence matrix
   `!![0, 0, 1; 1, 0, 1; 0, 1, 0]` after one simultaneous permutation of its
   rows and columns.
4. `pisot_ge_plastic` — every Pisot number `θ` of degree at most `3`
   satisfies `ρ ≤ θ`.
5. `padovan_rules_chiral` — under `s`, `ca` (`[2, 0]`) is a factor of an
   iterate from the seed `a` and `ac` (`[0, 2]`) is a factor of no iterate
   from any seed; under `mir s`, the reverse.

Statement 1 is the headline and combines two others: its bound is
statement 4 applied to `θ` (a root of the monic degree-`k` polynomial
`(inc σ).charpoly`, hence an algebraic integer of degree at most `3`), and
its equivalence is statement 2, which needs no Pisot hypothesis. Statement 3
is the matrix classification on which statement 2 rests. In statement 5 the
Padovan half is the companion entry's compared chirality statement,
restated over `sub s`; the mirror half follows because mirroring reverses
every iterate from a one-letter seed.

In statements 1, 2 and 4 the plastic number enters as any real `ρ` with
`ρ ^ 3 = ρ + 1` (exactly one real number satisfies that equation). Neither
primitivity nor the unit property is assumed, every alphabet size `k ≤ 3`
is allowed, and images may be empty; renaming the letters is an
equivalence `Fin k ≃ Fin 3` applied letterwise, so the equality case forces
`k = 3`. In statement 1, `θ` is an algebraic integer because it is a root
of the monic integer polynomial `(inc σ).charpoly`. That `ρ` itself occurs,
as a Pisot eigenvalue of the Padovan incidence matrix, is
`padovan_pisot_eigenvalue` in `Supplement.lean`, proved and not compared;
with statement 1 it makes `ρ` the least such eigenvalue.

## Prior art

The bound `ρ ≤ θ` is Siegel's theorem (Duke Math. J. 11 (1944), 597–602),
which holds in every degree; statement 4 restricts it to degree at most
three, and it is not new. Here it is obtained through the minimal Mahler
measures of the registered entry PALOMAR-2026-08-31-000004
([stalex444/mahler-measure-minima](https://github.com/stalex444/mahler-measure-minima)
at `ca3df22`) and a short bridge: a Pisot number is the Mahler measure of
its minimal polynomial (`Time.Clock.mahler_eq_of_pisot` in
`SlowestClock.lean`). The uniqueness was observed without proof by Mercat
(Experiment. Math. 29 (2020), §1,
[doi:10.1080/10586458.2018.1446063](https://doi.org/10.1080/10586458.2018.1446063)):
up to a permutation of the letters, the Padovan substitution and its
reversal are the only substitutions on three letters associated with the
smallest Pisot number. The abstract of his
[preprint](https://www.i2m.univ-amu.fr/perso/paul.mercat/Recherche/SmallestPisotSubstitution.pdf)
adds that no substitution on fewer letters is associated with it; statement
2 covers that case.

## Contribution

A kernel-checked proof of the combined statement, which Mercat states
without proof. In statement 2, `θ` may be any real eigenvalue of the
incidence matrix, not only the dominant one; no statement assumes
primitivity, the unit property or non-erasing images, and every alphabet
size `k ≤ 3` is allowed. In the equality case these are consequences, not
hypotheses: `θ = ρ` forces `k = 3` and characteristic polynomial
`x³ − x − 1`. The entry adds the chirality of both minimal rules
(statement 5; see Companion entry below for what is new in it). The
classification goes through statement 3: the trace `0` forces a zero diagonal, the sum of the principal
`2 × 2` minors leaves exactly one `2`-cycle and the determinant exactly one
`3`-cycle, which fixes the matrix up to relabelling; an incidence matrix
fixes each image as a multiset, and only the image `{a, b}` of `c` can be
ordered in two ways. No claim of a first formalization is made.

## Companion entry

This entry is the companion of the registered entry
PALOMAR-2026-08-19-000006,
[stalex444/arithmetic-of-time](https://github.com/stalex444/arithmetic-of-time),
whose compared statements concern the factor language of the Padovan
substitution: every `a` in a positive iterate is followed by `b`, `ca`
occurs and `ac` does not, and no factor of length at least four is a
palindrome. The Padovan half of statement 5 here is that entry's compared
chirality statement, restated over `sub s`; the mirror half, and
statements 1–4, are not compared there.

## Scope: the claim

The Scope of the companion entry applies to this one unchanged. It is
reproduced verbatim below from that entry's README (its one relative link,
to the paper directory, now points into the companion repository); the
declarations and files it names are in the companion repository at its
registered revision
[`c48eb12`](https://github.com/stalex444/arithmetic-of-time/tree/c48eb12817dd1d7ff3dc4d92306c7a4f249e6d7d).
`Time.tick_contraction` (in `Settling.lean`) and `Chirality.lean` are also
in this one, while `Time.aperiodic` and `Time.balanced`
([`MechanicalWord.lean`](https://github.com/stalex444/arithmetic-of-time/blob/c48eb12817dd1d7ff3dc4d92306c7a4f249e6d7d/MechanicalWord.lean))
and
[`OriginDefect.lean`](https://github.com/stalex444/arithmetic-of-time/blob/c48eb12817dd1d7ff3dc4d92306c7a4f249e6d7d/OriginDefect.lean)
are there only.

The position taken here is that **time is this arithmetic** — an identity, in
the same grammar as "heat is molecular motion," and earned the same way: by
coverage. The temporal invariants are, one by one, theorems of a single
structure. The tick is multiplication by a unit, and its contraction rate is
exact (`Time.tick_contraction`). The tick never repeats (the rotation is
irrational, `Time.aperiodic`), yet is never random (the word is balanced,
`Time.balanced`). And the settled history is *handed*: read backwards, it is
provably a different object — not by convention, but by theorem
(`Chirality.lean`). On this reading the history is one completed object; the
asymmetry of time is a property of the whole; and nothing needs to orient a
flow, because nothing flows — the "now" is where an observer sits in the
structure, with records on one side (the marked origin of
`OriginDefect.lean`).

Two kinds of statement appear in this repository, and the boundary between
them is kept explicit. **Theorems**: every mathematical claim in the Lean
modules compiles in the kernel; nothing rests on trust. **The
identification**: that physical time is this structure — rather than merely
being described by it — is an identification, the same kind of statement as
"the metric tensor is spacetime geometry." No experiment distinguishes an
exact description from an identity, so this is not a claim any theorem could
settle; it is validated the way every physical identification is validated,
through the measured consequences of the framework it belongs to (see [`paper/`](https://github.com/stalex444/arithmetic-of-time/tree/c48eb12817dd1d7ff3dc4d92306c7a4f249e6d7d/paper) and the companion deposits, e.g. doi:10.5281/zenodo.20417378). The mathematics stands regardless. The claim is which
thing it is.

## Layout and build

```
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build
```

Toolchain `leanprover/lean4:v4.35.0-rc2`, Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55` (pinned in `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`); a green build is the kernel
verification. The kernel check of `PdtMahlerBox.lean` takes a minute or
more.

| File | Content |
| --- | --- |
| `Challenge.lean` | the five compared statements, with `sorry` placeholders; imports Mathlib only |
| `Solution.lean` | the same five statements, proved by direct transfer from the proof modules, with an in-build axiom audit |
| `comparator.json` | the machine comparison surface: five theorems, four definitions (`s`, `mir`, `inc`, `sub`) |
| `Supplement.lean` | `padovan_pisot_eigenvalue`: `ρ` is a Pisot eigenvalue of the Padovan incidence matrix (proved, not compared) |
| `DefinitionAudit.lean` | kernel-checked facts about the imported definitions (not compared; imports Mathlib only) |
| `MATHLIB_DEFINITIONS.md` | the imported definitions, quoted verbatim at the pinned revisions |
| `formalization.yaml` | sources, classification, scope and disclosure |
| `BUILD.txt` | build record: toolchain, Mathlib revision, `#print axioms`, statement identity, module provenance, file hashes |

The `PDT` namespace and the `Pdt*` file prefix are inherited from the
author's parent development,
[stalex444/pdt-lean](https://github.com/stalex444/pdt-lean) (Pisot
Dimensional Theory); the degree-at-most-3 case of Siegel's bound is
`Time.Clock.pisot_ge_rho` in `SlowestClock.lean`.

Proof modules:

| Module | Content | Provenance |
| --- | --- | --- |
| `SlowestClock.lean` | `matrix_unique`, `clock_unique`, `mahler_eq_of_pisot`, `pisot_ge_rho`, `slowest_clock` (namespace `Time.Clock`) | the author's development; in neither registered entry |
| `PdtMirrorTensor.lean` | mirrors of substitutions on any alphabet: mirroring reverses every iterate from a one-letter seed (`PdtMirror.iterate_mir_seed`) | the author's development; in neither registered entry |
| `Chirality.lean` | the Padovan successor invariant and `ac_not_factor` (namespace `Time.Padovan`) | companion entry at `c48eb12`, module-system header added |
| `Irreducibility.lean` | `x³ − x − 1` and `x⁴ − x − 1` are irreducible over `ℚ` | companion entry at `c48eb12`, module-system header added, and one proof repair in `quartic_irred_zmod2` (statement unchanged) |
| `Settling.lean` | the root bound `one_lt_root` and the settling theorems of the companion entry | companion entry at `c48eb12`, module-system header added |
| `PdtMahler.lean`, `PdtMahlerBox.lean`, `PdtMahlerMain.lean`, `PdtMahlerTheta.lean`, `PdtMahlerWindow.lean` | the minimal Mahler measures in degrees 2, 3, 4 | PALOMAR-2026-08-31-000004 at `ca3df22`: statements and proofs unchanged; module-system header added; docstring edits in all but `PdtMahlerBox.lean` that remove internal cross-references |
| `PdtPisotBoundary.lean`, `PdtIrreducible.lean` | the non-real roots of `x³ − x − 1` have norm `< 1` (and those of `x⁴ − x − 1` norm `> 1`); `x³ − x − 1` and `x⁴ − x − 1` are irreducible over `ℤ` and `ℚ` | PALOMAR-2026-08-31-000004 at `ca3df22`, module-system header added, and in `PdtIrreducible.lean` the same proof repair in `quartic_irred_zmod2` |

**Imported definitions.** `MATHLIB_DEFINITIONS.md` quotes verbatim, with
file paths, line numbers and permalinks, the definitions the compared
statements rest on: from Mathlib at the pinned revision,
`Matrix.charmatrix` and `Matrix.charpoly`, `Polynomial.eval₂` and
`Polynomial.aeval`, `minpoly`, `Polynomial.roots` and `Polynomial.aroots`,
`Polynomial.degree` and `Polynomial.natDegree`, `IsIntegral`, the norm on
`ℂ` and `Nat.iterate` (`f^[n]`); from core Lean at the toolchain's commit,
`List.IsInfix` (`<:+:`), `List.countP` and `List.count`. The remaining
vocabulary (`List.map`, `List.reverse`, `List.flatten`, `Equiv`,
`Matrix.map`, `Fin`, the `!![…]` notation) is standard and is not quoted.
`DefinitionAudit.lean` (a default build target, imports Mathlib only, not
compared) kernel-checks the facts the informal account relies on: the
hypothesis `Polynomial.aeval θ (inc σ).charpoly = 0` says exactly that `θ`
is a real eigenvalue of `inc σ`; such a `θ` is an algebraic integer;
`(minpoly ℚ θ).aroots ℂ` is the multiset of complex conjugates of `θ`,
contains `θ` once, and has as many elements as the degree, which is
`(minpoly ℚ θ).natDegree`; `‖z‖` is the modulus; exactly one real `ρ`
satisfies `ρ³ = ρ + 1`; `!![0, 0, 1; 1, 0, 1; 0, 1, 0]` lists its rows,
counts the letters of the Padovan images and has characteristic polynomial
`X³ − X − 1`; and `<:+:` means a contiguous factor.

## License

MIT — see [`LICENSE`](./LICENSE).
