module
public import Chirality
public import PdtMirrorTensor
public import SlowestClock

@[expose] public section

/-!
# Solution: proved versions of the Challenge declarations

Each public declaration below has exactly the statement of its `Challenge.lean`
counterpart; the definitions `s`, `mir`, `inc` and `sub` are repeated verbatim.

* Statements 1–4 (`padovan_minimal_unique`, `padovan_eigenvalue_unique`,
  `padovan_matrix_unique`, `pisot_ge_plastic`) are transferred from `SlowestClock.lean`
  (namespace `Time.Clock`), whose Padovan substitution `pad` and incidence matrix `inc` agree
  with `s` and `inc` here and whose mirror is `PdtMirror.mir` of `PdtMirrorTensor.lean`.
  `SlowestClock.lean` obtains the bound `ρ ≤ θ` from the Mahler minima of the modules
  `PdtMahler*`, copied with statements and proofs unchanged from the registered entry
  PALOMAR-2026-08-31-000004.
* Statement 5 (`padovan_rules_chiral`) is transferred from `Chirality.lean` (namespace
  `Time.Padovan`, alphabet `Letter`), across the letter encoding `Letter ≃ Fin 3`, for the
  Padovan rule, and from `PdtMirror.iterate_mir_seed` (every iterate of the mirror from a
  one-letter seed is the reversal of the corresponding iterate) for its mirror.
-/

namespace ArithmeticOfTime

/-- The Padovan substitution on `Fin 3` (matches the Challenge definition). -/
def s : Fin 3 → List (Fin 3)
  | 0 => [1]
  | 1 => [2]
  | 2 => [0, 1]

/-! ### Mirror and incidence matrix on an arbitrary alphabet -/

/-- The mirror of a substitution (matches the Challenge). -/
def mir {A : Type*} (σ : A → List A) : A → List A := fun x => (σ x).reverse

private lemma mir_eq {A : Type*} (σ : A → List A) : mir σ = PdtMirror.mir σ := rfl

/-- The incidence matrix of a substitution (matches the Challenge). -/
def inc {A : Type*} [DecidableEq A] (σ : A → List A) : Matrix A A ℤ :=
  fun i j => ((σ j).count i : ℤ)

/-! ### Minimality and uniqueness of the Padovan rule: transfer from `Time.Clock` -/

private lemma s_eq_pad : s = Time.Clock.pad := by
  funext x
  fin_cases x <;> rfl

theorem padovan_minimal_unique {k : ℕ} (hk : k ≤ 3) (σ : Fin k → List (Fin k)) (θ : ℝ)
    (hθ : Polynomial.aeval θ (inc σ).charpoly = 0) (h1 : 1 < θ)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1)
    (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) :
    ρ ≤ θ ∧ (θ = ρ ↔ ∃ e : Fin k ≃ Fin 3,
      (∀ x, (σ x).map e = s (e x)) ∨ (∀ x, (σ x).map e = mir s (e x))) := by
  rw [s_eq_pad, mir_eq]
  exact Time.Clock.slowest_clock hk σ θ hθ h1 hpisot hρ

theorem padovan_eigenvalue_unique {k : ℕ} (hk : k ≤ 3) (σ : Fin k → List (Fin k)) (θ : ℝ)
    (hθ : Polynomial.aeval θ (inc σ).charpoly = 0) (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) :
    θ = ρ ↔ ∃ e : Fin k ≃ Fin 3,
      (∀ x, (σ x).map e = s (e x)) ∨ (∀ x, (σ x).map e = mir s (e x)) := by
  rw [s_eq_pad, mir_eq]
  exact Time.Clock.clock_unique hk σ θ hθ hρ

theorem padovan_matrix_unique (M : Matrix (Fin 3) (Fin 3) ℕ)
    (h : (M.map (Nat.cast : ℕ → ℤ)).charpoly = Polynomial.X ^ 3 - Polynomial.X - 1) :
    ∃ e : Fin 3 ≃ Fin 3, ∀ i j, M i j = !![0, 0, 1; 1, 0, 1; 0, 1, 0] (e i) (e j) :=
  Time.Clock.matrix_unique M h

theorem pisot_ge_plastic (θ : ℝ) (h1 : 1 < θ) (hint : IsIntegral ℤ θ)
    (hdeg : (minpoly ℚ θ).natDegree ≤ 3)
    (hpisot : ∀ z ∈ (minpoly ℚ θ).aroots ℂ, z ≠ (θ : ℂ) → ‖z‖ < 1)
    (ρ : ℝ) (hρ : ρ ^ 3 = ρ + 1) : ρ ≤ θ :=
  Time.Clock.pisot_ge_rho h1 hint hdeg hpisot hρ

/-! ### Both minimal rules are chiral -/

/-- Letterwise application of a substitution `σ` on an arbitrary alphabet: the
concatenation of the image blocks. -/
def sub {A : Type*} (σ : A → List A) (w : List A) : List A := (w.map σ).flatten

private lemma sub_eq_pdt {A : Type*} (σ : A → List A) : sub σ = PdtMirror.sub σ := by
  funext w
  induction w with
  | nil => rfl
  | cons x w ih =>
      rw [PdtMirror.sub_cons, ← ih]
      simp only [sub, List.map_cons, List.flatten_cons]

/-- Every iterate of the mirror from a one-letter seed is the reversal of the
corresponding iterate (transferred from `PdtMirror.iterate_mir_seed`). -/
private lemma iterate_mir_seed' {A : Type*} (σ : A → List A) (n : ℕ) (x : A) :
    (sub (mir σ))^[n] [x] = ((sub σ)^[n] [x]).reverse := by
  simp only [sub_eq_pdt, mir_eq]
  exact PdtMirror.iterate_mir_seed σ n x

/-! The letter encoding `Time.Padovan.Letter ≃ Fin 3` (`a, b, c ↦ 0, 1, 2`). -/

private def enc : Time.Padovan.Letter → Fin 3
  | .a => 0
  | .b => 1
  | .c => 2

private def dec : Fin 3 → Time.Padovan.Letter
  | 0 => .a
  | 1 => .b
  | 2 => .c

private lemma dec_enc (x : Time.Padovan.Letter) : dec (enc x) = x := by
  cases x <;> rfl

private lemma enc_dec (y : Fin 3) : enc (dec y) = y := by
  fin_cases y <;> rfl

private lemma dec_comp_enc : dec ∘ enc = id := funext dec_enc

private lemma s_enc (x : Time.Padovan.Letter) :
    s (enc x) = (Time.Padovan.s x).map enc := by
  cases x <;> rfl

private lemma sub_map_enc (w : List Time.Padovan.Letter) :
    sub s (w.map enc) = (Time.Padovan.S w).map enc := by
  induction w with
  | nil => rfl
  | cons x w ih =>
      simp only [List.map_cons, sub, List.flatten_cons, Time.Padovan.S_cons,
        List.map_append]
      rw [s_enc]
      simp only [sub] at ih
      rw [ih]

private lemma iter_map_enc (n : ℕ) (w : List Time.Padovan.Letter) :
    (sub s)^[n] (w.map enc) = (Time.Padovan.S^[n] w).map enc := by
  induction n generalizing w with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, sub_map_enc, ih]

private lemma iter_single (n : ℕ) (x : Fin 3) :
    (sub s)^[n] [x] = (Time.Padovan.S^[n] [dec x]).map enc := by
  have h := iter_map_enc n [dec x]
  simpa [enc_dec] using h

/-- `ca` is a factor of an iterate of the Padovan rule (`(sub s)^[5] [0] = [2, 0, 1]`). -/
private lemma ca_factor : ([2, 0] : List (Fin 3)) <:+: (sub s)^[5] [0] := by
  decide

/-- `ac` is a factor of no iterate of the Padovan rule, from any seed (transferred from
`Time.Padovan.ac_not_factor`). -/
private lemma ac_not_factor (n : ℕ) (x : Fin 3) :
    ¬ ([0, 2] : List (Fin 3)) <:+: (sub s)^[n] [x] := by
  intro hinf
  rw [iter_single] at hinf
  obtain ⟨s', t', hst⟩ := hinf
  apply Time.Padovan.ac_not_factor n (dec x)
  refine ⟨s'.map dec, t'.map dec, ?_⟩
  have hmap := congrArg (List.map dec) hst
  simpa [List.map_append, List.map_map, dec_comp_enc, dec] using hmap

theorem padovan_rules_chiral :
    ((([2, 0] : List (Fin 3)) <:+: (sub s)^[5] [0]) ∧
      ∀ (n : ℕ) (x : Fin 3), ¬ ([0, 2] : List (Fin 3)) <:+: (sub s)^[n] [x]) ∧
    ((([0, 2] : List (Fin 3)) <:+: (sub (mir s))^[5] [0]) ∧
      ∀ (n : ℕ) (x : Fin 3), ¬ ([2, 0] : List (Fin 3)) <:+: (sub (mir s))^[n] [x]) := by
  refine ⟨⟨ca_factor, fun n x => ac_not_factor n x⟩, ⟨?_, fun n x => ?_⟩⟩
  · rw [iterate_mir_seed']
    exact List.reverse_infix.mpr ca_factor
  · rw [iterate_mir_seed']
    intro h
    exact ac_not_factor n x (List.reverse_infix.mp h)

end ArithmeticOfTime

/-! ### Axiom audit (in-module): the five compared theorems -/

#print axioms ArithmeticOfTime.padovan_minimal_unique
#print axioms ArithmeticOfTime.padovan_eigenvalue_unique
#print axioms ArithmeticOfTime.padovan_matrix_unique
#print axioms ArithmeticOfTime.pisot_ge_plastic
#print axioms ArithmeticOfTime.padovan_rules_chiral
