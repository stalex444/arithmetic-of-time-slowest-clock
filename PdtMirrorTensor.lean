/-
# Mirroring substitutions reverses their iterates

For a substitution `s` on any alphabet, `mir s x = (s x).reverse`, and `tens` is
the row-major product of two substitutions on the product alphabet.

  L1  `sub (mir s) w.reverse = (sub s w).reverse`
  L2  `tens (mir s) (mir t) = mir (tens s t)`
  T   `(sub (tens (mir s) (mir t)))^[n] [z] = ((sub (tens s t))^[n] [z]).reverse`

So mirroring a substitution reverses every iterate from a one-letter seed
(`iterate_mir_seed`), and mirroring both factors reverses every iterate of the
product from a one-letter seed. Consequences: the two single-mirrored products
have mutually reversed iterates (`single_mirrors_reverse`), so no word is one-way
in both (`not_oneWay_both`, `not_oneWayAt_both`); and if both rules are
palindromic (`mir s = s`), every iterate of the product is a palindrome
(`palindromic_iterate`) and its factor set is closed under reversal
(`palindromic_reversal_closed`). The product is row-major; column-major follows
by swapping the factors.
-/

module
public import Mathlib

@[expose] public section

namespace PdtMirror

variable {A B : Type*}

/-! ## Substitutions and their mirrors -/

/-- Letterwise application of a substitution to a word. -/
def sub (s : A → List A) : List A → List A
  | [] => []
  | x :: w => s x ++ sub s w

@[simp] theorem sub_nil (s : A → List A) : sub s [] = [] := rfl

@[simp] theorem sub_cons (s : A → List A) (x : A) (w : List A) :
    sub s (x :: w) = s x ++ sub s w := rfl

theorem sub_append (s : A → List A) (u v : List A) :
    sub s (u ++ v) = sub s u ++ sub s v := by
  induction u with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

/-- The mirror of a substitution: every image word read backwards. -/
def mir (s : A → List A) : A → List A := fun x => (s x).reverse

@[simp] theorem mir_mir (s : A → List A) : mir (mir s) = s := by
  funext x; simp [mir]

/-! ## L1 — a mirrored substitution acts on the reversed word -/

/-- **Lemma 1.** Applying the mirrored substitution to the reversed word gives
the reverse of applying the original substitution to the word. -/
theorem sub_mir_reverse (s : A → List A) (w : List A) :
    sub (mir s) w.reverse = (sub s w).reverse := by
  induction w with
  | nil => simp
  | cons x xs ih =>
      simp [List.reverse_cons, sub_append, ih, mir]

/-- **Lemma 1, iterated.** Every iterate of the mirrored substitution on the
reversed word is the reverse of the corresponding iterate of the original. -/
theorem iterate_mir_reverse (s : A → List A) (n : ℕ) (w : List A) :
    (sub (mir s))^[n] w.reverse = ((sub s)^[n] w).reverse := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        sub_mir_reverse, ih]

/-- A one-letter seed is its own reversal, so the iterates of a mirrored
substitution from a seed reverse the iterates of the original from that seed. -/
theorem iterate_mir_seed (s : A → List A) (n : ℕ) (x : A) :
    (sub (mir s))^[n] [x] = ((sub s)^[n] [x]).reverse := by
  have := iterate_mir_reverse s n [x]; simpa using this

/-! ## L2 — the tensor commutes with mirroring -/

/-- The row-major tensor of two substitutions, on the product alphabet. -/
def tens (s : A → List A) (t : B → List B) : A × B → List (A × B) :=
  fun p => (s p.1).flatMap (fun x => (t p.2).map (fun y => (x, y)))

private theorem reverse_flatMap (l : List A) (f : A → List B) :
    (l.flatMap f).reverse = l.reverse.flatMap (fun x => (f x).reverse) := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.reverse_append, ih]

/-- **Lemma 2.** The tensor of the two mirrors is the mirror of the tensor:
reversing both factors' images reverses the product image exactly. -/
theorem tens_mir (s : A → List A) (t : B → List B) :
    tens (mir s) (mir t) = mir (tens s t) := by
  funext p
  simp [tens, mir, reverse_flatMap]

/-! ## The theorem -/

/-- **Mirror equivariance of the tensor.** Mirroring both factors reverses every
iterate of the product substitution, from every seed. -/
theorem iterate_tens_mir (s : A → List A) (t : B → List B) (n : ℕ) (z : A × B) :
    (sub (tens (mir s) (mir t)))^[n] [z] = ((sub (tens s t))^[n] [z]).reverse := by
  rw [tens_mir]; exact iterate_mir_seed (tens s t) n z

/-- Factor form: the words occurring in the double-mirrored system are exactly
the reversals of the words occurring in the original. -/
theorem infix_tens_mir (s : A → List A) (t : B → List B) (n : ℕ) (z : A × B)
    (u : List (A × B)) :
    u <:+: (sub (tens (mir s) (mir t)))^[n] [z] ↔
      u.reverse <:+: (sub (tens s t))^[n] [z] := by
  rw [iterate_tens_mir, ← List.reverse_infix, List.reverse_reverse]

/-! ## Words one-way in both single-mirrored products -/

/-- `u` is one-way for the substitution `T` when it occurs in some iterate from some seed and its reversal occurs in none. -/
def OneWay {C : Type*} (T : C → List C) (u : List C) : Prop :=
  (∃ n z, u <:+: (sub T)^[n] [z]) ∧ (∀ n z, ¬ u.reverse <:+: (sub T)^[n] [z])

/-- Mirroring one factor and mirroring the other give mutually reversed
languages. -/
theorem infix_single_mirrors (s : A → List A) (t : B → List B) (n : ℕ)
    (z : A × B) (u : List (A × B)) :
    u <:+: (sub (tens s (mir t)))^[n] [z] ↔
      u.reverse <:+: (sub (tens (mir s) t))^[n] [z] := by
  have h := infix_tens_mir (mir s) t n z u
  rwa [mir_mir] at h

/-- No word is one-way in both single-mirrored products, for any two substitutions on any alphabets. -/
theorem not_oneWay_both (s : A → List A) (t : B → List B) (u : List (A × B)) :
    ¬ (OneWay (tens (mir s) t) u ∧ OneWay (tens s (mir t)) u) := by
  rintro ⟨⟨⟨n, z, hz⟩, -⟩, -, hno⟩
  exact hno n z ((infix_single_mirrors s t n z u.reverse).2 (by simpa using hz))

/-- At one fixed depth `n` and seed `z`, no word occurs in the `s`-mirrored iterate with its reversal absent and also in the `t`-mirrored iterate with its reversal absent. -/
theorem not_oneWayAt_both (s : A → List A) (t : B → List B) (n : ℕ) (z : A × B)
    (u : List (A × B)) :
    ¬ ((u <:+: (sub (tens (mir s) t))^[n] [z] ∧
        ¬ u.reverse <:+: (sub (tens (mir s) t))^[n] [z]) ∧
       (u <:+: (sub (tens s (mir t)))^[n] [z] ∧
        ¬ u.reverse <:+: (sub (tens s (mir t)))^[n] [z])) := by
  rintro ⟨⟨-, hC⟩, hQ, -⟩
  exact hC ((infix_single_mirrors s t n z u).1 hQ)

/-- Corollary in factor-set form: at every depth and seed the two single-mirrored
iterates are exact reversals of one another. -/
theorem single_mirrors_reverse (s : A → List A) (t : B → List B) (n : ℕ) (z : A × B) :
    (sub (tens s (mir t)))^[n] [z] = ((sub (tens (mir s) t))^[n] [z]).reverse := by
  have h := iterate_tens_mir (mir s) t n z
  rwa [mir_mir] at h

/-! ## Palindromic rules give reversal-closed products -/

/-- **No manufacture.** If both substitution rules are palindromic, every
iterate of the tensor is a palindrome, so its factor set is closed under
reversal: the product cannot create handedness out of mirror-symmetric rules. -/
theorem palindromic_reversal_closed (s : A → List A) (t : B → List B)
    (hs : ∀ x, (s x).reverse = s x) (ht : ∀ y, (t y).reverse = t y)
    (n : ℕ) (z : A × B) (u : List (A × B)) :
    u <:+: (sub (tens s t))^[n] [z] ↔
      u.reverse <:+: (sub (tens s t))^[n] [z] := by
  have hms : mir s = s := by funext x; exact hs x
  have hmt : mir t = t := by funext y; exact ht y
  have h := infix_tens_mir s t n z u.reverse
  rw [hms, hmt, List.reverse_reverse] at h
  exact h.symm

/-- The palindrome itself, stated separately: with both rules mirror-symmetric
every iterate of the product reads the same in both directions. -/
theorem palindromic_iterate (s : A → List A) (t : B → List B)
    (hs : ∀ x, (s x).reverse = s x) (ht : ∀ y, (t y).reverse = t y)
    (n : ℕ) (z : A × B) :
    ((sub (tens s t))^[n] [z]).reverse = (sub (tens s t))^[n] [z] := by
  have hms : mir s = s := by funext x; exact hs x
  have hmt : mir t = t := by funext y; exact ht y
  have h := iterate_tens_mir s t n z
  rw [hms, hmt] at h
  exact h.symm

end PdtMirror
