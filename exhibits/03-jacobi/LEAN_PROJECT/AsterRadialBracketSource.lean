import AsterNearest

/-!
# Radial Sturm brackets

An inner radius has *zero* count drop; an outer radius has a *positive*
count drop. Both are exact rational assertions. Bisection never needs
an eigenvalue index or a nonroot search.
-/

namespace AsterCertificate

def radialCount (d b : ℕ → ℚ) (n : ℕ) (τ r : ℚ) : ℕ :=
  qCount d b n (τ - r) - qCount d b n (τ + r)

/-- We deliberately keep the two count comparisons directly rather than
subtracting Naturals: this avoids truncated-subtraction ambiguity. -/
structure RadialBracket (d b : ℕ → ℚ) (n : ℕ) (τ : ℚ) where
  inner : ℚ
  outer : ℚ
  inner_pos : 0 < inner
  ordered : inner < outer
  count_antitone : ∀ x y : ℚ, x ≤ y → qCount d b n y ≤ qCount d b n x
  inner_empty :
    qCount d b n (τ - inner) = qCount d b n (τ + inner)
  outer_occupied :
    qCount d b n (τ + outer) < qCount d b n (τ - outer)

namespace RadialBracket

variable {d b : ℕ → ℚ} {n : ℕ} {τ : ℚ}

def midpoint (w : RadialBracket d b n τ) : ℚ :=
  (w.inner + w.outer) / 2

theorem inner_lt_midpoint (w : RadialBracket d b n τ) :
    w.inner < w.midpoint := by
  dsimp [midpoint]
  linarith [w.ordered]

theorem midpoint_lt_outer (w : RadialBracket d b n τ) :
    w.midpoint < w.outer := by
  dsimp [midpoint]
  linarith [w.ordered]

/-- The exact rational Sturm test decides which radial bound can move.
An eigenvalue exactly at the midpoint is handled by the half-open
counting convention, not by a special-case root test. -/
def bisect (w : RadialBracket d b n τ) : RadialBracket d b n τ :=
  if h :
      qCount d b n (τ + w.midpoint) <
        qCount d b n (τ - w.midpoint) then
    ⟨w.inner, w.midpoint, w.inner_pos, w.inner_lt_midpoint,
      w.count_antitone, w.inner_empty, h⟩
  else
    ⟨w.midpoint, w.outer,
      lt_trans w.inner_pos w.inner_lt_midpoint,
      w.midpoint_lt_outer, w.count_antitone,
      by
        have hm :
            qCount d b n (τ - w.midpoint) ≤
              qCount d b n (τ + w.midpoint) := by omega
        have hmono :
            qCount d b n (τ + w.midpoint) ≤
              qCount d b n (τ - w.midpoint) := by
          apply w.count_antitone
          have hpos : 0 ≤ w.midpoint := (w.inner_pos.trans w.inner_lt_midpoint).le
          linarith
        omega,
      w.outer_occupied⟩

theorem bisect_width (w : RadialBracket d b n τ) :
    w.bisect.outer - w.bisect.inner =
      (w.outer - w.inner) / 2 := by
  dsimp [bisect]
  split_ifs <;> dsimp [midpoint] <;> ring

def refine (w : RadialBracket d b n τ) : ℕ → RadialBracket d b n τ
  | 0 => w
  | k + 1 => (refine w k).bisect

theorem refine_width (w : RadialBracket d b n τ) (k : ℕ) :
    (w.refine k).outer - (w.refine k).inner =
      (w.outer - w.inner) / (2 : ℚ)^k := by
  induction k with
  | zero => simp [refine]
  | succ k ih =>
      rw [refine, bisect_width, ih, pow_succ]
      ring

#print axioms bisect_width
#print axioms refine_width

end RadialBracket
end AsterCertificate
