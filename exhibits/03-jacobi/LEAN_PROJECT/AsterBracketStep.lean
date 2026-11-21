import AsterNearest

/-!
# Count-preserving rational bisection

The *half-open* spectral convention matters: a drop in the count of
eigenvalues strictly above an energy counts eigenvalues in `(left, right]`.
No root avoidance is needed to bisect this invariant, even when the
midpoint is exactly an eigenvalue.
-/

namespace AsterCertificate

/-- A rational interval with a certified positive Sturm-count drop.
The two endpoints and proof fields keep construction and validation
separate; no spectral approximation is hidden in the definition. -/
structure CountBracket (d b : ℕ → ℚ) (n : ℕ) where
  left : ℚ
  right : ℚ
  ordered : left < right
  drop : qCount d b n right < qCount d b n left

namespace CountBracket

variable {d b : ℕ → ℚ} {n : ℕ}

def midpoint (w : CountBracket d b n) : ℚ :=
  (w.left + w.right) / 2

theorem left_lt_midpoint (w : CountBracket d b n) :
    w.left < w.midpoint := by
  dsimp [midpoint]
  linarith [w.ordered]

theorem midpoint_lt_right (w : CountBracket d b n) :
    w.midpoint < w.right := by
  dsimp [midpoint]
  linarith [w.ordered]

/-- **Certified bisection.** The new interval always has a strict
Sturm-count drop. This remains valid even when its midpoint is a root. -/
def bisect (w : CountBracket d b n) : CountBracket d b n :=
  if h : qCount d b n w.midpoint < qCount d b n w.left then
    ⟨w.left, w.midpoint, w.left_lt_midpoint, h⟩
  else
    ⟨w.midpoint, w.right, w.midpoint_lt_right, by
      have hdrop := w.drop
      omega⟩

theorem bisect_width (w : CountBracket d b n) :
    (w.bisect.right - w.bisect.left) =
      (w.right - w.left) / 2 := by
  dsimp [bisect]
  split_ifs <;> dsimp [midpoint] <;> ring

theorem bisect_inside (w : CountBracket d b n) :
    w.left ≤ w.bisect.left ∧
    w.bisect.right ≤ w.right := by
  dsimp [bisect]
  split_ifs
  · exact ⟨le_rfl, (w.midpoint_lt_right).le⟩
  · exact ⟨(w.left_lt_midpoint).le, le_rfl⟩

/-- Iterate a total, exactly bounded number of count-preserving steps. -/
def refine (w : CountBracket d b n) : ℕ → CountBracket d b n
  | 0 => w
  | k + 1 => (refine w k).bisect

/-- Rational width after exactly `k` steps: no analytic estimate
or limiting argument is needed. -/
theorem refine_width (w : CountBracket d b n) (k : ℕ) :
    (w.refine k).right - (w.refine k).left =
      (w.right - w.left) / (2 : ℚ)^k := by
  induction k with
  | zero => simp [refine]
  | succ k ih =>
      rw [refine, bisect_width, ih, pow_succ]
      ring

#print axioms bisect_width
#print axioms refine_width

end CountBracket

end AsterCertificate
