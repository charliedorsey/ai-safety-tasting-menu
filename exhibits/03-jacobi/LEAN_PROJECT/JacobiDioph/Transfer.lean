import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Quantized-phase Diophantine conditioning

`g : ℝ → ℝ` is sampled at the quantized phases `k / q`, `0 < k < q`, and compared with the
target value `g α`. A *spike of exponent `p`* means that for infinitely many `q` some sample is
within `A / q ^ p` of `g α`. For a Hermitian family whose spectrum is `{g (k/q)}` this is exactly
`‖(H_q - g α)⁻¹‖ > q ^ p / A` infinitely often (resolvent norm = reciprocal spectral distance).

Main results:
* `sample_lower` / `sample_upper`: two-sided comparison of every sample distance with
  `(‖q α‖ / q) ^ m`. The upper bound has explicit thresholds.
* `spikeWith_iff_liouvilleWith`: for irrational `α` and `p > 0`,
  `SpikeWith g α (m * p) ↔ LiouvilleWith p α` (Mathlib's irrationality-exponent predicate).
* `spike_all_iff_liouville`: super-polynomial spikes ↔ `Liouville α`.
* `rational_singular_of_dvd`, `dvd_of_rational_singular`: for `α = a / b` (coprime), some
  sample hits `g α` exactly iff `b ∣ q`.
* `cos_phaseHyp`: the constant Jacobi dispersion `g x = c + 2 β cos (π x)` satisfies the
  hypotheses with `m = 1`, `c = 4 |β| min(α, 1 - α)` and `C = 2 π |β|`.
* `jacobi_resolvent_spike_iff`: the matrix statement, from the host resolvent-distance identity.
-/

open Real Filter Set

namespace JacobiDioph

/-- Distance to the nearest integer, `‖x‖`. -/
noncomputable def nint (x : ℝ) : ℝ := |x - round x|

/-- Spikes of exponent `p`: infinitely often some quantized sample is `A / q ^ p`-close. -/
def SpikeWith (g : ℝ → ℝ) (α p : ℝ) : Prop :=
  ∃ A : ℝ, ∃ᶠ q : ℕ in atTop, ∃ k : ℕ, 0 < k ∧ k < q ∧ |g (k / q) - g α| < A / (q : ℝ) ^ p

/-- Hypotheses of the transfer theorem. `lower` is GLOBAL on `(0,1)`: a merely local
bi-Lipschitz condition is false as a hypothesis (see `EDGE_CASES.md`, falsifier F1). -/
structure PhaseHyp (g : ℝ → ℝ) (α m : ℝ) : Prop where
  mem : α ∈ Ioo (0 : ℝ) 1
  m_pos : 0 < m
  lower : ∃ c > 0, ∀ x ∈ Ioo (0 : ℝ) 1, c * |x - α| ^ m ≤ |g x - g α|
  upper : ∃ C > 0, ∃ r > 0, ∀ x, |x - α| < r → |g x - g α| ≤ C * |x - α| ^ m

/-! ## The two-sided comparison -/

lemma sub_div_abs (k q : ℕ) (hq : 0 < q) (α : ℝ) :
    |(k : ℝ) / q - α| = |(q : ℝ) * α - k| / q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  rw [abs_sub_comm, eq_div_iff hq'.ne', ← abs_of_pos hq', ← abs_mul, abs_of_pos hq']
  congr 1; field_simp

/-- Every sample is at least `c (‖qα‖/q)^m` away (all `q ≥ 1`). -/
theorem sample_lower {g : ℝ → ℝ} {α m : ℝ} (h : PhaseHyp g α m) :
    ∃ c > 0, ∀ q k : ℕ, 0 < k → k < q →
      c * (nint (q * α) / q) ^ m ≤ |g (k / q) - g α| := by
  obtain ⟨c, hc, hlow⟩ := h.lower
  refine ⟨c, hc, fun q k hk hkq => ?_⟩
  have hq : 0 < q := lt_trans hk hkq
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : (k : ℝ) / q ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (by exact_mod_cast hk) hq', (div_lt_one hq').2 (by exact_mod_cast hkq)⟩
  refine le_trans ?_ (hlow _ hx)
  have hmain : nint ((q : ℝ) * α) / q ≤ |(k : ℝ) / q - α| := by
    rw [sub_div_abs k q hq, nint]
    exact div_le_div_of_nonneg_right (by simpa using round_le ((q : ℝ) * α) (k : ℤ)) hq'.le
  exact mul_le_mul_of_nonneg_left
    (rpow_le_rpow (div_nonneg (abs_nonneg _) hq'.le) hmain h.m_pos.le) hc.le

/-- The nearest sample is at most `C (‖qα‖/q)^m` away, with explicit thresholds on `q`. -/
theorem sample_upper {g : ℝ → ℝ} {α m : ℝ} (h : PhaseHyp g α m) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ q : ℕ, 1 / 2 < (q : ℝ) * α → 1 / 2 < (q : ℝ) * (1 - α) →
      1 / (2 * r) < (q : ℝ) →
      ∃ k : ℕ, 0 < k ∧ k < q ∧ |g (k / q) - g α| ≤ C * (nint (q * α) / q) ^ m := by
  obtain ⟨C, hC, r, hr, hup⟩ := h.upper
  refine ⟨C, hC, r, hr, fun q h1 h2 h3 => ?_⟩
  have hq' : (0 : ℝ) < q := by
    by_contra hneg; push Not at hneg
    have : (q : ℝ) * α ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg h.mem.1.le
    linarith
  have hq : 0 < q := by exact_mod_cast hq'
  set z := round ((q : ℝ) * α) with hz
  have hround := abs_sub_round ((q : ℝ) * α)
  rw [abs_le] at hround
  have hzpos : (0 : ℝ) < z := by linarith [hround.2]
  have hzlt : (z : ℝ) < q := by nlinarith [hround.1]
  have hz0 : 0 < z := by exact_mod_cast hzpos
  refine ⟨z.toNat, ?_, ?_, ?_⟩
  · omega
  · have : z < (q : ℤ) := by exact_mod_cast hzlt
    omega
  · have hcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      have : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0.le
      exact_mod_cast this
    have hdist : |((z.toNat : ℕ) : ℝ) / q - α| = nint (q * α) / q := by
      rw [sub_div_abs _ q hq, hcast, nint, abs_sub_comm]
    have hsmall : |((z.toNat : ℕ) : ℝ) / q - α| < r := by
      rw [hdist, nint, div_lt_iff₀ hq']
      have : |(q : ℝ) * α - z| ≤ 1 / 2 := abs_sub_round _
      have h3' : 1 < 2 * r * q := by
        rw [div_lt_iff₀ (by positivity)] at h3; linarith
      nlinarith
    calc |g ((z.toNat : ℕ) / q) - g α| ≤ C * |((z.toNat : ℕ) : ℝ) / q - α| ^ m := hup _ hsmall
      _ = C * (nint (q * α) / q) ^ m := by rw [hdist]

/-! ## Exponent transfer -/

lemma tendsto_div_rpow {C p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => C / (n : ℝ) ^ p) atTop (nhds (0 : ℝ)) :=
  tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop)

/-- **Transfer theorem.** For irrational `α` and `p > 0`, quantized-phase spikes of exponent
`m p` occur iff `α` is `LiouvilleWith p`. -/
theorem spikeWith_iff_liouvilleWith {g : ℝ → ℝ} {α m : ℝ} (h : PhaseHyp g α m)
    (hα : Irrational α) {p : ℝ} (hp : 0 < p) :
    SpikeWith g α (m * p) ↔ LiouvilleWith p α := by
  have hm := h.m_pos
  constructor
  · rintro ⟨A, hA⟩
    obtain ⟨c, hc, hlow⟩ := h.lower
    refine ⟨(A / c) ^ (1 / m), hA.mono fun q ⟨k, hk, hkq, hlt⟩ => ?_⟩
    have hq' : (0 : ℝ) < q := by exact_mod_cast lt_trans hk hkq
    have hx : (k : ℝ) / q ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos (by exact_mod_cast hk) hq', (div_lt_one hq').2 (by exact_mod_cast hkq)⟩
    refine ⟨(k : ℤ), ?_, ?_⟩
    · simpa using hα.ne_rational (k : ℤ) (q : ℤ)
    · have h1 : c * |(k : ℝ) / q - α| ^ m < A / (q : ℝ) ^ (m * p) := lt_of_le_of_lt (hlow _ hx) hlt
      have h2 : |(k : ℝ) / q - α| ^ m < (A / c) / (q : ℝ) ^ (m * p) := by
        rw [div_div, mul_comm c, ← div_div, lt_div_iff₀ hc]; linarith
      have hApos : 0 < A / c / (q : ℝ) ^ (m * p) := lt_of_le_of_lt (by positivity) h2
      have h3 := rpow_lt_rpow (by positivity) h2 (by positivity : (0 : ℝ) < 1 / m)
      rw [← rpow_mul (abs_nonneg _), mul_one_div_cancel hm.ne', rpow_one] at h3
      have hAc : 0 ≤ A / c := by
        have := mul_pos hApos (rpow_pos_of_pos hq' (m * p))
        rw [div_mul_cancel₀ _ (rpow_pos_of_pos hq' _).ne'] at this; exact this.le
      rw [div_rpow hAc (rpow_nonneg hq'.le _), ← rpow_mul hq'.le,
        show m * p * (1 / m) = p by field_simp] at h3
      simpa [abs_sub_comm] using h3
  · rintro ⟨C, hC⟩
    obtain ⟨C', hC', r, hr, hup⟩ := h.upper
    set ε := min (min α (1 - α)) r with hε
    have hεpos : 0 < ε := lt_min (lt_min h.mem.1 (by linarith [h.mem.2])) hr
    have hev : ∀ᶠ n : ℕ in atTop, C / (n : ℝ) ^ p < ε ∧ 0 < n :=
      ((tendsto_div_rpow hp).eventually (gt_mem_nhds hεpos)).and (eventually_gt_atTop 0)
    refine ⟨C' * C ^ m, (hC.and_eventually hev).mono fun n ⟨⟨j, hne, hj⟩, hsm, hn⟩ => ?_⟩
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hjlt : |α - j / n| < ε := lt_trans hj hsm
    have hCpos : 0 < C / (n : ℝ) ^ p := lt_of_le_of_lt (abs_nonneg _) hj
    have hle1 : ε ≤ α := le_trans (min_le_left _ _) (min_le_left _ _)
    have hle2 : ε ≤ 1 - α := le_trans (min_le_left _ _) (min_le_right _ _)
    rw [abs_lt] at hjlt
    have hjpos : (0 : ℝ) < j / n := by linarith
    have hjone : (j : ℝ) / n < 1 := by linarith
    have hj0 : (0 : ℝ) < j := by
      rcases (div_pos_iff.1 hjpos) with h' | h'
      · exact h'.1
      · exact absurd h'.2 (not_lt.2 hn'.le)
    have hjn : (j : ℝ) < n := by rwa [div_lt_one hn'] at hjone
    have hj0' : 0 < j := by exact_mod_cast hj0
    refine ⟨j.toNat, by omega, ?_, ?_⟩
    · have : j < (n : ℤ) := by exact_mod_cast hjn
      omega
    · have hcast : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by
        have : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0'.le
        exact_mod_cast this
      rw [hcast]
      have hd : |(j : ℝ) / n - α| < r := by
        rw [abs_lt]; constructor <;> linarith [min_le_right (min α (1 - α)) r]
      have hd2 : |(j : ℝ) / n - α| < C / (n : ℝ) ^ p := by rwa [abs_sub_comm]
      calc |g (j / n) - g α| ≤ C' * |(j : ℝ) / n - α| ^ m := hup _ hd
        _ < C' * (C / (n : ℝ) ^ p) ^ m := by
          gcongr
        _ = C' * C ^ m / (n : ℝ) ^ (m * p) := by
          have hCnn : 0 ≤ C := by
            have := mul_pos hCpos (rpow_pos_of_pos hn' p)
            rw [div_mul_cancel₀ _ (rpow_pos_of_pos hn' _).ne'] at this; exact this.le
          rw [div_rpow hCnn (rpow_nonneg hn'.le _), ← rpow_mul hn'.le, mul_comm p m, mul_div_assoc]

/-- Spikes are monotone in the exponent. -/
lemma SpikeWith.mono {g : ℝ → ℝ} {α p p' : ℝ} (h : SpikeWith g α p) (hle : p' ≤ p) :
    SpikeWith g α p' := by
  obtain ⟨A, hA⟩ := h
  refine ⟨max A 0, hA.mono fun q ⟨k, hk, hkq, hlt⟩ => ⟨k, hk, hkq, ?_⟩⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hpos : (0 : ℝ) < (q : ℝ) ^ p' := rpow_pos_of_pos (by linarith) _
  calc |g (k / q) - g α| < A / (q : ℝ) ^ p := hlt
    _ ≤ max A 0 / (q : ℝ) ^ p := by gcongr; exact le_max_left _ _
    _ ≤ max A 0 / (q : ℝ) ^ p' := by
        apply div_le_div_of_nonneg_left (le_max_right _ _) hpos
        exact rpow_le_rpow_of_exponent_le hq1 hle

/-- **Liouville phase.** Super-polynomial spikes of every exponent ↔ `Liouville α`. -/
theorem spike_all_iff_liouville {g : ℝ → ℝ} {α m : ℝ} (h : PhaseHyp g α m) (hα : Irrational α) :
    (∀ p, SpikeWith g α p) ↔ Liouville α := by
  have hm := h.m_pos
  rw [← forall_liouvilleWith_iff]
  constructor
  · intro hs p
    have hp : 0 < max p 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    exact ((spikeWith_iff_liouvilleWith h hα hp).1 (hs _)).mono (le_max_left _ _)
  · intro hl p
    have hp : 0 < max (p / m) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ((spikeWith_iff_liouvilleWith h hα hp).2 (hl _)).mono ?_
    calc p = m * (p / m) := by field_simp
      _ ≤ m * max (p / m) 1 := by gcongr; exact le_max_left _ _

/-! ## Rational phases: exact singularity iff `b ∣ q` -/

theorem rational_singular_of_dvd (g : ℝ → ℝ) {a b q : ℕ} (ha : 0 < a) (hab : a < b)
    (hbq : b ∣ q) (hq : 0 < q) :
    ∃ k : ℕ, 0 < k ∧ k < q ∧ g (k / q) = g ((a : ℝ) / b) := by
  obtain ⟨t, rfl⟩ := hbq
  have hb : 0 < b := lt_trans ha hab
  have ht : 0 < t := Nat.pos_of_mul_pos_left hq
  refine ⟨a * t, Nat.mul_pos ha ht, Nat.mul_lt_mul_of_pos_right hab ht, ?_⟩
  congr 1
  have : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  push_cast
  field_simp

theorem dvd_of_rational_singular {g : ℝ → ℝ} {m : ℝ} {a b q k : ℕ} (hb : 0 < b)
    (hcop : Nat.Coprime a b) (h : PhaseHyp g ((a : ℝ) / b) m) (hk : 0 < k) (hkq : k < q)
    (heq : g (k / q) = g ((a : ℝ) / b)) : b ∣ q := by
  obtain ⟨c, hc, hlow⟩ := h.lower
  have hq' : (0 : ℝ) < q := by exact_mod_cast lt_trans hk hkq
  have hx : (k : ℝ) / q ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (by exact_mod_cast hk) hq', (div_lt_one hq').2 (by exact_mod_cast hkq)⟩
  have h0 := hlow _ hx
  rw [heq, sub_self, abs_zero] at h0
  have hz : |(k : ℝ) / q - a / b| ^ m = 0 := by
    have := mul_nonneg hc.le (rpow_nonneg (abs_nonneg ((k : ℝ) / q - a / b)) m)
    nlinarith [mul_pos hc (show (0:ℝ) < 1 by norm_num)]
  have hz' : (k : ℝ) / q = a / b := by
    have := (rpow_eq_zero (abs_nonneg _) h.m_pos.ne').1 hz
    exact sub_eq_zero.1 (abs_eq_zero.1 this)
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_eq_div_iff hq'.ne' hb'.ne'] at hz'
  have hnat : k * b = a * q := by exact_mod_cast hz'
  have : b ∣ a * q := ⟨k, by rw [← hnat, mul_comm]⟩
  exact (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm this)

/-! ## The constant Jacobi dispersion `c + 2 β cos (π x)` -/

/-- `sin (π s) ≥ min(α, 1-α)` for `s ∈ (α/2, (1+α)/2)`. -/
lemma sin_mid_lower {α s : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (h1 : α / 2 < s) (h2 : s < (1 + α) / 2) :
    min α (1 - α) ≤ sin (π * s) := by
  rcases le_total s (1 / 2) with hs | hs
  · have := mul_le_sin (x := π * s) (by nlinarith [pi_pos, hα.1]) (by nlinarith [pi_pos])
    have e : 2 / π * (π * s) = 2 * s := by field_simp
    rw [e] at this
    exact le_trans (min_le_left _ _) (by linarith)
  · have := mul_le_sin (x := π * (1 - s)) (by nlinarith [pi_pos, hα.2]) (by nlinarith [pi_pos])
    have e : 2 / π * (π * (1 - s)) = 2 * (1 - s) := by field_simp
    rw [e, show π * (1 - s) = π - π * s by ring, sin_pi_sub] at this
    exact le_trans (min_le_right _ _) (by linarith)

/-- `|sin (π t / 2)| ≥ |t|` for `|t| ≤ 1`. -/
lemma abs_sin_half_lower {t : ℝ} (ht : |t| ≤ 1) : |t| ≤ |sin (π * t / 2)| := by
  rcases le_total 0 t with h0 | h0
  · have := mul_le_sin (x := π * t / 2) (by positivity) (by
      have : t ≤ 1 := le_trans (le_abs_self t) ht
      nlinarith [pi_pos])
    have e : 2 / π * (π * t / 2) = t := by field_simp
    rw [e] at this
    rw [abs_of_nonneg h0]; exact le_trans this (le_abs_self _)
  · have := mul_le_sin (x := π * (-t) / 2) (by nlinarith [pi_pos]) (by
      have : -t ≤ 1 := by rw [abs_of_nonpos h0] at ht; exact ht
      nlinarith [pi_pos])
    have e : 2 / π * (π * (-t) / 2) = -t := by field_simp
    rw [e, show π * (-t) / 2 = -(π * t / 2) by ring, sin_neg] at this
    rw [abs_of_nonpos h0]; exact le_trans this (neg_le_abs _)

/-- Global linear lower bound for the cosine dispersion on `(0,1)`. -/
theorem cos_lower {α x : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    2 * min α (1 - α) * |x - α| ≤ |cos (π * x) - cos (π * α)| := by
  rw [cos_sub_cos, show (π * x + π * α) / 2 = π * ((x + α) / 2) by ring,
    show (π * x - π * α) / 2 = π * (x - α) / 2 by ring]
  have hs := sin_mid_lower hα (s := (x + α) / 2) (by linarith [hx.1]) (by linarith [hx.2])
  have ht : |x - α| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hα.1, hα.2]
  have hd := abs_sin_half_lower ht
  have hmin : 0 ≤ min α (1 - α) := le_min hα.1.le (by linarith [hα.2])
  have hspos : 0 < sin (π * ((x + α) / 2)) := lt_of_lt_of_le (lt_min hα.1 (by linarith [hα.2])) hs
  rw [abs_mul, abs_mul, show |(-2 : ℝ)| = 2 by norm_num, abs_of_pos hspos]
  calc 2 * min α (1 - α) * |x - α| ≤ 2 * sin (π * ((x + α) / 2)) * |x - α| := by gcongr
    _ ≤ 2 * sin (π * ((x + α) / 2)) * |sin (π * (x - α) / 2)| :=
        mul_le_mul_of_nonneg_left hd (by linarith)

/-- The Jacobi dispersion `g x = c + 2 β cos (π x)`. -/
noncomputable def jacobiDisp (c β : ℝ) (x : ℝ) : ℝ := c + 2 * β * cos (π * x)

/-- **Jacobi instantiation.** `PhaseHyp` holds with `m = 1`,
lower constant `4 |β| min(α,1-α)`, upper constant `2 π |β|` (globally, any `r`). -/
theorem cos_phaseHyp {c β α : ℝ} (hβ : β ≠ 0) (hα : α ∈ Ioo (0 : ℝ) 1) :
    PhaseHyp (jacobiDisp c β) α 1 := by
  have hd : ∀ x, |jacobiDisp c β x - jacobiDisp c β α| = 2 * |β| * |cos (π * x) - cos (π * α)| := by
    intro x; unfold jacobiDisp
    rw [show c + 2 * β * cos (π * x) - (c + 2 * β * cos (π * α)) =
      (2 * β) * (cos (π * x) - cos (π * α)) by ring, abs_mul, abs_mul]; norm_num
  have hmin : 0 < min α (1 - α) := lt_min hα.1 (by linarith [hα.2])
  refine ⟨hα, one_pos, ⟨4 * |β| * min α (1 - α), by positivity, fun x hx => ?_⟩,
    ⟨2 * π * |β|, by positivity, 1, one_pos, fun x _ => ?_⟩⟩
  · rw [rpow_one, hd]
    have := cos_lower hα hx
    nlinarith [abs_nonneg β, abs_pos.2 hβ]
  · rw [rpow_one, hd]
    have := abs_cos_sub_cos_le (π * x) (π * α)
    rw [show π * x - π * α = π * (x - α) by ring, abs_mul, abs_of_pos pi_pos] at this
    nlinarith [abs_nonneg β]

/-- **Jacobi transfer.** For the constant chain dispersion and irrational interior phase,
spikes of exponent `p > 0` ↔ `LiouvilleWith p α`. -/
theorem jacobi_spike_iff {c β α p : ℝ} (hβ : β ≠ 0) (hα : α ∈ Ioo (0 : ℝ) 1) (hirr : Irrational α)
    (hp : 0 < p) : SpikeWith (jacobiDisp c β) α p ↔ LiouvilleWith p α := by
  simpa using spikeWith_iff_liouvilleWith (cos_phaseHyp (c := c) hβ hα) hirr hp

/-- **Matrix bridge (host interface).** Let `R q` be any quantity (e.g. `‖(J_{q-1}(c,β) - τ)⁻¹‖₂`)
such that, for `q ≥ 2`, `R q > 1/ε` holds iff some eigenvalue `c + 2 β cos (k π / q)`,
`0 < k < q`, is within `ε` of `τ = c + 2 β cos (π α)`. For a Hermitian `J` this is the
estate's resolvent-norm = reciprocal-spectral-distance identity together with its exact
constant-chain spectrum. Then polynomial resolvent spikes of exponent `p` ↔ `LiouvilleWith p α`. -/
theorem jacobi_resolvent_spike_iff {c β α p : ℝ} (hβ : β ≠ 0) (hα : α ∈ Ioo (0 : ℝ) 1)
    (hirr : Irrational α) (hp : 0 < p) (R : ℕ → ℝ)
    (hR : ∀ q : ℕ, 2 ≤ q → ∀ ε > 0, (1 / ε < R q ↔
      ∃ k : ℕ, 0 < k ∧ k < q ∧ |jacobiDisp c β (k / q) - jacobiDisp c β α| < ε)) :
    (∃ A > 0, ∃ᶠ q : ℕ in atTop, (q : ℝ) ^ p / A < R q) ↔ LiouvilleWith p α := by
  rw [← jacobi_spike_iff (c := c) hβ hα hirr hp]
  constructor
  · rintro ⟨A, hA, hfr⟩
    refine ⟨A, (hfr.and_eventually (eventually_ge_atTop 2)).mono fun q ⟨hq, h2⟩ => ?_⟩
    have hqpos : (0 : ℝ) < (q : ℝ) ^ p := rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < q)) _
    have hε : 0 < A / (q : ℝ) ^ p := div_pos hA hqpos
    refine (hR q h2 _ hε).1 ?_
    rwa [one_div_div]
  · rintro ⟨A, hfr⟩
    refine ⟨max A 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      (hfr.and_eventually (eventually_ge_atTop 2)).mono fun q ⟨⟨k, hk, hkq, hlt⟩, h2⟩ => ?_⟩
    have hqpos : (0 : ℝ) < (q : ℝ) ^ p := rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < q)) _
    have hε : 0 < max A 1 / (q : ℝ) ^ p := div_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) hqpos
    have := (hR q h2 _ hε).2 ⟨k, hk, hkq, lt_of_lt_of_le hlt (by gcongr; exact le_max_left _ _)⟩
    rwa [one_div_div] at this

end JacobiDioph
