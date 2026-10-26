module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! The exceptional eigenvalue has mass q^(-s) and normalized size
sqrt(2(q-1)). Its weighted k-th moment vanishes exactly in the range k < 2s
needed in Theorem 18. This is an actual limit theorem, not an asymptotic axiom.
-/

@[expose] public section

open Filter
open scoped Topology

namespace CayleyProof

theorem sqrt_pow_div_pow {q : ℝ} (hq : 0 < q) (k s : ℕ) :
    (Real.sqrt q) ^ k / q ^ s = q ^ ((k : ℝ) / 2 - (s : ℝ)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq.le,
    Real.rpow_sub hq, Real.rpow_natCast]
  congr 2
  ring

theorem principal_moment_bound {q : ℝ} (hq : 1 ≤ q) (k s : ℕ) :
    (q ^ s)⁻¹ * (1 + |Real.sqrt (2 * (q - 1))| ^ k) ≤
      (q ^ s)⁻¹ + (Real.sqrt 2) ^ k * q ^ ((k : ℝ) / 2 - (s : ℝ)) := by
  have hqpos : 0 < q := by linarith
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsq : Real.sqrt (2 * (q - 1)) ≤ Real.sqrt 2 * Real.sqrt q := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
    apply Real.sqrt_le_sqrt
    linarith
  calc
    (q ^ s)⁻¹ * (1 + Real.sqrt (2 * (q - 1)) ^ k)
        ≤ (q ^ s)⁻¹ * (1 + (Real.sqrt 2 * Real.sqrt q) ^ k) := by
      gcongr
    _ = (q ^ s)⁻¹ + (Real.sqrt 2) ^ k * ((Real.sqrt q) ^ k / q ^ s) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [sqrt_pow_div_pow hqpos]

theorem principal_weighted_moment_tendsto_zero
    {q : ℕ → ℝ} (hq : Tendsto q atTop atTop) (hqone : ∀ n, 1 ≤ q n)
    {k s : ℕ} (hs : 0 < s) (hks : k < 2 * s) :
    Tendsto (fun n => ((q n) ^ s)⁻¹ * (1 + |Real.sqrt (2 * (q n - 1))| ^ k))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun n => (q n) ^ s) atTop atTop := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      ((tendsto_rpow_atTop (show 0 < (s : ℝ) by exact_mod_cast hs)).comp hq)
  have hw : Tendsto (fun n => ((q n) ^ s)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hp
  have hneg : 0 < (s : ℝ) - (k : ℝ) / 2 := by
    have hcast : (k : ℝ) < 2 * (s : ℝ) := by exact_mod_cast hks
    linarith
  have hr : Tendsto (fun n => q n ^ ((k : ℝ) / 2 - (s : ℝ))) atTop (𝓝 0) := by
    have he : (k : ℝ) / 2 - (s : ℝ) = -((s : ℝ) - (k : ℝ) / 2) := by ring
    simpa only [he, Function.comp_def] using (tendsto_rpow_neg_atTop hneg).comp hq
  have hb : Tendsto (fun n => ((q n) ^ s)⁻¹ +
      (Real.sqrt 2) ^ k * q n ^ ((k : ℝ) / 2 - (s : ℝ))) atTop (𝓝 0) := by
    simpa using hw.add (hr.const_mul ((Real.sqrt 2) ^ k))
  exact squeeze_zero (fun n => by have := hqone n; positivity)
    (fun n => principal_moment_bound (hqone n) k s) hb

end CayleyProof
