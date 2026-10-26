module

public import CayleyProof.NormalizedSpectrum
public import CayleyProof.KatzSamples
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! The varying affine normalization between Katz samples and normalized
graph eigenvalues. Both coefficients are proved to have their asserted limits.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace CayleyProof

noncomputable def spectralSlope (q : ℝ) : ℝ :=
  2 * Real.sqrt q / Real.sqrt (2 * (q - 1))

noncomputable def spectralOffset (q : ℝ) : ℝ :=
  -2 / Real.sqrt (2 * (q - 1))

theorem spectralSlope_eq (q : ℝ) (hq : 1 < q) :
    spectralSlope q = Real.sqrt (2 / (1 - q⁻¹)) := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  unfold spectralSlope
  calc
    2 * Real.sqrt q / Real.sqrt (2 * (q - 1)) =
        Real.sqrt (4 * q) / Real.sqrt (2 * (q - 1)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    _ = Real.sqrt ((4 * q) / (2 * (q - 1))) := (Real.sqrt_div (by positivity) _).symm
    _ = _ := by
      congr 1
      field_simp
      ring

theorem spectralSlope_tendsto {q : ℕ → ℝ}
    (hq : Tendsto q atTop atTop) (hqone : ∀ n, 1 < q n) :
    Tendsto (fun n => spectralSlope (q n)) atTop (𝓝 (Real.sqrt 2)) := by
  have hi := tendsto_inv_atTop_zero.comp hq
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).sub hi
  have hr : Tendsto (fun n => 2 / (1 - (q n)⁻¹)) atTop (𝓝 (2 : ℝ)) := by
    have H := (tendsto_const_nhds (x := (2 : ℝ))).div hd
      (by norm_num : (1 : ℝ) - 0 ≠ 0)
    change Tendsto (fun n => 2 / (1 - (q n)⁻¹)) atTop (𝓝 (2 / (1 - 0))) at H
    simpa using H
  simpa only [spectralSlope_eq _ (hqone _), Function.comp_def] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hr

theorem spectralOffset_tendsto {q : ℕ → ℝ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun n => spectralOffset (q n)) atTop (𝓝 0) := by
  have hd : Tendsto (fun n => 2 * (q n - 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
      (by simpa only [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right atTop (-1) hq)
  have hs := Real.tendsto_sqrt_atTop.comp hd
  simpa [spectralOffset, div_eq_mul_inv] using
    (tendsto_inv_atTop_zero.comp hs).const_mul (-2)

variable {F : Type*} [Field F] [Fintype F] {s : ℕ}

theorem normalizedEigenvalue_affine (ψ : AddChar F ℂ) (b : Fin s → F) :
    normalizedEigenvalue ψ b = spectralSlope (Fintype.card F : ℝ) *
      normalizedCharacterSum ψ b + spectralOffset (Fintype.card F : ℝ) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card F : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  unfold normalizedEigenvalue realEigenvalue normalizedCharacterSum spectralSlope spectralOffset
  field_simp
  ring

theorem spectral_affine_error_bound (q y M : ℝ) (hy : |y| ≤ M) :
    |spectralSlope q * y + spectralOffset q - Real.sqrt 2 * y| ≤
      |spectralSlope q - Real.sqrt 2| * M + |spectralOffset q| := by
  calc
    _ = |(spectralSlope q - Real.sqrt 2) * y + spectralOffset q| := by congr 1; ring
    _ ≤ |(spectralSlope q - Real.sqrt 2) * y| + |spectralOffset q| := abs_add_le _ _
    _ ≤ _ := by rw [abs_mul]; gcongr

theorem spectral_affine_error_tendsto {q : ℕ → ℝ}
    (hq : Tendsto q atTop atTop) (hqone : ∀ n, 1 < q n) (M : ℝ) :
    Tendsto (fun n => |spectralSlope (q n) - Real.sqrt 2| * M +
      |spectralOffset (q n)|) atTop (𝓝 0) := by
  have h₁ := ((spectralSlope_tendsto hq hqone).sub
    (tendsto_const_nhds (x := Real.sqrt 2))).abs.mul_const M
  have h₂ := (spectralOffset_tendsto hq).abs
  simpa using h₁.add h₂

end CayleyProof
