module

public import CayleyProof.CurveSpectralMeasure
public import CayleyProof.SpectralNormalization
public import CayleyProof.EmpiricalConvergence

/-! Transfer the exact-degree Katz sample limit to the nonprincipal graph
spectrum: the omitted coefficient vectors have proportion at most 1/q and
the affine normalization converges uniformly on the Weil-bounded samples.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators Classical

namespace CayleyProof

variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem exactDegree_ne_zero {s : ℕ} {b : Fin (s + 1) → F}
    (hb : b (Fin.last s) ≠ 0) : b ≠ 0 := by
  intro h
  exact hb (congrFun h (Fin.last s))

instance topDegreeNonprincipal_nonempty (s : ℕ) :
    Nonempty {b : {b : Fin (s + 1) → F // b ≠ 0} // b.val (Fin.last s) ≠ 0} :=
  ⟨⟨⟨fun _ => 1, exactDegree_ne_zero one_ne_zero⟩, one_ne_zero⟩⟩

def topDegreeNonprincipalEquiv (s : ℕ) :
    {b : {b : Fin (s + 1) → F // b ≠ 0} // b.val (Fin.last s) ≠ 0} ≃
      {b : Fin (s + 1) → F // b (Fin.last s) ≠ 0} where
  toFun b := ⟨b.val.val, b.property⟩
  invFun b := ⟨⟨b.val, exactDegree_ne_zero b.property⟩, b.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lowerDegree_proportion_le (s : ℕ) :
    (Fintype.card {b : {b : Fin (s + 1) → F // b ≠ 0} //
      ¬ b.val (Fin.last s) ≠ 0} : ℝ) /
      Fintype.card {b : Fin (s + 1) → F // b ≠ 0} ≤ (Fintype.card F : ℝ)⁻¹ := by
  let N := Fintype.card {b : Fin (s + 1) → F // b ≠ 0}
  let G := Fintype.card {b : {b : Fin (s + 1) → F // b ≠ 0} // b.val (Fin.last s) ≠ 0}
  let B := Fintype.card {b : {b : Fin (s + 1) → F // b ≠ 0} // ¬ b.val (Fin.last s) ≠ 0}
  let q : ℝ := Fintype.card F
  have hq : 2 ≤ q := field_card_real_ge_two (F := F)
  have hN : 0 < (N : ℝ) := by exact_mod_cast Fintype.card_pos
  have hNval : (N : ℝ) = q ^ (s + 1) - 1 := by
    dsimp [N, q]
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_fin]
    rw [Nat.cast_sub (Nat.succ_le_of_lt (pow_pos Fintype.card_pos _)), Nat.cast_pow, Nat.cast_one]
  have hGval : (G : ℝ) = (q - 1) * q ^ s := by
    dsimp [G, q]
    rw [Fintype.card_congr (topDegreeNonprincipalEquiv (F := F) s), card_exactDegreeCoefficients]
    push_cast
    rw [Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos),
      Nat.cast_one]
  have hcount : (G : ℝ) + B = N := by
    simp [G, B, N]
  change (B : ℝ) / N ≤ q⁻¹
  rw [div_le_iff₀ hN]
  apply (le_inv_mul_iff₀ (by linarith : 0 < q)).mpr
  rw [hNval, hGval] at hcount
  rw [hNval, pow_succ] at *
  nlinarith

noncomputable def spectralClip (s : ℕ) : ℝ → spectralInterval s :=
  Set.projIcc _ _ (by have := Nat.cast_nonneg (α := ℝ) s; linarith)

noncomputable def scaledSpectralClip (s : ℕ) (x : ℝ) : spectralInterval s :=
  spectralClip s (Real.sqrt 2 * x)

theorem continuous_scaledSpectralClip (s : ℕ) : Continuous (scaledSpectralClip s) :=
  continuous_projIcc.comp (continuous_const.mul continuous_id)

theorem normalizedCharacterSum_bound (ψ : AddChar F ℂ) (s : ℕ)
    (hW : HasWeilBound ψ (s + 1)) (b : Fin (s + 1) → F) (hb : b ≠ 0) :
    |normalizedCharacterSum ψ b| ≤ (s : ℝ) := by
  have hq : 0 < Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  unfold normalizedCharacterSum
  rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
  have H := (Complex.abs_re_le_norm _).trans (hW b hb)
  simpa using H

theorem normalizedSample_clip_dist (ψ : AddChar F ℂ) (s : ℕ)
    (hW : HasWeilBound ψ (s + 1)) (b : Fin (s + 1) → F) (hb : b ≠ 0) :
    dist (⟨normalizedEigenvalue ψ b,
      normalizedEigenvalue_mem_interval ψ b (by omega) (hW b hb)⟩ : spectralInterval (s + 1))
      (scaledSpectralClip (s + 1) (normalizedCharacterSum ψ b)) ≤
      |spectralSlope (Fintype.card F : ℝ) - Real.sqrt 2| * s +
        |spectralOffset (Fintype.card F : ℝ)| := by
  have hx := normalizedEigenvalue_mem_interval ψ b (by omega) (hW b hb)
  have H := (LipschitzWith.projIcc (show -2 * ((s + 1 : ℕ) + 1 : ℝ) ≤
      2 * ((s + 1 : ℕ) + 1 : ℝ) by have := Nat.cast_nonneg (α := ℝ) s; push_cast; linarith)).dist_le_mul
      (normalizedEigenvalue ψ b) (Real.sqrt 2 * normalizedCharacterSum ψ b)
  rw [Set.projIcc_of_mem _ hx] at H
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at H
  apply H.trans
  rw [normalizedEigenvalue_affine]
  exact spectral_affine_error_bound _ _ _ (normalizedCharacterSum_bound ψ s hW b hb)

theorem curveNonprincipalLaw_tendsto_of_katz
    (s : ℕ) (E : ℕ → Type*) [∀ n, Field (E n)] [∀ n, Fintype (E n)]
    (ψ : ∀ n, AddChar (E n) ℂ) (hW : ∀ n, HasWeilBound (ψ n) (s + 1))
    (hq : Tendsto (fun n => (Fintype.card (E n) : ℝ)) atTop atTop)
    (μ : ProbabilityMeasure ℝ)
    (hKatz : Tendsto (fun n => katzSampleLaw (ψ n) s) atTop (𝓝 μ)) :
    Tendsto (fun n => curveNonprincipalLaw (ψ n) (s + 1) (by omega) (hW n))
      atTop (𝓝 (μ.map (scaledSpectralClip (s + 1)))) := by
  let J (n : ℕ) := {b : Fin (s + 1) → E n // b ≠ 0}
  let P (n : ℕ) (b : J n) := b.val (Fin.last s) ≠ 0
  let x (n : ℕ) (b : J n) : spectralInterval (s + 1) :=
    ⟨normalizedEigenvalue (ψ n) b.val,
      normalizedEigenvalue_mem_interval (ψ n) b.val (by omega) (hW n b.val b.property)⟩
  let y (n : ℕ) (b : {b : J n // P n b}) : spectralInterval (s + 1) :=
    scaledSpectralClip (s + 1) (normalizedCharacterSum (ψ n) b.val.val)
  have hbad : Tendsto (fun n => (Fintype.card {b : J n // ¬ P n b} : ℝ) /
      Fintype.card (J n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => by positivity) (fun n => lowerDegree_proportion_le (F := E n) s)
    exact tendsto_inv_atTop_zero.comp hq
  have hy : Tendsto (fun n => empiricalLaw (y n)) atTop
      (𝓝 (μ.map (scaledSpectralClip (s + 1)))) := by
    have H := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hKatz
      (continuous_scaledSpectralClip (s + 1))
    convert H using 1
    funext n
    rw [katzSampleLaw, empiricalLaw_map _ _ (continuous_scaledSpectralClip (s + 1)).measurable]
    exact empiricalLaw_reindex (topDegreeNonprincipalEquiv (F := E n) s)
      (fun b => scaledSpectralClip (s + 1) (normalizedCharacterSum (ψ n) b.val))
  have hgood : Tendsto (fun n => empiricalLaw (fun b : {b : J n // P n b} => x n b.val))
      atTop (𝓝 (μ.map (scaledSpectralClip (s + 1)))) := by
    apply empirical_uniform_perturbation_tendsto (fun n => {b : J n // P n b})
      (fun n b => x n b.val) y _ _ hy
    intro ε hε
    have herror := spectral_affine_error_tendsto hq
      (fun n => (by have := field_card_real_ge_two (F := E n); linarith)) (s : ℝ)
    filter_upwards [(tendsto_order.mp herror).2 ε hε] with n hn b
    exact (normalizedSample_clip_dist (ψ n) s (hW n) b.val.val b.val.property).trans_lt hn
  apply empirical_subsample_tendsto J P x _ _ hgood
  simpa using hbad

end CayleyProof
