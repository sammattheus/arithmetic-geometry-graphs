module

public import CayleyProof.CharacterEigenvectors
public import CayleyProof.ExceptionalMoment
public import Mathlib.Order.Interval.Set.Infinite

/-! Normalization and moment estimates for the eigenvalues of the actual curve
Cayley graph. A character-sum bound is an explicit input where Weil is needed.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology Matrix Classical

namespace CayleyProof

variable {F : Type*} [Field F] [Fintype F] {s : ℕ}

noncomputable def normalizedEigenvalue (ψ : AddChar F ℂ) (b : Fin s → F) : ℝ :=
  realEigenvalue ψ b / Real.sqrt (2 * ((Fintype.card F : ℝ) - 1))

/-- The normalized coefficient list is a complete eigenvalue list of the
normalized adjacency matrix, including multiplicities. The odd-characteristic
and primitive-character hypotheses belong at this identification step. -/
theorem normalized_coefficient_eigenbasis (hs : 2 ≤ s) (hchar : (2 : F) ≠ 0)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ∃ b : Module.Basis (Fin s → F) ℂ ((Fin s → F) → ℂ),
      ∀ a, (((Real.sqrt (2 * ((Fintype.card F : ℝ) - 1)) : ℂ)⁻¹) •
        (curveGraph F s).adjMatrix ℂ) *ᵥ b a =
          (normalizedEigenvalue ψ a : ℂ) • b a := by
  obtain ⟨b, hb⟩ := coefficient_eigenbasis hs hchar hψ
  refine ⟨b, ?_⟩
  intro a
  rw [Matrix.smul_mulVec, hb, smul_smul]
  congr 1
  simp [normalizedEigenvalue, div_eq_mul_inv, mul_comm]

theorem field_card_real_ge_two : 2 ≤ (Fintype.card F : ℝ) := by
  exact_mod_cast Fintype.one_lt_card (α := F)

@[simp] theorem normalizedEigenvalue_zero (ψ : AddChar F ℂ) :
    normalizedEigenvalue (s := s) ψ 0 = Real.sqrt (2 * ((Fintype.card F : ℝ) - 1)) := by
  have hq := field_card_real_ge_two (F := F)
  have hd : 0 < 2 * ((Fintype.card F : ℝ) - 1) := by linarith
  unfold normalizedEigenvalue
  rw [realEigenvalue_zero, div_eq_iff (Real.sqrt_pos.mpr hd).ne']
  simpa only [pow_two] using (Real.sq_sqrt hd.le).symm

/-- A fixed compact interval containing every nonprincipal eigenvalue under
the stated Weil character-sum estimate. -/
theorem normalizedEigenvalue_mem_interval (ψ : AddChar F ℂ) (b : Fin s → F)
    (hs : 1 ≤ s)
    (hWeil : ‖∑ t : F, ψ (∑ i, b i * t ^ (i.val + 1))‖ ≤
      ((s : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ)) :
    normalizedEigenvalue ψ b ∈ Set.Icc (-2 * ((s : ℝ) + 1)) (2 * ((s : ℝ) + 1)) := by
  have hq := field_card_real_ge_two (F := F)
  have hsreal : 1 ≤ (s : ℝ) := by exact_mod_cast hs
  let q : ℝ := Fintype.card F
  let z := ∑ t : F, ψ (∑ i, b i * t ^ (i.val + 1))
  have hq' : 2 ≤ q := hq
  have hsqrt : Real.sqrt q ≤ Real.sqrt (2 * (q - 1)) := Real.sqrt_le_sqrt (by linarith)
  have hsqrtone : 1 ≤ Real.sqrt (2 * (q - 1)) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    norm_num
    linarith
  have hz : |z.re| ≤ ((s : ℝ) - 1) * Real.sqrt q :=
    (Complex.abs_re_le_norm z).trans hWeil
  have hnum : |2 * z.re - 2| ≤ 2 * (((s : ℝ) - 1) * Real.sqrt q) + 2 := by
    calc
      |2 * z.re - 2| ≤ |2 * z.re| + |(2 : ℝ)| := abs_sub _ _
      _ ≤ _ := by rw [abs_mul]; norm_num; linarith
  have habs : |normalizedEigenvalue ψ b| ≤ 2 * ((s : ℝ) + 1) := by
    change |(2 * z.re - 2) / Real.sqrt (2 * (q - 1))| ≤ _
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_iff₀ (by positivity)).mpr
    have hsmul := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ (s : ℝ) - 1 by linarith)
    nlinarith
  simpa only [Set.mem_Icc, neg_mul] using abs_le.mp habs

/-- The exact degree-q^s exceptional mass in the graph's empirical spectrum. -/
theorem graph_principal_moment_tendsto_zero
    {q : ℕ → ℝ} (hq : Tendsto q atTop atTop) (hqone : ∀ n, 1 ≤ q n)
    {k : ℕ} (hk : 5 ≤ k) :
    Tendsto (fun n => ((q n) ^ (k / 2 + 1))⁻¹ *
      (1 + |Real.sqrt (2 * (q n - 1))| ^ k)) atTop (𝓝 0) :=
  principal_weighted_moment_tendsto_zero hq hqone (by omega)
    (parameter_inequalities k hk).2.2

theorem spectral_interval_infinite (s : ℕ) :
    (Set.Icc (-2 * ((s : ℝ) + 1)) (2 * ((s : ℝ) + 1))).Infinite :=
  Set.Icc_infinite (by have := Nat.cast_nonneg (α := ℝ) s; linarith)

end CayleyProof
