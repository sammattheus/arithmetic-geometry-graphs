module

public import CayleyProof.ExternalInputs
public import CayleyProof.FiniteFieldGraph

/-! The manuscript's Theorem 22, relative to the two explicitly declared
external inputs in ExternalInputs.lean.  The fields E n have size Q^(n+1):
this indexes all positive extension degrees without introducing q=1.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace CayleyProof

theorem theorem22
    (d p a : ℕ) (hd : 3 ≤ d) [Fact p.Prime] (hp : 5 < p)
    (hpd : ¬ p ∣ d) (_ha : 1 ≤ a) (hdiv : d ∣ p ^ (2 * a) - 1)
    (F : Type) [Field F] [Fintype F] [CharP F p]
    (hF : Fintype.card F = p ^ (2 * a))
    (E : ℕ → Type) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    (hrank : ∀ n, Module.finrank F (E n) = n + 1)
    (χ : ∀ n, AddChar (E n) ℂ) (hχ : ∀ n, χ n ≠ 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      Tendsto (fun n => katzSampleLaw (χ n) (d - 1)) atTop (𝓝 μ) ∧
      (μ : Measure ℝ).support ⊆ Set.Icc (1 - (d : ℝ)) ((d : ℝ) - 1) ∧
      (μ : Measure ℝ).support.Infinite := by
  let m := d - 3
  have hmd : m + 3 = d := Nat.sub_add_cancel hd
  have hidx : m + 2 = d - 1 := by omega
  obtain ⟨ψ, hψ⟩ := exists_primitive_character F
  obtain ⟨D⟩ := External.katzDeligneCohomologicalRealization m p hp
    (by simpa only [hmd] using hpd) F E hrank ψ hψ
  have hψ₁ : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ one_ne_zero
  have hdiv' : m + 3 ∣ Fintype.card F - 1 := by simpa only [hmd, hF] using hdiv
  have hcard : Fintype.card F = (p ^ a) ^ 2 := by
    rw [hF, ← pow_mul, Nat.mul_comm a 2]
  obtain ⟨μ, hconv, hsupp, hinf⟩ := theorem22_from_standard_data m E hrank hdiv' hcard
    ψ hψ χ hχ (fun n => External.hasseDavenport F (E n) ψ hψ₁)
    (positiveNormalization F) (sqrt_card_normalization (F := F)) D
  refine ⟨μ, ?_, ?_, hinf⟩
  · simpa only [hidx] using hconv
  · have hr : (m : ℝ) + 3 = d := by exact_mod_cast hmd
    have hI : Set.Icc (-(m + 2 : ℝ)) (m + 2 : ℝ) =
        Set.Icc (1 - (d : ℝ)) ((d : ℝ) - 1) := by
      congr 1 <;> linarith
    rwa [hI] at hsupp

theorem theorem22_extension_cardinality
    (p a : ℕ) (F : Type) [Field F] [Fintype F]
    (hF : Fintype.card F = p ^ (2 * a))
    (E : ℕ → Type) [∀ n, Field (E n)] [∀ n, Fintype (E n)] [∀ n, Algebra F (E n)]
    (hrank : ∀ n, Module.finrank F (E n) = n + 1) (n : ℕ) :
    Fintype.card (E n) = (p ^ (2 * a)) ^ (n + 1) := by
  rw [Module.card_eq_pow_finrank (K := F), hF, hrank]

end CayleyProof
