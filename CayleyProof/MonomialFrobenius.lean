module

public import CayleyProof.CharacterLifts
public import CayleyProof.MonomialFourier
public import CayleyProof.PowerSums

/-! The appendix's monomial Frobenius deduction.  The external inputs are
the ordinary cohomological power-trace formula and Hasse-Davenport.  The
Fourier expansion, character lifting, signs, normalization, Newton recovery,
and determinant-one choice are deductions proved in this project.
-/

@[expose] public section

open scoped BigOperators Classical

namespace CayleyProof

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem normalized_monomial_sum_eq_powerSum {d : ℕ} (hd : 0 < d)
    (hdiv : d ∣ Fintype.card F - 1) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    (hHD : HasseDavenportIdentity (E := E) ψ) (c : ℂ) (u : Fˣ) :
    -(c ^ Module.finrank F E) *
      (∑ t : E, traceLift (E := E) ψ (algebraMap F E (u : F) * t ^ d)) =
      ∑ χ : nontrivialTorsionCharacters F d,
        monomialGaussFactor ψ c u χ.val ^ Module.finrank F E := by
  let uE : Eˣ := Units.map (algebraMap F E).toMonoidHom u
  have hm := monomial_sum_eq_gauss d hd (traceLift (E := E) ψ)
    (traceLift_nontrivial (E := E) hψ) uE
  change -(c ^ Module.finrank F E) *
    (∑ t : E, traceLift (E := E) ψ ((uE : E) * t ^ d)) = _
  rw [hm, Finset.mul_sum]
  rw [← Finset.sum_coe_sort (nontrivialTorsionCharacters E d)]
  have he := Fintype.sum_bijective (normLiftTorsion (F := F) (E := E) (d := d))
    (normLiftTorsion_bijective (E := E) hdiv)
    (fun χ : nontrivialTorsionCharacters F d =>
      -(c ^ Module.finrank F E) *
        ((normLift (E := E) χ.val (uE : E))⁻¹ *
          gaussSum (normLift (E := E) χ.val) (traceLift (E := E) ψ)))
    (fun χ : nontrivialTorsionCharacters E d =>
      -(c ^ Module.finrank F E) *
        ((χ.val (uE : E))⁻¹ * gaussSum χ.val (traceLift (E := E) ψ)))
    (fun _ => rfl)
  rw [← he]
  apply Finset.sum_congr rfl
  intro χ _
  simpa [uE, mul_assoc] using lifted_normalized_gauss_factor ψ hHD c (u : F) χ.val
    ((mem_nontrivialTorsionCharacters d _).mp χ.property).2

/-- The spectral form of the standard cohomological trace formula suffices
to identify the determinant; no equality of individual eigenvalue labels is
required.  The extension indexed by n has degree n+1, so no field of size 1
or zero-degree extension is introduced. -/
theorem exists_determinant_one_from_monomial_traces
    (E : ℕ → Type*) [∀ n, Field (E n)] [∀ n, Fintype (E n)]
    [∀ n, Algebra F (E n)]
    (hrank : ∀ n, Module.finrank F (E n) = n + 1)
    {d v : ℕ} (hd : 0 < d) (hdiv : d ∣ Fintype.card F - 1)
    (hcard : Fintype.card F = v ^ 2)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (hHD : ∀ n, HasseDavenportIdentity (E := E n) ψ)
    (c : ℂ) (hc : c ^ 2 * Fintype.card F = 1)
    (eigenvalues : Fˣ → Fin (d - 1) → ℂ) (determinant : Fˣ → ℂ)
    (hdet : ∀ u, determinant u = ∏ i, eigenvalues u i)
    (htrace : ∀ (u : Fˣ) (n : ℕ),
      (∑ i, eigenvalues u i ^ (n + 1)) =
        -(c ^ (n + 1)) * ∑ t : E n,
          traceLift (E := E n) ψ (algebraMap F (E n) (u : F) * t ^ d)) :
    ∃ u : Fˣ, determinant u = 1 := by
  have hψ₁ : ψ ≠ 1 := by simpa only [AddChar.mulShift_one] using hψ one_ne_zero
  have hprod (u : Fˣ) : determinant u =
      ∏ χ : nontrivialTorsionCharacters F d, monomialGaussFactor ψ c u χ.val := by
    rw [hdet]
    apply prod_eq_of_powerSums
    · rw [Fintype.card_fin, Fintype.card_coe, card_nontrivialTorsionCharacters hdiv]
    · intro r hr
      have hh := normalized_monomial_sum_eq_powerSum (E := E (r - 1)) hd hdiv ψ hψ₁
        (hHD (r - 1)) c u
      rw [hrank, Nat.sub_add_cancel hr] at hh
      have ht := htrace u (r - 1)
      rw [Nat.sub_add_cancel hr] at ht
      exact ht.trans hh
  obtain ⟨u, hu, hprod1⟩ := exists_monomialGauss_product_one hψ hc hdiv hcard
  refine ⟨Units.mk0 u hu, ?_⟩
  rw [hprod]
  simpa only [Finset.prod_coe_sort, Units.val_mk0] using hprod1

end CayleyProof
