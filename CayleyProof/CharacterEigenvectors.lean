module

public import CayleyProof.CurveGraph
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! The character eigenvector calculation for the actual adjacency matrix.
The eigenbasis is mathlib's existing complex character basis.
-/

open scoped BigOperators Matrix Classical

@[expose] public section

namespace CayleyProof

variable {F : Type*} [Field F] [Fintype F] {s : ℕ}

def dotCharacter (ψ : AddChar F ℂ) (b : Fin s → F) : AddChar (Fin s → F) ℂ where
  toFun x := ψ (∑ i, b i * x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, AddChar.map_add_eq_mul]

omit [Fintype F] in
theorem dotCharacter_injective {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    Function.Injective (dotCharacter ψ (s := s)) := by
  intro b c h
  funext j
  apply AddChar.to_mulShift_inj_of_isPrimitive hψ
  ext t
  have hj := DFunLike.congr_fun h (Pi.single j t)
  simpa [dotCharacter, Pi.single_apply, mul_ite, AddChar.mulShift_apply] using hj

theorem dotCharacter_bijective {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    Function.Bijective (dotCharacter ψ (s := s)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨dotCharacter_injective hψ, (AddChar.card_eq (α := Fin s → F)).symm⟩

noncomputable def realEigenvalue (ψ : AddChar F ℂ) (b : Fin s → F) : ℝ :=
  2 * (∑ t : F, ψ (∑ i, b i * t ^ (i.val + 1))).re - 2

@[simp] theorem realEigenvalue_zero (ψ : AddChar F ℂ) :
    realEigenvalue (s := s) ψ 0 = 2 * ((Fintype.card F : ℝ) - 1) := by
  simp [realEigenvalue]
  ring

/-- The eigenvalue as a sum over the generator set. -/
noncomputable def characterEigenvalue (χ : AddChar (Fin s → F) ℂ) : ℂ := by
  classical
  exact ∑ z : generators F s, χ z.val

theorem character_eigenvector (hs : 0 < s) (χ : AddChar (Fin s → F) ℂ)
    (x : Fin s → F) :
    ((curveGraph F s).adjMatrix ℂ *ᵥ (fun v => χ v)) x = characterEigenvalue χ * χ x := by
  classical
  rw [SimpleGraph.adjMatrix_mulVec_apply,
    Finset.sum_subtype (p := fun w => w ∈ (curveGraph F s).neighborSet x)
      ((curveGraph F s).neighborFinset x) (by intro w; simp) (fun v => χ v)]
  rw [← (generatorNeighborEquiv hs x).sum_comp (fun z => χ z.val)]
  simp only [generatorNeighborEquiv_apply_val, AddChar.map_add_eq_mul]
  rw [← Finset.mul_sum, mul_comm]
  rfl

/-- The generator sum is the sum of a character and its conjugate on each
nonzero point of the curve. -/
theorem characterEigenvalue_eq_pair_sum (hs : 2 ≤ s) (hchar : (2 : F) ≠ 0)
    (χ : AddChar (Fin s → F) ℂ) :
    characterEigenvalue χ =
      ∑ t : {t : F // t ≠ 0}, (χ (curve s t.val) + star (χ (curve s t.val))) := by
  classical
  unfold characterEigenvalue
  rw [← (Equiv.ofBijective (signedGenerator (F := F) (s := s))
    (signedGenerator_bijective hs hchar)).sum_comp (fun z => χ z.val)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp [signedGenerator, AddChar.map_neg_eq_conj]

/-- Exact real eigenvalue formula, including the correction for deleting `t = 0`. -/
theorem characterEigenvalue_eq (hs : 2 ≤ s) (hchar : (2 : F) ≠ 0)
    (χ : AddChar (Fin s → F) ℂ) :
    characterEigenvalue χ =
      ((2 * (∑ t : F, χ (curve s t)).re - 2 : ℝ) : ℂ) := by
  classical
  rw [characterEigenvalue_eq_pair_sum hs hchar]
  have hp (z : ℂ) : z + star z = ((2 * z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp; ring
  simp_rw [hp]
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun t : F => χ (curve s t)) 0]
  simp only [curve_zero, AddChar.map_zero_eq_one, Complex.add_re, Complex.one_re]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, Complex.re_sum]
  simp only [Complex.ofReal_add, Complex.ofReal_one]
  ring

omit [Fintype F] in
theorem character_function_ne_zero (χ : AddChar (Fin s → F) ℂ) :
    (fun v => χ v) ≠ 0 := by
  intro h
  have h₀ := congrFun h 0
  simp at h₀

/-- Completeness: the actual adjacency matrix has a character eigenbasis. -/
theorem character_eigenbasis (hs : 0 < s) :
    ∃ b : Module.Basis (AddChar (Fin s → F) ℂ) ℂ ((Fin s → F) → ℂ),
      ∀ χ, (curveGraph F s).adjMatrix ℂ *ᵥ b χ = characterEigenvalue χ • b χ := by
  refine ⟨AddChar.complexBasis (Fin s → F), ?_⟩
  intro χ
  ext x
  simpa only [AddChar.complexBasis_apply, Pi.smul_apply, smul_eq_mul] using
    character_eigenvector hs χ x

/-- The exact eigenvalue formula is indexed by coefficient vectors, with
one basis vector per coefficient vector. Thus repetitions count with
their actual algebraic multiplicities. -/
theorem coefficient_eigenbasis (hs : 2 ≤ s) (hchar : (2 : F) ≠ 0)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ∃ b : Module.Basis (Fin s → F) ℂ ((Fin s → F) → ℂ),
      ∀ a, (curveGraph F s).adjMatrix ℂ *ᵥ b a =
        (realEigenvalue ψ a : ℂ) • b a := by
  let e := Equiv.ofBijective (dotCharacter ψ (s := s)) (dotCharacter_bijective hψ)
  refine ⟨(AddChar.complexBasis (Fin s → F)).reindex e.symm, ?_⟩
  intro a
  have he : characterEigenvalue (dotCharacter ψ a) = (realEigenvalue ψ a : ℂ) := by
    simpa [realEigenvalue, dotCharacter, curve] using
      characterEigenvalue_eq hs hchar (dotCharacter ψ a)
  ext x
  simpa only [Module.Basis.reindex_apply, Equiv.symm_symm, e, Equiv.ofBijective_apply,
    AddChar.complexBasis_apply,
    Pi.smul_apply, smul_eq_mul, he] using
    character_eigenvector (by omega : 0 < s) (dotCharacter ψ a) x

end CayleyProof
