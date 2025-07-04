/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Coprime.Ideal
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Torsion submodules

## Main definitions

* `torsionOf R M x` : the torsion ideal of `x`, containing all `a` such that `a • x = 0`.
* `Submodule.torsionBy R M a` : the `a`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0`.
* `Submodule.torsionBySet R M s` : the submodule containing all elements `x` of `M` such that
  `a • x = 0` for all `a` in `s`.
* `Submodule.torsion' R M S` : the `S`-torsion submodule, containing all elements `x` of `M` such
  that `a • x = 0` for some `a` in `S`.
* `Submodule.torsion R M` : the torsion submodule, containing all elements `x` of `M` such that
  `a • x = 0` for some non-zero-divisor `a` in `R`.
* `Module.IsTorsionBy R M a` : the property that defines an `a`-torsion module. Similarly,
  `IsTorsionBySet`, `IsTorsion'` and `IsTorsion`.
* `Module.IsTorsionBySet.module` : Creates an `R ⧸ I`-module from an `R`-module that
  `IsTorsionBySet R _ I`.

## Main statements

* `quot_torsionOf_equiv_span_singleton` : isomorphism between the span of an element of `M` and
  the quotient by its torsion ideal.
* `torsion' R M S` and `torsion R M` are submodules.
* `torsionBySet_eq_torsionBySet_span` : torsion by a set is torsion by the ideal generated by it.
* `Submodule.torsionBy_is_torsionBy` : the `a`-torsion submodule is an `a`-torsion module.
  Similar lemmas for `torsion'` and `torsion`.
* `Submodule.torsionBy_isInternal` : a `∏ i, p i`-torsion module is the internal direct sum of its
  `p i`-torsion submodules when the `p i` are pairwise coprime. A more general version with coprime
  ideals is `Submodule.torsionBySet_is_internal`.
* `Submodule.noZeroSMulDivisors_iff_torsion_bot` : a module over a domain has
  `NoZeroSMulDivisors` (that is, there is no non-zero `a`, `x` such that `a • x = 0`)
  iff its torsion submodule is trivial.
* `Submodule.QuotientTorsion.torsion_eq_bot` : quotienting by the torsion submodule makes the
  torsion submodule of the new module trivial. If `R` is a domain, we can derive an instance
  `Submodule.QuotientTorsion.noZeroSMulDivisors : NoZeroSMulDivisors R (M ⧸ torsion R M)`.

## Notation

* The notions are defined for a `CommSemiring R` and a `Module R M`. Some additional hypotheses on
  `R` and `M` are required by some lemmas.
* The letters `a`, `b`, ... are used for scalars (in `R`), while `x`, `y`, ... are used for vectors
  (in `M`).

## Tags

Torsion, submodule, module, quotient
-/

namespace Ideal

section TorsionOf

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- The torsion ideal of `x`, containing all `a` such that `a • x = 0`. -/
@[simps!]
def torsionOf (x : M) : Ideal R :=
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation on LinearMap.ker https://github.com/leanprover/lean4/issues/1629
  LinearMap.ker (LinearMap.toSpanSingleton R M x)

@[simp]
theorem torsionOf_zero : torsionOf R M (0 : M) = ⊤ := by simp [torsionOf]

variable {R M}

@[simp]
theorem mem_torsionOf_iff (x : M) (a : R) : a ∈ torsionOf R M x ↔ a • x = 0 :=
  Iff.rfl

variable (R)

@[simp]
theorem torsionOf_eq_top_iff (m : M) : torsionOf R M m = ⊤ ↔ m = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [← one_smul R m, ← mem_torsionOf_iff m (1 : R), h]
  exact Submodule.mem_top

@[simp]
theorem torsionOf_eq_bot_iff_of_noZeroSMulDivisors [Nontrivial R] [NoZeroSMulDivisors R M] (m : M) :
    torsionOf R M m = ⊥ ↔ m ≠ 0 := by
  refine ⟨fun h contra => ?_, fun h => (Submodule.eq_bot_iff _).mpr fun r hr => ?_⟩
  · rw [contra, torsionOf_zero] at h
    exact bot_ne_top.symm h
  · rw [mem_torsionOf_iff, smul_eq_zero] at hr
    tauto

/-- See also `iSupIndep.linearIndependent` which provides the same conclusion
but requires the stronger hypothesis `NoZeroSMulDivisors R M`. -/
theorem iSupIndep.linearIndependent' {ι R M : Type*} {v : ι → M} [Ring R]
    [AddCommGroup M] [Module R M] (hv : iSupIndep fun i => R ∙ v i)
    (h_ne_zero : ∀ i, Ideal.torsionOf R M (v i) = ⊥) : LinearIndependent R v := by
  refine linearIndependent_iff_eq_zero_of_smul_mem_span.mpr fun i r hi => ?_
  replace hv := iSupIndep_def.mp hv i
  simp only [iSup_subtype', ← Submodule.span_range_eq_iSup (ι := Subtype _), disjoint_iff] at hv
  have : r • v i ∈ (⊥ : Submodule R M) := by
    rw [← hv, Submodule.mem_inf]
    refine ⟨Submodule.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
    convert hi
    ext
    simp
  rw [← Submodule.mem_bot R, ← h_ne_zero i]
  simpa using this

@[deprecated (since := "2024-11-24")]
alias CompleteLattice.Independent.linear_independent' := iSupIndep.linearIndependent'

end TorsionOf

section

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- The span of `x` in `M` is isomorphic to `R` quotiented by the torsion ideal of `x`. -/
noncomputable def quotTorsionOfEquivSpanSingleton (x : M) : (R ⧸ torsionOf R M x) ≃ₗ[R] R ∙ x :=
  (LinearMap.toSpanSingleton R M x).quotKerEquivRange.trans <|
    LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range R M x).symm

variable {R M}

@[simp]
theorem quotTorsionOfEquivSpanSingleton_apply_mk (x : M) (a : R) :
    quotTorsionOfEquivSpanSingleton R M x (Submodule.Quotient.mk a) =
      a • ⟨x, Submodule.mem_span_singleton_self x⟩ :=
  rfl

end

end Ideal

open nonZeroDivisors

section Defs

namespace Submodule

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

-- TODO: generalize to `Submodule S M` with `SMulCommClass R S M`.
/-- The `a`-torsion submodule for `a` in `R`, containing all elements `x` of `M` such that
  `a • x = 0`. -/
@[simps!]
def torsionBy (a : R) : Submodule R M :=
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation on LinearMap.ker https://github.com/leanprover/lean4/issues/1629
  LinearMap.ker (DistribMulAction.toLinearMap R M a)

/-- The submodule containing all elements `x` of `M` such that `a • x = 0` for all `a` in `s`. -/
@[simps!]
def torsionBySet (s : Set R) : Submodule R M :=
  sInf (torsionBy R M '' s)

/-- The `S`-torsion submodule, containing all elements `x` of `M` such that `a • x = 0` for some
`a` in `S`. -/
@[simps!]
def torsion' (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M] :
    Submodule R M where
  carrier := { x | ∃ a : S, a • x = 0 }
  add_mem' := by
    intro x y ⟨a,hx⟩ ⟨b,hy⟩
    use b * a
    rw [smul_add, mul_smul, mul_comm, mul_smul, hx, hy, smul_zero, smul_zero, add_zero]
  zero_mem' := ⟨1, smul_zero 1⟩
  smul_mem' := fun a x ⟨b, h⟩ => ⟨b, by rw [smul_comm, h, smul_zero]⟩

/-- The torsion submodule, containing all elements `x` of `M` such that `a • x = 0` for some
  non-zero-divisor `a` in `R`. -/
abbrev torsion :=
  torsion' R M R⁰

end Submodule

namespace Module

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- An `a`-torsion module is a module where every element is `a`-torsion. -/
abbrev IsTorsionBy (a : R) :=
  ∀ ⦃x : M⦄, a • x = 0

/-- A module where every element is `a`-torsion for all `a` in `s`. -/
abbrev IsTorsionBySet (s : Set R) :=
  ∀ ⦃x : M⦄ ⦃a : s⦄, (a : R) • x = 0

/-- An `S`-torsion module is a module where every element is `a`-torsion for some `a` in `S`. -/
abbrev IsTorsion' (S : Type*) [SMul S M] :=
  ∀ ⦃x : M⦄, ∃ a : S, a • x = 0

/-- A torsion module is a module where every element is `a`-torsion for some non-zero-divisor `a`.
-/
abbrev IsTorsion :=
  ∀ ⦃x : M⦄, ∃ a : R⁰, a • x = 0

theorem isTorsionBySet_annihilator : IsTorsionBySet R M (annihilator R M) :=
  fun _ r ↦ Module.mem_annihilator.mp r.2 _

theorem isTorsionBy_iff_mem_annihilator {a : R} :
    IsTorsionBy R M a ↔ a ∈ annihilator R M := by
  rw [IsTorsionBy, mem_annihilator]

theorem isTorsionBySet_iff_subset_annihilator {s : Set R} :
    IsTorsionBySet R M s ↔ s ⊆ annihilator R M := by
  simp_rw [IsTorsionBySet, Set.subset_def, SetLike.mem_coe, mem_annihilator]
  rw [forall_comm, SetCoe.forall]

end Module

end Defs

lemma isSMulRegular_iff_torsionBy_eq_bot {R} (M : Type*)
    [CommRing R] [AddCommGroup M] [Module R M] (r : R) :
    IsSMulRegular M r ↔ Submodule.torsionBy R M r = ⊥ :=
  Iff.symm (DistribMulAction.toLinearMap R M r).ker_eq_bot

variable {R M : Type*}

section

namespace Submodule

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

@[simp]
theorem smul_torsionBy (x : torsionBy R M a) : a • x = 0 :=
  Subtype.ext x.prop

@[simp]
theorem smul_coe_torsionBy (x : torsionBy R M a) : a • (x : M) = 0 :=
  x.prop

@[simp]
theorem mem_torsionBy_iff (x : M) : x ∈ torsionBy R M a ↔ a • x = 0 :=
  Iff.rfl

@[simp]
theorem mem_torsionBySet_iff (x : M) : x ∈ torsionBySet R M s ↔ ∀ a : s, (a : R) • x = 0 := by
  refine ⟨fun h ⟨a, ha⟩ => mem_sInf.mp h _ (Set.mem_image_of_mem _ ha), fun h => mem_sInf.mpr ?_⟩
  rintro _ ⟨a, ha, rfl⟩; exact h ⟨a, ha⟩

@[simp]
theorem torsionBySet_singleton_eq : torsionBySet R M {a} = torsionBy R M a := by
  ext x
  simp only [mem_torsionBySet_iff, SetCoe.forall, Set.mem_singleton_iff, forall_eq,
    mem_torsionBy_iff]

theorem torsionBySet_le_torsionBySet_of_subset {s t : Set R} (st : s ⊆ t) :
    torsionBySet R M t ≤ torsionBySet R M s :=
  sInf_le_sInf fun _ ⟨a, ha, h⟩ => ⟨a, st ha, h⟩

/-- Torsion by a set is torsion by the ideal generated by it. -/
theorem torsionBySet_eq_torsionBySet_span :
    torsionBySet R M s = torsionBySet R M (Ideal.span s) := by
  refine le_antisymm (fun x hx => ?_) (torsionBySet_le_torsionBySet_of_subset subset_span)
  rw [mem_torsionBySet_iff] at hx ⊢
  suffices Ideal.span s ≤ Ideal.torsionOf R M x by
    rintro ⟨a, ha⟩
    exact this ha
  rw [Ideal.span_le]
  exact fun a ha => hx ⟨a, ha⟩

theorem torsionBySet_span_singleton_eq : torsionBySet R M (R ∙ a) = torsionBy R M a :=
  (torsionBySet_eq_torsionBySet_span _).symm.trans <| torsionBySet_singleton_eq _

theorem torsionBy_le_torsionBy_of_dvd (a b : R) (dvd : a ∣ b) :
    torsionBy R M a ≤ torsionBy R M b := by
  rw [← torsionBySet_span_singleton_eq, ← torsionBySet_singleton_eq]
  apply torsionBySet_le_torsionBySet_of_subset
  rintro c (rfl : c = b); exact Ideal.mem_span_singleton.mpr dvd

@[simp]
theorem torsionBy_one : torsionBy R M 1 = ⊥ :=
  eq_bot_iff.mpr fun _ h => by
    rw [mem_torsionBy_iff, one_smul] at h
    exact h

@[simp]
theorem torsionBySet_univ : torsionBySet R M Set.univ = ⊥ := by
  rw [eq_bot_iff, ← torsionBy_one, ← torsionBySet_singleton_eq]
  exact torsionBySet_le_torsionBySet_of_subset fun _ _ => trivial

end Submodule

open Submodule

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBySet_of_subset {s t : Set R} (h : s ⊆ t)
    (ht : IsTorsionBySet R M t) : IsTorsionBySet R M s :=
  fun m r ↦ @ht m ⟨r, h r.2⟩

@[simp]
theorem isTorsionBySet_singleton_iff : IsTorsionBySet R M {a} ↔ IsTorsionBy R M a := by
  refine ⟨fun h x => @h _ ⟨_, Set.mem_singleton _⟩, fun h x => ?_⟩
  rintro ⟨b, rfl : b = a⟩; exact @h _

theorem isTorsionBySet_iff_is_torsion_by_span :
    IsTorsionBySet R M s ↔ IsTorsionBySet R M (Ideal.span s) := by
  simpa only [isTorsionBySet_iff_subset_annihilator] using Ideal.span_le.symm

theorem isTorsionBySet_span_singleton_iff : IsTorsionBySet R M (R ∙ a) ↔ IsTorsionBy R M a :=
  (isTorsionBySet_iff_is_torsion_by_span _).symm.trans <| isTorsionBySet_singleton_iff _

end Module

namespace Module

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBySet_iff_torsionBySet_eq_top :
    IsTorsionBySet R M s ↔ torsionBySet R M s = ⊤ :=
  ⟨fun h => eq_top_iff.mpr fun _ _ => (mem_torsionBySet_iff _ _).mpr <| @h _, fun h x => by
    rw [← mem_torsionBySet_iff, h]
    trivial⟩

/-- An `a`-torsion module is a module whose `a`-torsion submodule is the full space. -/
theorem isTorsionBy_iff_torsionBy_eq_top : IsTorsionBy R M a ↔ torsionBy R M a = ⊤ := by
  rw [← torsionBySet_singleton_eq, ← isTorsionBySet_singleton_iff,
    isTorsionBySet_iff_torsionBySet_eq_top]

theorem isTorsionBySet_iff_subseteq_ker_lsmul :
    IsTorsionBySet R M s ↔ s ⊆ LinearMap.ker (LinearMap.lsmul R M) where
  mp h r hr := LinearMap.mem_ker.mpr <| LinearMap.ext fun x => @h x ⟨r, hr⟩
  mpr | h, x, ⟨_, hr⟩ => DFunLike.congr_fun (LinearMap.mem_ker.mp (h hr)) x

theorem isTorsionBy_iff_mem_ker_lsmul :
    IsTorsionBy R M a ↔ a ∈ LinearMap.ker (LinearMap.lsmul R M) :=
  Iff.symm LinearMap.ext_iff

end Module

namespace Submodule

open Module

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_isTorsionBySet : IsTorsionBySet R (torsionBySet R M s) s :=
  fun ⟨_, hx⟩ a => Subtype.ext <| (mem_torsionBySet_iff _ _).mp hx a

/-- The `a`-torsion submodule is an `a`-torsion module. -/
theorem torsionBy_isTorsionBy : IsTorsionBy R (torsionBy R M a) a := smul_torsionBy a

@[simp]
theorem torsionBy_torsionBy_eq_top : torsionBy R (torsionBy R M a) a = ⊤ :=
  (isTorsionBy_iff_torsionBy_eq_top a).mp <| torsionBy_isTorsionBy a

@[simp]
theorem torsionBySet_torsionBySet_eq_top : torsionBySet R (torsionBySet R M s) s = ⊤ :=
  (isTorsionBySet_iff_torsionBySet_eq_top s).mp <| torsionBySet_isTorsionBySet s

variable (R M)

theorem torsion_gc :
    @GaloisConnection (Submodule R M) (Ideal R)ᵒᵈ _ _ annihilator fun I =>
      torsionBySet R M ↑(OrderDual.ofDual I) :=
  fun _ _ =>
  ⟨fun h x hx => (mem_torsionBySet_iff _ _).mpr fun ⟨_, ha⟩ => mem_annihilator.mp (h ha) x hx,
    fun h a ha => mem_annihilator.mpr fun _ hx => (mem_torsionBySet_iff _ _).mp (h hx) ⟨a, ha⟩⟩

variable {R M}

section Coprime

variable {ι : Type*} {p : ι → Ideal R} {S : Finset ι}

theorem iSup_torsionBySet_ideal_eq_torsionBySet_iInf
    (hp : (S : Set ι).Pairwise fun i j => p i ⊔ p j = ⊤) :
    ⨆ i ∈ S, torsionBySet R M (p i) = torsionBySet R M ↑(⨅ i ∈ S, p i) := by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  apply le_antisymm
  · apply iSup_le _
    intro i
    apply iSup_le _
    intro is
    apply torsionBySet_le_torsionBySet_of_subset
    exact (iInf_le (fun i => ⨅ _ : i ∈ S, p i) i).trans (iInf_le _ is)
  · intro x hx
    rw [mem_iSup_finset_iff_exists_sum]
    obtain ⟨μ, hμ⟩ :=
      (mem_iSup_finset_iff_exists_sum _ _).mp
        ((Ideal.eq_top_iff_one _).mp <| (Ideal.iSup_iInf_eq_top_iff_pairwise h _).mpr hp)
    refine ⟨fun i => ⟨(μ i : R) • x, ?_⟩, ?_⟩
    · rw [mem_torsionBySet_iff] at hx ⊢
      rintro ⟨a, ha⟩
      rw [smul_smul]
      suffices a * μ i ∈ ⨅ i ∈ S, p i from hx ⟨_, this⟩
      rw [mem_iInf]
      intro j
      rw [mem_iInf]
      intro hj
      by_cases ij : j = i
      · rw [ij]
        exact Ideal.mul_mem_right _ _ ha
      · have := coe_mem (μ i)
        simp only [mem_iInf] at this
        exact Ideal.mul_mem_left _ _ (this j hj ij)
    · rw [← Finset.sum_smul, hμ, one_smul]

theorem supIndep_torsionBySet_ideal (hp : (S : Set ι).Pairwise fun i j => p i ⊔ p j = ⊤) :
    S.SupIndep fun i => torsionBySet R M <| p i :=
  fun T hT i hi hiT => by
  rw [disjoint_iff, Finset.sup_eq_iSup,
    iSup_torsionBySet_ideal_eq_torsionBySet_iInf fun i hi j hj ij => hp (hT hi) (hT hj) ij]
  have := GaloisConnection.u_inf
    (b₁ := OrderDual.toDual (p i)) (b₂ := OrderDual.toDual (⨅ i ∈ T, p i)) (torsion_gc R M)
  dsimp at this ⊢
  rw [← this, Ideal.sup_iInf_eq_top, top_coe, torsionBySet_univ]
  intro j hj; apply hp hi (hT hj); rintro rfl; exact hiT hj

variable {q : ι → R}

open scoped Function -- required for scoped `on` notation

theorem iSup_torsionBy_eq_torsionBy_prod (hq : (S : Set ι).Pairwise <| (IsCoprime on q)) :
    ⨆ i ∈ S, torsionBy R M (q i) = torsionBy R M (∏ i ∈ S, q i) := by
  rw [← torsionBySet_span_singleton_eq, Ideal.submodule_span_eq, ←
    Ideal.finset_inf_span_singleton _ _ hq, Finset.inf_eq_iInf, ←
    iSup_torsionBySet_ideal_eq_torsionBySet_iInf]
  · congr
    ext : 1
    congr
    ext : 1
    exact (torsionBySet_span_singleton_eq _).symm
  exact fun i hi j hj ij => (Ideal.sup_eq_top_iff_isCoprime _ _).mpr (hq hi hj ij)

theorem supIndep_torsionBy (hq : (S : Set ι).Pairwise <| (IsCoprime on q)) :
    S.SupIndep fun i => torsionBy R M <| q i := by
  convert supIndep_torsionBySet_ideal (M := M) fun i hi j hj ij =>
      (Ideal.sup_eq_top_iff_isCoprime (q i) _).mpr <| hq hi hj ij
  exact (torsionBySet_span_singleton_eq (R := R) (M := M) _).symm

end Coprime

end Submodule

end

section NeedsGroup

namespace Submodule

variable [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type*} [DecidableEq ι] {S : Finset ι}

/-- If the `p i` are pairwise coprime, a `⨅ i, p i`-torsion module is the internal direct sum of
its `p i`-torsion submodules. -/
theorem torsionBySet_isInternal {p : ι → Ideal R}
    (hp : (S : Set ι).Pairwise fun i j => p i ⊔ p j = ⊤)
    (hM : Module.IsTorsionBySet R M (⨅ i ∈ S, p i : Ideal R)) :
    DirectSum.IsInternal fun i : S => torsionBySet R M <| p i :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_iff_supIndep.mpr <| supIndep_torsionBySet_ideal hp)
    (by
      apply (iSup_subtype'' ↑S fun i => torsionBySet R M <| p i).trans
      -- Porting note: times out if we change apply below to <|
      apply (iSup_torsionBySet_ideal_eq_torsionBySet_iInf hp).trans <|
        (Module.isTorsionBySet_iff_torsionBySet_eq_top _).mp hM)

open scoped Function in -- required for scoped `on` notation
/-- If the `q i` are pairwise coprime, a `∏ i, q i`-torsion module is the internal direct sum of
its `q i`-torsion submodules. -/
theorem torsionBy_isInternal {q : ι → R} (hq : (S : Set ι).Pairwise <| (IsCoprime on q))
    (hM : Module.IsTorsionBy R M <| ∏ i ∈ S, q i) :
    DirectSum.IsInternal fun i : S => torsionBy R M <| q i := by
  rw [← Module.isTorsionBySet_span_singleton_iff, Ideal.submodule_span_eq, ←
    Ideal.finset_inf_span_singleton _ _ hq, Finset.inf_eq_iInf] at hM
  convert torsionBySet_isInternal
      (fun i hi j hj ij => (Ideal.sup_eq_top_iff_isCoprime (q i) _).mpr <| hq hi hj ij) hM
  exact (torsionBySet_span_singleton_eq _ (R := R) (M := M)).symm

end Submodule

namespace Module

variable [Ring R] [AddCommGroup M] [Module R M]
variable {I : Ideal R} {r : R}

/-- can't be an instance because `hM` can't be inferred -/
def IsTorsionBySet.hasSMul (hM : IsTorsionBySet R M I) : SMul (R ⧸ I) M where
  smul b := QuotientAddGroup.lift I.toAddSubgroup (smulAddHom R M)
    (by rwa [isTorsionBySet_iff_subset_annihilator] at hM) b

/-- can't be an instance because `hM` can't be inferred -/
abbrev IsTorsionBy.hasSMul (hM : IsTorsionBy R M r) : SMul (R ⧸ Ideal.span {r}) M :=
  ((isTorsionBySet_span_singleton_iff r).mpr hM).hasSMul

@[simp]
theorem IsTorsionBySet.mk_smul [I.IsTwoSided] (hM : IsTorsionBySet R M I) (b : R) (x : M) :
    haveI := hM.hasSMul
    Ideal.Quotient.mk I b • x = b • x :=
  rfl

@[simp]
theorem IsTorsionBy.mk_smul [(Ideal.span {r}).IsTwoSided] (hM : IsTorsionBy R M r) (b : R) (x : M) :
    haveI := hM.hasSMul
    Ideal.Quotient.mk (Ideal.span {r}) b • x = b • x :=
  rfl

/-- An `(R ⧸ I)`-module is an `R`-module which `IsTorsionBySet R M I`. -/
def IsTorsionBySet.module [I.IsTwoSided] (hM : IsTorsionBySet R M I) : Module (R ⧸ I) M :=
  letI := hM.hasSMul; I.mkQ_surjective.moduleLeft _ (IsTorsionBySet.mk_smul hM)

instance IsTorsionBySet.isScalarTower [I.IsTwoSided] (hM : IsTorsionBySet R M I)
    {S : Type*} [SMul S R] [SMul S M] [IsScalarTower S R M] [IsScalarTower S R R] :
    @IsScalarTower S (R ⧸ I) M _ (IsTorsionBySet.module hM).toSMul _ :=
  -- Porting note: still needed to be fed the Module R / I M instance
  @IsScalarTower.mk S (R ⧸ I) M _ (IsTorsionBySet.module hM).toSMul _
    (fun b d x => Quotient.inductionOn' d fun c => (smul_assoc b c x :))

/-- If a `R`-module `M` is annihilated by a two-sided ideal `I`, then the identity is a semilinear
map from the `R`-module `M` to the `R ⧸ I`-module `M`. -/
def IsTorsionBySet.semilinearMap [I.IsTwoSided] (hM : IsTorsionBySet R M I) :
    let _ := hM.module; M →ₛₗ[Ideal.Quotient.mk I] M :=
  let _ := hM.module
  { toFun := id
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }

theorem IsTorsionBySet.isSemisimpleModule_iff [I.IsTwoSided]
    (hM : Module.IsTorsionBySet R M I) : let _ := hM.module
    IsSemisimpleModule (R ⧸ I) M ↔ IsSemisimpleModule R M :=
  let _ := hM.module
  (hM.semilinearMap.isSemisimpleModule_iff_of_bijective Function.bijective_id).symm

/-- An `(R ⧸ Ideal.span {r})`-module is an `R`-module for which `IsTorsionBy R M r`. -/
abbrev IsTorsionBy.module [h : (Ideal.span {r}).IsTwoSided] (hM : IsTorsionBy R M r) :
    Module (R ⧸ Ideal.span {r}) M := by
  rw [Ideal.span] at h; exact ((isTorsionBySet_span_singleton_iff r).mpr hM).module

/-- Any module is also a module over the quotient of the ring by the annihilator.
Not an instance because it causes synthesis failures / timeouts. -/
def quotientAnnihilator : Module (R ⧸ Module.annihilator R M) M :=
  (isTorsionBySet_annihilator R M).module

theorem isTorsionBy_quotient_iff (N : Submodule R M) (r : R) :
    IsTorsionBy R (M⧸N) r ↔ ∀ x, r • x ∈ N :=
  Iff.trans N.mkQ_surjective.forall <| forall_congr' fun _ =>
    Submodule.Quotient.mk_eq_zero N

theorem IsTorsionBy.quotient (N : Submodule R M) {r : R}
    (h : IsTorsionBy R M r) : IsTorsionBy R (M⧸N) r :=
  (isTorsionBy_quotient_iff N r).mpr fun x => @h x ▸ N.zero_mem

theorem isTorsionBySet_quotient_iff (N : Submodule R M) (s : Set R) :
    IsTorsionBySet R (M⧸N) s ↔ ∀ x, ∀ r ∈ s, r • x ∈ N :=
  Iff.trans N.mkQ_surjective.forall <| forall_congr' fun _ =>
    Iff.trans Subtype.forall <| forall₂_congr fun _ _ =>
      Submodule.Quotient.mk_eq_zero N

theorem IsTorsionBySet.quotient (N : Submodule R M) {s}
    (h : IsTorsionBySet R M s) : IsTorsionBySet R (M⧸N) s :=
  (isTorsionBySet_quotient_iff N s).mpr fun x r h' => @h x ⟨r, h'⟩ ▸ N.zero_mem

variable (M I) (s : Set R) (r : R)

open Pointwise Submodule

lemma isTorsionBySet_quotient_set_smul :
    IsTorsionBySet R (M⧸s • (⊤ : Submodule R M)) s :=
  (isTorsionBySet_quotient_iff _ _).mpr fun _ _ h =>
    mem_set_smul_of_mem_mem h mem_top

lemma isTorsionBySet_quotient_ideal_smul :
    IsTorsionBySet R (M⧸I • (⊤ : Submodule R M)) I :=
  (isTorsionBySet_quotient_iff _ _).mpr fun _ _ h => smul_mem_smul h ⟨⟩

instance [I.IsTwoSided] : Module (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
  (isTorsionBySet_quotient_ideal_smul M I).module

lemma Quotient.mk_smul_mk [I.IsTwoSided] (r : R) (m : M) :
    Ideal.Quotient.mk I r •
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) m =
      Submodule.Quotient.mk (p := (I • ⊤ : Submodule R M)) (r • m) :=
  rfl

end Module

namespace Module

variable (M) [CommRing R] [AddCommGroup M] [Module R M] (s : Set R) (r : R)

open Pointwise

lemma isTorsionBy_quotient_element_smul :
    IsTorsionBy R (M⧸r • (⊤ : Submodule R M)) r :=
  (isTorsionBy_quotient_iff _ _).mpr (Submodule.smul_mem_pointwise_smul · r ⊤ ⟨⟩)

instance : Module (R ⧸ Ideal.span s) (M ⧸ s • (⊤ : Submodule R M)) :=
  ((isTorsionBySet_iff_is_torsion_by_span s).mp
    (isTorsionBySet_quotient_set_smul M s)).module

instance : Module (R ⧸ Ideal.span {r}) (M ⧸ r • (⊤ : Submodule R M)) :=
  (isTorsionBy_quotient_element_smul M r).module

end Module

namespace Submodule

variable [CommRing R] [AddCommGroup M] [Module R M]

instance (I : Ideal R) : Module (R ⧸ I) (torsionBySet R M I) :=
  -- Porting note: times out without the (R := R)
  Module.IsTorsionBySet.module <| torsionBySet_isTorsionBySet (R := R) I

@[simp]
theorem torsionBySet.mk_smul (I : Ideal R) (b : R) (x : torsionBySet R M I) :
    Ideal.Quotient.mk I b • x = b • x :=
  rfl

instance (I : Ideal R) {S : Type*} [SMul S R] [SMul S M] [IsScalarTower S R M]
    [IsScalarTower S R R] : IsScalarTower S (R ⧸ I) (torsionBySet R M I) :=
  inferInstance

/-- The `a`-torsion submodule as an `(R ⧸ R∙a)`-module. -/
instance instModuleQuotientTorsionBy (a : R) : Module (R ⧸ R ∙ a) (torsionBy R M a) :=
  Module.IsTorsionBySet.module <|
    (Module.isTorsionBySet_span_singleton_iff a).mpr <| torsionBy_isTorsionBy a

instance (a : R) : Module (R ⧸ Ideal.span {a}) (torsionBy R M a) :=
   inferInstanceAs <| Module (R ⧸ R ∙ a) (torsionBy R M a)

@[simp]
theorem torsionBy.mk_ideal_smul (a b : R) (x : torsionBy R M a) :
    (Ideal.Quotient.mk (Ideal.span {a})) b • x = b • x :=
  rfl

theorem torsionBy.mk_smul (a b : R) (x : torsionBy R M a) :
    Ideal.Quotient.mk (R ∙ a) b • x = b • x :=
  rfl

instance (a : R) {S : Type*} [SMul S R] [SMul S M] [IsScalarTower S R M] [IsScalarTower S R R] :
    IsScalarTower S (R ⧸ R ∙ a) (torsionBy R M a) :=
  inferInstance

/-- Given an `R`-module `M` and an element `a` in `R`, submodules of the `a`-torsion submodule of
`M` do not depend on whether we take scalars to be `R` or `R ⧸ R ∙ a`. -/
def submodule_torsionBy_orderIso (a : R) :
    Submodule (R ⧸ R ∙ a) (torsionBy R M a) ≃o Submodule R (torsionBy R M a) :=
  { restrictScalarsEmbedding R (R ⧸ R ∙ a) (torsionBy R M a) with
    invFun := fun p ↦
      { carrier := p
        add_mem' := add_mem
        zero_mem' := p.zero_mem
        smul_mem' := by rintro ⟨b⟩; exact p.smul_mem b }
    left_inv := by intro; ext; simp [restrictScalarsEmbedding]
    right_inv := by intro; ext; simp [restrictScalarsEmbedding] }

end Submodule

end NeedsGroup

namespace Submodule

section Torsion'

open Module

variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M]

@[simp]
theorem mem_torsion'_iff (x : M) : x ∈ torsion' R M S ↔ ∃ a : S, a • x = 0 :=
  Iff.rfl

theorem mem_torsion_iff (x : M) : x ∈ torsion R M ↔ ∃ a : R⁰, a • x = 0 :=
  Iff.rfl

@[simps]
instance : SMul S (torsion' R M S) :=
  ⟨fun s x =>
    ⟨s • (x : M), by
      obtain ⟨x, a, h⟩ := x
      use a
      dsimp
      rw [smul_comm, h, smul_zero]⟩⟩

instance : DistribMulAction S (torsion' R M S) :=
  Subtype.coe_injective.distribMulAction (torsion' R M S).subtype.toAddMonoidHom fun (_ : S) _ =>
    rfl

instance : SMulCommClass S R (torsion' R M S) :=
  ⟨fun _ _ _ => Subtype.ext <| smul_comm _ _ _⟩

/-- An `S`-torsion module is a module whose `S`-torsion submodule is the full space. -/
theorem isTorsion'_iff_torsion'_eq_top : IsTorsion' M S ↔ torsion' R M S = ⊤ :=
  ⟨fun h => eq_top_iff.mpr fun _ _ => @h _, fun h x => by
    rw [← @mem_torsion'_iff R, h]
    trivial⟩

/-- The `S`-torsion submodule is an `S`-torsion module. -/
theorem torsion'_isTorsion' : IsTorsion' (torsion' R M S) S := fun ⟨_, ⟨a, h⟩⟩ => ⟨a, Subtype.ext h⟩

@[simp]
theorem torsion'_torsion'_eq_top : torsion' R (torsion' R M S) S = ⊤ :=
  (isTorsion'_iff_torsion'_eq_top S).mp <| torsion'_isTorsion' S

/-- The torsion submodule of the torsion submodule (viewed as a module) is the full
torsion module. -/
theorem torsion_torsion_eq_top : torsion R (torsion R M) = ⊤ :=
  torsion'_torsion'_eq_top R⁰

/-- The torsion submodule is always a torsion module. -/
theorem torsion_isTorsion : Module.IsTorsion R (torsion R M) :=
  torsion'_isTorsion' R⁰

end Torsion'

section Torsion

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (R M)

theorem _root_.Module.isTorsionBySet_annihilator_top :
    Module.IsTorsionBySet R M (⊤ : Submodule R M).annihilator := fun x ha =>
  mem_annihilator.mp ha.prop x mem_top

variable {R M}

theorem _root_.Submodule.annihilator_top_inter_nonZeroDivisors [Module.Finite R M]
    (hM : Module.IsTorsion R M) : ((⊤ : Submodule R M).annihilator : Set R) ∩ R⁰ ≠ ∅ := by
  obtain ⟨S, hS⟩ := ‹Module.Finite R M›.fg_top
  refine Set.Nonempty.ne_empty ⟨_, ?_, (∏ x ∈ S, (@hM x).choose : R⁰).prop⟩
  rw [Submonoid.coe_finset_prod, SetLike.mem_coe, ← hS, mem_annihilator_span]
  intro n
  letI := Classical.decEq M
  rw [← Finset.prod_erase_mul _ _ n.prop, mul_smul, ← Submonoid.smul_def, (@hM n).choose_spec,
    smul_zero]

variable [NoZeroDivisors R] [Nontrivial R]

theorem coe_torsion_eq_annihilator_ne_bot :
    (torsion R M : Set M) = { x : M | (R ∙ x).annihilator ≠ ⊥ } := by
  ext x; simp_rw [Submodule.ne_bot_iff, mem_annihilator, mem_span_singleton]
  exact
    ⟨fun ⟨a, hax⟩ =>
      ⟨a, fun _ ⟨b, hb⟩ => by rw [← hb, smul_comm, ← Submonoid.smul_def, hax, smul_zero],
        nonZeroDivisors.coe_ne_zero _⟩,
      fun ⟨a, hax, ha⟩ => ⟨⟨_, mem_nonZeroDivisors_of_ne_zero ha⟩, hax x ⟨1, one_smul _ _⟩⟩⟩

/-- A module over a domain has `NoZeroSMulDivisors` iff its torsion submodule is trivial. -/
theorem noZeroSMulDivisors_iff_torsion_eq_bot : NoZeroSMulDivisors R M ↔ torsion R M = ⊥ := by
  constructor <;> intro h
  · haveI : NoZeroSMulDivisors R M := h
    rw [eq_bot_iff]
    rintro x ⟨a, hax⟩
    change (a : R) • x = 0 at hax
    rcases eq_zero_or_eq_zero_of_smul_eq_zero hax with h0 | h0
    · exfalso
      exact nonZeroDivisors.coe_ne_zero a h0
    · exact h0
  · exact
      { eq_zero_or_eq_zero_of_smul_eq_zero := fun {a} {x} hax => by
          by_cases ha : a = 0
          · left
            exact ha
          · right
            rw [← mem_bot R, ← h]
            exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, hax⟩ }

lemma torsion_int {G} [AddCommGroup G] :
    (torsion ℤ G).toAddSubgroup = AddCommGroup.torsion G := by
  ext x
  refine ((isOfFinAddOrder_iff_zsmul_eq_zero (x := x)).trans ?_).symm
  simp [mem_nonZeroDivisors_iff_ne_zero]

end Torsion

namespace QuotientTorsion

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Quotienting by the torsion submodule gives a torsion-free module. -/
@[simp]
theorem torsion_eq_bot : torsion R (M ⧸ torsion R M) = ⊥ :=
  eq_bot_iff.mpr fun z =>
    Quotient.inductionOn' z fun x ⟨a, hax⟩ => by
      rw [Quotient.mk''_eq_mk, ← Quotient.mk_smul, Quotient.mk_eq_zero] at hax
      rw [mem_bot, Quotient.mk''_eq_mk, Quotient.mk_eq_zero]
      obtain ⟨b, h⟩ := hax
      exact ⟨b * a, (mul_smul _ _ _).trans h⟩

instance noZeroSMulDivisors [IsDomain R] : NoZeroSMulDivisors R (M ⧸ torsion R M) :=
  noZeroSMulDivisors_iff_torsion_eq_bot.mpr torsion_eq_bot

end QuotientTorsion

section PTorsion

open Module

section

variable [Monoid R] [AddCommMonoid M] [DistribMulAction R M]

theorem isTorsion'_powers_iff (p : R) :
    IsTorsion' M (Submonoid.powers p) ↔ ∀ x : M, ∃ n : ℕ, p ^ n • x = 0 := by
  constructor
  · intro h x
    let ⟨⟨a, ⟨n, hn⟩⟩, hx⟩ := @h x
    dsimp at hn
    use n
    rw [hn]
    apply hx
  · intro h x
    let ⟨n, hn⟩ := h x
    exact ⟨⟨_, ⟨n, rfl⟩⟩, hn⟩

/-- In a `p ^ ∞`-torsion module (that is, a module where all elements are cancelled by scalar
multiplication by some power of `p`), the smallest `n` such that `p ^ n • x = 0`. -/
def pOrder {p : R} (hM : IsTorsion' M <| Submonoid.powers p) (x : M)
    [∀ n : ℕ, Decidable (p ^ n • x = 0)] :=
  Nat.find <| (isTorsion'_powers_iff p).mp hM x

@[simp]
theorem pow_pOrder_smul {p : R} (hM : IsTorsion' M <| Submonoid.powers p) (x : M)
    [∀ n : ℕ, Decidable (p ^ n • x = 0)] : p ^ pOrder hM x • x = 0 :=
  Nat.find_spec <| (isTorsion'_powers_iff p).mp hM x

end

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [∀ x : M, Decidable (x = 0)]

theorem exists_isTorsionBy {p : R} (hM : IsTorsion' M <| Submonoid.powers p) (d : ℕ) (hd : d ≠ 0)
    (s : Fin d → M) (hs : span R (Set.range s) = ⊤) :
    ∃ j : Fin d, Module.IsTorsionBy R M (p ^ pOrder hM (s j)) := by
  let oj := List.argmax (fun i => pOrder hM <| s i) (List.finRange d)
  have hoj : oj.isSome :=
    Option.ne_none_iff_isSome.mp fun eq_none =>
      hd <| List.finRange_eq_nil.mp <| List.argmax_eq_none.mp eq_none
  use Option.get _ hoj
  rw [isTorsionBy_iff_torsionBy_eq_top, eq_top_iff, ← hs, Submodule.span_le,
    Set.range_subset_iff]
  intro i; change (p ^ pOrder hM (s (Option.get oj hoj))) • s i = 0
  have : pOrder hM (s i) ≤ pOrder hM (s <| Option.get _ hoj) :=
    List.le_of_mem_argmax (List.mem_finRange i) (Option.get_mem hoj)
  rw [← Nat.sub_add_cancel this, pow_add, mul_smul, pow_pOrder_smul, smul_zero]

end PTorsion

end Submodule

namespace Ideal.Quotient

open Submodule

universe w
theorem torsionBy_eq_span_singleton {R : Type w} [CommRing R] (a b : R) (ha : a ∈ R⁰) :
    torsionBy R (R ⧸ R ∙ a * b) a = R ∙ mk (R ∙ a * b) b := by
  ext x; rw [mem_torsionBy_iff, Submodule.mem_span_singleton]
  obtain ⟨x, rfl⟩ := mk_surjective x; constructor <;> intro h
  · rw [← mk_eq_mk, ← Quotient.mk_smul, Quotient.mk_eq_zero, Submodule.mem_span_singleton] at h
    obtain ⟨c, h⟩ := h
    rw [smul_eq_mul, smul_eq_mul, mul_comm, mul_assoc, mul_cancel_left_mem_nonZeroDivisors ha,
      mul_comm] at h
    use c
    rw [← h, ← mk_eq_mk, ← Quotient.mk_smul, smul_eq_mul, mk_eq_mk]
  · obtain ⟨c, h⟩ := h
    rw [← h, smul_comm, ← mk_eq_mk, ← Quotient.mk_smul,
      (Quotient.mk_eq_zero _).mpr <| mem_span_singleton_self _, smul_zero]

end Ideal.Quotient

namespace AddMonoid

theorem isTorsion_iff_isTorsion_nat [AddCommMonoid M] :
    AddMonoid.IsTorsion M ↔ Module.IsTorsion ℕ M := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨n, h0, hn⟩ := (h x).exists_nsmul_eq_zero
    exact ⟨⟨n, mem_nonZeroDivisors_of_ne_zero <| ne_of_gt h0⟩, hn⟩
  · rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    obtain ⟨n, hn⟩ := @h x
    exact ⟨n, Nat.pos_of_ne_zero (nonZeroDivisors.coe_ne_zero _), hn⟩

theorem isTorsion_iff_isTorsion_int [AddCommGroup M] :
    AddMonoid.IsTorsion M ↔ Module.IsTorsion ℤ M := by
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · obtain ⟨n, h0, hn⟩ := (h x).exists_nsmul_eq_zero
    exact
      ⟨⟨n, mem_nonZeroDivisors_of_ne_zero <| ne_of_gt <| Int.natCast_pos.mpr h0⟩,
        (natCast_zsmul _ _).trans hn⟩
  · rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    obtain ⟨n, hn⟩ := @h x
    exact ⟨_, Int.natAbs_pos.2 (nonZeroDivisors.coe_ne_zero n), natAbs_nsmul_eq_zero.2 hn⟩

end AddMonoid

namespace AddSubgroup

variable (A : Type*) [AddCommGroup A] (n : ℤ)

/-- The additive `n`-torsion subgroup for an integer `n`, denoted as `A[n]`. -/
@[reducible]
def torsionBy : AddSubgroup A :=
  (Submodule.torsionBy ℤ A n).toAddSubgroup

@[inherit_doc torsionBy]
scoped syntax:max (name := torsionByStx) (priority := high) term noWs "[" term "]" : term

macro_rules | `($A[$n]) => `(torsionBy $A $n)

/-- Unexpander for `torsionBy`. -/
@[scoped app_unexpander torsionBy]
def torsionByUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $A $n) => `($A[$n])
  | _ => throw ()

lemma torsionBy.neg : A[-n] = A[n] := by
  ext a
  simp

variable {A} {n : ℕ}

@[simp]
lemma torsionBy.nsmul (x : A[n]) : n • x = 0 :=
  Nat.cast_smul_eq_nsmul ℤ n x ▸ Submodule.smul_torsionBy ..

lemma torsionBy.nsmul_iff {x : A} :
    x ∈ A[n] ↔ n • x = 0 :=
  Nat.cast_smul_eq_nsmul ℤ n x ▸ Submodule.mem_torsionBy_iff ..

lemma torsionBy.mod_self_nsmul (s : ℕ) (x : A[n]) :
    s • x = (s % n) • x :=
  nsmul_eq_mod_nsmul s (torsionBy.nsmul x)

lemma torsionBy.mod_self_nsmul' (s : ℕ) {x : A} (h : x ∈ A[n]) :
    s • x = (s % n) • x :=
  nsmul_eq_mod_nsmul s (torsionBy.nsmul_iff.mp h)

/-- For a natural number `n`, the `n`-torsion subgroup of `A` is a `ZMod n` module. -/
def torsionBy.zmodModule : Module (ZMod n) A[n] :=
  AddCommGroup.zmodModule torsionBy.nsmul

end AddSubgroup

section InfiniteRange

@[simp]
lemma infinite_range_add_smul_iff
    [AddCommGroup M] [Ring R] [Module R M] [Infinite R] [NoZeroSMulDivisors R M] (x y : M) :
    (Set.range <| fun r : R ↦ x + r • y).Infinite ↔ y ≠ 0 := by
  refine ⟨fun h hy ↦ by simp [hy] at h, fun h ↦ Set.infinite_range_of_injective fun r s hrs ↦ ?_⟩
  rw [add_right_inj] at hrs
  exact smul_left_injective _ h hrs

@[simp]
lemma infinite_range_add_nsmul_iff [AddCommGroup M] [NoZeroSMulDivisors ℤ M] (x y : M) :
    (Set.range <| fun n : ℕ ↦ x + n • y).Infinite ↔ y ≠ 0 := by
  refine ⟨fun h hy ↦ by simp [hy] at h, fun h ↦ Set.infinite_range_of_injective fun r s hrs ↦ ?_⟩
  rw [add_right_inj, ← natCast_zsmul, ← natCast_zsmul] at hrs
  simpa using smul_left_injective _ h hrs

end InfiniteRange
