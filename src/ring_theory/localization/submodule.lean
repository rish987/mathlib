/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import ring_theory.localization.fraction_ring
import ring_theory.localization.ideal
import ring_theory.principal_ideal_domain

/-!
# Submodules in localizations of commutative rings

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]

namespace is_localization

/-- Map from ideals of `R` to submodules of `S` induced by `f`. -/
-- This was previously a `has_coe` instance, but if `S = R` then this will loop.
-- It could be a `has_coe_t` instance, but we keep it explicit here to avoid slowing down
-- the rest of the library.
def coe_submodule (I : ideal R) : submodule R S := submodule.map (algebra.linear_map R S) I

lemma mem_coe_submodule (I : ideal R) {x : S} :
  x ∈ coe_submodule S I ↔ ∃ y : R, y ∈ I ∧ algebra_map R S y = x :=
iff.rfl

lemma coe_submodule_mono {I J : ideal R} (h : I ≤ J) :
  coe_submodule S I ≤ coe_submodule S J :=
submodule.map_mono h

@[simp] lemma coe_submodule_bot : coe_submodule S (⊥ : ideal R) = ⊥ :=
by rw [coe_submodule, submodule.map_bot]

@[simp] lemma coe_submodule_top : coe_submodule S (⊤ : ideal R) = 1 :=
by rw [coe_submodule, submodule.map_top, submodule.one_eq_range]

@[simp] lemma coe_submodule_sup (I J : ideal R) :
  coe_submodule S (I ⊔ J) = coe_submodule S I ⊔ coe_submodule S J :=
submodule.map_sup _ _ _

@[simp] lemma coe_submodule_mul (I J : ideal R) :
  coe_submodule S (I * J) = coe_submodule S I * coe_submodule S J :=
submodule.map_mul _ _ (algebra.of_id R S)

lemma coe_submodule_fg
  (hS : function.injective (algebra_map R S)) (I : ideal R) :
  submodule.fg (coe_submodule S I) ↔ submodule.fg I :=
⟨submodule.fg_of_fg_map _ (linear_map.ker_eq_bot.mpr hS), submodule.fg.map _⟩

@[simp]
lemma coe_submodule_span (s : set R) :
  coe_submodule S (ideal.span s) = submodule.span R ((algebra_map R S) '' s) :=
by { rw [is_localization.coe_submodule, ideal.span, submodule.map_span], refl }

@[simp]
lemma coe_submodule_span_singleton (x : R) :
  coe_submodule S (ideal.span {x}) = submodule.span R {(algebra_map R S) x} :=
by rw [coe_submodule_span, set.image_singleton]

variables {g : R →+* P}
variables {T : submonoid P} (hy : M ≤ T.comap g) {Q : Type*} [comm_ring Q]
variables [algebra P Q] [is_localization T Q]
variables [is_localization M S]

section

include M

lemma is_noetherian_ring (h : is_noetherian_ring R) : is_noetherian_ring S :=
begin
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at h ⊢,
  exact order_embedding.well_founded ((is_localization.order_embedding M S).dual) h
end

end

variables {S Q M}

@[mono]
lemma coe_submodule_le_coe_submodule (h : M ≤ non_zero_divisors R)
  {I J : ideal R} :
  coe_submodule S I ≤ coe_submodule S J ↔ I ≤ J :=
submodule.map_le_map_iff_of_injective (is_localization.injective _ h) _ _

@[mono]
lemma coe_submodule_strict_mono (h : M ≤ non_zero_divisors R) :
  strict_mono (coe_submodule S : ideal R → submodule R S) :=
strict_mono_of_le_iff_le (λ _ _, (coe_submodule_le_coe_submodule h).symm)

variables (S) {Q M}

lemma coe_submodule_injective (h : M ≤ non_zero_divisors R) :
  function.injective (coe_submodule S : ideal R → submodule R S) :=
injective_of_le_imp_le _ (λ _ _, (coe_submodule_le_coe_submodule h).mp)

lemma coe_submodule_is_principal {I : ideal R} (h : M ≤ non_zero_divisors R) :
  (coe_submodule S I).is_principal ↔ I.is_principal :=
begin
  split; unfreezingI { rintros ⟨⟨x, hx⟩⟩ },
  { have x_mem : x ∈ coe_submodule S I := hx.symm ▸ submodule.mem_span_singleton_self x,
    obtain ⟨x, x_mem, rfl⟩ := (mem_coe_submodule _ _).mp x_mem,
    refine ⟨⟨x, coe_submodule_injective S h _⟩⟩,
    rw [ideal.submodule_span_eq, hx, coe_submodule_span_singleton] },
  { refine ⟨⟨algebra_map R S x, _⟩⟩,
    rw [hx, ideal.submodule_span_eq, coe_submodule_span_singleton] }
end

end is_localization

namespace is_fraction_ring

open is_localization

variables {R} {A K : Type*} [comm_ring A]

section comm_ring

variables [comm_ring K] [algebra R K] [is_fraction_ring R K] [algebra A K] [is_fraction_ring A K]

@[simp, mono]
lemma coe_submodule_le_coe_submodule
  {I J : ideal R} : coe_submodule K I ≤ coe_submodule K J ↔ I ≤ J :=
is_localization.coe_submodule_le_coe_submodule le_rfl

@[mono]
lemma coe_submodule_strict_mono :
  strict_mono (coe_submodule K : ideal R → submodule R K) :=
strict_mono_of_le_iff_le (λ _ _, coe_submodule_le_coe_submodule.symm)

variables (R K)

lemma coe_submodule_injective :
  function.injective (coe_submodule K : ideal R → submodule R K) :=
injective_of_le_imp_le _ (λ _ _, (coe_submodule_le_coe_submodule).mp)

@[simp]
lemma coe_submodule_is_principal {I : ideal R} :
  (coe_submodule K I).is_principal ↔ I.is_principal :=
is_localization.coe_submodule_is_principal _ le_rfl

end comm_ring

end is_fraction_ring
