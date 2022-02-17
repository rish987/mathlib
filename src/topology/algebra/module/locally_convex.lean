/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.convex.topology
/-!
# Locally convex topological modules

A `locally_convex_space` is a topological semimodule over an ordered semiring in which any point
admits a neighborhood basis made of convex sets, or equivalently, in which convex neighborhoods of
a point form a neighborhood basis at that point.

In a module, this is equivalent to `0` satisfying such properties.

## Main results

- `locally_convex_space_iff_zero` : in a module, local convexity at zero gives
  local convexity everywhere
- `seminorm.locally_convex_space` : a topology generated by a family of seminorms is locally convex
- `normed_space.locally_convex_space` : a normed space is locally convex

## TODO

- define a structure `locally_convex_filter_basis`, extending `module_filter_basis`, for filter
  bases generating a locally convex topology
- show that any locally convex topology is generated by a family of seminorms

-/

open topological_space filter

open_locale topological_space

section semimodule

/-- A `locally_convex_space` is a topological semimodule over an ordered semiring in which convex
neighborhoods of a point form a neighborhood basis at that point. -/
class locally_convex_space (𝕜 E : Type*) [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E]
  [topological_space E] : Prop :=
(convex_basis : ∀ x : E, (𝓝 x).has_basis (λ (s : set E), s ∈ 𝓝 x ∧ convex 𝕜 s) id)

variables (𝕜 E : Type*) [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] [topological_space E]

lemma locally_convex_space_iff :
  locally_convex_space 𝕜 E ↔
  ∀ x : E, (𝓝 x).has_basis (λ (s : set E), s ∈ 𝓝 x ∧ convex 𝕜 s) id :=
⟨@locally_convex_space.convex_basis _ _ _ _ _ _, locally_convex_space.mk⟩

⟨λ x, (hbasis x).to_has_basis
  (λ s hs, ⟨(hbasis x).index s hs.1,
    ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩)⟩

lemma locally_convex_space.convex_basis_zero [locally_convex_space 𝕜 E] :
  (𝓝 0 : filter E).has_basis (λ s, s ∈ (𝓝 0 : filter E) ∧ convex 𝕜 s) id :=
locally_convex_space.convex_basis 0

lemma locally_convex_space_iff_exists_convex_subset :
  locally_convex_space 𝕜 E ↔ ∀ x : E, ∀ U ∈ 𝓝 x, ∃ S ∈ 𝓝 x, convex 𝕜 S ∧ S ⊆ U :=
(locally_convex_space_iff 𝕜 E).trans (forall_congr $ λ x, has_basis_self)

end semimodule

section module

variables (𝕜 E : Type*) [ordered_semiring 𝕜] [add_comm_group E] [module 𝕜 E] [topological_space E]
  [topological_add_group E]

lemma locally_convex_space.of_basis_zero {ι : Type*} (b : ι → set E) (p : ι → Prop)
  (hbasis : (𝓝 0).has_basis p b) (hconvex : ∀ i, p i → convex 𝕜 (b i)) :
  locally_convex_space 𝕜 E :=
begin
  refine locally_convex_space.of_bases 𝕜 E (λ (x : E) (i : ι), ((+) x) '' b i) p (λ x, _)
    (λ x i hi, (hconvex i hi).translate x),
  rw ← map_add_left_nhds_zero,
  exact hbasis.map _
end

lemma locally_convex_space_iff_zero :
  locally_convex_space 𝕜 E ↔
  (𝓝 0 : filter E).has_basis (λ (s : set E), s ∈ (𝓝 0 : filter E) ∧ convex 𝕜 s) id :=
⟨λ h, @locally_convex_space.convex_basis _ _ _ _ _ _ h 0,
 λ h, locally_convex_space.of_basis_zero 𝕜 E _ _ h (λ s, and.right)⟩

lemma locally_convex_space_iff_exists_convex_subset_zero :
  locally_convex_space 𝕜 E ↔
  ∀ U ∈ (𝓝 0 : filter E), ∃ S ∈ (𝓝 0 : filter E), convex 𝕜 S ∧ S ⊆ U :=
(locally_convex_space_iff_zero 𝕜 E).trans has_basis_self

end module
