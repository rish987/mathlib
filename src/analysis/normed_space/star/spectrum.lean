/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.star.basic
import analysis.normed_space.spectrum

/-!
In this file, we establish various propreties related to the spectrum of elements in a
C⋆-algebra over ℂ.
-/

local postfix `⋆`:std.prec.max_plus := star

variables {A : Type*}
[normed_ring A] [normed_algebra ℂ A] [star_ring A] [cstar_ring A] [complete_space A]
[measurable_space A] [borel_space A] [topological_space.second_countable_topology A]

open_locale topological_space ennreal
open filter ennreal cstar_ring spectrum

lemma spectral_radius_eq_nnnorm_of_self_adjoint {a : A} (ha : a ∈ self_adjoint A) :
  spectral_radius ℂ a = ∥a∥₊ :=
begin
  have hconst : tendsto (λ n : ℕ, (∥a∥₊ : ℝ≥0∞)) at_top _ := tendsto_const_nhds,
  refine tendsto_nhds_unique _ hconst,
  convert (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a : A)).comp
      (nat.tendsto_pow_at_top_at_top_of_one_lt (by linarith : 1 < 2)),
  refine funext (λ n, _),
  rw [function.comp_app, self_adjoint.nnnorm_pow_two_pow ha, ennreal.coe_pow, ←rpow_nat_cast,
    ←rpow_mul],
  simp,
end

lemma spectral_radius_eq_nnnorm_of_star_normal (a : A) [is_star_normal a] :
  spectral_radius ℂ a = ∥a∥₊ :=
begin
  refine (ennreal.pow_strict_mono (by linarith : 2 ≠ 0)).injective _,
  have ha : a⋆ * a ∈ self_adjoint A,
    from self_adjoint.mem_iff.mpr (by simpa only [star_star] using (star_mul a⋆ a)),
  have heq : (λ n : ℕ, ((∥(a⋆ * a) ^ n∥₊ ^ (1 / n : ℝ)) : ℝ≥0∞))
    = (λ x, x ^ 2) ∘ (λ n : ℕ, ((∥a ^ n∥₊ ^ (1 / n : ℝ)) : ℝ≥0∞)),
  { funext,
    rw [function.comp_apply, ←rpow_nat_cast, ←rpow_mul, mul_comm, rpow_mul, rpow_nat_cast,
      ←coe_pow, sq, ←nnnorm_star_mul_self, (star_comm_self a).mul_pow, star_pow], },
  have h₂ := ((ennreal.continuous_pow 2).tendsto (spectral_radius ℂ a)).comp
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius a),
  rw ←heq at h₂,
  convert tendsto_nhds_unique h₂ (pow_nnnorm_pow_one_div_tendsto_nhds_spectral_radius (a⋆ * a)),
  rw [spectral_radius_eq_nnnorm_of_self_adjoint ha, sq, nnnorm_star_mul_self, coe_mul],
end
