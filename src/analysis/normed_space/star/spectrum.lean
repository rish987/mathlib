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

variables {A : Type*}
[normed_ring A] [normed_algebra ℂ A] [star_ring A] [cstar_ring A] [complete_space A]
[measurable_space A] [borel_space A] [topological_space.second_countable_topology A]

open_locale topological_space ennreal
open filter ennreal

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

lemma foo₀ (a : A) [is_star_normal a] (n : ℕ) : commute ((star a) ^ n) a :=
nat.rec_on n (by simp only [pow_zero, commute.one_left])
  (λ k hk, calc (star a) ^ (k + 1) * a = a * (star a) ^ (k + 1)
    : by rw [pow_succ, mul_assoc, hk.eq, ←mul_assoc, star_comm_self', mul_assoc, ←pow_succ])

lemma foo₁ (a : A) [is_star_normal a] (n m : ℕ) : commute ((star a) ^ n) (a ^ m) :=
nat.rec_on m (by simp only [pow_zero, commute.one_right])
  (λ k hk, calc ((star a) ^ n) * (a ^ (k + 1)) = (a ^ (k + 1)) * ((star a) ^ n)
    : by rw [pow_succ, ←mul_assoc, (foo₀ a n).eq, mul_assoc, hk.eq, ←mul_assoc])

lemma foo₂ (a : A) [is_star_normal a] (n : ℕ) : (star a * a) ^ n = (star a) ^ n * a ^ n :=
nat.rec_on n (by simp only [pow_zero, mul_one]) (λ n hn, by rw [pow_succ, hk, ←mul_assoc,
  mul_assoc _ a _, (foo₀ a k).eq.symm, ←mul_assoc, ←pow_succ, mul_assoc, ←pow_succ])
