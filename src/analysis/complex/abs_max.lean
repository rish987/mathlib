/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.complex.cauchy_integral
import analysis.convex.integral

/-!
# Maximum modulus principle

In this file we prove several versions of the maximum modulus principle and Liouville's Theorem.

There are several statements that can be called "the maximum modulus principle" for maps between
normed complex spaces.

In the most general case, see `complex.norm_eventually_eq_of_is_local_max`, we can only say that for
a differentiable function `f : E → F`, if the norm has a local maximum at `z`, then *the norm* is
constant in a neighborhood of `z`.

If the domain is a nontrivial finite dimensional space, then this implies the following version of
the maximum modulus principle, see `complex.exists_mem_frontier_is_max_on_norm`. If `f : E → F` is
complex differentiable on a nonempty compact set `K`, then there exists a point `z ∈ frontier K`
such that `λ z, ∥f z∥` takes it maximum value on `K` at `z`.

Finally, if the codomain is a strictly convex space, then the function cannot have a local maximum
of the norm unless the function (not only its norm) is a constant. This version is not formalized
yet.

## TODO

All theorems in this file assume that the codomain is a complete space with second countable
topology. Both assumption can and should be removed, either during the planned refactor of the
Bochner integral, or by applying current version to the completion of the span of the range of `f`.
-/

open topological_space metric set filter asymptotics function measure_theory
open_locale topological_space filter nnreal real

universes u v w
variables {E : Type u} [normed_group E] [normed_space ℂ E]
  {F : Type v} [normed_group F] [normed_space ℂ F] [measurable_space F] [borel_space F]
    [second_countable_topology F] [complete_space F]

namespace complex

/-- Auxiliary lemma, use `complex.norm_eq_norm_of_is_max_on_of_closed_ball_subset` instead. -/
lemma norm_eq_norm_of_is_max_on_of_closed_ball_subset_dim1
  {f : ℂ → F} {s : set ℂ} {z w : ℂ} (hd : differentiable_on ℂ f s) (hz : is_max_on (norm ∘ f) s z)
  (hsub : closed_ball z (dist w z) ⊆ s) :
  ∥f w∥ = ∥f z∥ :=
begin
  set r := dist w z,
  have hw_mem : w ∈ closed_ball z r, from mem_closed_ball.2 le_rfl,
  refine (is_max_on_iff.1 hz _ (hsub hw_mem)).antisymm (not_lt.1 _),
  rintro hw_lt : ∥f w∥ < ∥f z∥,
  have hr : 0 < r, from dist_pos.2 (λ h, hw_lt.ne $ h ▸ rfl),
  have hsub' : sphere z r ⊆ s, from sphere_subset_closed_ball.trans hsub,
  have hne : ∀ ζ ∈ sphere z r, ζ ≠ z,
    from λ ζ hζ, ne_of_mem_of_not_mem hζ (ne_of_lt $ (dist_self z).symm ▸ hr),
  have hcont : continuous_on (λ ζ, (ζ - z)⁻¹ • f ζ) (sphere z r),
    from ((continuous_on_id.sub continuous_on_const).inv₀ $
      λ ζ hζ, sub_ne_zero.2 (hne ζ hζ)).smul (hd.continuous_on.mono hsub'),
  have hle : ∀ ζ ∈ sphere z r, ∥(ζ - z)⁻¹ • f ζ∥ ≤ ∥f z∥ / r,
  { rintros ζ (hζ : abs (ζ - z) = r),
    simpa [norm_smul, hζ, ← div_eq_inv_mul] using (div_le_div_right hr).2 (hz (hsub' hζ)) },
  have hlt : ∥(w - z)⁻¹ • f w∥ < ∥f z∥ / r,
    by simpa [norm_smul, ← div_eq_inv_mul] using (div_lt_div_right hr).2 hw_lt,
  have : ∥∮ ζ in C(z, r), (ζ - z)⁻¹ • f ζ∥ < 2 * π * r * (∥f z∥ / r),
    from circle_integral.norm_integral_lt_of_norm_le_const_of_lt hr hcont hle ⟨w, rfl, hlt⟩,
  refine this.ne _,
  rw circle_integral_sub_inv_smul_of_differentiable_on (mem_ball_self hr) (hd.mono hsub),
  field_simp [norm_smul, hr.ne', abs_of_pos real.pi_pos],
  ac_refl
end

/-- If `f : E → F` is complex differentiable on a set `s`, the norm of `f` takes it maximum on `s`
at `z` and `w` is a point such that the closed ball with center `z` and radius `dist w z` is
included in `s`, then `∥f w∥ = ∥f z∥`. -/
lemma norm_eq_norm_of_is_max_on_of_closed_ball_subset {f : E → F} {s : set E} {z w : E}
  (hd : differentiable_on ℂ f s) (hz : is_max_on (norm ∘ f) s z)
  (hsub : closed_ball z (dist w z) ⊆ s) :
  ∥f w∥ = ∥f z∥ :=
begin
  set e : ℂ → E := λ t : ℂ, t • (w - z) + z,
  suffices : ∥(f ∘ e) 1∥ = ∥(f ∘ e) 0∥, by simpa [e],
  have : differentiable_on ℂ (f ∘ e) ((λ t : ℂ, t • (w - z) + z) ⁻¹' s),
    from hd.comp ((differentiable_on_id.smul_const (w - z)).add_const z) subset.rfl,
  refine norm_eq_norm_of_is_max_on_of_closed_ball_subset_dim1
    this _ _,
  { refine λ t ht, _, simpa [e] using hz ht },
  { refine λ t ht, hsub _,
    have : abs t ≤ 1, by simpa using ht,
    simpa [dist_eq_norm, norm_smul] using mul_le_of_le_one_left (norm_nonneg (w - z)) this }
end

lemma norm_eventually_eq_of_is_local_max {f : E → F} {c : E}
  (hd : ∀ᶠ z in 𝓝 c, differentiable_at ℂ f z) (hc : is_local_max (norm ∘ f) c) :
  ∀ᶠ y in 𝓝 c, ∥f y∥ = ∥f c∥ :=
begin
  rcases nhds_basis_closed_ball.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩,
  exact nhds_basis_closed_ball.eventually_iff.2 ⟨r, hr₀, λ w hw,
    norm_eq_norm_of_is_max_on_of_closed_ball_subset
      (λ z hz, (hr hz).1.differentiable_within_at) (λ z hz, (hr hz).2)
      (closed_ball_subset_closed_ball hw)⟩
end

lemma is_open_set_of_mem_nhds_and_is_max_on_norm {f : E → F} {s : set E}
  (hd : differentiable_on ℂ f s) :
  is_open {z | s ∈ 𝓝 z ∧ is_max_on (norm ∘ f) s z} :=
begin
  refine is_open_iff_mem_nhds.2 (λ z hz, (eventually_eventually_nhds.2 hz.1).and _),
  replace hd : ∀ᶠ w in 𝓝 z, differentiable_at ℂ f w, from hd.eventually_differentiable_at hz.1,
  exact (norm_eventually_eq_of_is_local_max hd $ (hz.2.is_local_max hz.1)).mono
    (λ x hx y hy, le_trans (hz.2 hy) hx.ge)
end

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a nonempty compact
set `K`, then there exists a point `z ∈ frontier K` such that `λ z, ∥f z∥` takes it maximum value on
`K` at `z`. -/
lemma exists_mem_frontier_is_max_on_norm [nontrivial E] {f : E → F} {K : set E} (hK : is_compact K)
  (hne : K.nonempty) (hd : differentiable_on ℂ f K) :
  ∃ z ∈ frontier K, is_max_on (norm ∘ f) K z :=
begin
  rcases hK.exists_forall_ge hne hd.continuous_on.norm with ⟨w, hwK, hle⟩,
  rcases hK.exists_mem_frontier_inf_dist_compl_eq_dist hwK with ⟨z, hzK, hzw⟩,
  refine ⟨z, hzK, λ x hx, (hle x hx).trans_eq _⟩,
  refine (norm_eq_norm_of_is_max_on_of_closed_ball_subset hd hle _).symm,
  calc closed_ball w (dist z w) = closed_ball w (inf_dist w Kᶜ) : by rw [hzw, dist_comm]
  ... ⊆ closure K : closed_ball_inf_dist_compl_subset_closure hwK hK.ne_univ
  ... = K : hK.is_closed.closure_eq
end

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a compact set `K` and
`∥f z∥ ≤ C` for any `z ∈ frontier K`, then the same is true for any `z ∈ K`. -/
lemma norm_le_of_forall_mem_frontier_norm_le [nontrivial E] {f : E → F} {K : set E}
  (hK : is_compact K) (hd : differentiable_on ℂ f K)
  {C : ℝ} (hC : ∀ z ∈ frontier K, ∥f z∥ ≤ C) {z : E} (hz : z ∈ K) :
  ∥f z∥ ≤ C :=
let ⟨w, hwK, hw⟩ := exists_mem_frontier_is_max_on_norm hK ⟨z, hz⟩ hd in le_trans (hw hz) (hC w hwK)

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a compact
set `K`, then they are equal on `K`. -/
lemma eq_on_of_eq_on_frontier [nontrivial E] {f g : E → F} {K : set E} (hK : is_compact K)
  (hf : differentiable_on ℂ f K) (hg : differentiable_on ℂ g K) (hfg : eq_on f g (frontier K)) :
  eq_on f g K :=
begin
  suffices H : ∀ z ∈ K, ∥f z - g z∥ ≤ 0, by simpa [sub_eq_zero] using H,
  convert λ z hz, norm_le_of_forall_mem_frontier_norm_le hK (hf.sub hg) _ hz,
  simpa [sub_eq_zero]
end

end complex
