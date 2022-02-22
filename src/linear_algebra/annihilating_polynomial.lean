/-
Copyright (c) 2022 Justin Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Thomas
-/
import data.polynomial
import data.polynomial.ring_division
import ring_theory.principal_ideal_domain
import algebra.module.linear_map
import field_theory.minpoly
import linear_algebra
import ring_theory.ideal.operations
import ring_theory.polynomial_algebra

/-!
# Annihilating Ideal

Given a commutative ring `A` and an `A`-module `M`
(`[comm_ring A] [add_comm_group M] [module A M]`)
Every element `u : U` defines
an ideal (`alg_hom.annihilating_ideal u ⊆ A[X]`.
Simply put, this is the set of polynomials `p` where
the polynomial evaluation `p(u)` is 0.

## Special case where the ground ring is a field

In the special case that `A` is a field, we use the notation `A = 𝕜`.
Here `𝕜[X]` is a PID, so there is a polynomial `g ∈ alg_hom.annihilating_ideal u`
which generates the ideal. We show that if this generator is
chosen to be monic, then it is the minimal polynomial of `u`,
as defined in `field_theory.minpoly`.

## Special case: endomorphism algebra

* `U = M →ₗ[A] M`, the endomorphism algebra of an `A`-module M.
* `U = n × n` matrices with entries in `A`.
-/

variables {A U : Type*} [comm_semiring A] [semiring U] [algebra A U]

open_locale polynomial

open polynomial

variables (A)

/--
The informal notation `p(u)` stand for `polynomial.aeval u p`.
Again informally, the annihilating ideal of `u` is
`{ p ∈ A[x] | p(u) = 0 }`. This is an ideal in `A[X]`.
The formal definition uses the kernel of the aeval map. -/
noncomputable def annihilating_ideal (u : U) : ideal A[X] :=
ring_hom.ker (aeval u).to_ring_hom

variables {A}

/-- It is useful to refer to ideal membership sometimes
 and the annihilation condition other times -/
lemma mem_annihilating_ideal_iff_aeval_0 (u : U) (p : A[X]) :
  p ∈ annihilating_ideal A u ↔ aeval u p = 0 :=
iff.rfl

variables {𝕜 V : Type*} [field 𝕜] [ring V] [algebra 𝕜 V]
variables (𝕜)

/-- Since `𝕜[x]` is a principal ideal domain there is a polynomial `g` such that
 `span 𝕜 {g} = annihilating_ideal u` -/
noncomputable def annihilating_ideal_generator (u : V) : 𝕜[X] :=
submodule.is_principal.generator (annihilating_ideal 𝕜 u)

variables {𝕜}

section minpoly_generates

/-- We are working toward showing the generator of the annihilating ideal
in the field case is the minimal polynomial. We are going to use a uniqueness
theorem of the minimal polynomial. This is the first condition: it must annihilate
the original element `u : U`. -/
lemma annihilating_ideal_generator_aeval_0 (u : V) :
  aeval u (annihilating_ideal_generator 𝕜 u) = 0 :=
begin
  rw annihilating_ideal_generator,
  have gen_u_member := submodule.is_principal.generator_mem (annihilating_ideal 𝕜 u),
  exact (ring_hom.mem_ker (polynomial.aeval u).to_ring_hom).1 gen_u_member,
end

/-- This is a stepping stone to show the generator has minimal degree -/
lemma mem_iff_generator_dvd (u : V) (p : 𝕜[X]) :
  p ∈ annihilating_ideal 𝕜 u ↔ annihilating_ideal_generator 𝕜 u ∣ p :=
submodule.is_principal.mem_iff_generator_dvd (annihilating_ideal 𝕜 u)

/-- The generator of the annihilating ideal has minimal degree among
 the non-zero members of the annihilating ideal -/
lemma degree_annihilating_ideal_generator_le_of_mem (u : V) (p : 𝕜[X])
  (hp : p ∈ annihilating_ideal 𝕜 u) (hpn0 : p ≠ 0) :
  degree (annihilating_ideal_generator 𝕜 u) ≤ degree p :=
degree_le_of_dvd hpn0 ((mem_iff_generator_dvd u p).1 hp)

/-- This is what we have been building to:
The monic generator of the annihilating ideal is the minimal polynomial. -/
lemma minpoly_eq_monic_annihilating_ideal_generator (u : V)
  (h : (annihilating_ideal_generator 𝕜 u).monic) :
  annihilating_ideal_generator 𝕜 u = minpoly 𝕜 u :=
begin
  /- 3 conditions for a poly being the minpoly -/
  apply minpoly.unique,
  /- 1st condition: the poly is monic -/
  { apply h, },
  /- 2nd condition: the poly annihilates u -/
  { apply annihilating_ideal_generator_aeval_0, },
  /- 3rd condition: the poly has minimal degree among annihilators of u -/
  { intros q hqm heval,
    apply degree_annihilating_ideal_generator_le_of_mem u q _ _,
    exact (mem_annihilating_ideal_iff_aeval_0 u q).2 heval,
    exact monic.ne_zero hqm, }
end

end minpoly_generates

/- Other simple facts about the annihilating ideal -/

/-- If the annihilating ideal is generated by zero, then every member is 0 -/
lemma eq_zero_of_mem_eq_zero (u : V) (p : 𝕜[X])
  (hp : p ∈ annihilating_ideal 𝕜 u) (hu0 : annihilating_ideal_generator 𝕜 u = 0) :
  p = 0 :=
begin
  rwa [mem_iff_generator_dvd, hu0, zero_dvd_iff] at hp,
end
