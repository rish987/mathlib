import representation_theory.basic

--noncomputable theory

open_locale big_operators
open monoid_algebra
open finset
open finite_dimensional
open linear_map
open representation

section average
variables (k G : Type*) [comm_semiring k] [group G]
variables [fintype G] [invertible (fintype.card G : k)]

/--
The average of all elements of the group `G`, considered as an element of `monoid_algebra k G`.
-/
noncomputable def average : monoid_algebra k G :=
  ⅟(fintype.card G : k) • ∑ g : G, of k G g

lemma average_def : average k G = ⅟(fintype.card G : k) • ∑ g : G, of k G g := rfl

/--
`average k G` is invariant under left multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_left (g : G) : (of k G g) * average k G = average k G :=
begin
  simp [average_def, finset.mul_sum],
  set f : G → monoid_algebra k G := λ x, finsupp.single x 1,
  show ⅟ ↑(fintype.card G) • ∑ (x : G), f (g * x) = ⅟ ↑(fintype.card G) • ∑ (x : G), f x,
  rw function.bijective.sum_comp (group.mul_left_bijective g) _,
end

/--
`average k G` is invariant under right multiplication by elements of `G`.
-/
@[simp]
theorem mul_average_right (g : G) : average k G * (of k G g) = average k G :=
begin
  simp [average_def, finset.sum_mul],
  set f : G → monoid_algebra k G := λ x, finsupp.single x 1,
  show ⅟ ↑(fintype.card G) • ∑ (x : G), f (x * g) = ⅟ ↑(fintype.card G) • ∑ (x : G), f x,
  rw function.bijective.sum_comp (group.mul_right_bijective g) _,
end

end average

section fixed_space
variables (k G V : Type*) [comm_semiring k] [group G] [add_comm_group V]
variables [module k V] [distrib_mul_action G V] [smul_comm_class G k V]

/--
The subspace of vectors fixed by all elements of `G`
-/
def fixed_space : submodule k V :=
{ carrier := set_of (λ v, ∀ (g : G), g • v = v),
  zero_mem' := by simp,
  add_mem' := λ v w hv hw g, by simp [hv g, hw g],
  smul_mem' := λ r v hv g, by simp [smul_comm, hv g] }

@[simp]
lemma mem_fixed_space (v : V) : v ∈ (fixed_space k G V) ↔ ∀ (g: G), g • v = v := by refl

variables [fintype G] [invertible (fintype.card G : k)]

/--
Scalar multiplication by `average k G` sends elements of `V` to the subspace of fixed points
-/
theorem smul_average_fixed (v : V) : (average k G) • v ∈ fixed_space k G V :=
λ g, by rw [←smul_of k, smul_smul, mul_average_left]

/--
`average k G` acts as the identity on the subspace of fixed points
-/
theorem smul_average_id (v ∈ fixed_space k G V) : (average k G) • v = v :=
begin
  simp at H,
  simp [average_def, sum_smul, H, card_univ, nsmul_eq_smul_cast k _ v, smul_smul, -of_apply],
end

/--
Scalar multiplication by `average k G` gives a projection map onto the subspace of fixed points
-/
noncomputable def average_map : V →ₗ[k] V := (as_algebra_hom k G V) (average k G)

end fixed_space