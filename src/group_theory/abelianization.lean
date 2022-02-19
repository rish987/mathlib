/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes
-/
import group_theory.general_commutator
import group_theory.quotient_group

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `algebra/category/Group/adjunctions`.

## Main definitions

* `commutator`: defines the commutator of a group `G` as a subgroup of `G`.
* `abelianization`: defines the abelianization of a group `G` as the quotient of a group by its
  commutator subgroup.
* `abelianization.map`: lifts a group homomorphism to a homomorphism between the abelianizations
* `mul_equiv.abelianization_congr`: Equivalent groups have equivalent abelianizations

-/

universes u v w

-- Let G be a group.
variables (G : Type u) [group G]

/-- The commutator subgroup of a group G is the normal subgroup
  generated by the commutators [p,q]=`p*q*p⁻¹*q⁻¹`. -/
@[derive subgroup.normal]
def commutator : subgroup G :=
⁅(⊤ : subgroup G), ⊤⁆

lemma commutator_def : commutator G = ⁅(⊤ : subgroup G), ⊤⁆ := rfl

lemma commutator_eq_closure : commutator G = subgroup.closure {g | ∃ g₁ g₂ : G, ⁅g₁, g₂⁆ = g} :=
by simp_rw [commutator, subgroup.commutator_def, subgroup.mem_top, exists_true_left]

lemma commutator_eq_normal_closure :
  commutator G = subgroup.normal_closure {g | ∃ g₁ g₂ : G, ⁅g₁, g₂⁆ = g} :=
by simp_rw [commutator, subgroup.commutator_def', subgroup.mem_top, exists_true_left]

/-- The abelianization of G is the quotient of G by its commutator subgroup. -/
def abelianization : Type u :=
G ⧸ (commutator G)

namespace abelianization

local attribute [instance] quotient_group.left_rel

instance : comm_group (abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂' x y $ λ a b, quotient.sound' $
    subgroup.subset_closure ⟨b⁻¹, subgroup.mem_top b⁻¹, a⁻¹, subgroup.mem_top a⁻¹, by group⟩,
.. quotient_group.quotient.group _ }

instance : inhabited (abelianization G) := ⟨1⟩

instance [fintype G] [decidable_pred (∈ commutator G)] :
  fintype (abelianization G) :=
quotient_group.fintype (commutator G)

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
def of : G →* abelianization G :=
{ to_fun := quotient_group.mk,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

@[simp] lemma mk_eq_of (a : G) : quot.mk _ a = of a := rfl

section lift
-- So far we have built Gᵃᵇ and proved it's an abelian group.
-- Furthremore we defined the canonical projection `of : G → Gᵃᵇ`

-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
variables {A : Type v} [comm_group A] (f : G →* A)

lemma commutator_subset_ker : commutator G ≤ f.ker :=
begin
  rw [commutator_eq_closure, subgroup.closure_le],
  rintros x ⟨p, q, rfl⟩,
  simp [monoid_hom.mem_ker, mul_right_comm (f p) (f q)],
end

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map from
  the abelianization of a `G` to `A` that factors through `f`. -/
def lift : (G →* A) ≃ (abelianization G →* A) :=
{ to_fun := λ f, quotient_group.lift _ f (λ x h, f.mem_ker.2 $ commutator_subset_ker _ h),
  inv_fun := λ F, F.comp of,
  left_inv := λ f, monoid_hom.ext $ λ x, rfl,
  right_inv := λ F, monoid_hom.ext $ λ x, quotient_group.induction_on x $ λ z, rfl }

@[simp] lemma lift.of (x : G) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (φ : abelianization G →* A)
  -- hφ : φ agrees with f on the image of G in Gᵃᵇ
  (hφ : ∀ (x : G), φ (of x) = f x)
  {x : abelianization G} :
  φ x = lift f x :=
quotient_group.induction_on x hφ

@[simp] lemma lift_of : lift of = monoid_hom.id (abelianization G) :=
lift.apply_symm_apply $ monoid_hom.id _

end lift

variables {A : Type v} [monoid A]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext (φ ψ : abelianization G →* A)
  (h : φ.comp of = ψ.comp of) : φ = ψ :=
monoid_hom.ext $ λ x, quotient_group.induction_on x $ monoid_hom.congr_fun h

section map

variables {H : Type v} [group H] (f : G →* H)

/-- The map operation of the `abelianization` functor -/
def map : abelianization G →* abelianization H := lift (of.comp f)

@[simp]
lemma map_of (x : G) : map f (of x) = of (f x) := rfl

@[simp]
lemma map_id : map (monoid_hom.id G) = monoid_hom.id (abelianization G) := hom_ext _ _ rfl

@[simp]
lemma map_comp {I : Type w} [group I] (g : H →* I) :
  (map g).comp (map f) = map (g.comp f) := hom_ext _ _ rfl

@[simp]
lemma map_map_apply {I : Type w} [group I] {g : H →* I} {x : abelianization G}:
  map g (map f x) = map (g.comp f) x := monoid_hom.congr_fun (map_comp _ _) x

end map

end abelianization

section abelianization_congr

variables {G} {H : Type v} [group H] (e : G ≃* H)

/-- Equivalent groups have equivalent abelianizations -/
def mul_equiv.abelianization_congr : abelianization G ≃* abelianization H :=
{ to_fun := abelianization.map e.to_monoid_hom,
  inv_fun := abelianization.map e.symm.to_monoid_hom,
  left_inv := by { rintros ⟨a⟩, simp },
  right_inv := by { rintros ⟨a⟩, simp },
  map_mul' := monoid_hom.map_mul _ }

@[simp]
lemma abelianization_congr_of (x : G) :
  (e.abelianization_congr) (abelianization.of x) = abelianization.of (e x) := rfl

@[simp]
lemma abelianization_congr_refl :
  (mul_equiv.refl G).abelianization_congr = mul_equiv.refl (abelianization G) :=
mul_equiv.to_monoid_hom_injective abelianization.lift_of

@[simp]
lemma abelianization_congr_symm  :
  e.abelianization_congr.symm = e.symm.abelianization_congr := rfl

@[simp]
lemma abelianization_congr_trans {I : Type v} [group I] (e₂ : H ≃* I) :
  e.abelianization_congr.trans e₂.abelianization_congr = (e.trans e₂).abelianization_congr :=
mul_equiv.to_monoid_hom_injective (abelianization.hom_ext _ _ rfl)

end abelianization_congr

/-- An Abelian group is equivalent to its own abelianization. -/
@[simps] def abelianization.equiv_of_comm {H : Type*} [comm_group H] :
  H ≃* abelianization H :=
{ to_fun    := abelianization.of,
  inv_fun   := abelianization.lift (monoid_hom.id H),
  left_inv  := λ a, rfl,
  right_inv := by { rintros ⟨a⟩, refl, },
  .. abelianization.of }
