/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ines Wright
-/

import group_theory.general_commutator
import group_theory.quotient_group
import group_theory.solvable
import group_theory.sylow

/-!

# Nilpotent groups

An API for nilpotent groups, that is, groups for which the upper central series
reaches `⊤`.

## Main definitions

Recall that if `H K : subgroup G` then `⁅H, K⁆ : subgroup G` is the subgroup of `G` generated
by the commutators `hkh⁻¹k⁻¹`. Recall also Lean's conventions that `⊤` denotes the
subgroup `G` of `G`, and `⊥` denotes the trivial subgroup `{1}`.

* `upper_central_series G : ℕ → subgroup G` : the upper central series of a group `G`.
     This is an increasing sequence of normal subgroups `H n` of `G` with `H 0 = ⊥` and
     `H (n + 1) / H n` is the centre of `G / H n`.
* `lower_central_series G : ℕ → subgroup G` : the lower central series of a group `G`.
     This is a decreasing sequence of normal subgroups `H n` of `G` with `H 0 = ⊤` and
     `H (n + 1) = ⁅H n, G⁆`.
* `is_nilpotent` : A group G is nilpotent if its upper central series reaches `⊤`, or
    equivalently if its lower central series reaches `⊥`.
* `nilpotency_class` : the length of the upper central series of a nilpotent group.
* `is_ascending_central_series (H : ℕ → subgroup G) : Prop` and
* `is_descending_central_series (H : ℕ → subgroup G) : Prop` : Note that in the literature
    a "central series" for a group is usually defined to be a *finite* sequence of normal subgroups
    `H 0`, `H 1`, ..., starting at `⊤`, finishing at `⊥`, and with each `H n / H (n + 1)`
    central in `G / H (n + 1)`. In this formalisation it is convenient to have two weaker predicates
    on an infinite sequence of subgroups `H n` of `G`: we say a sequence is a *descending central
    series* if it starts at `G` and `⁅H n, ⊤⁆ ⊆ H (n + 1)` for all `n`. Note that this series
    may not terminate at `⊥`, and the `H i` need not be normal. Similarly a sequence is an
    *ascending central series* if `H 0 = ⊥` and `⁅H (n + 1), ⊤⁆ ⊆ H n` for all `n`, again with no
    requirement that the series reaches `⊤` or that the `H i` are normal.

## Main theorems

`G` is *defined* to be nilpotent if the upper central series reaches `⊤`.
* `nilpotent_iff_finite_ascending_central_series` : `G` is nilpotent iff some ascending central
    series reaches `⊤`.
* `nilpotent_iff_finite_descending_central_series` : `G` is nilpotent iff some descending central
    series reaches `⊥`.
* `nilpotent_iff_lower` : `G` is nilpotent iff the lower central series reaches `⊥`.
* The `nilpotency_class` can likeways be obtained from these equivalent
  definitions, see `least_ascending_central_series_length_eq_nilpotency_class`,
  `least_descending_central_series_length_eq_nilpotency_class` and
  `lower_central_series_length_eq_nilpotency_class`.
* `is_nilpotent.to_is_solvable`: If `G` is nilpotent, it is solvable.


## Warning

A "central series" is usually defined to be a finite sequence of normal subgroups going
from `⊥` to `⊤` with the property that each subquotient is contained within the centre of
the associated quotient of `G`. This means that if `G` is not nilpotent, then
none of what we have called `upper_central_series G`, `lower_central_series G` or
the sequences satisfying `is_ascending_central_series` or `is_descending_central_series`
are actually central series. Note that the fact that the upper and lower central series
are not central series if `G` is not nilpotent is a standard abuse of notation.

-/

open subgroup

variables {G : Type*} [group G] (H : subgroup G) [normal H]

/-- If `H` is a normal subgroup of `G`, then the set `{x : G | ∀ y : G, x*y*x⁻¹*y⁻¹ ∈ H}`
is a subgroup of `G` (because it is the preimage in `G` of the centre of the
quotient group `G/H`.)
-/
def upper_central_series_step : subgroup G :=
{ carrier := {x : G | ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ H},
  one_mem' := λ y, by simp [subgroup.one_mem],
  mul_mem' := λ a b ha hb y, begin
    convert subgroup.mul_mem _ (ha (b * y * b⁻¹)) (hb y) using 1,
    group,
  end,
  inv_mem' := λ x hx y, begin
    specialize hx y⁻¹,
    rw [mul_assoc, inv_inv] at ⊢ hx,
    exact subgroup.normal.mem_comm infer_instance hx,
  end }

lemma mem_upper_central_series_step (x : G) :
  x ∈ upper_central_series_step H ↔ ∀ y, x * y * x⁻¹ * y⁻¹ ∈ H := iff.rfl

open quotient_group

/-- The proof that `upper_central_series_step H` is the preimage of the centre of `G/H` under
the canonical surjection. -/
lemma upper_central_series_step_eq_comap_center :
  upper_central_series_step H = subgroup.comap (mk' H) (center (G ⧸ H)) :=
begin
  ext,
  rw [mem_comap, mem_center_iff, forall_coe],
  apply forall_congr,
  intro y,
  change x * y * x⁻¹ * y⁻¹ ∈ H ↔ ((y * x : G) : G ⧸ H) = (x * y : G),
  rw [eq_comm, eq_iff_div_mem, div_eq_mul_inv],
  congr' 2,
  group,
end

instance : normal (upper_central_series_step H) :=
begin
  rw upper_central_series_step_eq_comap_center,
  apply_instance,
end

variable (G)

/-- An auxiliary type-theoretic definition defining both the upper central series of
a group, and a proof that it is normal, all in one go. -/
def upper_central_series_aux : ℕ → Σ' (H : subgroup G), normal H
| 0 := ⟨⊥, infer_instance⟩
| (n + 1) := let un := upper_central_series_aux n, un_normal := un.2 in
   by exactI ⟨upper_central_series_step un.1, infer_instance⟩

/-- `upper_central_series G n` is the `n`th term in the upper central series of `G`. -/
def upper_central_series (n : ℕ) : subgroup G := (upper_central_series_aux G n).1

instance (n : ℕ) : normal (upper_central_series G n) := (upper_central_series_aux G n).2

@[simp] lemma upper_central_series_zero : upper_central_series G 0 = ⊥ := rfl

@[simp] lemma upper_central_series_one : upper_central_series G 1 = center G :=
begin
  ext,
  simp [upper_central_series, upper_central_series_aux, upper_central_series_step,
    center, set.center],
  apply forall_congr,
  intro y,
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, eq_comm ],
end

/-- The `n+1`st term of the upper central series `H i` has underlying set equal to the `x` such
that `⁅x,G⁆ ⊆ H n`-/
lemma mem_upper_central_series_succ_iff (n : ℕ) (x : G) :
  x ∈ upper_central_series G (n + 1) ↔
  ∀ y : G, x * y * x⁻¹ * y⁻¹ ∈ upper_central_series G n := iff.rfl

-- is_nilpotent is already defined in the root namespace (for elements of rings).
/-- A group `G` is nilpotent if its upper central series is eventually `G`. -/
class group.is_nilpotent (G : Type*) [group G] : Prop :=
(nilpotent [] : ∃ n : ℕ, upper_central_series G n = ⊤)

open group

variable {G}

/-- A sequence of subgroups of `G` is an ascending central series if `H 0` is trivial and
  `⁅H (n + 1), G⁆ ⊆ H n` for all `n`. Note that we do not require that `H n = G` for some `n`. -/
def is_ascending_central_series (H : ℕ → subgroup G) : Prop :=
  H 0 = ⊥ ∧ ∀ (x : G) (n : ℕ), x ∈ H (n + 1) → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H n

/-- A sequence of subgroups of `G` is a descending central series if `H 0` is `G` and
  `⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. Note that we do not requre that `H n = {1}` for some `n`. -/
def is_descending_central_series (H : ℕ → subgroup G) := H 0 = ⊤ ∧
  ∀ (x : G) (n : ℕ), x ∈ H n → ∀ g, x * g * x⁻¹ * g⁻¹ ∈ H (n + 1)

/-- Any ascending central series for a group is bounded above by the upper central series. -/
lemma ascending_central_series_le_upper (H : ℕ → subgroup G) (hH : is_ascending_central_series H) :
  ∀ n : ℕ, H n ≤ upper_central_series G n
| 0 := hH.1.symm ▸ le_refl ⊥
| (n + 1) := begin
  specialize ascending_central_series_le_upper n,
  intros x hx,
  have := hH.2 x n hx,
  rw mem_upper_central_series_succ_iff,
  intro y,
  apply ascending_central_series_le_upper,
  apply this,
end

variable (G)

/-- The upper central series of a group is an ascending central series. -/
lemma upper_central_series_is_ascending_central_series :
  is_ascending_central_series (upper_central_series G) :=
⟨rfl, λ x n h, h⟩

lemma upper_central_series_mono : monotone (upper_central_series G) :=
begin
  refine monotone_nat_of_le_succ _,
  intros n x hx y,
  rw [mul_assoc, mul_assoc, ← mul_assoc y x⁻¹ y⁻¹],
  exact mul_mem (upper_central_series G n) hx
    (normal.conj_mem (upper_central_series.subgroup.normal G n) x⁻¹ (inv_mem _ hx) y),
end

/-- A group `G` is nilpotent iff there exists an ascending central series which reaches `G` in
  finitely many steps. -/
theorem nilpotent_iff_finite_ascending_central_series :
  is_nilpotent G ↔ ∃ n : ℕ, ∃ H : ℕ → subgroup G, is_ascending_central_series H ∧ H n = ⊤ :=
begin
  split,
  { rintro ⟨n, nH⟩,
    refine ⟨_, _, upper_central_series_is_ascending_central_series G, nH⟩ },
  { rintro ⟨n, H, hH, hn⟩,
    use n,
    have := ascending_central_series_le_upper H hH n,
    rw hn at this,
    exact eq_top_iff.mpr this }
end

lemma is_decending_rev_series_of_is_ascending
  {H: ℕ → subgroup G} {n : ℕ} (hn : H n = ⊤) (hasc : is_ascending_central_series H) :
  is_descending_central_series (λ (m : ℕ), H (n - m)) :=
begin
  cases hasc with h0 hH,
  refine ⟨hn, λ x m hx g, _⟩,
  dsimp at hx,
  by_cases hm : n ≤ m,
  { have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm,
    rw [hnm, h0, subgroup.mem_bot] at hx,
    subst hx,
    convert subgroup.one_mem _,
    group },
  { push_neg at hm,
    apply hH,
    convert hx,
    rw nat.sub_succ,
    exact nat.succ_pred_eq_of_pos (tsub_pos_of_lt hm) },
end

lemma is_ascending_rev_series_of_is_descending
  {H: ℕ → subgroup G} {n : ℕ} (hn : H n = ⊥) (hdesc : is_descending_central_series H) :
  is_ascending_central_series (λ (m : ℕ), H (n - m)) :=
begin
  cases hdesc with h0 hH,
  refine ⟨hn, λ x m hx g, _⟩,
  dsimp only at hx,
  by_cases hm : n ≤ m,
  { have hnm : n - m = 0 := tsub_eq_zero_iff_le.mpr hm,
    dsimp only,
    rw [hnm, h0],
    exact mem_top _ },
  { push_neg at hm,
    dsimp only,
    convert hH x _ hx g,
    rw nat.sub_succ,
    exact (nat.succ_pred_eq_of_pos (tsub_pos_of_lt hm)).symm }
end

/-- A group `G` is nilpotent iff there exists a descending central series which reaches the
  trivial group in a finite time. -/
theorem nilpotent_iff_finite_descending_central_series :
  is_nilpotent G ↔ ∃ n : ℕ, ∃ H : ℕ → subgroup G, is_descending_central_series H ∧ H n = ⊥ :=
begin
  rw nilpotent_iff_finite_ascending_central_series,
  split,
  { rintro ⟨n, H, hH, hn⟩,
    use n, use (λ m, H (n - m)),
    split,
    { apply (is_decending_rev_series_of_is_ascending G hn hH) },
    { simp, exact hH.1 } },
  { rintro ⟨n, H, hH, hn⟩,
    use n, use (λ m, H (n - m)),
    split,
    { apply (is_ascending_rev_series_of_is_descending G hn hH) },
    { simp, exact hH.1 } },
end

/-- The lower central series of a group `G` is a sequence `H n` of subgroups of `G`, defined
  by `H 0` is all of `G` and for `n≥1`, `H (n + 1) = ⁅H n, G⁆` -/
def lower_central_series (G : Type*) [group G] : ℕ → subgroup G
| 0 := ⊤
| (n+1) := ⁅lower_central_series n, ⊤⁆

variable {G}

@[simp] lemma lower_central_series_zero : lower_central_series G 0 = ⊤ := rfl

@[simp] lemma lower_central_series_one : lower_central_series G 1 = commutator G :=
  by simp [lower_central_series]

lemma mem_lower_central_series_succ_iff (n : ℕ) (q : G) :
  q ∈ lower_central_series G (n + 1) ↔
  q ∈ closure {x | ∃ (p ∈ lower_central_series G n) (q ∈ (⊤ : subgroup G)), p * q * p⁻¹ * q⁻¹ = x}
:= iff.rfl

lemma lower_central_series_succ (n : ℕ) :
  lower_central_series G (n + 1) =
  closure {x | ∃ (p ∈ lower_central_series G n) (q ∈ (⊤ : subgroup G)), p * q * p⁻¹ * q⁻¹ = x} :=
rfl

instance (n : ℕ) : normal (lower_central_series G n) :=
begin
  induction n with d hd,
  { exact (⊤ : subgroup G).normal_of_characteristic },
  { exactI general_commutator_normal (lower_central_series G d) ⊤ },
end

lemma lower_central_series_antitone :
  antitone (lower_central_series G) :=
begin
  refine antitone_nat_of_succ_le (λ n x hx, _),
  simp only [mem_lower_central_series_succ_iff, exists_prop, mem_top, exists_true_left, true_and]
    at hx,
  refine closure_induction hx _ (subgroup.one_mem _) (@subgroup.mul_mem _ _ _)
    (@subgroup.inv_mem _ _ _),
  rintros y ⟨z, hz, a, ha⟩,
  rw [← ha, mul_assoc, mul_assoc, ← mul_assoc a z⁻¹ a⁻¹],
  exact mul_mem (lower_central_series G n) hz
    (normal.conj_mem (lower_central_series.subgroup.normal n) z⁻¹ (inv_mem _ hz) a),
end

/-- The lower central series of a group is a descending central series. -/
theorem lower_central_series_is_descending_central_series :
  is_descending_central_series (lower_central_series G) :=
begin
  split, refl,
  intros x n hxn g,
  exact general_commutator_containment _ _ hxn (subgroup.mem_top g),
end

/-- Any descending central series for a group is bounded below by the lower central series. -/
lemma descending_central_series_ge_lower (H : ℕ → subgroup G)
  (hH : is_descending_central_series H) : ∀ n : ℕ, lower_central_series G n ≤ H n
| 0 := hH.1.symm ▸ le_refl ⊤
| (n + 1) := begin
  specialize descending_central_series_ge_lower n,
  apply (general_commutator_le _ _ _).2,
  intros x hx q _,
  exact hH.2 x n (descending_central_series_ge_lower hx) q,
end

/-- A group is nilpotent if and only if its lower central series eventually reaches
  the trivial subgroup. -/
theorem nilpotent_iff_lower_central_series : is_nilpotent G ↔ ∃ n, lower_central_series G n = ⊥ :=
begin
  rw nilpotent_iff_finite_descending_central_series,
  split,
  { rintro ⟨n, H, ⟨h0, hs⟩, hn⟩,
    use n,
    have := descending_central_series_ge_lower H ⟨h0, hs⟩ n,
    rw hn at this,
    exact eq_bot_iff.mpr this },
  { rintro ⟨n, hn⟩,
    use [n, lower_central_series G, lower_central_series_is_descending_central_series, hn] },
end

section classical

open_locale classical

variables [hG : is_nilpotent G]
include hG

variable (G)

/-- The nilpotency class of a nilpotent group is the smallest natural `n` such that
the `n`'th term of the upper central series is `G`. -/
noncomputable def group.nilpotency_class : ℕ :=
nat.find (is_nilpotent.nilpotent G)

variable {G}

/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which an ascending
central series reaches `G` in its `n`'th term. -/
lemma least_ascending_central_series_length_eq_nilpotency_class :
  nat.find ((nilpotent_iff_finite_ascending_central_series G).mp hG) = group.nilpotency_class G :=
begin
  refine le_antisymm (nat.find_mono _) (nat.find_mono _),
  { intros n hn,
    exact ⟨upper_central_series G, upper_central_series_is_ascending_central_series G, hn ⟩, },
  { rintros n ⟨H, ⟨hH, hn⟩⟩,
    apply top_le_iff.mp,
    rw ← hn,
    exact (ascending_central_series_le_upper H hH n), }
end

/-- The nilpotency class of a nilpotent `G` is equal to the smallest `n` for which the descending
central series reaches `⊥` in its `n`'th term. -/
lemma least_descending_central_series_length_eq_nilpotency_class :
  nat.find ((nilpotent_iff_finite_descending_central_series G).mp hG) = group.nilpotency_class G :=
begin
  rw ← least_ascending_central_series_length_eq_nilpotency_class,
  refine le_antisymm (nat.find_mono _) (nat.find_mono _),
  { rintros n ⟨H, ⟨hH, hn⟩⟩,
    use (λ m, H (n - m)),
    split,
    { apply is_decending_rev_series_of_is_ascending G hn hH },
    { simp, exact hH.1 } },
  { rintros n ⟨H, ⟨hH, hn⟩⟩,
    use (λ m, H (n - m)),
    split,
    { apply is_ascending_rev_series_of_is_descending G hn hH },
    { simp, exact hH.1 } },
end

/-- The nilpotency class of a nilpotent `G` is equal to the length of the lower central series. -/
lemma lower_central_series_length_eq_nilpotency_class :
  nat.find (nilpotent_iff_lower_central_series.mp hG) = @group.nilpotency_class G _ _ :=
begin
  rw ← least_descending_central_series_length_eq_nilpotency_class,
  refine le_antisymm (nat.find_mono _) (nat.find_mono _),
  { rintros n ⟨H, ⟨hH, hn⟩⟩,
    apply le_bot_iff.mp,
    rw ← hn,
    exact (descending_central_series_ge_lower H hH n), },
  { rintros n h,
    refine ⟨lower_central_series G, ⟨lower_central_series_is_descending_central_series, h⟩⟩ },
end

end classical

lemma lower_central_series_map_subtype_le (H : subgroup G) (n : ℕ) :
  (lower_central_series H n).map H.subtype ≤ lower_central_series G n :=
begin
  induction n with d hd,
  { simp },
  { rw [lower_central_series_succ, lower_central_series_succ, monoid_hom.map_closure],
    apply subgroup.closure_mono,
    rintros x1 ⟨x2, ⟨x3, hx3, x4, hx4, rfl⟩, rfl⟩,
    exact ⟨x3, (hd (mem_map.mpr ⟨x3, hx3, rfl⟩)), x4, by simp⟩ }
end

/-- A subgroup of a nilpotent group is nilpotent -/
instance subgroup.is_nilpotent (H : subgroup G) [hG : is_nilpotent G] :
  is_nilpotent H :=
begin
  rw nilpotent_iff_lower_central_series at *,
  rcases hG with ⟨n, hG⟩,
  use n,
  have := lower_central_series_map_subtype_le H n,
  simp only [hG, set_like.le_def, mem_map, forall_apply_eq_imp_iff₂, exists_imp_distrib] at this,
  exact eq_bot_iff.mpr (λ x hx, subtype.ext (this x hx)),
end

/-- A the nilpotency class of a subgroup is less or equal the the nilpotency class of the group -/
lemma subgroup.nilpotency_class_le (H : subgroup G) [hG : is_nilpotent G] :
  group.nilpotency_class H ≤ group.nilpotency_class G :=
begin
  repeat { rw ← lower_central_series_length_eq_nilpotency_class },
  apply nat.find_mono,
  intros n hG,
  have := lower_central_series_map_subtype_le H n,
  simp only [hG, set_like.le_def, mem_map, forall_apply_eq_imp_iff₂, exists_imp_distrib] at this,
  exact eq_bot_iff.mpr (λ x hx, subtype.ext (this x hx)),
end

@[priority 100]
instance is_nilpotent_of_subsingleton [subsingleton G] : is_nilpotent G :=
nilpotent_iff_lower_central_series.2 ⟨0, subsingleton.elim ⊤ ⊥⟩

lemma upper_central_series.map {H : Type*} [group H] {f : G →* H} (h : function.surjective f)
  (n : ℕ) : subgroup.map f (upper_central_series G n) ≤ upper_central_series H n :=
begin
  induction n with d hd,
  { simp },
  { rintros _ ⟨x, hx : x ∈ upper_central_series G d.succ, rfl⟩ y',
    rcases (h y') with ⟨y, rfl⟩,
    simpa using hd (mem_map_of_mem f (hx y)) }
end

lemma lower_central_series.map {H : Type*} [group H] (f : G →* H) (n : ℕ) :
  subgroup.map f (lower_central_series G n) ≤ lower_central_series H n :=
begin
  induction n with d hd,
  { simp [nat.nat_zero_eq_zero] },
  { rintros a ⟨x, hx : x ∈ lower_central_series G d.succ, rfl⟩,
    refine closure_induction hx _ (by simp [f.map_one, subgroup.one_mem _])
      (λ y z hy hz, by simp [monoid_hom.map_mul, subgroup.mul_mem _ hy hz])
      (λ y hy, by simp [f.map_inv, subgroup.inv_mem _ hy]),
    rintros a ⟨y, hy, z, ⟨-, rfl⟩⟩,
    apply mem_closure.mpr,
    exact λ K hK, hK ⟨f y, hd (mem_map_of_mem f hy), by simp⟩ }
end

lemma lower_central_series_succ_eq_bot {n : ℕ} (h : lower_central_series G n ≤ center G) :
  lower_central_series G (n + 1) = ⊥ :=
begin
  rw [lower_central_series_succ, closure_eq_bot_iff, set.subset_singleton_iff],
  rintro x ⟨y, hy1, z, ⟨⟩, rfl⟩,
  symmetry,
  rw [eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, one_mul],
  exact mem_center_iff.mp (h hy1) z,
end

/-- The preimage of a nilpotent group is nilpotent if the kernel of the homomorphism is contained
in the center -/
lemma is_nilpotent_of_ker_le_center {H : Type*} [group H] {f : G →* H}
  (hf1 : f.ker ≤ center G) (hH : is_nilpotent H) : is_nilpotent G :=
begin
  rw nilpotent_iff_lower_central_series at *,
  rcases hH with ⟨n, hn⟩,
  use (n + 1),
  refine lower_central_series_succ_eq_bot (le_trans ((map_eq_bot_iff _).mp _) hf1),
  exact eq_bot_iff.mpr (hn ▸ (lower_central_series.map f n)),
end

section classical

open_locale classical

lemma nilpotency_class_le_of_ker_le_center {H : Type*} [group H] {f : G →* H}
  (hf1 : f.ker ≤ center G) (hH : is_nilpotent H) :
  @group.nilpotency_class G _ (is_nilpotent_of_ker_le_center hf1 hH) ≤
    group.nilpotency_class H + 1 :=
begin
  repeat { rw ← lower_central_series_length_eq_nilpotency_class },
  apply nat.find_min',
  have hn := nat.find_spec (nilpotent_iff_lower_central_series.mp hH),
  refine lower_central_series_succ_eq_bot (le_trans ((map_eq_bot_iff _).mp _) hf1),
  apply eq_bot_iff.mpr,
  apply (le_trans (lower_central_series.map f _)),
  rw hn,
  exact (le_refl _),
end

end classical


lemma nilpotent_of_surjective
  {G' : Type*} [group G'] {f : G →* G'} (hf : function.surjective f) [h : is_nilpotent G] :
  is_nilpotent G' :=
begin
  unfreezingI { rcases h with ⟨n, hn⟩ },
  use n,
  apply eq_top_iff.mpr,
  calc ⊤ = f.range : symm (monoid_hom.range_eq_top_of_surjective hf)
    ... = subgroup.map f ⊤ : monoid_hom.range_eq_map _
    ... = subgroup.map f (upper_central_series G n) : by rw hn
    ... ≤ upper_central_series G' n : upper_central_series.map hf n,
end

lemma nilpotency_class_le_of_surjective
  {G' : Type*} [group G'] {f : G →* G'} (hf : function.surjective f) [h : is_nilpotent G] :
  @group.nilpotency_class G' _ (nilpotent_of_surjective hf) ≤
    group.nilpotency_class G :=
begin
  apply nat.find_mono,
  intros n hn,
  apply eq_top_iff.mpr,
  calc ⊤ = f.range : symm (monoid_hom.range_eq_top_of_surjective hf)
    ... = subgroup.map f ⊤ : monoid_hom.range_eq_map _
    ... = subgroup.map f (upper_central_series G n) : by rw hn
    ... ≤ upper_central_series G' n : upper_central_series.map hf n,
end

instance nilpotent_quotient_of_nilpotent (H : subgroup G) [H.normal] [h : is_nilpotent G] :
  is_nilpotent (G ⧸ H) :=
 nilpotent_of_surjective (show function.surjective (quotient_group.mk' H), by tidy)

lemma nilpotency_class_quotient_le (H : subgroup G) [H.normal] [h : is_nilpotent G] :
  group.nilpotency_class (G ⧸ H) ≤ group.nilpotency_class G := nilpotency_class_le_of_surjective _


lemma comap_comap_center {H₁ : subgroup G} [H₁.normal] {H₂ : subgroup (G ⧸ H₁)} [H₂.normal] :
  comap (mk' H₁) (comap (mk' H₂) (center ((G ⧸ H₁) ⧸ H₂))) =
    comap (mk' (comap (mk' H₁) H₂)) (center (G ⧸ comap (mk' H₁) H₂)) :=
begin
  ext,
  simp,
  repeat { rw mem_center_iff },
  split; intros hx,
  {
    intro y,
    obtain ⟨y,rfl⟩ := quotient.surjective_quotient_mk' y,
    specialize hx (quotient.mk' (quotient.mk' y)),
    apply eq_iff_div_mem.mpr,
    simp,
    have hx' := eq_iff_div_mem.mp hx, clear hx,
    apply hx',
    apply_instance,
  },
  {
    intro y,
    obtain ⟨y,rfl⟩ := quotient.surjective_quotient_mk' y,
    obtain ⟨y,rfl⟩ := quotient.surjective_quotient_mk' y,
    specialize hx (quotient.mk' y),
    apply eq_iff_div_mem.mpr,
    have hx' := eq_iff_div_mem.mp hx, clear hx,
    simp at hx',
    apply hx',
    apply_instance,
  }
end

-- This lemma is just because `rw h` doesn’t work below.
lemma comap_center_subst {H₁ H₂ : subgroup G} [normal H₁] [normal H₂] (h : H₁ = H₂) :
  comap (mk' H₁) (center (G ⧸ H₁)) = comap (mk' H₂) (center (G ⧸ H₂)) :=
  by { unfreezingI { subst h, } }

lemma comap_upper_central_series_quotient_center (n : ℕ) :
  comap (mk' (center G)) (upper_central_series (G ⧸ center G) n) = upper_central_series G n.succ :=
begin
  induction n with n ih,
  { simp, },
  {
    let Hn := upper_central_series (G ⧸ center G) n,
    calc comap (mk' (center G)) (upper_central_series (G ⧸ center G) n.succ)
        = comap (mk' (center G)) (upper_central_series_step Hn)
        : rfl
    ... = comap (mk' (center G)) (comap (mk' Hn) (center ((G ⧸ center G) ⧸ Hn)))
        : by rw upper_central_series_step_eq_comap_center
    ... = comap (mk' (comap (mk' (center G)) Hn)) (center (G ⧸ (comap (mk' (center G)) Hn)))
        : comap_comap_center
    ... = comap (mk' (upper_central_series G n.succ)) (center (G ⧸ upper_central_series G n.succ))
        : symm (comap_center_subst (symm ih))
    ... = upper_central_series_step (upper_central_series G n.succ)
        : symm (upper_central_series_step_eq_comap_center _)
    ... = upper_central_series G n.succ.succ
        : rfl,
  },
end

lemma nilpotency_class_zero_iff_subsingleton [is_nilpotent G] :
  group.nilpotency_class G = 0 ↔ subsingleton G :=
by simp [group.nilpotency_class, nat.find_eq_zero, subsingleton_iff_bot_eq_top]

lemma subsingleton_quotient_of_subsingleton
  {H : subgroup G} [H.normal] [subsingleton G] :
  subsingleton (G ⧸ H) :=
begin
  apply subsingleton.intro,
  intros x y,
  obtain ⟨x,rfl⟩ := quotient.surjective_quotient_mk' x,
  obtain ⟨y,rfl⟩ := quotient.surjective_quotient_mk' y,
  have := subsingleton.elim x y,
  subst this,
end

section classical

open_locale classical

lemma nilpotency_class_quotient_center [hH : is_nilpotent G] :
  group.nilpotency_class (G ⧸ center G) = group.nilpotency_class G - 1 :=
begin
  generalize hn : group.nilpotency_class G = n,
  rcases n with rfl | n,
  {
    simp [nilpotency_class_zero_iff_subsingleton] at *,
    haveI := hn,
    apply subsingleton_quotient_of_subsingleton,
  },
  { apply le_antisymm,
    {
      apply nat.find_min',
      apply (@comap_injective G _ _ _ (mk' (center G)) (surjective_quot_mk _)),
      rw comap_upper_central_series_quotient_center,
      simp,
      rw ← hn,
      have : (∃ n : ℕ, upper_central_series G n = ⊤) := begin
          unfreezingI { obtain ⟨n, h⟩ := hH, },
          refine ⟨n,h⟩
      end,
      apply (nat.find_spec this) ,
    },
    {
      simp,
      apply le_of_add_le_add_right,
      calc n + 1 = n.succ : rfl
        ... = group.nilpotency_class G : symm hn
        ... ≤ group.nilpotency_class (G ⧸ center G) + 1
            : nilpotency_class_le_of_ker_le_center (le_of_eq (ker_mk _)) _,
    }
  }
end

end classical

lemma derived_le_lower_central (n : ℕ) : derived_series G n ≤ lower_central_series G n :=
by { induction n with i ih, { simp }, { apply general_commutator_mono ih, simp } }

/-- A nilpotent subgroup is solvable -/
@[priority 100]
instance is_nilpotent.to_is_solvable [h : is_nilpotent G]: is_solvable G :=
begin
  obtain ⟨n, hn⟩ := nilpotent_iff_lower_central_series.1 h,
  use n,
  apply le_bot_iff.mp,
  calc derived_series G n ≤ lower_central_series G n : derived_le_lower_central n
    ... = ⊥ : hn
end

section normalizer_condition

/-- Every proper subgroup `H` of `G` is a proper normal subgroup of the normalizer of `H` in `G`. -/
def normalizer_condition (G : Type*) [group G] :=
  ∀ (H : subgroup G), H < ⊤ → H < normalizer H

/-- Alternative phrasing of the normalizer condition: Only the full group is self-normalizing.
This may be easier to work with, as it avoids inequalities or negations.  -/
lemma normalizer_condition_iff_only_full_group_self_normalizing :
  normalizer_condition G ↔ ∀ (H : subgroup G), H.normalizer = H → H = ⊤ :=
begin
  apply forall_congr, intro H,
  simp [normalizer_condition, lt_top_iff_ne_top, lt_iff_le_and_ne, le_normalizer],
  tauto!,
end
lemma _root_.subgroup.center_le_normalizer {G : Type*} [group G] (H : subgroup G) : center G ≤ H.normalizer :=
begin
  intros x hx,
  rewrite mem_center_iff at hx,
  intros y,
  specialize (hx y),
  simp [← hx, mul_assoc],
end

/- A custom induction principle for nilpotent groups.
   Unfortunately, `induction G using nilpotent_center_quotient_ind` does not work.
-/
lemma nilpotent_center_quotient_ind
  {P : Π G [group G], by exactI ∀ [is_nilpotent G], Prop}
  (hbase : ∀ G [group G], by exactI ∀ [is_nilpotent G], by exactI ∀ [subsingleton G], P G)
  (hstep : ∀ G [group G], by exactI ∀ [is_nilpotent G], by exactI P (G ⧸ center G) -> P G)
  (G : Type*)
  [group G]
  [is_nilpotent G]
  :
  P G :=
begin
  obtain ⟨n, h⟩ : ∃ n, group.nilpotency_class G = n := ⟨ _, rfl⟩,
  unfreezingI { induction n with n ih generalizing G },
  { haveI := nilpotency_class_zero_iff_subsingleton.mp h,
    exact hbase _, },
  { have hn : group.nilpotency_class (G ⧸ center G) = n :=
      by simp [nilpotency_class_quotient_center, h],
    exact hstep _ (ih _ hn), },
end

lemma normalizer_condition_of_is_nilpotent : is_nilpotent G → normalizer_condition G :=
begin
  -- roughly based on https://groupprops.subwiki.org/wiki/Nilpotent_implies_normalizer_condition
  rw normalizer_condition_iff_only_full_group_self_normalizing,
  -- in leiu of the induction tactic:
  unfreezingI { revert G _inst_1 }, refine (@nilpotent_center_quotient_ind _ _ _),
  {
    intro G, introsI _ _ _,
    rintros H -,
    apply subsingleton.elim,
  },
  { intro G, introsI _ _, intros ih,
    intros H hH,

    by_cases hch : center G ≤ H,
    {
      let H' := H.map (mk' (center G)),

      have hH' : H'.normalizer = H' :=
      begin
        apply (@comap_injective G _ _ _ (mk' (center G)) (surjective_quot_mk _)),
        rw comap_normalizer_eq_of_surjective,
        show function.surjective _, exact (surjective_quot_mk _),
        rw comap_map_eq_self,
        show (_ ≤ H), simp, exact hch,
        exact hH,
      end,

      specialize ih (H.map (mk' (center G))) hH',

      show H = ⊤,
      begin -- this needs to be prettier…
        rw eq_top_iff' at *,
        intro x,
        specialize ih (mk' (center G) x),
        simp at *,
        rcases ih with ⟨x', hx, heq⟩,
        rw eq_iff_div_mem at heq,
        rw div_mem_comm_iff at heq,
        have := mul_mem H (hch heq) hx,
        simp at this,
        assumption,
      end
    },
    { exfalso, apply hch,
      calc center G ≤ H.normalizer : H.center_le_normalizer
                ... = H : hH, }
  },
end

end normalizer_condition


section finite

/-- A subgroup is maximal if it is a proper subgroup that is not contained in
anyother proper subgroup -/
def subgroup.is_maximal (H : subgroup G) :=
  H < ⊤  ∧ (∀ H' : subgroup G, H < H' → H < ⊤ → H' = H)

variable (G)

/-- Every Sylow group is normal --/
def sylow_group_normal :=
  ∀ p, ∀ H : subgroup G, sylow p G → H.normal

/-- All maximal subgroups are normal --/
def all_maximal_subgroups_normal :=
  ∀ p, ∀ H : subgroup G, sylow p G → H.is_maximal


end finite
