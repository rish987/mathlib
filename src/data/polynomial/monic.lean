/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.degree
import algebra.associated
import tactic.omega

/-!
# Theory of monic polynomials

We give several tools for proving that polynomials are monic, e.g.
`monic_mul`, `monic_map`.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

open finset
open_locale big_operators

namespace polynomial
universes u v y
variables {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

section semiring
variables [semiring R] {p q r : polynomial R}

lemma monic.as_sum {p : polynomial R} (hp : p.monic) :
  p = X^(p.nat_degree) + (∑ i in finset.range p.nat_degree, C (p.coeff i) * X^i) :=
begin
  conv_lhs { rw [p.as_sum_range_C_mul_X_pow, finset.sum_range_succ] },
  suffices : C (p.coeff p.nat_degree) = 1,
  { rw [this, one_mul] },
  exact congr_arg C hp
end

lemma ne_zero_of_monic_of_zero_ne_one (hp : monic p) (h : (0 : R) ≠ 1) :
  p ≠ 0 := mt (congr_arg leading_coeff) $ by rw [monic.def.1 hp, leading_coeff_zero]; cc

lemma ne_zero_of_ne_zero_of_monic (hp : p ≠ 0) (hq : monic q) : q ≠ 0 :=
begin
  intro h, rw [h, monic.def, leading_coeff_zero] at hq,
  rw [← mul_one p, ← C_1, ← hq, C_0, mul_zero] at hp,
  exact hp rfl
end

lemma monic_map [semiring S] (f : R →+* S) (hp : monic p) : monic (p.map f) :=
if h : (0 : S) = 1 then
  by haveI := subsingleton_of_zero_eq_one h;
  exact subsingleton.elim _ _
else
have f (leading_coeff p) ≠ 0,
  by rwa [show _ = _, from hp, is_semiring_hom.map_one f, ne.def, eq_comm],
by
begin
  rw [monic, leading_coeff, coeff_map],
  suffices : p.coeff (map f p).nat_degree = 1, simp [this],
  suffices : (map f p).nat_degree = p.nat_degree, rw this, exact hp,
  rwa nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero _ _),
end

lemma monic_mul_C_of_leading_coeff_mul_eq_one [nontrivial R] {b : R}
  (hp : p.leading_coeff * b = 1) : monic (p * C b) :=
by rw [monic, leading_coeff_mul' _]; simp [leading_coeff_C b, hp]

theorem monic_of_degree_le (n : ℕ) (H1 : degree p ≤ n) (H2 : coeff p n = 1) : monic p :=
decidable.by_cases
  (assume H : degree p < n, eq_of_zero_eq_one
    (H2 ▸ (coeff_eq_zero_of_degree_lt H).symm) _ _)
  (assume H : ¬degree p < n,
    by rwa [monic, leading_coeff, nat_degree, (lt_or_eq_of_le H1).resolve_left H])

theorem monic_X_pow_add {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) + p) :=
have H1 : degree p < n+1, from lt_of_le_of_lt H (with_bot.coe_lt_coe.2 (nat.lt_succ_self n)),
monic_of_degree_le (n+1)
  (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H1)))
  (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H1, add_zero])

theorem monic_X_add_C (x : R) : monic (X + C x) :=
pow_one (X : polynomial R) ▸ monic_X_pow_add degree_C_le

lemma monic_mul (hp : monic p) (hq : monic q) : monic (p * q) :=
if h0 : (0 : R) = 1 then by haveI := subsingleton_of_zero_eq_one h0;
  exact subsingleton.elim _ _
else
  have leading_coeff p * leading_coeff q ≠ 0, by simp [monic.def.1 hp, monic.def.1 hq, ne.symm h0],
  by rw [monic.def, leading_coeff_mul' this, monic.def.1 hp, monic.def.1 hq, one_mul]

lemma monic_pow (hp : monic p) : ∀ (n : ℕ), monic (p ^ n)
| 0     := monic_one
| (n+1) := monic_mul hp (monic_pow n)

lemma monic_add_of_left {p q : polynomial R} (hp : monic p) (hpq : degree q < degree p) :
  monic (p + q) :=
by rwa [monic, add_comm, leading_coeff_add_of_degree_lt hpq]

lemma monic_add_of_right {p q : polynomial R} (hq : monic q) (hpq : degree p < degree q) :
  monic (p + q) :=
by rwa [monic, leading_coeff_add_of_degree_lt hpq]

end semiring

section comm_semiring
variables [comm_semiring R] {p : polynomial R}

lemma monic_prod_of_monic (s : finset ι) (f : ι → polynomial R) (hs : ∀ i ∈ s, monic (f i)) :
monic (∏ i in s, f i) :=
prod_induction _ _ (@monic_mul _ _) monic_one hs

lemma is_unit_C {x : R} : is_unit (C x) ↔ is_unit x :=
begin
  rw [is_unit_iff_dvd_one, is_unit_iff_dvd_one],
  split,
  { rintros ⟨g, hg⟩,
    replace hg := congr_arg (eval 0) hg,
    rw [eval_one, eval_mul, eval_C] at hg,
    exact ⟨g.eval 0, hg⟩ },
  { rintros ⟨y, hy⟩,
    exact ⟨C y, by rw [← C_mul, ← hy, C_1]⟩ }
end

lemma eq_one_of_is_unit_of_monic (hm : monic p) (hpu : is_unit p) : p = 1 :=
have degree p ≤ 0,
  from calc degree p ≤ degree (1 : polynomial R) :
    let ⟨u, hu⟩ := is_unit_iff_dvd_one.1 hpu in
    if hu0 : u = 0
    then begin
        rw [hu0, mul_zero] at hu,
        rw [← mul_one p, hu, mul_zero],
        simp
      end
    else have p.leading_coeff * u.leading_coeff ≠ 0,
        by rw [hm.leading_coeff, one_mul, ne.def, leading_coeff_eq_zero];
          exact hu0,
      by rw [hu, degree_mul' this];
        exact le_add_of_nonneg_right (degree_nonneg_iff_ne_zero.2 hu0)
  ... ≤ 0 : degree_one_le,
by rw [eq_C_of_degree_le_zero this, ← nat_degree_eq_zero_iff_degree_le_zero.2 this,
    ← leading_coeff, hm.leading_coeff, C_1]


end comm_semiring

section ring
variables [ring R]
namespace monic

lemma coeff_nat_degree {p : polynomial R} (hp : p.monic) : p.coeff (p.nat_degree) = 1 := hp

@[simp]
lemma degree_eq_zero_iff_eq_one {p : polynomial R} (hp : p.monic) :
  p.nat_degree = 0 ↔ p = 1 :=
begin
  split; intro h,
  swap, { rw h, exact nat_degree_one },
  have : p = C (p.coeff 0),
  { rw ← polynomial.degree_le_zero_iff,
    rwa polynomial.nat_degree_eq_zero_iff_degree_le_zero at h },
  rw this, convert C_1, rw ← h, apply hp,
end

lemma nat_degree_mul [nontrivial R] {p q : polynomial R} (hp : p.monic) (hq : q.monic) :
(p * q).nat_degree = p.nat_degree + q.nat_degree :=
by { apply nat_degree_mul', rw [hp.leading_coeff, hq.leading_coeff], simp }

lemma next_coeff_mul {p q : polynomial R} (hp : monic p) (hq : monic q) :
  next_coeff (p * q) = next_coeff p + next_coeff q :=
begin
  classical,
  nontriviality R,
  simp only [next_coeff, monic.nat_degree_mul hp hq],
  simp only [hp, hq, degree_eq_zero_iff_eq_one, add_eq_zero_iff],
  set dp := p.nat_degree, set dq := q.nat_degree,
  suffices : p ≠ 1 → q ≠ 1 → (p * q).coeff (dp + dq - 1) = p.coeff (dp - 1) + q.coeff (dq - 1),
  { by_cases hp0 : p = 1; by_cases hq0 : q = 1; simp [dp, dq, hp0, hq0, this] },
  intros hp0 hq0,
  replace hp0 : dp ≠ 0 := mt hp.degree_eq_zero_iff_eq_one.1 hp0,
  replace hq0 : dq ≠ 0 := mt hq.degree_eq_zero_iff_eq_one.1 hq0,
  rw coeff_mul,
  have : {(dp - 1, dq), (dp, dq - 1)} ⊆ nat.antidiagonal (dp + dq - 1),
  { suffices : dp - 1 + dq = dp + dq - 1 ∧ dp + (dq - 1) = dp + dq - 1,
      by simpa [insert_subset, singleton_subset_iff],
    omega },
  rw [← sum_subset this, sum_pair],
  { simp [hp, hq] },
  { suffices : dp - 1 ≠ dp, from mt (congr_arg prod.fst) this,
    omega },
  { rintros ⟨x, y⟩ hx hx1,
    simp only [nat.mem_antidiagonal] at hx,
    simp only [mem_insert, mem_singleton] at hx1,
    contrapose! hx1,
    have hxp : x ≤ dp, from le_nat_degree_of_ne_zero (left_ne_zero_of_mul hx1),
    have hyq : y ≤ dq, from le_nat_degree_of_ne_zero (right_ne_zero_of_mul hx1),
    have : dq - 1 ≤ y, omega,
    by_cases hy : y = dq,
    { subst y, left, congr, omega },
    { have : y = dq - 1, by omega, subst y, right, congr, omega } }
end

end monic
end ring

section comm_ring
namespace monic
variable [comm_ring R]
lemma next_coeff_prod
  (s : finset ι) (f : ι → polynomial R) (h : ∀ i ∈ s, monic (f i)) :
next_coeff (∏ i in s, f i) = ∑ i in s, next_coeff (f i) :=
begin
  classical,
  revert h, apply finset.induction_on s,
  { simp only [finset.not_mem_empty, forall_prop_of_true, forall_prop_of_false, finset.sum_empty,
  finset.prod_empty, not_false_iff, forall_true_iff],
  rw ← C_1, rw next_coeff_C_eq_zero },
  { intros a s ha hs monic,
    rw finset.prod_insert ha,
    rw finset.sum_insert ha,
    rw next_coeff_mul (monic a (finset.mem_insert_self a s)), swap,
    { apply monic_prod_of_monic, intros b bs,
      apply monic, apply finset.mem_insert_of_mem bs },
    { refine congr rfl (hs _),
      intros b bs, apply monic, apply finset.mem_insert_of_mem bs }}
end
end monic
end comm_ring

section ring
variables [ring R] {p : polynomial R}

theorem monic_X_sub_C (x : R) : monic (X - C x) :=
by simpa only [sub_eq_add_neg, C_neg] using monic_X_add_C (-x)

theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) - p) :=
by simpa [sub_eq_add_neg] using monic_X_pow_add (show degree (-p) ≤ n, by rwa ←degree_neg p at H)

/-- `X ^ n - a` is monic. -/
lemma monic_X_pow_sub_C {R : Type u} [ring R] (a : R) {n : ℕ} (h : n ≠ 0) : (X ^ n - C a).monic :=
begin
  obtain ⟨k, hk⟩ := nat.exists_eq_succ_of_ne_zero h,
  convert monic_X_pow_sub _,
  exact le_trans degree_C_le nat.with_bot.coe_nonneg,
end

lemma monic_sub_of_left {p q : polynomial R} (hp : monic p) (hpq : degree q < degree p) :
  monic (p - q) :=
by { rw sub_eq_add_neg, apply monic_add_of_left hp, rwa degree_neg }

lemma monic_sub_of_right {p q : polynomial R}
  (hq : q.leading_coeff = -1) (hpq : degree p < degree q) : monic (p - q) :=
have (-q).coeff (-q).nat_degree = 1 :=
by rw [nat_degree_neg, coeff_neg, show q.coeff q.nat_degree = -1, from hq, neg_neg],
by { rw sub_eq_add_neg, apply monic_add_of_right this, rwa degree_neg }

end ring
section injective
variables [semiring R] {p : polynomial R}
open function
variables [semiring S] {f : R →+* S} (hf : injective f)
include hf

lemma leading_coeff_of_injective (p : polynomial R) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  delta leading_coeff,
  rw [coeff_map f, nat_degree_map' hf p]
end

lemma monic_of_injective {p : polynomial R} (hp : (p.map f).monic) : p.monic :=
begin
  apply hf,
  rw [← leading_coeff_of_injective hf, hp.leading_coeff, is_semiring_hom.map_one f]
end

end injective

section nonzero_semiring
variables [semiring R] [nontrivial R] {p q : polynomial R}

@[simp] lemma not_monic_zero : ¬monic (0 : polynomial R) :=
by simpa only [monic, leading_coeff_zero] using (zero_ne_one : (0 : R) ≠ 1)

lemma ne_zero_of_monic (h : monic p) : p ≠ 0 :=
λ h₁, @not_monic_zero R _ _ (h₁ ▸ h)

end nonzero_semiring


end polynomial
