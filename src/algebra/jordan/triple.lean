/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import algebra.lie.of_associative

/-!
# Jordan triples

Let `A` be a module over a ring `R`. A triple product on `A` is a trilinear map
$\{.\,.\,\}:A\times A\times A\mapsto A$ which is symmetric in the first and third variables. The
module `A` is said to be a Jordan triple if, for any `a`, `b`, `c`, `d` and `e` in `A` the following
Lebintz rule is satisfied:
$$
\{a\,b\,\{c\,d\,e\}\} = \{\{a\,b\,c\}\,d\,e\} - \{c\,\{b\,a\,d\}\,e\} + \{c\,d\,\{a\,b\,e\}\}
$$
A module `A` over a *-ring `R` is said to be a *-triple if it has a triple product linear and
symmetric in the first and thrid variable and conjugate linear in the second variable. A *-triple
satisfying the Lebintz rule is said to be a Jordan *-triple.

As well as being of algebraic interest, Jordan *-triples arise naturally in mathematical physics,
functional analysis and differential geometry. For more information about these connections the
interested reader is referred to [alfsenshultz2003], [chu2012], [friedmanscarr2005],
[iordanescu2003] and [upmeier1987].

## Main results

(None yet, we're just getting started.)

## References

* [Chu, Jordan Structures in Geometry and Analysis][chu2012]
-/

class has_tp (A : Type*) := (tp : A → A → A → A )

notation ⦃a, b, c⦄ := has_tp.tp a b c

class is_tp (A : Type*) [has_tp A] [has_add A] :=
(comm : ∀ (a b c : A), ⦃a, b, c⦄ = ⦃c, b, a⦄)
(ladd : ∀ (a₁ a₂ b c : A), ⦃(a₁+a₂), b, c⦄ = ⦃a₁, b, c⦄ + ⦃a₂, b, c⦄)
(madd : ∀ (a b₁ b₂ c : A), ⦃a, (b₁+b₂), c⦄ = ⦃a, b₁, c⦄ + ⦃a, b₂, c⦄)

class is_jordan_tp (A : Type*) [has_tp A] [has_add A] [has_sub A] :=
(lebintz : ∀ (a b c d e: A), ⦃a, b, ⦃c, d, e⦄⦄  =
  ⦃⦃a, b, c⦄, d, e⦄ - ⦃c, ⦃b, a, d⦄, e⦄ + ⦃c, d, ⦃a, b, e⦄⦄)

namespace is_tp

lemma radd {A : Type*} [has_tp A] [has_add A] [is_tp A] (a b c₁ c₂ : A) :
  ⦃a, b, c₁ + c₂⦄ = ⦃a, b, c₁⦄ + ⦃a, b, c₂⦄ := by rw [comm, ladd, comm, comm c₂]

variables {A : Type*} [has_tp A] [add_comm_group A] [is_tp A]

lemma lzero (b c : A) : ⦃0, b, c⦄ = 0 :=
(add_monoid_hom.mk' (λ (a : A), ⦃a, b, c⦄) (λ a₁ a₂, ladd a₁ a₂ b c )).map_zero

lemma mzero (a c : A) : ⦃a, 0, c⦄ = 0 :=
(add_monoid_hom.mk' (λ (b : A), ⦃a, b, c⦄) (λ b₁ b₂ , madd a b₁ b₂ c)).map_zero

lemma rzero (a b : A) : ⦃a, b, 0⦄ = 0 :=
by rw [comm, lzero]

lemma lgsmul (a b c : A) (z : ℤ) : ⦃z•a, b, c⦄ = z•⦃a, b, c⦄ :=
add_monoid_hom.map_zsmul ⟨λ (a : A), ⦃a, b, c⦄, lzero b c, λ _ _, ladd _ _ _ _⟩ _ _

lemma mgsmul (a b c : A) (z : ℤ) : ⦃a, z•b, c⦄ = z•⦃a, b, c⦄ :=
add_monoid_hom.map_zsmul ⟨λ (b : A), ⦃a, b, c⦄, mzero a c, λ _ _, madd _ _ _ _⟩ _ _

lemma rgsmul (a b : A) (z : ℤ) (c : A) : ⦃a, b, z•c⦄ = z•⦃a, b, c⦄ :=
  by rw [comm, lgsmul, comm]

lemma lneg (a b c : A) : ⦃-a, b, c⦄ = -⦃a, b, c⦄ :=
by rw [←sub_eq_zero, sub_neg_eq_add, ←ladd, neg_add_self, lzero]

lemma mneg (a b c : A): ⦃a, -b, c⦄ = -⦃a, b, c⦄ :=
by rw [←sub_eq_zero, sub_neg_eq_add, ←madd, neg_add_self, mzero]

lemma rneg (a b c : A): ⦃a, b, -c⦄ = -⦃a, b, c⦄ := by rw [comm, lneg, comm]

lemma lsub (a b c d : A) : ⦃a - d, b, c⦄ = ⦃a, b, c⦄ - ⦃d, b, c⦄ :=
by rw [eq_sub_iff_add_eq, ← ladd, sub_add_cancel]

lemma msub (a b c d : A) : ⦃a, b - c, d⦄ = ⦃a, b, d⦄ - ⦃a, c, d⦄ :=
by rw [eq_sub_iff_add_eq, ← madd, sub_add_cancel]


lemma rsub (a b c d : A) : ⦃a, b, c - d⦄ = ⦃a, b, c⦄ - ⦃a, b, d⦄ :=
by rw [comm, lsub, comm, comm d]

lemma lr_bilinear (a₁ a₂ b c₁ c₂ : A) : ⦃a₁ + a₂, b, c₁ + c₂⦄ =
  ⦃a₁, b, c₁⦄ + ⦃a₁, b, c₂⦄ + ⦃a₂, b, c₁⦄ + ⦃a₂, b, c₂⦄ :=
calc ⦃a₁ + a₂, b, c₁ + c₂⦄ = ⦃a₁, b, c₁ + c₂⦄ + ⦃a₂, b, c₁ + c₂⦄ : by rw ladd
... = ⦃a₁, b, c₁⦄ + ⦃a₁, b, c₂⦄ + ⦃a₂, b, c₁ + c₂⦄ : by rw radd
... = ⦃a₁, b, c₁⦄ + ⦃a₁, b, c₂⦄ + (⦃a₂, b, c₁⦄ + ⦃a₂, b, c₂⦄) : by rw radd
... = ⦃a₁, b, c₁⦄ + ⦃a₁, b, c₂⦄ + ⦃a₂, b, c₁⦄ + ⦃a₂, b, c₂⦄ : by rw ← add_assoc

lemma polar (a b c : A) : ⦃a + c, b, a + c⦄ = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ :=
calc ⦃a + c, b, a + c⦄ = ⦃a, b, a⦄ + ⦃a, b, c⦄ + ⦃c, b, a⦄ + ⦃c, b, c⦄ :
  by rw lr_bilinear a c b a c
... = ⦃a, b, a⦄ + ⦃a, b, c⦄ + ⦃a, b, c⦄ + ⦃c, b, c⦄ : by rw comm c b a
... = ⦃a, b, a⦄ + (⦃a, b, c⦄ + ⦃a, b, c⦄)  + ⦃c, b, c⦄ : by rw ← add_assoc
... = ⦃a, b, a⦄ + 2•⦃a, b, c⦄ + ⦃c, b, c⦄ : by rw two_nsmul

@[simps] def D (a b : A) : add_monoid.End A :=
{
  to_fun := λ c, ⦃a, b, c⦄,
  map_zero' := rzero _ _,
  map_add' := radd _ _,
}

@[simps] def Q (a c : A) : add_monoid.End A :=
{
  to_fun := λ b, ⦃a, b, c⦄,
  map_zero' := mzero _ _,
  map_add' := begin
    intros,
    rw madd _ _,
    exact _inst_3,
  end
}

/--
For a in A, the map b → D a b is an additive monoid homomorphism from A to add_monoid.End A
-/
@[simps] lemma D_madd (a : A) : A  →+  add_monoid.End A :=  {
  to_fun := λ b, D a b,
  map_zero' := begin
    ext c,
    rw [D_apply, mzero, add_monoid_hom.zero_apply],
  end,
  map_add' := λ b₁ b₂, begin
    ext c,
    rw [D_apply, madd, add_monoid_hom.add_apply, D_apply, D_apply],
  end,
}

/--
The map a → D a is an additive monoid homomorphism from A to (A  →+  add_monoid.End A)
-/
@[simps] lemma D_ladd : A  →+ (A  →+  add_monoid.End A) := {
  to_fun := λ a, D_madd a,
  map_zero' := begin
    ext b c,
    rw [D_madd_apply, D_apply, add_monoid_hom.zero_apply,  add_monoid_hom.zero_apply, lzero ],
  end,
  map_add' := λ a₁ a₂, begin
    ext b c,
    rw [D_madd_apply, D_apply, add_monoid_hom.add_apply, D_madd_apply, D_madd_apply,
      add_monoid_hom.add_apply, D_apply, D_apply, ladd],
  end
}

@[simps] lemma Q_radd (a : A) : (A  →+  add_monoid.End A) :=  {
  _root_.add_monoid_hom . to_fun := λ c, Q a c,
  map_zero' := begin
    ext b,
    rw [Q_apply, rzero, add_monoid_hom.zero_apply],
  end,
  map_add' := λ  c₁ c₂, begin
    ext b,
    rw [add_monoid_hom.add_apply, Q_apply, Q_apply, Q_apply, radd],
  end,
}


lemma Q_ladd : A  →+ (A  →+  add_monoid.End A) := {
  to_fun := λ a, Q_radd a,
  map_zero' := begin
    ext b c,
    rw [Q_radd_apply, Q_apply, add_monoid_hom.zero_apply, add_monoid_hom.zero_apply, lzero],
  end,
  map_add' := λ a₁ a₂, begin
    ext b c,
    rw [Q_radd_apply, add_monoid_hom.add_apply, Q_radd_apply, Q_radd_apply, Q_apply,
      add_monoid_hom.add_apply, Q_apply, Q_apply, ladd],
  end,
}


end is_tp

variables {A : Type*} [has_tp A] [add_comm_group A] [is_tp A]

open is_tp (D)

lemma lie_D_D [is_jordan_tp A] (a b c d: A) : ⁅D a b, D c d⁆ = D ⦃a, b, c⦄ d - D c ⦃b, a, d⦄ :=
begin
  ext e,
  rw ring.lie_def,
  simp only [add_monoid_hom.sub_apply, function.comp_app, is_tp.D_apply, add_monoid.coe_mul],
  rw [sub_eq_iff_eq_add, is_jordan_tp.lebintz],
end

def lebnitz (D : A → A) (D'  : A → A) :=
  ∀ (a b c : A),  D ⦃ a, b, c ⦄  = ⦃ D a, b, c⦄ + ⦃a, D' b, c⦄ + ⦃a, b, D c⦄

/--
For a and b in A, the pair D(a,b) and -D(b,a) are Lebintz
-/
lemma D_D_lebintz [is_jordan_tp A] (a b : A) : lebnitz (D a b) (-D b a) := begin
  unfold lebnitz,
  intros c d e,
  rw [pi.neg_apply, is_tp.mneg, tactic.ring.add_neg_eq_sub, is_tp.D_apply, is_tp.D_apply,
    is_tp.D_apply, is_tp.D_apply, is_jordan_tp.lebintz],
end