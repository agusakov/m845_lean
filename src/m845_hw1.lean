import algebra.group.basic
import data.real.basic
import group_theory.order_of_element

noncomputable theory
open_locale classical


def star_set := set.Ico (0:ℝ) 1

#check star_set


section star_group


#check has_coe_to_sort
#check semigroup

def star : ℝ → ℝ → ℝ
| x y := x + y - ⌊ x + y ⌋


notation x`⋆`y := star x y
variables (x y : ℝ) (A : Type*)

#check star_set

lemma star_closed {a b : ℝ} (ha : a ∈ star_set) (hb : b ∈ star_set) : (a ⋆ b) ∈ star_set :=
begin
    unfold star,
    unfold star_set,
    split,
    exact fract_nonneg (a + b),
    exact fract_lt_one (a + b),
end


lemma star_assoc {a b c : ℝ} (ha : a ∈ star_set) (hb : b ∈ star_set) (hc : c ∈ star_set): (a ⋆ b ⋆ c) = (a ⋆ (b ⋆ c)) :=
begin
    unfold star,
    repeat {rw ← fract},
    rw fract_eq_fract,
    let z : ℤ := _,
    use z,
    repeat {rw fract},
    ring,
    norm_cast,
    --thanks Reid!
end

lemma zero_in_star_set : (0 : ℝ) ∈ star_set :=
begin
    unfold star_set,
    split,
    by refl,
    exact zero_lt_one,
end

lemma star_identity_is_zero {a : ℝ} (ha : a ∈ star_set) : (a ⋆ 0) = a :=
begin
    unfold star,
    unfold star_set at ha,
    cases ha with h0 h1,
    rw add_zero,
    rw ← fract,
    have h2 := fract_nonneg a,
    have h3 := fract_lt_one a,
    rw fract_eq_iff,
    split,
    {exact h0},
    {split,
        {exact h1},
        {use 0, exact sub_self a},
    },
end

lemma star_inverses {a : ℝ} (ha : a ∈ star_set) : ∃ (b : ℝ), (a ⋆ b) = (0 : ℝ) ∧ b ∈ star_set :=
begin
    by_cases (a = 0),
    {   rw h,
        use (0 : ℝ),
        split,
        unfold star,
        rw ← fract,
        rw add_zero,
        exact fract_zero,
        rw h at ha,
        exact ha
    },
    {   use (1 - a),
        split,
        {
            unfold star,
            rw add_comm,
            rw sub_add,
            rw sub_self,
            rw sub_zero,
            simp
        },
        {
            unfold star_set,
            unfold star_set at ha,
            cases ha with h0 h1,
            have h2 : 0 < a := by {
                rw lt_iff_le_and_ne,
                split,
                {exact h0},
                {exact ne.symm h},
            },
            split,
            {   
                apply le_of_lt,
                apply lt_sub_right_of_add_lt,
                rw zero_add,
                exact h1,
            },
            {
                apply sub_lt_self,
                exact h2,
            },
        },
    }
end
#lint

end star_group

section my_group

universe u
/- Prove that (a\_1a_2···a_n)^-1 = a_n^−1···a_2^−1a_1^−1 
for all a_1,a_2,···,a_n ∈G -/
-- use rcases here cause I guess it does inductive magic <3

--(list.map a (list.range n)), where (a : ℕ → G)

variables (G : Type*) [group G] (a : G)

lemma inv_prod' {G : Type*} [group G] (l : list G) :
(l.prod)⁻¹ = (list.map (λ (x : G), x⁻¹) l.reverse).prod :=
begin
    induction l with hd tl h,
    simp only [one_inv, list.prod_nil, list.map, list.reverse_nil],
    simp only [h, list.reverse_cons, mul_inv_rev, mul_one, list.map_append, list.prod_append, list.prod_cons, list.prod_nil, list.map],
end


/-Let x be an element of G.  Prove that if
|x|=n for some positive integer n then x^−1 = x^n−1 -/
/-lemma gpow_eq_mod_order_of' {i : ℤ} : a ^ i = a ^ (i % order_of a) :=
calc a ^ i = a ^ (i % order_of a + order_of a * (i / order_of a)) :
    by rw [int.mod_add_div]
  ... = a ^ (i % order_of a) :
    by simp [gpow_add, gpow_mul, pow_order_of_eq_one]-/




end my_group
