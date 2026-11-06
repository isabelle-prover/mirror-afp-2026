theory Finite_Dimensional_Towers
  imports Tower_Bases
    Scalar_Restriction_Bridge
begin

section \<open>Dimension in a tower\<close>

context indexed_algebra_tower
begin

theorem finite_rank_tower:
  "card (range tower_basis) = card (range lower_basis) * card (range upper_basis)"
proof -
  have tower_card: "card (range tower_basis) = CARD('i \<times> 'j)"
    using card_image tower_basis_inj by blast
  have lower_card: "card (range lower_basis) = CARD('i)"
    using card_image lower_basis_inj by blast
  have upper_card: "card (range upper_basis) = CARD('j)"
    using card_image upper_basis_inj by blast
  show ?thesis
    by (simp add: tower_card lower_card upper_card)
qed

end

locale indexed_field_tower =
  indexed_algebra_tower rS sA rA lower_basis upper_basis
  for rS :: "'r::field \<Rightarrow> 's::field \<Rightarrow> 's"
    and sA :: "'s \<Rightarrow> 'a::comm_ring_1 \<Rightarrow> 'a"
    and rA :: "'r \<Rightarrow> 'a \<Rightarrow> 'a"
    and lower_basis :: "'i::finite \<Rightarrow> 's"
    and upper_basis :: "'j::finite \<Rightarrow> 'a"
begin

sublocale lower_space: vector_space rS
  using RS.module_axioms
  by (simp add: module_iff_vector_space)

sublocale upper_space: vector_space sA
  using SA.module_axioms
  by (simp add: module_iff_vector_space)

sublocale direct_space: vector_space rA
  using RA.module_axioms
  by (simp add: module_iff_vector_space)

theorem finrank_tower:
  "direct_space.dim UNIV =
    lower_space.dim UNIV * upper_space.dim UNIV"
proof -
  have lower_dim:
    "card (range lower_basis) = lower_space.dim UNIV"
    by (rule lower_space.basis_card_eq_dim)
      (simp_all add: lower_basis_span lower_basis_independent)
  have upper_dim:
    "card (range upper_basis) = upper_space.dim UNIV"
    by (rule upper_space.basis_card_eq_dim)
      (simp_all add: upper_basis_span upper_basis_independent)
  have direct_dim:
    "card (range tower_basis) = direct_space.dim UNIV"
    by (rule direct_space.basis_card_eq_dim)
      (simp_all add: tower_basis_span tower_basis_independent)
  show ?thesis
    using finite_rank_tower
    by (simp add: lower_dim upper_dim direct_dim)
qed

end

text \<open>
The carrier-based formulation permits the top carrier to be a vector
subspace, including the zero space; it does not assume that the top carrier
is a field.  The two finite-basis assumptions express finite dimensionality
of the intermediate field over the base and of the vector space over the
intermediate field.
\<close>

context scalar_restriction_tower
begin

corollary embedded_field_dimension_tower:
  assumes "\<exists>B. lower.basis B" "\<exists>C. upper.basis C"
  shows "\<exists>P. direct.basis P"
    and "direct.dimension = lower.dimension * upper.dimension"
  using finite_dimension_tower[OF assms] .

end

end
