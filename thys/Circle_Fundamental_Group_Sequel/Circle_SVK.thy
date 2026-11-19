theory Circle_SVK
  imports Circle_Radial_Retract "Seifert-Van-Kampen.Seifert_Van_Kampen"
begin

section \<open>Seifert--van Kampen interface\<close>

text \<open>
  The substantial open-cover construction lives in the AFP
  \<open>Seifert-Van-Kampen\<close> entry.  This theory makes that result a named layer
  of this development, so later circle and punctured-plane applications can depend on
  the established carrier-level fundamental-group interface.
\<close>

context classical_svk_setup
begin

theorem sequel_classical_seifert_van_kampen:
  "bij_betw classical_svk_quotient_map (fundamental_group_space W x0)
    (carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2)"
  by (rule classical_seifert_van_kampen_bij_betw)

end

context topological_svk
begin

interpretation sequel_svk:
  carrier_svk_encode_decode_interface
    G1 G2 H i1 i2 mult1 one1 mult2 one2 encode svk_decode
  by (rule svk_locale)

theorem sequel_topological_seifert_van_kampen:
  "bij_betw sequel_svk.carrier_svk_quotient_map UNIV
    (carrier_full_amalgamated_free_product_space G1 G2 H i1 i2 mult1 one1 mult2 one2)"
  by (rule sequel_svk.carrier_seifert_van_kampen_bij_betw)

end

end
