section \<open>Type consistency for environments and states\<close>
theory TypeSafe_Def
  imports TypeSafe_Memory TypeSafe_Storage

begin

subsection \<open>Ensuring unique locations\<close>

text \<open>No two entries of a @{const Denvalue} map share a location.\<close>

definition unique_locations :: "(String.literal, type \<times> denvalue) fmap \<Rightarrow> bool" where
  "unique_locations denval = (\<forall>x y. x |\<in>| fmran denval \<and> y |\<in>| fmran denval \<and> snd x = snd y \<longrightarrow> x = y)"


text \<open>If an environment has unique locations, two entries of its @{const Denvalue}
with the same location are equal. Hence no two variables share a location.\<close>
lemma uniqueLocs:
  assumes "unique_locations (Denvalue ev)"
    and "x |\<in>| fmran (Denvalue ev)"
    and "y |\<in>| fmran (Denvalue ev)"
    and "snd x = snd y"
  shows "x = y" using assms unique_locations_def by blast


subsubsection \<open>Pushing to the stack maintains stackLocations\<close>

lemma stackPushToplocSafe:
  assumes "lessThanTopLocs k"
    and "k' = push p k"
  shows "lessThanTopLocs k'" unfolding lessThanTopLocs_def
proof(intros)
  fix tloc loc
  assume **:"Toploc k' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
  have a120:"Toploc k<Toploc k'" using assms by (simp add:push_def allocate_def updateStore_def accessStore_def)
  have a125:"tloc \<noteq> Toploc k" using "**" a120 by auto
  then have a126:"(ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))"
    by (metis Read_Show_nat'_id)
  have a130:"\<forall>tloc loc. Toploc k \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc k = None"
    using assms(1) unfolding lessThanTopLocs_def by simp
  have a140:"k' = (let s = updateStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) p k in snd (allocate s))" unfolding push_def assms(2) by auto
  then have acces:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) \<longrightarrow> accessStore locs k' = accessStore locs k" unfolding accessStore_def updateStore_def
    by (simp add:push_def allocate_def updateStore_def accessStore_def split:if_split_asm)
  have a150:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) k = None" using a130 a120 **
    by (metis LSubPrefL2_def dual_order.strict_trans1 nless_le)
  then show "accessStore loc k' = None"
  proof(cases "loc = (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)")
    case True
    then show ?thesis using acces a150 a126 by simp
  next
    case False
    then show ?thesis using acces a150 a126 ShowLNatDot
      by (metis "**" LSubPrefL2_def a120 a130 hash_inequality hash_int_prefix hash_suffixes_associative nat_less_le order_less_le_trans)
  qed
next
  fix loc y
  assume *:"accessStore loc k' = Some y"
  have a140:"k' = (let s = updateStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) p k in snd (allocate s))" unfolding push_def assms(2) by auto
  then have acces:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) \<longrightarrow> accessStore locs k' = accessStore locs k" unfolding accessStore_def updateStore_def
    by (simp add:push_def allocate_def updateStore_def accessStore_def split:if_split_asm)
  have " \<exists>tloc<Toploc k'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
  proof(cases "loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))")
    case True
    have a10:"Toploc k < Toploc k'" using a140 unfolding allocate_def updateStore_def by simp
    have "LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))" using True LSubPrefL2_def by simp
    have "\<forall>l. l\<noteq>(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) \<longrightarrow> \<not>(LSubPrefL2
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) l)" using ShowLNatDot unfolding LSubPrefL2_def hash_def
      using subPrefCannotBeInt by auto
    then show ?thesis using True a10 assms
      using LSubPrefL2_def by auto
  next
    case False
    have "((\<forall>tloc loc. Toploc k \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc k = None)
          \<and> (\<forall>loc y. accessStore loc k = Some y \<longrightarrow> (\<exists>tloc<Toploc k. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
      using assms lessThanTopLocs_def[of k] by blast
    then obtain tloc where tlocdef:"tloc < Toploc k \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using False * acces by metis
    moreover have "Toploc k < Toploc k'" using a140 unfolding allocate_def updateStore_def by simp
    ultimately show ?thesis using assms lessThanTopLocs_def[of k] * tlocdef
      using order.strict_trans by auto
  qed
  then show "\<exists>tloc<Toploc k'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" by simp
qed

lemma lessThanSome_imps_Locs:
  assumes "lessThanTopLocs mem"
    and "accessStore p' mem = Some y"
    and "LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
  shows "x < Toploc mem"
proof(cases "p' = (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
  case True
  have a10:"\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None"
    using assms(1) unfolding lessThanTopLocs_def by simp

  have a20:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t x) mem = Some y" using assms(2) True by simp
  have "ReadL\<^sub>n\<^sub>a\<^sub>t(ShowL\<^sub>n\<^sub>a\<^sub>t x) = x" using Read_Show_nat'_id by auto
  have "x < Toploc mem" using a10 a20
    by (metis LSubPrefL2_def linorder_le_less_linear option.discI)
  then have "LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t x) (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> x < Toploc mem" unfolding LSubPrefL2_def by simp
  then show ?thesis using True by simp
next
  case False
  have a10:"\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None"
    using assms(1) unfolding lessThanTopLocs_def by simp
  then obtain i where a20:"(p' = hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i)" using assms(3) False unfolding LSubPrefL2_def by blast
  then have a20:"accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i) mem = Some y" using assms(2) by simp
  have "x < Toploc mem" using a10 a20
    by (metis LSubPrefL2_def linorder_le_less_linear option.discI)
  then show ?thesis by blast
qed

lemma lessThanSome_imps_Locs_hash:
  assumes "lessThanTopLocs mem"
    and " accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some y"
    and "LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
  shows "x < Toploc mem"
proof(cases "p' = (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
  case True
  have a10:"\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None"
    using assms(1) unfolding lessThanTopLocs_def by simp

  have a20:"accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some y" using assms(2) True by simp
  have "ReadL\<^sub>n\<^sub>a\<^sub>t(ShowL\<^sub>n\<^sub>a\<^sub>t x) = x" using Read_Show_nat'_id by auto
  have "x < Toploc mem" using a10 a20
    by (metis LSubPrefL2_def True assms(1) lessThanSome_imps_Locs)
  then have "LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t x) (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> x < Toploc mem" unfolding LSubPrefL2_def by simp
  then show ?thesis using True by simp
next
  case False
  have a10:"\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None"
    using assms(1) unfolding lessThanTopLocs_def by simp
  then obtain i' where a20:"(p' = hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i')" using assms(3) False unfolding LSubPrefL2_def by blast
  then have a20:"accessStore (hash (hash (ShowL\<^sub>n\<^sub>a\<^sub>t x) i') (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some y" using assms(2) by simp
  have "x < Toploc mem" using a10 a20
    by (metis LSubPrefL2_def assms(1) hash_suffixes_associative lessThanSome_imps_Locs)
  then show ?thesis by blast
qed

lemma subPtrs_nonTop:
  assumes "MCon (MTArray x11' x12') mem stl1"
    and "(\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None)"
    and "(\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<longrightarrow> accessStore locs mem' = accessStore locs mem"
    and "TypedMemSubPrefPtrs mem' x11' x12' stl1 dloc1"
  shows "\<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
proof(cases x12')
  case (MTArray x11 x12)
  then obtain i l where idef:"i<x11' \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs mem' x11 x12 l dloc1)"
    using assms by auto
  have "\<not> LSubPrefL2 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem))" using assms(1,2) LSubPrefL2_def
    by (metis MConArrayPointers MTArray gr_zeroI idef le_refl less_nat_zero_code option.discI)
  then have mconl:"MCon (MTArray x11 x12) mem l" using assms(1,4) MTArray idef
    by (metis MCon_imps_sub_Mcon)
  then have lsubloc:"\<not> LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using assms(2) LSubPrefL2_def hash_suffixes_associative mconl idef
    by (metis (no_types, lifting) MCon_imps_Some le_refl option.discI)
  show ?thesis
  proof
    assume *:"LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
    show False
    proof(cases "l = dloc1")
      case True
      then show ?thesis using "*" lsubloc by blast
    next
      case False
      then have lneq2:"\<forall>i<x11. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> dloc1" using mconl lsubloc idef assms(3,4)
        using "*" MemLSubPrefL2_specific_imps_general by blast
      then have "TypedMemSubPrefPtrs mem' x11 x12 l dloc1" using idef False by blast
      then show ?thesis using lneq2 lsubloc mconl
      proof(induction x12 arbitrary:x11 l)
        case (MTArray x1 x12')
        have "\<exists>i'<x11. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l') \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' dloc1)"
          using MTArray(2) unfolding TypedMemSubPrefPtrs.simps by simp
        then obtain i' l' where i'def:"i'<x11 \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l')
            \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' dloc1)" by blast
        then have mconl':"MCon (MTArray x1 x12') mem l'" using assms(4) MTArray(5)
          by (metis MCon_imps_sub_Mcon MTArray.prems(3) MemLSubPrefL2_specific_imps_general)
        have l'neq:"l' \<noteq> dloc1"
          using "*" AllPtrsNotTop_MCon assms(2,3) lessThanTopLocs_def mconl' by blast
        then have "TypedMemSubPrefPtrs mem' x1 x12' l' dloc1" using i'def by simp
        then have l'subloc:"\<not> LSubPrefL2 l' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using l'neq assms i'def mconl'
          using AllPtrsNotTop_MCon lessThanTopLocs_def by blast
        moreover have "\<forall>i<x1. hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> dloc1" using l'subloc
          using "*" MemLSubPrefL2_specific_imps_general by blast
        ultimately show ?case using MTArray.IH[of x1 l'] i'def
          using l'neq mconl' by blast
      next
        case (MTValue x)
        then show ?case by auto
      qed
    qed
  qed
next
  case (MTValue x2)
  then show ?thesis using assms(1,2,5) by fastforce
qed

lemma PreExistMconNotChangeByToploc:
  assumes "(\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
    and "(\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None)"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem)) \<or> locs =
        (ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem)) \<longrightarrow> accessStore locs mem = accessStore locs m"
    and "MCon tp1 mem stl1"
  shows "MCon tp1 m stl1" using assms(4)
proof(induction tp1 arbitrary: stl1)
  case (MTArray x1 struct)
  then have accessSome:"\<forall>i'<x1. \<exists>y. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = Some y"
    by (metis bot_nat_0.not_eq_extremum less_nat_zero_code mcon_accessStore)
  moreover have accessSame:"\<forall>i'<x1. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m" using calculation
    by (metis Read_Show_nat'_id antisym_conv1 assms(2,3) option.distinct(1) readLintNotEqual)

  have "\<forall>i<x1.
(case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
  | Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct m (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
  | Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct m loc2 | MTValue Types \<Rightarrow> False))"
  proof intros
    fix i' assume asm3:"i'<x1"
    show "case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m of None \<Rightarrow> False
        | Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct m (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')))
        | Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct m loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases "accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m")
      case None
      then show ?thesis using accessSome accessSame asm3 by auto
    next
      case (Some a)
      then show ?thesis
      proof(cases a)
        case (MValue x1')
        then show ?thesis using accessSome accessSame Some asm3 MTArray by (cases struct; auto)
      next
        case (MPointer x2)
        then have "MCon struct mem x2" using accessSome accessSame Some asm3 MTArray
          by (metis MconSameTypeSameAccessWithTyping)
        then have "MCon struct m x2" using MTArray by simp
        then show ?thesis using accessSome accessSame Some asm3 MTArray MPointer by (cases struct; auto)
      qed
    qed
  qed
  moreover have "x1>0" using MTArray(2) unfolding MCon.simps by presburger
  moreover have "(\<exists>p. accessStore stl1 m = Some (MPointer p)) \<or> accessStore stl1 m = None" using calculation(3) MTArray unfolding MCon.simps
    by (metis accessSome lessThanSome_imps_Locs_hash lessThanTopLocs_def assms(1,2,3) nat_less_le )
  ultimately show ?case using MCon.simps(2)[of x1 struct m ] by simp
next
  case (MTValue x')
  then show ?case
    by (metis MCon.simps(1) assms(2,3) case_optionE le_refl option.discI)
qed

subsection \<open>Balances and message values conform\<close>
definition balanceTypes :: "accounts \<Rightarrow> bool" where
  "balanceTypes acc = (\<forall>adv. typeCon (TUInt b256) (Bal (acc adv)))"

definition addressFormat::"address \<Rightarrow> bool"
  where "addressFormat cur = (typeCon TAddr cur)"

abbreviation envAddressesWellFormed :: "environment \<Rightarrow> bool" where
  "envAddressesWellFormed ev \<equiv> addressFormat (Address ev) \<and> addressFormat (Sender ev)"

definition svalueTypes :: "valuetype \<Rightarrow> bool" where
  "svalueTypes sval = typeCon (TUInt b256) sval"

subsection \<open>Compatible pointers\<close>


text \<open>Arguments: parent type, parent location, sub-prefix type, sub-prefix location.\<close>
primrec Subpref :: "stypes \<Rightarrow> location \<Rightarrow> stypes \<Rightarrow> location \<Rightarrow> bool"
  where
    "Subpref (STValue typ) Modulatedparent typ2 subloc = ((Modulatedparent = subloc) \<and> typ2 = (STValue typ))"
  |"Subpref (STArray len arr) Modulatedparent typ2 subloc = (((STArray len arr) = typ2 \<and> Modulatedparent = subloc)
                                                        \<or> ( \<exists>i::nat. i < len \<and> Subpref arr (hash Modulatedparent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) typ2 subloc))"
  |"Subpref (STMap fromTyp toTyp) Modulatedparent typ2 subloc = (((STMap fromTyp toTyp) = typ2 \<and> Modulatedparent = subloc)
                                                            \<or>(\<exists>i::String.literal. (typeCon fromTyp i) \<and> Subpref toTyp (hash Modulatedparent i) typ2 subloc))"


lemma "\<not>Subpref (STArray 3 (STValue TBool)) (STR ''1.5'') (STValue TBool) (STR ''4.1.5'')" using Subpref.simps hash_def by simp? eval
lemma "Subpref (STArray 5 (STValue TBool)) (STR ''1.5'') (STValue TBool) (STR ''1.1.5'')" using Subpref.simps hash_def by simp? eval
lemma "Subpref (STArray 5 (STArray 4 (STArray 3 (STValue TBool)))) (STR ''1.5'') ((STValue TBool)) (STR ''1.1.1.1.5'') " using Subpref.simps hash_def by simp? eval
lemma "Subpref (STArray 5 (STArray 4 (STArray 3 (STValue TBool)))) (STR ''1.5'') ((STArray 3 (STValue TBool))) (STR ''1.1.1.5'') " using Subpref.simps hash_def by simp? eval

text \<open>The value stored for one variable of the environment conforms to its declared type.\<close>

abbreviation denvalueCon :: "stack \<Rightarrow> memoryT \<Rightarrow> storageT \<Rightarrow> calldataT \<Rightarrow> type \<Rightarrow> denvalue \<Rightarrow> bool"
  where "denvalueCon sck mem sto cd t l \<equiv>
    (case l of Stackloc loc \<Rightarrow>
       (case accessStore loc sck of None \<Rightarrow> False
        | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
        | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
        | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct mem stloc | _ \<Rightarrow> False)
        | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc sto | _ \<Rightarrow> False))
     | Storeloc loc \<Rightarrow> (case t of type.Storage typ \<Rightarrow> SCon typ loc sto | _ \<Rightarrow> False))"

definition typeCompat::"(String.literal, type \<times> denvalue) fmap \<Rightarrow> stack \<Rightarrow> memoryT \<Rightarrow> storageT \<Rightarrow> calldataT \<Rightarrow> bool"
  where "typeCompat den sckO mem sto cd = (\<forall>t l. (t, l) |\<in>| fmran (den) \<longrightarrow> denvalueCon sckO mem sto cd t l)"

subsection \<open>Supplementary lemmas\<close>
text \<open>Collection of lemmas which shorten common proof obligations\<close>

text \<open>Support functions to simplify the typeCon expressions definition \<close>
fun extractValueType :: "stackvalue \<Rightarrow> valuetype" where
  "extractValueType (KValue v) = v"
| "extractValueType (KCDptr v) = v"
| "extractValueType (KMemptr v) = v"
| "extractValueType (KStoptr v) = v"

text \<open>A value of a given type is consistent with calldata, memory, and storage.\<close>

abbreviation valueCon :: "environment \<Rightarrow> calldataT \<Rightarrow> state \<Rightarrow> stackvalue \<Rightarrow> type \<Rightarrow> bool"
  where "valueCon ev cd st v t \<equiv>
    (case t of Value typ \<Rightarrow> typeCon typ (extractValueType v)
     | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v)
     | type.Memory struct \<Rightarrow> MCon struct (Memory st) (extractValueType v)
     | type.Storage struct \<Rightarrow> SCon struct (extractValueType v) (Storage st (Address ev)))"

text \<open>The result of evaluating an expression is consistent with its type and, for
  pointers, is related to a variable of the environment: calldata and memory
  pointers reach the value through a stack variable, storage pointers through a
  storage variable.\<close>

abbreviation exprResultCon :: "environment \<Rightarrow> calldataT \<Rightarrow> state \<Rightarrow> stackvalue \<Rightarrow> type \<Rightarrow> bool"
  where "exprResultCon ev cd st v t \<equiv>
    (case t of Value typ \<Rightarrow> typeCon typ (extractValueType v) \<and> (\<exists>xx. v = KValue xx)
     | Calldata struct \<Rightarrow> MCon struct cd (extractValueType v) \<and> (\<exists>xx. v = KCDptr xx) \<and>
         (\<exists>stloc tp'' p. (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
            accessStore stloc (Stack st) = Some (KCDptr p) \<and>
            (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and>
               tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))
     | type.Memory struct \<Rightarrow> MCon struct (Memory st) (extractValueType v) \<and> (\<exists>xx. v = KMemptr xx) \<and>
         (\<exists>stloc tp'' p. (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
            accessStore stloc (Stack st) = Some (KMemptr p) \<and>
            (tp'' = struct \<and> v = KMemptr p \<or> (\<exists>len arr. extractValueType v \<noteq> p \<and>
               tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))
     | type.Storage struct \<Rightarrow> SCon struct (extractValueType v) (Storage st (Address ev)) \<and>
         (\<exists>xx. v = KStoptr xx) \<and>
         (\<exists>stloc tp''. (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue ev) \<and>
            (tp'' = struct \<and> v = KStoptr stloc \<or>
             extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))"


locale typesafe_base = statement_with_gas +
  assumes methodVarsNoPref: "\<forall>c ct dud i1 i2 t1 t2. i1 \<noteq> i2 \<and> ep $$ c = Some(ct,dud) \<and> ct $$ i1 = Some (Var t1) \<and> ct $$ i2 = Some (Var t2)
                              \<longrightarrow> (\<not>TypedStoSubpref i1 i2 t2) \<and> (\<not>TypedStoSubpref i2 i1 t1)"

context typesafe_base
begin

text \<open>An environment and state are fully initialised if the contract has an
  initialised account and all contract variables are bound in the @{const Denvalue}.
  These are the first steps when creating a new environment (see statement \<open>NEW\<close>).\<close>

definition fullyInitialised::"environment \<Rightarrow> accounts \<Rightarrow> stack \<Rightarrow> bool"
  where "fullyInitialised env acc sk = (
(\<exists>c ct dud.
          Type (acc (Address env)) = Some (atype.Contract c) \<and>
          Contract env = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. ct $$ id = Some (Var v) \<longleftrightarrow>
                  Denvalue env $$ id = Some (type.Storage v, Storeloc id)) \<and>
          (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>

          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
              accessStore l sk = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and>
                       CompStoType t' t l' p)))


)"

lemma test_not_vacuous:
  fixes my_contract :: "String.literal"
  fixes n :: "stypes"
  assumes blueprint_def: "my_blueprint = fmupd (STR ''balance'') (Var n) fmempty"
  assumes ep_def: "ep $$ my_contract = Some (my_blueprint, dud)"

  shows "\<exists>env acc sk. fullyInitialised env acc sk \<and>
                      Denvalue env $$ (STR ''balance'') = Some (type.Storage n, Storeloc (STR ''balance''))"
proof -
  let ?addr = "STR ''A''"
  let ?den = "fmupd (STR ''balance'') (type.Storage n, Storeloc (STR ''balance'')) fmempty"
  let ?env = "(emptyEnv ?addr my_contract (STR '''') (STR ''''))\<lparr>Denvalue := ?den\<rparr>"
  let ?acc = "emptyAccount(?addr := emptyAcc\<lparr>Type := Some (atype.Contract my_contract)\<rparr>)"

  have map_eq: "\<And>i v. my_blueprint $$ i = Some (Var v) \<longleftrightarrow>
                    Denvalue ?env $$ i = Some (type.Storage v, Storeloc i)"
    using blueprint_def by simp

  have loc_eq: "\<And>id v loc.
      Denvalue ?env $$ id = Some (type.Storage v, Storeloc loc) \<Longrightarrow> id = loc"
    using fmlookup by (simp split:if_splits)

  have ptr_vacuous: "\<And>t l p.
      (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue ?env) \<and>
      accessStore l emptyStore = Some (KStoptr p)
      \<Longrightarrow> (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue ?env) \<and> CompStoType t' t l' p)"
    by (simp add: accessStore_def emptyStore_def)

  have fi: "fullyInitialised ?env ?acc emptyStore"
    unfolding fullyInitialised_def
    using ep_def map_eq loc_eq ptr_vacuous
    by (intro exI[of _ my_contract] exI[of _ my_blueprint] exI[of _ dud]) simp

  moreover have "Denvalue ?env $$ (STR ''balance'') =
      Some (type.Storage n, Storeloc (STR ''balance''))"
    by simp
  ultimately show ?thesis
    by blast
qed


definition AddressTypes :: "accounts \<Rightarrow> bool" where
    "AddressTypes ac =
      (\<forall>adv. case Type (ac adv) of
               Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep
             | _ \<Rightarrow> True)"

abbreviation accountsWellTyped :: "accounts \<Rightarrow> bool" where
  "accountsWellTyped acc \<equiv> balanceTypes acc \<and> AddressTypes acc"


definition safeContract :: "accounts \<Rightarrow> (address \<Rightarrow> storageT) \<Rightarrow> bool" where
  "safeContract acc sto =
    (\<forall>e ct dud i tp.
      Type (acc (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
      ep $$ Contract e = Some (ct, dud) \<and>
      fmlookup ct i = Some (Var tp)
      \<longrightarrow> SCon tp i (sto (Address (e::environment))))"

text \<open>@{const safeContract} depends on the accounts only through their types.\<close>

lemma safeContract_Type_cong:
  assumes "safeContract acc sto"
    and "\<forall>a. Type (acc' a) = Type (acc a)"
  shows "safeContract acc' sto"
  using assms unfolding safeContract_def by simp


subsection \<open>Type consistency for reachable locations\<close>

text \<open>This property ensures that the types stored in the typed mapping
of memory are consistent with the types derivable from the denvalue for locations
that are reachable from variables in the environment.\<close>

definition denvalueTypeCorrectness :: "environment \<Rightarrow> stack \<Rightarrow> memoryT \<Rightarrow> bool"
  where
    "denvalueTypeCorrectness env sck mem =
    (\<forall>t l ptr_loc. (type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
        accessStore l sck = Some (KMemptr ptr_loc) \<longrightarrow>
        (case t of MTArray len arr \<Rightarrow>
                (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr)
          | MTValue val \<Rightarrow> accessTypeStore ptr_loc mem = Some (MTValue val))
      )"

definition subPrefixStructuralConsistency :: "memoryT \<Rightarrow> bool"
  where
    "subPrefixStructuralConsistency mem =
      (\<forall>locs tp. accessTypeStore locs mem = Some tp \<longrightarrow>
          (case accessStore locs mem of Some (MPointer p) \<Rightarrow>
               (\<exists>len arr. MCon tp mem p \<and> tp = MTArray len arr
                  \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr)
                )
           | Some (MValue v) \<Rightarrow>
               (\<exists>val. MCon tp mem locs \<and> tp = MTValue val \<and>accessTypeStore locs mem = Some tp)
           | None \<Rightarrow> False))"

definition SomeValSomeTyp:: "memoryT \<Rightarrow> bool"
  where
    "SomeValSomeTyp mem = (\<forall>locs. (\<exists>t. accessStore locs mem = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore locs mem = Some tt))"

subsection \<open>Typesafe environments\<close>
text \<open>@{text TypeSafe} states that an environment, accounts, stack, memory, storage,
  and calldata are mutually type-consistent. It combines two groups of properties:
  \<^enum> structural properties of the environment and stores, such as unique locations,
    compatible pointers, and bounded locations;
  \<^enum> value conformance: for every variable in the @{const Denvalue}, the string
    representation of its value conforms to its declared type.\<close>
definition TypeSafe :: "environment \<Rightarrow> accounts \<Rightarrow> stack \<Rightarrow> memoryT \<Rightarrow> (address \<Rightarrow> storageT) \<Rightarrow> calldataT \<Rightarrow> bool"
  where "TypeSafe ev acc sck mem sto cd= (
          typeCompat (Denvalue ev) sck mem (sto (Address ev)) cd \<and>
          (unique_locations (Denvalue ev)) \<and>
          (compPointers sck (Denvalue ev)) \<and>
          (lessThanTopLocs sck) \<and> (lessThanTopLocs mem) \<and> (lessThanTopLocs cd) \<and>
          envAddressesWellFormed ev \<and>
          accountsWellTyped acc \<and>
          (safeContract acc sto) \<and>
          (svalueTypes (Svalue ev)) \<and>
          denvalueTypeCorrectness ev sck mem \<and>
          subPrefixStructuralConsistency mem \<and>
          SomeValSomeTyp mem)"


text \<open>Memory of a type-safe state holds values only below its top location.\<close>

lemma TypeSafe_memory_bounds:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))"
    and "\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem = None"
  using assms unfolding TypeSafe_def lessThanTopLocs_def by simp_all

subsection \<open>All stack locations in the denvalue have a value in the stack\<close>
lemma typeSafeAllStacklocsExist:
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(t, l2) |\<in>| fmran (Denvalue ev)"
    and "l2 = Stackloc l"
  shows "\<exists>v. accessStore l sck = Some v"
proof -
  have "\<forall>t l. (t, l) |\<in>| fmran (Denvalue ev) \<longrightarrow>
        (case l of (Stackloc loc) \<Rightarrow>
          (case (accessStore loc sck) of
            Some(KValue val) \<Rightarrow> (case t of (Value typ) \<Rightarrow> typeCon typ val | _ \<Rightarrow> False )
          | Some(KMemptr stloc) \<Rightarrow> (case t of (type.Memory struct) \<Rightarrow> MCon struct mem stloc | _ \<Rightarrow> False)
          | Some(KCDptr stloc) \<Rightarrow> (case t of (Calldata struct) \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
          | Some(KStoptr stloc) \<Rightarrow> (case t of (type.Storage struct) \<Rightarrow> SCon struct stloc (sto (Address ev)) | _ \<Rightarrow> False)
          | _ \<Rightarrow> False)
        | (Storeloc loc) \<Rightarrow> (case t of (type.Storage typ) \<Rightarrow> SCon typ loc (sto (Address ev)) | _ \<Rightarrow> False))"
    using assms(1) unfolding TypeSafe_def typeCompat_def by simp
  then have "case l2 of (Stackloc loc) \<Rightarrow> \<exists>v. accessStore loc sck = Some v"
    using assms(2) assms(3) denvalue.simps(5) case_optionE by fastforce
  then show ?thesis using assms(3) by simp
qed


subsection \<open>@{const astack} preserves unique locations\<close>
lemma updateEnvUniqueLocs:
  assumes "TypeSafe ev' (Accounts st) sck' mem' (Storage st) cd'"
    and "(k',e) = astack ip (v) (p) (sck', ev')"
  shows "unique_locations (Denvalue e)" unfolding unique_locations_def
proof(intros)
  have a10:"e = (updateEnv ip (v) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev')" using assms(2) by simp
  then have a15:"Denvalue e = Denvalue(ev' \<lparr> Denvalue := fmupd ip ((v),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) (Denvalue ev') \<rparr>)" by simp
  then have a17:"(Denvalue e) $$ ip = Some ((v),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp
  have a20:"unique_locations (Denvalue ev')" using assms(1) TypeSafe_def by simp
  have a30:"lessThanTopLocs sck'" using assms(1) TypeSafe_def by simp
  fix x' y
  assume aULoc:"x' |\<in>| fmran (Denvalue e) \<and> y |\<in>| fmran (Denvalue e) \<and> snd x' = snd y"
  then have a40:" (\<forall>tloc loc. Toploc sck' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow>
      accessStore loc sck' = None)" using lessThanTopLocs_def Read_Show_nat'_id a30 by auto
  then have "\<forall>x y. \<not>((Denvalue ev') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" using TypeSafe_def assms typeSafeAllStacklocsExist fmranI a40
    by (metis LSubPrefL2_def nle_le option.distinct(1) prod.exhaust_sel)
  then have a50:"\<forall>x' y. ((Denvalue e) $$ x' = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))
      \<longrightarrow> x' = ip \<and> (fst y) = (v)" using a30 a15 fmranI by auto
  show "x' = y"
  proof(cases "snd x' = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))")
    case True
    then obtain x'' where "(Denvalue e) $$ x'' = Some x'" using fmranI aULoc by auto
    then have "x'' = ip" using a50 True by blast
    then show ?thesis using a50 aULoc True by (metis fmlookup_ran_iff prod_eq_iff)
  next
    case False
    then obtain x'' where a140:"(Denvalue e) $$ x'' = Some x'" using fmranI aULoc by auto
    then have a150:"x'' \<noteq> ip" using a50 False a17 by (metis option.inject snd_conv)
    have a160:"\<forall>x y. x \<noteq> ip \<and> (Denvalue e) $$ x = Some y \<longrightarrow> (Denvalue ev') $$ x = Some y" using a15 by simp
    then have "(Denvalue ev') $$ x'' = Some x'" using a140 a150 by blast
    then show ?thesis using aULoc a20 unique_locations_def False a160 a17 by (metis fmranE fmranI option.inject snd_conv)
  qed
qed

lemma sameMemTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((type.Memory struct), (Stackloc loc)) |\<in>| fmran (Denvalue ev) \<and> accessStore loc sck = Some (KMemptr stloc) \<longrightarrow> MCon struct mem stloc"
  using assms unfolding TypeSafe_def typeCompat_def by fastforce

lemma sameStoLocTSafe:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "\<forall>struct loc. ((type.Storage struct), (Storeloc loc)) |\<in>| fmran (Denvalue ev) \<longrightarrow> SCon struct loc (sto (Address ev))" using assms
  unfolding TypeSafe_def typeCompat_def by fastforce

lemma typeSafeUnique:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "unique_locations (Denvalue ev)" using assms unfolding TypeSafe_def by simp

lemma typeSafeAccounts:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "balanceTypes acc" using assms unfolding TypeSafe_def by simp

lemma typeSafeEnvAddresses:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "envAddressesWellFormed ev" using assms unfolding TypeSafe_def by simp

lemma typeSafeSvalue:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "svalueTypes (Svalue ev)" using assms unfolding TypeSafe_def by simp

lemma typeSafeCompPointers:
  assumes "TypeSafe ev acc sck mem sto cd"
  shows "compPointers sck (Denvalue ev)" using assms unfolding TypeSafe_def by simp

lemma lexp_stackloc_imps_id:
  assumes "lexp lv env cd st g = Normal ((LStackloc l2, t'), g')"
  shows "\<exists>i. lv = Id i"
proof (cases lv)
  case (Id i)
  then show ?thesis by auto
next
  case (Ref i r)
  then have "lexp (Ref i r) env cd st g =
    (case Denvalue env $$ i of None \<Rightarrow> throw Err
     | Some (tp, Stackloc l) \<Rightarrow>
         (case accessStore l (Stack st) of None \<Rightarrow> throw Err
         | Some (KMemptr l') \<Rightarrow> (case tp of type.Memory x \<Rightarrow> return x | _ \<Rightarrow> throw Err) \<bind>
             (\<lambda>t. local.msel True t l' r env cd (st) \<bind> (\<lambda>(l'', t'). return (LMemloc l'', type.Memory t')))
         | Some (KStoptr l') \<Rightarrow> (case tp of type.Storage x \<Rightarrow> return x | _ \<Rightarrow> throw Err) \<bind>
             (\<lambda>t. local.ssel t l' r env cd (st) \<bind> (\<lambda>(l'', t'). return (LStoreloc l'', type.Storage t')))
         | Some _ \<Rightarrow> throw Err)
     | Some (tp, Storeloc l) \<Rightarrow> (case tp of type.Storage x \<Rightarrow> return x | _ \<Rightarrow> throw Err) \<bind>
         (\<lambda>t. local.ssel t l r env cd (st) \<bind> (\<lambda>(l', t'). return (LStoreloc l', type.Storage t'))))
     g" using lexp.simps(2)[of i r env cd st g] Ref by simp
  then have "\<not>(\<exists>l tp. lexp (Ref i r) env cd (st) g = Normal ((LStackloc l, tp), g'))"
    by (auto split: option.splits prod.splits denvalue.split_asm type.splits stackvalue.splits result.splits)
  then have False using assms Ref by simp
  then show ?thesis by simp
qed

lemma lexpDen:
  assumes "lexp lv env cd (st) g = Normal ((LStackloc l2, t'), g')"
    and "lv = Id i"
  shows "(t', Stackloc l2) |\<in>| fmran (Denvalue env)"
proof -
  have "(case (Denvalue env) $$ i of
      Some (tp, (Stackloc l)) \<Rightarrow> return (LStackloc l, tp)
    | Some (tp, (Storeloc l)) \<Rightarrow> return (LStoreloc l, tp)
    | _ \<Rightarrow> throw Err) g = Normal ((LStackloc l2, t'), g')" using lexp.simps(1) assms by auto
  then have "(Denvalue env) $$ i = Some (t', Stackloc l2)" by (simp split: option.split_asm prod.split_asm denvalue.split_asm)
  then show ?thesis using Finite_Map.fmranI[of "(Denvalue env)" i "(t', Stackloc l2)"] by simp
qed

lemma lexpStackloc_imps_inDen:
  assumes "lexp lv env cd (st) g = Normal ((LStackloc l2, t'), g')"
  shows "(t', Stackloc l2) |\<in>| fmran (Denvalue env)" using assms lexpDen lexp_stackloc_imps_id by metis

lemma stackLocs_imp_NotDen:
  assumes "lessThanTopLocs sck'"
    and "TypeSafe ev' (Accounts st) sck' mem' (Storage st) cd'"
  shows "\<forall>x y. (Denvalue ev') $$ x = Some y \<longrightarrow> snd y \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))"
proof -
  have " accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' = None" using lessThanTopLocs_def Read_Show_nat'_id assms(1) using LSubPrefL2_def by auto
  then show ?thesis using assms(2) unfolding TypeSafe_def typeCompat_def using fmranI by fastforce
qed

lemma typeSafe_noDenElementOverToploc_mem:
  assumes " TypeSafe env (Accounts st) (Stack st) mem (Storage st) cd"
    and "((type.Memory struct), (Stackloc loc)) |\<in>| fmran (Denvalue env)"
    and "(accessStore loc (Stack st)) = Some(KMemptr stloc)"
  shows "\<not>LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
proof
  assume *:"LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
  have h1:"((\<forall>tloc loc. Toploc mem \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc)) \<longrightarrow> accessStore loc mem = None) \<and>
   (\<forall>loc y. accessStore loc mem = Some y \<longrightarrow> (\<exists>tloc<Toploc mem. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
    using assms(1) unfolding TypeSafe_def lessThanTopLocs_def by blast
  have h2:"MCon struct mem stloc" using assms unfolding TypeSafe_def typeCompat_def by fastforce
  then show False
    using * h1 MCon_imps_Some lessThanSome_imps_Locs lessThanSome_imps_Locs_hash lessThanTopLocs_def by fast
qed

lemma typeSafeAllPtrsNotTop:
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue ev)"
    and "accessStore l sck = Some (KMemptr ptr)"
  shows "\<forall>tl. tl \<ge> Toploc mem \<longrightarrow>
        (\<not>LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t tl))\<and>
        (\<not>LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t tl) ptr)"
proof intros
  fix tl
  assume *:" Toploc mem \<le> tl"
  have ptrMCon:"MCon t mem ptr" using assms(1,2,3) unfolding TypeSafe_def typeCompat_def by force
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x"
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) mem = None
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def
    using LSubPrefL2_def by blast
  show "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t tl)"
    using LSubPrefL2_def SomeA hash_suffixes_associative noneA *
    by (metis lessThanTopLocs_def option.discI toplocs)
  show "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t tl) ptr" using LSubPrefL2_def MemLSubPrefL2_specific_imps_general *
    using MemLSubPrefTransitive \<open>\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t tl)\<close> by blast

qed

lemma typeSafeAllMemPtrsCantTop:
  assumes "TypeSafe ev acc sck mem sto cd"
  assumes "(type.Memory tp, Stackloc l) |\<in>| fmran (Denvalue ev)"
    and "accessStore l sck = Some (KMemptr ptr)"
  shows "\<forall>len arr loc tl. tl \<ge> Toploc mem \<and> tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem len arr ptr loc \<longrightarrow>
        (\<not>LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tl))\<and>
        (\<not>LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t tl) loc)"
proof intros
  fix len arr loc tl
  assume *:"Toploc mem \<le> tl \<and> tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem len arr ptr loc"
  then have ptrMCon:"MCon (MTArray len arr) mem ptr" using assms(1,2,3) unfolding TypeSafe_def typeCompat_def by fastforce
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x"
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) mem = None
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def
    using LSubPrefL2_def by blast
  show "\<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tl)" using * noneA SomeA
    using assms(1,2,3) ptrMCon
    by (metis LSubPrefL2_def MCon_imps_Some hash_flatten_right lessThanTopLocs_def
        mcon_typedptrs_imps_existence option.discI toplocs)
  then show "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (tl)) loc" using * noneA SomeA LSubPrefL2_def MemLSubPrefL2_specific_imps_general
    by metis
qed

lemma AccessedMemPtrsCantTop:
  assumes "lessThanTopLocs mem"
  shows "\<forall>len arr loc tl. tl \<ge> Toploc mem \<and> tp = MTArray len arr \<and>
        MCon (MTArray len arr) mem ptr \<and> TypedMemSubPrefPtrs mem len arr ptr loc \<longrightarrow>
        (\<not>LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tl))\<and>
        (\<not>LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t tl) loc)"
proof intros
  fix len arr loc tl
  assume *:"Toploc mem \<le> tl \<and> tp = MTArray len arr \<and> MCon (MTArray len arr) mem ptr \<and> TypedMemSubPrefPtrs mem len arr ptr loc"
  then have ptrMCon:"MCon (MTArray len arr) mem ptr" by fastforce
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x"
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) unfolding TypeSafe_def by blast
  then have noneA:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) mem = None
            \<and> (\<forall>locs. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) locs) mem = None)"
    unfolding lessThanTopLocs_def
    using LSubPrefL2_def by blast
  show "\<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tl)" using * noneA SomeA
    using assms(1) ptrMCon
    by (metis LSubPrefL2_def MCon_imps_Some hash_flatten_right lessThanTopLocs_def
        mcon_typedptrs_imps_existence option.discI toplocs)
  then show "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (tl)) loc" using * noneA SomeA LSubPrefL2_def MemLSubPrefL2_specific_imps_general
    by metis
qed

lemma CompMemTypeSubIndexes:
  assumes "CompMemType mem len arr (MTArray x t) pParentPtr p"
    and "subPrefixStructuralConsistency mem"
    and "MCon (MTArray len arr) mem pParentPtr"
    and "\<forall>i<len. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr"
  shows "\<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some t" using assms
proof(induction arr arbitrary:len pParentPtr)
  case (MTArray x1 arr)
  obtain i l where idef:"i<len \<and> accessStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l)
              \<and> (l = p \<and> MTArray x1 arr = MTArray x t \<or> CompMemType mem x1 arr (MTArray x t) l p)"
    using MTArray.prems(1) unfolding CompMemType.simps by blast
  then have mc:"MCon (MTArray x1 arr) mem l" using MTArray.prems(3) by auto
  then show ?case
  proof(cases "l = p")
    case True
    then have tps:"MTArray x1 arr = MTArray x t" using idef MTArray.prems
      by (metis existingLocation_imps_allLocs_same)
    have "\<forall>i<len.\<exists>p'. accessStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p')"
      using MTArray.prems(3)
      by (metis MConArrayPointers bot_nat_0.not_eq_extremum less_nat_zero_code)
    then have "\<forall>i<len.\<exists>p'. accessStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p') \<and>
          (\<exists>len arr'. MCon (MTArray x1 arr) mem p' \<and> (MTArray x1 arr) = MTArray len arr'
                      \<and> (\<forall>i<len. accessTypeStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr'))"
      using MTArray.prems(2,4) unfolding subPrefixStructuralConsistency_def by fastforce
    then show ?thesis using idef True tps by auto
  next
    case False
    then have cmp:"CompMemType mem x1 arr (MTArray x t) l p" using idef by simp
    have "\<forall>i<x1. accessTypeStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some arr"
      using idef MTArray.prems(2,4) unfolding subPrefixStructuralConsistency_def by fastforce
    then have "\<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some t"
      using MTArray.IH[OF cmp MTArray.prems(2) mc _] by blast
    then show ?thesis by blast
  qed
next
  case (MTValue x)
  then show ?case by simp
qed


end

text \<open>A storage pointer derived from a declared storage variable is again
  related to a declared storage variable.\<close>

lemma CompStoType_ptr_witness:
  assumes decl: "(type.Storage tp0, Storeloc s0) |\<in>| fmran den"
    and base: "CompStoType tp0 t s0 l'"
    and rel: "t = t' \<and> v = KStoptr l' \<or> extractValueType v \<noteq> l' \<and> CompStoType t t' l' (extractValueType v)"
    and ptr: "\<exists>xx. v = KStoptr xx"
  shows "\<exists>stloc tp''. (type.Storage tp'', Storeloc stloc) |\<in>| fmran den \<and>
    (tp'' = t' \<and> v = KStoptr stloc \<or>
     extractValueType v \<noteq> stloc \<and> CompStoType tp'' t' stloc (extractValueType v))"
proof -
  have c: "CompStoType tp0 t' s0 (extractValueType v)"
    using rel base CompStoType_trns by auto
  show ?thesis
  proof (cases "extractValueType v = s0")
    case True
    then have "tp0 = t'" using c CompStoType_sameLoc_sameType by simp
    moreover have "v = KStoptr s0" using ptr True by auto
    ultimately show ?thesis using decl by blast
  next
    case False
    then show ?thesis using decl c by blast
  qed
qed

end
