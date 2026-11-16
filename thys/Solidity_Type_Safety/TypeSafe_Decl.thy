section \<open>Declarations\<close>

theory TypeSafe_Decl
  imports TypeSafe_Environment
begin

context typesafe_base
begin

subsection \<open>Declarations are type-safe\<close>
text \<open>@{const decl} is used by @{const load} to declare the contract variables in the newly created environment.
  For simple cases (Stack values) decl will copy the value from the source location into the top of the Stack.
  For more complex data types such as copying a Memory structure the structure is copied recursively using
  a support function (such as @{const cpm2mrec})\<close>

lemma cdMemLocsToploc:
  assumes "lessThanTopLocs cd'"
    and "l = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc cd'))"
    and "\<exists>dud. (dud, c') = allocate cd'"
    and "Toploc c' = Toploc c"
    and "\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs cd' = accessStore locs c"
  shows "lessThanTopLocs c" unfolding lessThanTopLocs_def
proof intros
  fix tloc loc
  assume b20:"Toploc c \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
  then have "Toploc c' \<le> tloc" using assms by simp
  then have b30:"Toploc cd' < tloc" using assms unfolding allocate_def by simp
  then have "ReadL\<^sub>n\<^sub>a\<^sub>t l < tloc" using assms
    by (simp add: Read_Show_nat'_id)
  then have "l \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
    using Read_Show_nat'_id by auto
  then have "\<not> LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
    by (metis LSubPrefL2_def assms(2) hash_inequality ShowLNatDot hash_int_prefix hash_suffixes_associative)
  then have b40:"\<not> LSubPrefL2 loc l" using b20 assms(2) ShowLNatDot
    by (metis LSubPrefL2_def assms(2) hash_suffixes_associative hashesInts)
  then have "accessStore loc cd' = None" using assms b20 b30 unfolding lessThanTopLocs_def using nat_less_le by auto
  then show "accessStore loc c= None" using assms b40 by auto
next
  fix loc y
  assume b20:" accessStore loc c = Some y"
  then show "\<exists>tloc<Toploc c. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
  proof(cases "LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc cd'))")
    case True
    have a10:"Toploc cd' < Toploc c'" using assms unfolding allocate_def updateStore_def by simp
    have "LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc cd'))" using True LSubPrefL2_def by simp
    have "\<forall>l. l\<noteq>(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc cd')) \<longrightarrow> \<not>(LSubPrefL2
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc cd')) l)" using ShowLNatDot unfolding LSubPrefL2_def hash_def
      using subPrefCannotBeInt by auto
    then show ?thesis using True a10 assms
      using LSubPrefL2_def by auto
  next
    case False
    have a20:"((\<forall>tloc loc. Toploc cd' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc cd' = None)
          \<and> (\<forall>loc y. accessStore loc cd' = Some y \<longrightarrow> (\<exists>tloc<Toploc cd'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
      using assms lessThanTopLocs_def[of cd'] by blast
    then obtain tloc where tlocdef:"tloc < Toploc cd' \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      by (metis False assms(2) assms(5) b20)
    moreover have "Toploc cd' < Toploc c'" using assms unfolding allocate_def updateStore_def by simp
    ultimately show ?thesis using assms lessThanTopLocs_def[of cd'] b20 tlocdef
      using order.strict_trans by metis
  qed
qed


subsubsection \<open>Type safety of @{const decl}\<close>
text \<open>Given a type-safe source environment, a type-consistent value to copy, and a
  successful @{const decl}, the result of @{const decl} is type-safe.\<close>

text \<open>Postcondition of @{const decl} without an initial value.\<close>

abbreviation declNonePost :: "environment \<Rightarrow> stack \<Rightarrow> calldataT \<Rightarrow> memoryT \<Rightarrow> 'a state_scheme \<Rightarrow> environment \<Rightarrow> calldataT \<Rightarrow> memoryT \<Rightarrow> stack \<Rightarrow> bool"
  where "declNonePost ev' sck' cd' mem' st e c m' k' \<equiv> TypeSafe e (Accounts st) k' m' (Storage st) c

\<and> (\<forall>x l. (\<nexists>y y'. x = type.Memory y \<or> x = Value y') \<and> (x, l) |\<in>| fmran(Denvalue e) \<longrightarrow> (x,l)|\<in>| fmran(Denvalue ev') )
\<and> (\<forall>sckl ptr. accessStore sckl k' = Some (ptr) \<and> (\<nexists>y y'. ptr = KMemptr y \<or> ptr = KValue y') \<longrightarrow> accessStore sckl sck' = Some ptr)
\<and> cd' = c
\<and> Toploc mem' \<le> Toploc m'
\<and> (\<forall>locs v. accessStore locs mem' = Some v \<longrightarrow> accessStore locs m' = Some v)
\<and> (\<forall>locs t. accessTypeStore locs mem' = Some t \<longrightarrow> accessTypeStore locs m' = Some t)
\<and> (\<forall>locs. (\<exists>tloc<Toploc mem'. LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc)) \<and> accessStore locs mem' = None) \<longrightarrow> accessStore locs m' = None)"

context
  fixes c cd cd' cp e ev ev' ip k' m' mem' sck' st tp
  assumes typeSafeDeclNone_hyps: "TypeSafe ev' (Accounts st) sck' mem' (Storage st ) cd'"
      "decl ip tp None cp cd (Memory st) (Storage st (Address ev)) (cd', mem', sck', ev') = Some (c, m', k', e)"
begin

text \<open>A value-type variable declared without an initial value: its default value is pushed on the stack.\<close>

lemma typeSafeDeclNone_1:
  assumes "tp = Value t"
    and "None = None"
    and "cp = cp0"
    and "cd = cd0"
    and "state.Memory st = mem0"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (c', m, k, e')"
    and "Some (c, m', k', e) = Some (c', m, astack_dup ip (Value t) (KValue (ival t)) (k, e'))"
  shows "declNonePost ev' sck' cd' mem' st e c m' k'"
proof -
  let ?case = "declNonePost ev' sck' cd' mem' st e c m' k'"
  note 1 = assms
  have tsOld:"TypeSafe e' (Accounts st) k m' (Storage st ) c'"
    using 1 typeSafeDeclNone_hyps by simp
  have a1:"(k', e) = (case Denvalue e' $$ ip of None \<Rightarrow> (push (KValue (ival t)) k, updateEnv ip (Value t) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))) e')
                  | Some x \<Rightarrow> (k, e'))" using 1 unfolding astack_dup.simps by simp
  have sameMem:"m' = mem'" using 1 by blast

  show ?thesis
  proof(cases "Denvalue e' $$ ip")
    case (Some a)
    then have same:"k' = k \<and> e = e'" using a1 by simp
    have ts1:"TypeSafe e (Accounts st) k' m' (Storage st) c"
      using 1(7,8) typeSafeDeclNone_hyps(1)
      using same by fastforce
    moreover have sameMem:"mem' = m" using 1 by blast
    then have "Mapping mem' \<subseteq>\<^sub>f Mapping m" using fmsubset_def
      by (simp add: fmsubset.rep_eq)
    moreover have "(\<forall>t id' loc. Denvalue ev' $$ id' = Some (type.Storage t, loc) \<longrightarrow> Denvalue e $$ id' = Some (type.Storage t, loc))"
      using same "1"(7) by force
    moreover have "(\<forall>loc. accessStore loc mem' \<noteq> accessStore loc m' \<longrightarrow> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')))"
      using sameMem 1 by simp
    moreover have "Toploc mem' \<le> Toploc m'" using 1 by blast
    moreover have "(\<forall>loc v. accessStore loc k' = Some (KStoptr v) \<longrightarrow> accessStore loc sck' = Some (KStoptr v))"
      using same 1 by blast
    moreover have "cd' = c" using 1 by simp
    moreover have "ReachableMem e k' m' = ReachableMem ev' sck' mem'"
      unfolding ReachableMem.simps using 1 sameMem same by blast
    moreover have " AllocatedMem_between mem' m' = {}" using 1 sameMem unfolding AllocatedMem_between_def by simp
    moreover have "(\<forall>locs. (\<exists>tloc<Toploc mem'. LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc)) \<and> accessStore
        locs mem' = None) \<longrightarrow> accessStore locs m' = None)"
      using sameMem 1 by auto
    ultimately show ?thesis using ts1 same 1 sameMem by blast
  next
    case None
    then have eDef:"updateEnv ip (Value t) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))) e' = e" using a1 by simp
    have k'Def:"k' = push (KValue (ival t)) k" using a1 None by simp
    have sameMem:"m' = mem'" using 1 by blast
    have sameAddress:"Address e = Address ev'" using eDef 1 by auto
    have sameCd:"c = cd'" using 1 by blast
    have lessTop:"lessThanTopLocs sck'" using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by blast
    show ?thesis
    proof(intros)
      show "TypeSafe e (Accounts st) k' m' (Storage st) c"
        unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st)" using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
      next
        show "safeContract (Accounts st) (Storage st)" using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
      next
        show "unique_locations (Denvalue e)" unfolding unique_locations_def
        proof intros
          fix x y

          assume *:"x |\<in>| fmran (Denvalue e) \<and> y |\<in>| fmran (Denvalue e) \<and> snd x = snd y"
          then obtain i1 i2 where i1def:"(Denvalue e) $$ i1 = Some x" and i2def:"Denvalue e $$ i2 = Some y" by blast
          show "x = y"
          proof(cases "i1 = ip")
            case True
            then have xIs:"x = (Value t, Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)))" using i1def eDef unfolding updateEnv.simps by auto
            then show ?thesis
            proof(cases "i2 = ip")
              case t2:True
              then show ?thesis using True i1def i2def by simp
            next
              case False
              then have "y |\<in>| fmran (Denvalue e')" using eDef i2def * unfolding updateEnv.simps
                by (metis DenvalueChange fmranI)
              then show ?thesis using stackLocs_imp_NotDen[OF _ typeSafeDeclNone_hyps(1)] 1(7) * xIs
                by (metis fmranE snd_conv stackLocs_imp_NotDen tsOld TypeSafe_def)
            qed
          next
            case False
            then have xOld:"x |\<in>| fmran (Denvalue e')" using eDef i1def * unfolding updateEnv.simps
              by (metis "1"(7) typeSafeDeclNone_hyps(2) decl_env_not_i fmranI)
            then show ?thesis
            proof(cases "i2 = ip")
              case True
              then have yIs:"y = (Value t, Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)))" using i2def eDef unfolding updateEnv.simps by auto
              then show ?thesis using stackLocs_imp_NotDen[OF _ typeSafeDeclNone_hyps(1)] 1(7) * xOld
                by (metis eq_snd_iff fmranE stackLocs_imp_NotDen tsOld TypeSafe_def)
            next
              case False
              then have "y |\<in>| fmran (Denvalue e')" using eDef i2def * unfolding updateEnv.simps
                by (metis DenvalueChange fmranI)
              then show ?thesis using xOld * typeSafeDeclNone_hyps(1) 1(7) unfolding TypeSafe_def unique_locations_def by blast
            qed
          qed
        qed
      next
        show "compPointers k' (Denvalue e)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume in1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
         (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
         (l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
         (l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and>
         (type.Storage tp2, l2) |\<in>| fmran (Denvalue e')" using eDef unfolding updateEnv.simps

            by (auto split: option.splits memoryvalue.splits mtypes.splits stypes.splits if_splits prod.splits stackvalue.splits type.splits
                denvalue.splits simp: None typeSafeDeclNone_hyps(2) decl_env_kval decl_env_not_i fmlookup_ran_iff)
          moreover have "l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1) \<longrightarrow> l1 = Stackloc l1' \<and> accessStore l1' k = Some (KStoptr stl1)"
            using k'Def in1 unfolding push_def allocate_def updateStore_def accessStore_def by simp
          moreover have "l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2) \<longrightarrow> l2 = Stackloc l2' \<and> accessStore l2' k = Some (KStoptr stl2)"
            using k'Def in1 unfolding push_def allocate_def updateStore_def accessStore_def by simp
          ultimately show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2
         else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
            using typeSafeDeclNone_hyps(1) 1(7) in1 unfolding TypeSafe_def compPointers_def by blast
        qed
      next
        show "balanceTypes (Accounts st)" using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
      next
        show "addressFormat (Address e)" using eDef unfolding updateEnv.simps using 1(7) typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by auto
      next
        show "addressFormat (Sender e)" using eDef unfolding updateEnv.simps using 1(7) typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by auto
      next
        show " svalueTypes (Svalue e)" using eDef unfolding updateEnv.simps using 1(7) typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by auto
      next
        show "lessThanTopLocs k'" unfolding lessThanTopLocs_def
        proof intros
          fix tloc loc
          assume *:"Toploc k' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          then show "accessStore loc k' = None"
            by (metis k'Def lessThanTopLocs_def stackPushToplocSafe tsOld TypeSafe_def)
        next
          fix loc y
          assume *:"accessStore loc k' = Some y "
          then show "\<exists>tloc<Toploc k'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
            by (metis k'Def lessThanTopLocs_def stackPushToplocSafe tsOld TypeSafe_def)
        qed
      next
        show "lessThanTopLocs c" using 1 typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs m'" using 1 typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
      next
        show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c "
          unfolding typeCompat_def
        proof intros
          fix t' l'
          assume inDen:"(t', l') |\<in>| fmran (Denvalue e)"
          then obtain i1 where i1Def:"(Denvalue e) $$ i1 = Some (t', l')" by blast
          show "denvalueCon k' m' (Storage st (Address e)) c t' l'"
          proof(cases l')
            case (Stackloc x1)
            then show ?thesis
            proof(cases "x1 = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))")
              case True
              then have acc:"accessStore x1 k' = Some (KValue (ival t))"
                using k'Def unfolding push_def allocate_def updateStore_def accessStore_def by simp
              have t'Def:"(Value t) = t'"
              proof(rule ccontr)
                assume "Value t \<noteq> t'"
                then have "i1 \<noteq> ip" using i1Def eDef by auto
                then have "(t', l') |\<in>| fmran (Denvalue e')" using i1Def inDen fmranI
                  by (metis "1"(7) typeSafeDeclNone_hyps(2) decl_env_not_i)
                then show False using Stackloc True stackLocs_imp_NotDen[OF _ typeSafeDeclNone_hyps(1)] 1(7)
                  by (metis fmranE snd_eqD stackLocs_imp_NotDen tsOld TypeSafe_def)
              qed
              have "typeCon t (ival t)"
                by (simp add: ivalTypeCon)
              then show ?thesis using acc Stackloc inDen t'Def by auto
            next
              case False
              then have sameACC:"accessStore x1 k' = accessStore x1 sck'"
                using k'Def 1(7) unfolding push_def allocate_def accessStore_def updateStore_def by simp
              obtain i where iDef:"(Denvalue e) $$ i = Some (t', l')" using inDen by blast
              then have "i \<noteq> ip" using eDef False Stackloc by auto
              then have "Denvalue e' $$ i = Some (t', l')" using iDef eDef by auto
              then have inOld:"(t', l') |\<in>| fmran (Denvalue e')" using fmranI by metis
              have "(case accessStore x1 sck' of None \<Rightarrow> False
                    | Some (KValue val) \<Rightarrow> (case t' of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                    | Some (KCDptr stloc) \<Rightarrow> (case t' of Calldata struct \<Rightarrow> MCon struct cd' stloc | _ \<Rightarrow> False)
                    | Some (KMemptr stloc) \<Rightarrow> (case t' of type.Memory struct \<Rightarrow> MCon struct mem' stloc | _ \<Rightarrow> False)
                    | Some (KStoptr stloc) \<Rightarrow> (case t' of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st (Address ev')) | _ \<Rightarrow> False))"
                using inOld sameACC sameMem Stackloc using typeSafeDeclNone_hyps(1) 1(7) unfolding TypeSafe_def typeCompat_def by fastforce
              then show ?thesis using Stackloc sameACC sameCd sameMem sameAddress
                by (metis denvalue.simps(5))
            qed
          next
            case (Storeloc x2)
            then have inOld:"(t', l') |\<in>| fmran (Denvalue e')"using eDef inDen unfolding updateEnv.simps

              by (metis "1"(1,7) None type.distinct(5) typeSafeDeclNone_hyps(2) decl_env_storage DenvalueChange fmranI i1Def)
            then have "(case t' of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st (Address ev')) | _ \<Rightarrow> False)"
              using typeSafeDeclNone_hyps(1) 1(7) Storeloc inDen sameAddress unfolding TypeSafe_def typeCompat_def by fastforce
            then obtain struct where "t' = type.Storage struct" by (cases t', simp+)
            then show ?thesis using typeSafeDeclNone_hyps(1) 1(7) Storeloc inDen sameAddress inOld
              unfolding TypeSafe_def typeCompat_def by fastforce
          qed
        qed
      next

        show "denvalueTypeCorrectness e k' m'"
          unfolding denvalueTypeCorrectness_def
        proof intros
          fix tt l ptr_loc
          assume *:"(type.Memory tt, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"
          then obtain i where idef:"Denvalue e $$ i = Some (type.Memory tt, Stackloc l)" by blast
          then have "i \<noteq> ip" using eDef by auto
          then have inOld:"(type.Memory tt, Stackloc l) |\<in>| fmran (Denvalue e')"
            using idef eDef * fmranI by fastforce
          then have "l \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))"
            using k'Def * unfolding push_def updateStore_def allocate_def accessStore_def by auto
          then have "accessStore l k' = accessStore l k"
            using k'Def unfolding push_def updateStore_def allocate_def accessStore_def by simp
          then show "case tt of
      MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)

       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
            using inOld typeSafeDeclNone_hyps(1) 1(7,8) *
            unfolding TypeSafe_def denvalueTypeCorrectness_def by auto
        qed
      next
        show "subPrefixStructuralConsistency m'"
          using typeSafeDeclNone_hyps(1) sameMem unfolding TypeSafe_def subPrefixStructuralConsistency_def by auto
      next
        show "SomeValSomeTyp m'"
          using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def
          using sameMem by blast
      qed
    next
      fix x l
      assume *:"(\<nexists>y y'. x = type.Memory y \<or> x = Value y') \<and> (x, l) |\<in>| fmran (Denvalue e)"
      then obtain ip' where **:"Denvalue e $$ ip' = Some (x, l)" by blast
      then have "ip' \<noteq> ip" using eDef * unfolding updateEnv.simps by auto
      then have "Denvalue ev' $$ ip' = Some (x, l)"
        using eDef ** decl_env_not_i 1 by force
      then show "(x, l) |\<in>| fmran (Denvalue ev')" using fmranI by metis
    next
      fix sckl ptr
      assume *:" accessStore sckl k' = Some ptr \<and> (\<nexists>y y'. ptr = KMemptr y \<or> ptr = KValue y')"
      have "\<exists>v. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) k' = (Some (KValue v))"
        using k'Def unfolding push_def allocate_def updateStore_def accessStore_def by simp
      then have "sckl \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))" using * by auto
      then have "accessStore sckl k' =accessStore sckl sck'"
        using k'Def 1 unfolding push_def allocate_def updateStore_def accessStore_def by simp
      then show "accessStore sckl sck' = Some ptr " using * by simp
    next
      show "cd' = c" using 1 by blast
    next
      show "Toploc mem' \<le> Toploc m'" using 1 by blast
    next
      show " \<And>locs v. accessStore locs mem' = Some v \<Longrightarrow> accessStore locs m' = Some v" using 1 by blast
    next
      show "\<And>locs t. accessTypeStore locs mem' = Some t \<Longrightarrow> accessTypeStore locs m' = Some t"
        using 1 by blast
    next
      show "\<And>locs. \<exists>tloc<Toploc mem'. LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc)) \<and> accessStore locs mem' = None \<Longrightarrow> accessStore locs m' = None"
        using 1 by blast
    qed
  qed
qed

text \<open>A memory array declared without an initial value: a fresh array is allocated and initialised with @{const minit}.\<close>

lemma typeSafeDeclNone_18:
  assumes "tp = type.Memory (MTArray x t)"
    and "None = None"
    and "cp = cp0"
    and "cd = cd0"
    and "state.Memory st = mem0"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (c', m, k, e')"
    and "Some (c, m', k', e) = (if Denvalue e' $$ ip = None \<and> arraysGreaterZero (MTArray x t) then let m' = minit x t m in Some (c',
        m', astack_dup ip (type.Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))) (k, e')) else None)"
  shows "declNonePost ev' sck' cd' mem' st e c m' k'"
proof -
  let ?case = "declNonePost ev' sck' cd' mem' st e c m' k'"
  note 18 = assms
  have tsOld:"TypeSafe e' (Accounts st) k m (Storage st ) c'"
    using 18 typeSafeDeclNone_hyps(1) by simp
  have NoneIP:"Denvalue e' $$ ip = None \<and> arraysGreaterZero (MTArray x t)" using 18 by (simp split:if_splits)

  then have "(k', e) = (push (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))) k, updateEnv ip (type.Memory (MTArray x t)) (Stackloc
      (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))) e')" using 18 by simp
  then have k'Def:"k' = push (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))) k" and eDef:"e = updateEnv ip (type.Memory (MTArray x t)) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))) e'"
    by blast+
  have m'Def:"m' = minit x t m" using 18 by (auto split:if_split_asm)
  then obtain mm where mmDef:"mm = iter (\<lambda>i. minitRec (hash ((ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t) m x" unfolding minit_def by blast
  then have topMM:"Toploc mm = Toploc m" using minitToploc mmDef by metis
  have m'Def2:"snd (allocate mm) = m'" using m'Def unfolding minit_def using mmDef by metis

  have sameAddress:"Address e = Address ev'" using eDef 18 by auto
  have sameCd:"c = cd'" using 18 by (simp split:if_splits)
  have lessTop:"lessThanTopLocs sck'" using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by blast
  have mLim:"((\<forall>tloc loc. Toploc m \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc m = None) \<and>
     (\<forall>loc y. accessStore loc m = Some y \<longrightarrow> (\<exists>tloc<Toploc m. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
    using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def lessThanTopLocs_def using 18(7) by blast
  then have noneTop:"\<forall>l. TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<or> l =
      (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<longrightarrow> accessStore l m = None"
    by (meson LSubPrefL2_def le_refl typedPrefix_imp_SubPref)
  then have SameAccM_mm:"\<forall>l accx. accessStore l m = Some accx \<longrightarrow> accessStore l mm = Some accx"
    using minitSomeOldNew[OF mmDef[symmetric] ] by blast
  have mM'Acc:"\<forall>l accx. accessStore l m = Some accx \<longrightarrow> accessStore l m' = Some accx"
  proof intros
    fix l accx
    assume *:"accessStore l m = Some accx "
    have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) m = None" using mLim
      using LSubPrefL2_def by blast
    then show "accessStore l m' = Some accx" using * m'Def SameAccM_mm mmDef unfolding minit_def
      by (metis allocateSameAccess)
  qed

  have selfPoint:"\<forall>l l'. TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t)
                    \<and> accessStore l m' = Some (MPointer l') \<longrightarrow> l' = l"
  proof intros
    have in5:"\<forall>l l'. TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<and> accessStore l mm = Some (MPointer l') \<longrightarrow> l' = l"
      using minitSelfPointers[OF mmDef[symmetric]] by blast
    fix l l'
    assume *:"TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<and> accessStore l m' = Some (MPointer l')"
    have sameAcc:"\<forall>l. accessStore l m' = accessStore l mm" using m'Def allocateSameAccess mmDef unfolding minit_def by metis
    then show "l' = l " using in5 * by metis
  qed

  then have prefPtrs_imps_Pref:"\<forall>l. TypedMemSubPrefPtrs m' x t (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) l \<longrightarrow>
      TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t)"
    using selfPoint_imps_TypedMemSubPref by blast

  have nonLocChanged:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<or> locs =
      (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<longrightarrow> accessStore locs m = accessStore locs m'"
    using minitSingleChange_typedPref[OF mmDef[symmetric]] m'Def allocateSameAccess mmDef unfolding minit_def by metis
  have nonLocChanged2:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<or> locs =
      (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<longrightarrow> accessStore locs m = accessStore locs m'"
    using minitSingleChange[OF mmDef[symmetric]] allocateSameAccess m'Def2 by auto
  have nonLocChanged2_Typed:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<or> locs =
      (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<longrightarrow> accessTypeStore locs m = accessTypeStore locs m'"
    using minitSingleChange_typed[OF mmDef[symmetric]] allocateTypeSameAccess m'Def2 by auto
  have nonLocChanged_Typed:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<or> locs =
      (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<longrightarrow> accessTypeStore locs m = accessTypeStore locs m'"
    using minitSingleChange_typedPref_typed[OF mmDef[symmetric]] allocateTypeSameAccess m'Def2 by auto
  have mcTop:"MCon (MTArray x t) mm (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))"
    using MConMinit[of "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))" t m x mm] mmDef noneTop NoneIP by metis
  then have mcTop:"MCon (MTArray x t) m' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))" using allocateMCon m'Def2 by blast
  have mcTypes:"\<forall>destl'.
       TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<longrightarrow>
       (\<exists>st. CompMemType mm x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' mm = Some (MTValue pval)))"
    using minit_TypeCompChange[OF mmDef[symmetric]] m'Def allocateTypeSameAccess allocateSameAccess
      mmDef CompMemType_SameAccessAllocate unfolding minit_def by blast

  have mcTypes:"\<forall>destl'.
       TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<longrightarrow>
       (\<exists>st. CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' m' = Some (MTValue pval)))"
  proof intros
    fix destl'
    assume in1:"TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t)"
    then obtain st where stDef:"CompMemType mm x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' mm = Some (MTValue pval))"
      using mcTypes by blast
    then have "CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) destl'"
      using CompMemType_SameAccessAllocate allocateSameAccess m'Def2 mcTypes by metis
    moreover have "(case st of MTArray parent_len parent_arr \<Rightarrow>
              \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' m' = Some (MTValue pval))"
      using m'Def2 allocateTypeSameAccess[of mm] mcTypes in1 stDef
      by presburger
    ultimately show "\<exists>st. CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) destl' \<and>
            (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
             | MTValue pval \<Rightarrow> accessTypeStore destl' m' = Some (MTValue pval))" by auto
  qed

  have immediateIndex:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some t"
    using minit_TypeCompChangeIndexs[OF mmDef[symmetric]]
    by (metis allocateTypeSameAccess m'Def2)


  have a120:"lessThanTopLocs sck'" using typeSafeDeclNone_hyps(1) TypeSafe_def 18(7) by simp
  then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''"
    using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
  then have a140:"\<forall>x y. \<not>((Denvalue ev') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))"
    using TypeSafe_def typeSafeDeclNone_hyps(1) typeSafeAllStacklocsExist fmranI 18(7) by fastforce
  then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip"
    using eDef lessThanTopLocs_def fmranI 18(7) by auto

  show ?thesis
  proof(intros)
    show "TypeSafe e (Accounts st) k' m' (Storage st) c"
      unfolding TypeSafe_def
    proof intros
      show "AddressTypes (Accounts st)" using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
    next
      show "safeContract (Accounts st) (Storage st)" using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
    next
      show "unique_locations (Denvalue e)" unfolding unique_locations_def
      proof intros
        fix x' y
        assume *:"x' |\<in>| fmran (Denvalue e) \<and> y |\<in>| fmran (Denvalue e) \<and> snd x' = snd y"
        then obtain i1 i2 where i1def:"(Denvalue e) $$ i1 = Some x'" and i2def:"Denvalue e $$ i2 = Some y" by blast
        show "x' = y"
        proof(cases "i1 = ip")
          case True
          then have xIs:"x' = (type.Memory (MTArray x t), Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)))" using i1def eDef unfolding updateEnv.simps by simp
          then show ?thesis
          proof(cases "i2 = ip")
            case t2:True
            then show ?thesis using True i1def i2def by simp
          next
            case False
            then have "y |\<in>| fmran (Denvalue e')" using eDef i2def * unfolding updateEnv.simps
              by (simp add: fmranI)
            then show ?thesis using stackLocs_imp_NotDen[OF lessTop typeSafeDeclNone_hyps(1)] 18(7) * xIs by fastforce
          qed
        next
          case False
          then have xOld:"x' |\<in>| fmran (Denvalue e')" using eDef i1def * unfolding updateEnv.simps
            by (simp add: fmranI)
          then show ?thesis
          proof(cases "i2 = ip")
            case True
            then have yIs:"y = (type.Memory (MTArray x t), Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)))" using i2def eDef unfolding updateEnv.simps by simp
            then show ?thesis using stackLocs_imp_NotDen[OF lessTop typeSafeDeclNone_hyps(1)] 18(7) * xOld by fastforce
          next
            case False
            then have "y |\<in>| fmran (Denvalue e')" using eDef i2def * unfolding updateEnv.simps
              by (simp add: fmranI)
            then show ?thesis using xOld * typeSafeDeclNone_hyps(1) 18(7) unfolding TypeSafe_def unique_locations_def by blast
          qed
        qed
      qed
    next
      show "compPointers k' (Denvalue e)" unfolding compPointers_def
      proof intros
        fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
        assume in1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
        then have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e')" using eDef unfolding updateEnv.simps
          by (auto split: option.splits memoryvalue.splits mtypes.splits stypes.splits if_splits prod.splits stackvalue.splits type.splits
              denvalue.splits simp: NoneIP typeSafeDeclNone_hyps(2) decl_env_not_i decl_env_storage fmranE fmranI)

        moreover have "l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1) \<longrightarrow> l1 = Stackloc l1' \<and> accessStore l1' k = Some (KStoptr stl1)"
          using k'Def in1 unfolding push_def allocate_def updateStore_def accessStore_def by simp
        moreover have "l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2) \<longrightarrow> l2 = Stackloc l2' \<and> accessStore l2' k = Some (KStoptr stl2)"
          using k'Def in1 unfolding push_def allocate_def updateStore_def accessStore_def by simp
        ultimately show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2
       else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
          using typeSafeDeclNone_hyps(1) 18(7) in1 unfolding TypeSafe_def compPointers_def by blast
      qed
    next
      show "balanceTypes (Accounts st)" using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
    next
      show "addressFormat (Address e)" using eDef unfolding updateEnv.simps using 18(7) typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
    next
      show "addressFormat (Sender e)" using eDef unfolding updateEnv.simps using 18(7) typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
    next
      show " svalueTypes (Svalue e)" using eDef unfolding updateEnv.simps using 18(7) typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
    next
      show "lessThanTopLocs k'" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume *:"Toploc k' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then show "accessStore loc k' = None"
          by (metis k'Def lessThanTopLocs_def stackPushToplocSafe tsOld TypeSafe_def)
      next
        fix loc y
        assume *:"accessStore loc k' = Some y "
        then show "\<exists>tloc<Toploc k'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          by (metis k'Def lessThanTopLocs_def stackPushToplocSafe tsOld TypeSafe_def)
      qed
    next
      show "lessThanTopLocs c" using NoneIP 18 typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by simp
    next
      show "lessThanTopLocs m'" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume *:"Toploc m' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have "Toploc m' > Toploc m" using topMM m'Def2 unfolding allocate_def by auto
        then have "\<not>LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))" using *
          by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general hash_inequality hash_suffixes_associative hashesIntSame nat_less_le
              order_antisym_conv)
        then have "\<not> TypedMemSubPref loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<or> loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))"
          using neg_MemLSubPrefL2_imps_TypedMemSubPref by blast
        then show "accessStore loc m' = None"
          using 18 typeSafeDeclNone_hyps(1) nonLocChanged unfolding TypeSafe_def lessThanTopLocs_def
          by (metis "*" \<open>Toploc m < Toploc m'\<close> dual_order.trans mLim nat_less_le)
      next
        fix loc y
        assume *:"accessStore loc m' = Some y"
        then have "Toploc m' > Toploc m" using topMM m'Def2 unfolding allocate_def by auto
        then show "\<exists>tloc<Toploc m'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using *
          by (metis mLim neg_MemLSubPrefL2_imps_TypedMemSubPref nonLocChanged order_less_trans)
      qed
    next
      show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c "
        unfolding typeCompat_def
      proof intros
        fix t' l'
        assume inDen:"(t', l') |\<in>| fmran (Denvalue e)"
        then obtain i1 where i1Def:"(Denvalue e) $$ i1 = Some (t', l')" by blast
        show "denvalueCon k' m' (Storage st (Address e)) c t' l'"
        proof(cases l')
          case (Stackloc x1)
          then show ?thesis
          proof(cases "x1 = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))")
            case True
            then have acc:"accessStore x1 k' = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)))"
              using k'Def unfolding push_def allocate_def updateStore_def accessStore_def by auto
            have t'Def:"t' = (type.Memory (MTArray x t))" using eDef inDen True Stackloc i1Def a150
              using "18"(7) by fastforce
            have "MCon (MTArray x t) m' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))" using mcTop by simp
            then show ?thesis using Stackloc acc t'Def by simp
          next
            case False
            then have sameACC:"accessStore x1 k' = accessStore x1 sck'"
              using k'Def 18(7) unfolding push_def allocate_def accessStore_def updateStore_def by simp
            obtain i where iDef:"(Denvalue e) $$ i = Some (t', l')" using inDen by blast
            then have "i \<noteq> ip" using eDef False Stackloc by auto
            then have "Denvalue e' $$ i = Some (t', l')" using iDef eDef by simp
            then have inOld:"(t', l') |\<in>| fmran (Denvalue e')" using fmranI by metis
            have ol:"(case accessStore x1 sck' of None \<Rightarrow> False
                  | Some (KValue val) \<Rightarrow> (case t' of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                  | Some (KCDptr stloc) \<Rightarrow> (case t' of Calldata struct \<Rightarrow> MCon struct cd' stloc | _ \<Rightarrow> False)
                  | Some (KMemptr stloc) \<Rightarrow> (case t' of type.Memory struct \<Rightarrow> MCon struct mem' stloc | _ \<Rightarrow> False)
                  | Some (KStoptr stloc) \<Rightarrow> (case t' of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st (Address ev')) | _ \<Rightarrow> False))"
              using inOld sameACC sameAddress Stackloc using typeSafeDeclNone_hyps(1) 18(7) unfolding TypeSafe_def typeCompat_def by fastforce
            then show ?thesis
            proof(cases "accessStore x1 k'")
              case None
              then show ?thesis using inOld sameACC Stackloc ol by simp
            next
              case (Some a)
              then show ?thesis
              proof(cases a)
                case (KValue x1)
                then show ?thesis using Some inOld sameACC Stackloc ol by simp
              next
                case (KCDptr x2)
                then show ?thesis using Some inOld sameACC Stackloc ol 18(7) sameCd by auto
              next
                case (KMemptr x3)
                then obtain struct where structdef:"t' = type.Memory struct"
                  using ol Some sameACC by (cases t', simp+)
                then have lims:"\<not> LSubPrefL2 x3 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) x3"
                  using typeSafeAllPtrsNotTop[OF typeSafeDeclNone_hyps(1), of struct x1 x3] Stackloc inOld 18(7) sameACC Some KMemptr by simp
                have lim2:"\<forall>len arr loc. struct = MTArray len arr \<and> TypedMemSubPrefPtrs mem' len arr x3 loc
                          \<longrightarrow> \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) loc"
                  using typeSafeAllMemPtrsCantTop[OF typeSafeDeclNone_hyps(1), of struct x1 x3] structdef
                    Stackloc inOld 18(7) sameACC Some KMemptr by auto
                have mcO:"MCon struct mem' x3" using ol Some KMemptr structdef sameACC by simp
                then have "MCon struct m' x3" using MCon_memory_transfer[OF mcO lims lim2, of m'] 18(7) nonLocChanged2 by simp
                then show ?thesis using sameAddress Some inOld sameACC Stackloc ol 18(7) KMemptr structdef by simp
              next
                case (KStoptr x4)
                then show ?thesis using sameAddress Some inOld sameACC Stackloc ol 18(7) by (cases t',simp+)
              qed
            qed
          qed
        next
          case (Storeloc x2)
          then have inOld:"(t', l') |\<in>| fmran (Denvalue e')"using eDef inDen unfolding updateEnv.simps

            using "18"(7) typeSafeDeclNone_hyps(2) decl_env_not_i fmlookup_ran_iff by fastforce
          then have "(case t' of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st (Address ev')) | _ \<Rightarrow> False)"
            using typeSafeDeclNone_hyps(1) 18(7) Storeloc inDen sameAddress unfolding TypeSafe_def typeCompat_def by fastforce
          then obtain struct where "t' = type.Storage struct" by (cases t', simp+)
          then show ?thesis using typeSafeDeclNone_hyps(1) 18(7) Storeloc inDen sameAddress inOld
            unfolding TypeSafe_def typeCompat_def by fastforce
        qed
      qed
    next
      show "denvalueTypeCorrectness e k' m'"
        unfolding denvalueTypeCorrectness_def
      proof intros
        fix t2 l2 ptr_loc
        assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue e) \<and> accessStore l2 k' = Some (KMemptr ptr_loc)"
        then obtain i where idef:"Denvalue e $$ i = Some (type.Memory t2, Stackloc l2)" by blast
        show "case t2 of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
        proof(cases "l2 = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))")
          case True
          then have acc:"accessStore l2 k' = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)))"
            using k'Def unfolding push_def allocate_def updateStore_def accessStore_def by auto
          then have "ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))" using * by simp
          have t'Def:"t2 = (MTArray x t)" using * eDef True a150
            using "18"(7) by fastforce
          have "\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some t"
            by (metis \<open>ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))\<close> allocateTypeSameAccess m'Def2 minit_TypeCompChangeIndexs mmDef)
          then show ?thesis using t'Def \<open>ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))\<close>
            using nonLocChanged noneTop by force
        next
          case False
          then have sameACC:"accessStore l2 k' = accessStore l2 sck'"
            using k'Def 18(7) unfolding push_def allocate_def accessStore_def updateStore_def by simp

          obtain i where iDef:"(Denvalue e) $$ i = Some (type.Memory t2, Stackloc l2)" using * by blast
          then have "i \<noteq> ip" using eDef False by auto
          then have inold:"Denvalue e' $$ i = Some (type.Memory t2, Stackloc l2)" using iDef eDef by simp
          then have ptrDef:"accessStore l2 sck' = Some (KMemptr ptr_loc)" using 18(7) sameACC
            using "*" by auto
          then have old:"(case t2 of
                         MTArray len arr \<Rightarrow>
           (\<forall>i<len.
              accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some arr)
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc mem' = Some (MTValue val))"
            using typeSafeDeclNone_hyps(1) 18(7) inold
            unfolding TypeSafe_def denvalueTypeCorrectness_def
            by (meson \<open>i \<noteq> ip\<close> typeSafeDeclNone_hyps(2) decl_env_not_i fmranI iDef)
          have notSubTop:"\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))"
            using ptrDef "18"(8) False \<open>Denvalue e' $$ i = Some (type.Memory t2, Stackloc l2)\<close> decl.simps(18) decl_stack_change fmranI sameACC tsOld
              typeSafeAllPtrsNotTop
            by (metis dual_order.refl)
          then show ?thesis
          proof(cases t2)
            case (MTArray x11 x12)
            have cc1:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<longrightarrow> accessTypeStore loc m' = accessTypeStore loc mem'"
              using nonLocChanged2 old nonLocChanged2_Typed 18(7) by simp
            have old': "\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some x12"
              using old MTArray by simp

            then show ?thesis using MTArray notSubTop cc1 old' MemLSubPrefL2_specific_imps_general
            proof -
              have "\<forall>i. \<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))"
                using notSubTop MemLSubPrefL2_specific_imps_general by blast
              then show ?thesis using MTArray cc1 old' by simp
            qed
          next
            case (MTValue x2)
            then show ?thesis using notSubTop nonLocChanged2_Typed old 18(7) by simp
          qed
        qed
      qed
    next
      show "subPrefixStructuralConsistency m'" unfolding subPrefixStructuralConsistency_def
      proof(intros)
        fix locs tp
        assume in1:"accessTypeStore locs m' = Some tp"
        have tloc:"Toploc m' > Toploc m" using topMM m'Def2 unfolding allocate_def by auto

        show "case accessStore locs m' of None \<Rightarrow> False | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m' locs \<and> tp = MTValue val \<and> accessTypeStore locs m' = Some tp
       | Some (MPointer p) \<Rightarrow> \<exists>len arr.
              MCon tp m' p \<and>
              tp = MTArray len arr \<and>
              (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr) "
        proof(cases "accessTypeStore locs mem' = Some tp")
          case True
          then have accL:"\<exists>v. accessStore locs mem' = Some v"
            using typeSafeDeclNone_hyps(1) 18(7) unfolding TypeSafe_def SomeValSomeTyp_def by simp
          have notSub:"\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))"
          proof
            assume c:"LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))"
            then have "accessStore locs mem' = None"
              using mLim 18(7) tloc
              using nless_le by auto
            then show False using accL by auto
          qed
          then have sameACC:" accessStore locs m' = accessStore locs mem'" using nonLocChanged2 18(7) by simp
          then consider (ptr) p where "accessStore locs m' = Some (MPointer p)"
            | (val) val2 where "accessStore locs m' = Some (MValue val2)"
            using typeSafeDeclNone_hyps(1) 18(7) True unfolding TypeSafe_def subPrefixStructuralConsistency_def
            by (metis memoryvalue.exhaust accL)
          then show ?thesis
          proof(cases)
            case ptr
            then obtain len arr where
              old:"MCon tp mem' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some arr)
                  "
              using typeSafeDeclNone_hyps(1) 18(7) True sameACC unfolding TypeSafe_def subPrefixStructuralConsistency_def by fastforce
            then have lim2:"\<forall>len arr loc. tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem' len arr p loc
                        \<longrightarrow> \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) loc"
              using AccessedMemPtrsCantTop[of "mem'" tp p] typeSafeDeclNone_hyps(1) 18(7) unfolding TypeSafe_def by blast
            have lim:" \<not> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) p"
              using AllPtrsNotTop_MCon notSub ptr using typeSafeDeclNone_hyps(1) 18(7) old unfolding TypeSafe_def by blast
            have accTLoc:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<or> loc =
                (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<longrightarrow> accessStore loc m' = accessStore loc mem'"
              using 18(7) nonLocChanged2 by auto
            have "MCon tp m' p" using MCon_memory_transfer[OF _ lim lim2 accTLoc] old by blast
            moreover have "\<forall>i<len. \<not> LSubPrefL2 (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))" using lim
              using MemLSubPrefL2_specific_imps_general by blast
            ultimately have " MCon tp m' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)"
              using nonLocChanged2_Typed old 18(7) by simp

            then show ?thesis using ptr by fastforce
          next
            case val
            then have old:"\<exists>val. MCon tp mem' locs \<and> tp = MTValue val \<and> accessTypeStore locs mem' = Some tp"
              using typeSafeDeclNone_hyps(1) 18(7) True sameACC unfolding TypeSafe_def subPrefixStructuralConsistency_def by fastforce
            then have "\<exists>val. MCon tp m' locs \<and> tp = MTValue val \<and> accessTypeStore locs m' = Some tp"
              using nonLocChanged2_Typed MCon.simps val notSub 18(7) sameACC by fastforce
            then show ?thesis using val by auto
          qed
        next
          case False
          then have sub:"TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<and> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))"
            using nonLocChanged_Typed 18(7) in1 by fastforce
          then have "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t)"
            using prefPtrs_imps_Pref by simp
          then obtain st where stD:"(CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) locs \<and>
           (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
            | MTValue pval \<Rightarrow> accessTypeStore locs m' = Some (MTValue pval)))" using mcTypes by blast
          then have cmp:"CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) locs " by blast

          have mcLocs:"MCon st m' locs" using cmp mcTop CompTypeRemainsMCon by auto

          show ?thesis
          proof(cases st)
            case (MTArray x11 x12)
            have subs:"t = MTArray x11 x12 \<and> (\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs)) \<or>
                       (\<exists>midP subL subA i. CompMemType m' x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) midP
                       \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
              using CompMemType_imps_Mid[of m' x t x11 x12 "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m))" locs] cmp MTArray by simp

            then have acc:"accessStore locs m' = Some (MPointer locs)" using selfPoint mcLocs sub MTArray
              by (metis (no_types, lifting) MCon.simps(2) MCon_imps_TypedMemSubPref_Some mcTop option.distinct(1))

            moreover have "\<exists>len arr. MCon tp m' locs \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
                            \<and> (\<forall>v. accessStore locs m' = Some (MPointer v) \<longrightarrow> accessTypeStore locs m' = Some (MTArray len arr))"
              using in1
            proof(cases "(\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> t = MTArray x11 x12)")
              case True
              then obtain i where idef:"i<x \<and> accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs)
                                    \<and> t = MTArray x11 x12"
                by auto
              then have "TypedMemSubPref (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) " by auto
              then have locsD:"locs = (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint idef by blast
              have "\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MTArray x11 x12)" using idef
                by (metis allocateTypeSameAccess m'Def2 minit_TypeCompChangeIndexs mmDef)
              then have "tp = MTArray x11 x12" using in1 locsD idef by simp
              moreover have "(\<forall>i<x11. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some x12)" using stD MTArray by simp
              ultimately show ?thesis using mcLocs MTArray
                using in1 by blast
            next
              case False
              then obtain midP i subL subA where mid:"(CompMemType m' x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) midP
                   \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
                using subs by blast
              then have locD:"locs = (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint
                using CompMemType_imps_in_GetAllMemoryLocations_ptr mcTop memSet_selfPoint by blast
              then obtain st2 where st2D:"(CompMemType m' x t st2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) midP \<and>
             (case st2 of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore midP m' = Some (MTValue pval)))" using mid mcTypes
                using CompMemTypeSameLocsSameType CompMemType_imps_TypedMemSubPrefPtrs prefPtrs_imps_Pref by blast
              then have "st2 = (MTArray subL subA)" using mid CompMemTypeSameLocsSameType mcTop by blast
              then have " \<forall>i<subL. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some subA" using st2D by simp
              then have "MTArray x11 x12 = tp" using in1 locD mid by simp
              then show ?thesis using mcLocs MTArray stD in1 by auto
            qed
            ultimately show ?thesis by auto
          next
            case (MTValue x2)
            then obtain v where vDef:"accessStore locs m' = Some (MValue v)"
              using mcLocs MCon.simps(1)[of x2 m' locs] by (auto split:option.splits memoryvalue.splits)
            moreover have "accessTypeStore locs m' = Some (MTValue x2)" using stD MTValue by auto
            moreover have "tp = MTValue x2" using calculation in1 by simp
            moreover have "MCon tp m' locs" using mcLocs calculation MTValue by blast
            ultimately show ?thesis using MTValue by simp
          qed
        qed
      qed
    next
      have old:"SomeValSomeTyp mem'" using typeSafeDeclNone_hyps(1) unfolding TypeSafe_def by blast
      have non:"\<forall>loc. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) \<longrightarrow> accessStore loc mem' = None"
        using 18(7) typeSafeDeclNone_hyps(1) unfolding TypeSafe_def lessThanTopLocs_def
        by auto
      have somesomeT:"\<forall>destl'.
     TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t) \<longrightarrow>
     (\<exists>t. accessStore destl' m' = Some t) = (\<exists>tt. accessTypeStore destl' m' = Some tt)"
        using minit_TypeCompChange_somesome[OF mmDef[symmetric]]
        by (metis allocateSameAccess allocateTypeSameAccess m'Def2)
      show "SomeValSomeTyp m'" unfolding SomeValSomeTyp_def
      proof intros
        fix locs
        show "(\<exists>t. accessStore locs m' = Some t) = (\<exists>tt. accessTypeStore locs m' = Some tt) "

        proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc m)) (MTArray x t)")
          case True
          then show ?thesis using somesomeT by simp
        next
          case False
          then have "accessStore locs m' = accessStore locs mem'"
            using "18"(7) nonLocChanged by auto
          moreover have "accessTypeStore locs m' = accessTypeStore locs mem'" using False
            by (metis (no_types, lifting) "18"(7) allocateTypeSameAccess ext m'Def2 minitSingleChange_typedPref_typed mmDef prod.inject)
          ultimately show ?thesis using old
            by (simp add: SomeValSomeTyp_def)
        qed
      qed
    qed
  next
    fix x l
    assume *:"(\<nexists>y y'. x = type.Memory y \<or> x = Value y') \<and> (x, l) |\<in>| fmran (Denvalue e)"
    then obtain ip' where **: "Denvalue e $$ ip' = Some (x, l)" by blast
    then have "ip' \<noteq> ip " using * eDef unfolding updateEnv.simps by auto
    then have "Denvalue ev' $$ ip' = Some (x, l)" using 18 ** decl_env_not_i by (auto split:if_splits)
    then show "(x, l) |\<in>| fmran (Denvalue ev')" using fmranI by metis
  next
    fix sckl ptr
    assume *:" accessStore sckl k' = Some ptr \<and> (\<nexists>y y'. ptr = KMemptr y \<or> ptr = KValue y')"
    have "\<exists>v. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k)) k' = (Some (KMemptr v))"
      using k'Def unfolding push_def allocate_def updateStore_def accessStore_def by simp
    then have "sckl \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc k))" using * by auto
    then have "accessStore sckl k' =accessStore sckl sck'"
      using k'Def 18 unfolding push_def allocate_def updateStore_def accessStore_def by simp
    then show "accessStore sckl sck' = Some ptr " using * by simp
  next
    show "cd' = c" using sameCd by auto
  next
    have "Toploc m' > Toploc m" using topMM m'Def2 unfolding allocate_def by auto
    then show "Toploc mem' \<le> Toploc m'" using 18(7) by simp
  next
    fix locs v
    assume in1:"accessStore locs mem' = Some v "
    then obtain tloc where tlocDef: " (tloc<Toploc mem' \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc)))"
      using 18 typeSafeDeclNone_hyps(1) unfolding TypeSafe_def lessThanTopLocs_def by blast
    then have "\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" using 18(7) LSubPrefL2_def
      by (metis dual_order.refl in1 mLim old.prod.inject option.discI)
    then show "accessStore locs m' = Some v " using in1 nonLocChanged2 18(7) by simp
  next
    fix locs t
    assume in1:"accessTypeStore locs mem' = Some t"
    then obtain v where in2:"accessStore locs mem' = Some v"
      using 18 typeSafeDeclNone_hyps(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
    then obtain tloc where tlocDef: " (tloc<Toploc mem' \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc)))"
      using 18 typeSafeDeclNone_hyps(1) unfolding TypeSafe_def lessThanTopLocs_def by blast
    then have "\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" using 18(7) LSubPrefL2_def
      by (metis dual_order.refl in2 mLim old.prod.inject option.discI)
    then show "accessTypeStore locs m' = Some t"
      using in1 nonLocChanged2_Typed 18(7) by simp
  next
    fix locs
    assume in1:" \<exists>tloc<Toploc mem'. LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc)) \<and> accessStore locs mem' = None"
    then obtain tloc where "tloc<Toploc mem' \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (tloc))" by blast
    then have "\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" using 18(7) LSubPrefL2_def
      by (metis MemLSubPrefTransitive Read_Show_nat'_id ShowLNatDot hash_contains_dot nat_neq_iff)
    then show "accessStore locs m' = None" using in1 nonLocChanged2 18(7) by auto

  qed
qed


lemma typeSafeDeclNone:
  shows "declNonePost ev' sck' cd' mem' st e c m' k'" using typeSafeDeclNone_hyps(2)
proof(cases rule:decl.elims)
  case (1 t _ _ _ _ c' m k e')
  from 1 show ?thesis by (rule typeSafeDeclNone_1)
next
  case (2 t v t' _ _ _ _ c m k e)
  then show ?thesis by simp
next
  case 3
  then show ?thesis by simp
next
  case 4
  then show ?thesis by simp
next
  case 5
  then show ?thesis by simp
next
  case 6
  then show ?thesis by simp
next
  case 7
  then show ?thesis by simp
next
  case 8
  then show ?thesis by simp
next
  case (9 x t p t' cd _ _ c m k e)
  then show ?thesis by simp
next
  case (10 x t p t' _ mem _ c m k e)
  then show ?thesis by simp
next
  case (11 v _ _ _ _ _ _)
  then show ?thesis by simp
next
  case 12
  then show ?thesis by simp
next
  case 13
  then show ?thesis by simp
next
  case (14 v _ _ _ _ _ _ _)
  then show ?thesis by simp
next
  case 15
  then show ?thesis by simp
next
  case 16
  then show ?thesis by simp
next
  case 17
  then show ?thesis by simp
next
  case (18 x t _ _ _ _ c' m k e')
  from 18 show ?thesis by (rule typeSafeDeclNone_18)
next
  case (19 x t p t' _ mem _ c m k e)
  then show ?thesis by simp
next
  case (20 x t p t' _ _ _ c m k e)
  then show ?thesis by simp
next
  case (21 x t p t' _ cd _ _ c m k e)
  then show ?thesis by simp
next
  case (22 x t p x' t' _ _ _ s c m k e)
  then show ?thesis by simp
next
  case (23 v _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (24 _ v _ _ _ _ _)
  then show ?thesis by simp
next
  case 25
  then show ?thesis by simp
next
  case (26 v _ _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (27 v _ _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (28 _ _ v _ _ _ _ _)
  then show ?thesis by simp
next
  case (29 _ _ v _ _ _ _ _)
  then show ?thesis by simp
next
  case (30 _ _ v _ _ _ _ _)
  then show ?thesis by simp
next
  case 31
  then show ?thesis by simp
next
  case 32
  then show ?thesis by simp
next
  case (33 _ v _ _ _ _)
  then show ?thesis by simp
next
  case 34
  then show ?thesis by simp
next
  case (35 v _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (36 v _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (37 _ _ v _ _ _ _)
  then show ?thesis by simp
next
  case (38 _ _ v _ _ _ _)
  then show ?thesis by simp
next
  case (39 _ _ v _ _ _ _)
  then show ?thesis by simp
next
  case 40
  then show ?thesis by simp
next
  case 41
  then show ?thesis by simp
next
  case (42 x t p t' _ _ _ _ c m k e)
  then show ?thesis by simp
next
  case (43 t t' p t'' _ _ _ _ c m k e)
  then show ?thesis by simp
next
  case (44 v _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (45 v _ _ _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (46 v _ _ _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (47 v _ _ _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (48 v _ _ _ _ _ _)
  then show ?thesis by simp
next
  case 49
  then show ?thesis by simp
next
  case 50
  then show ?thesis by simp
next
  case 51
  then show ?thesis by simp
next
  case 52
  then show ?thesis by simp
qed



end

definition ncpElementsNoSubPref::"memoryT \<Rightarrow> memoryT \<Rightarrow> bool"
  where "ncpElementsNoSubPref lmO lmD = (\<forall>i l1 t1 l2 t2 loc i2 loc2. Toploc lmO > i
                                              \<and> Toploc lmO \<le> i2
                                              \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)
                                              \<and> LSubPrefL2 loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)
                                              \<and> MCon (MTArray l1 t1) lmO loc \<longrightarrow>
                                      \<not>TypedMemSubPrefPtrs lmD l2 t2 loc2 loc
                                              \<and> \<not>TypedMemSubPrefPtrs lmD l1 t1 loc loc2)"

definition ncpOMemInDMem::"memoryT \<Rightarrow> memoryT \<Rightarrow> bool"
  where "ncpOMemInDMem lmO lmD = (\<forall>i loc. i < Toploc lmO \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)
                                  \<longrightarrow> accessStore loc lmO = accessStore loc lmD \<and> accessTypeStore loc lmO = accessTypeStore loc lmD)"

text \<open>Every memory reference in \<open>lev0\<close> (the extended environment) that is below the
  top location of the original memory \<open>mem\<close> already existed in the original
  environment \<open>lev\<close> and stack \<open>lk\<close>.\<close>
definition ncpDenvalueLimit::"environment \<Rightarrow> environment \<Rightarrow> stack \<Rightarrow> stack \<Rightarrow> memoryT \<Rightarrow> bool "
  where "ncpDenvalueLimit lev0 lev lk lst mem = (\<forall>tp' locs p i. (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue lev0)
                                            \<and> accessStore locs lk = Some (KMemptr p) \<and> i < Toploc mem \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t i)\<longrightarrow>
                                              (\<exists>tp'' loc2 p'.( (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue lev)
                                                                  \<and> accessStore loc2 lst = Some (KMemptr p') \<and>
                                                     ((p' = p \<and> tp'' = tp' ) \<or> (\<exists>len arr. p' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType mem len arr tp' p' p))))

                     )"

definition ncpNewSelfPoint::"memoryT \<Rightarrow> memoryT \<Rightarrow> bool"
  where "ncpNewSelfPoint lmO lmD = (\<forall>i loc loc2. Toploc lmD > i
                                              \<and> Toploc lmO \<le> i
                                              \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)
                                              \<and> accessStore loc lmD = Some (MPointer loc2)
                                             \<longrightarrow> loc = loc2
                                      )"

lemma ncpElementsNoSubPref_sameMem:
  assumes "TypeSafe e (Accounts st) (Stack st) (Memory st) (Storage st) cd"
  shows "ncpElementsNoSubPref (Memory st) (Memory st)" unfolding ncpElementsNoSubPref_def
proof intros
  fix i l1 t1 l2 t2 loc i2 loc2
  assume f1:" i < Toploc (Memory st) \<and> Toploc (Memory st) \<le> i2
             \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> LSubPrefL2 loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> MCon (MTArray l1 t1) (Memory st) loc"
  then have stringdif:"(ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t i2)"
    by (metis Read_Show_nat'_id linorder_not_less)
  then have notHash1:"\<forall>lll. hash loc lll \<noteq> loc2" using f1
    by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general hash_inequality hash_suffixes_associative)
  have notHash2:"\<forall>lll. hash loc2 lll \<noteq> loc" using f1 stringdif
    by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general hash_inequality hash_suffixes_associative)

  have "\<not> TypedMemSubPrefPtrs (Memory st) l2 t2 loc2 loc \<and> \<not> TypedMemSubPrefPtrs (Memory st) l1 t1 loc loc2"
  proof -
    have " TypeSafe e (Accounts st) (Stack st) (Memory st) (Storage st) cd" using assms by simp
    then have limits:"((\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None) \<and>
               (\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
      unfolding TypeSafe_def lessThanTopLocs_def by blast
    show "\<not> TypedMemSubPrefPtrs (Memory st) l2 t2 loc2 loc \<and> \<not> TypedMemSubPrefPtrs (Memory st) l1 t1 loc loc2"
    proof
      show "\<not> TypedMemSubPrefPtrs (Memory st) l2 t2 loc2 loc"
      proof
        assume f2:"TypedMemSubPrefPtrs (Memory st) l2 t2 loc2 loc"
        then show False
        proof(cases t2)
          case (MTArray x11 x12)
          then obtain i' l where "(i'<l2 \<and> accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some (MPointer l)
                                \<and> (l = loc \<or> TypedMemSubPrefPtrs (Memory st) x11 x12 l loc))"
            using TypedMemSubPrefPtrs.simps(2)[of "Memory st" l2 x11 x12 loc2 loc] f2 by blast
          then show ?thesis using f1 limits
            by (metis LSubPrefL2_def hash_suffixes_associative not_Some_eq)
        next
          case (MTValue x2)
          then have "(\<exists>i<l2. hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = loc)" using TypedMemSubPrefPtrs.simps(1)[of "Memory st" l2 x2 loc2 loc] f2 by auto
          then show ?thesis using notHash2 by simp
        qed

      qed
    next
      show "\<not> TypedMemSubPrefPtrs (Memory st) l1 t1 loc loc2 "
      proof
        assume f2:"TypedMemSubPrefPtrs (Memory st) l1 t1 loc loc2"
        then show False using f1 notHash1
        proof(induction t1 arbitrary:loc l1 i)
          case (MTArray x11 x12)
          then obtain i' l where i'def:"(i'<l1 \<and> accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some (MPointer l)
                                      \<and> (l = loc2 \<or> TypedMemSubPrefPtrs (Memory st) x11 x12 l loc2))"
            using TypedMemSubPrefPtrs.simps(2)[of "Memory st" l1 x11 x12 loc loc2] f2 by blast
          then show ?thesis
          proof(cases "l = loc2")
            case True
            then have "MCon (MTArray l1 (MTArray x11 x12)) (Memory st) loc" using MTArray by blast
            then have " MCon (MTArray x11 x12) (Memory st) loc2 " using MCon.simps(2)[of l1 t1 "Memory st" loc] i'def MTArray
              using CompTypeRemainsMCon True CompMemType.simps(2) by blast
            then have "\<exists>x i. accessStore l (Memory st) = Some x \<or> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x"
              using i'def MCon_imps_Some[of " (MTArray x11 x12)" "Memory st" loc2] True by simp
            then show ?thesis using limits True f1
              by (metis LSubPrefL2_def Not_Sub_More_Specific not_Some_eq)
          next
            case False
            then have "MCon (MTArray l1 (MTArray x11 x12)) (Memory st) loc" using MTArray by blast
            then have " MCon (MTArray x11 x12) (Memory st) l " using MCon.simps(2)[of l1 t1 "Memory st" l] i'def MTArray
              using CompTypeRemainsMCon False CompMemType.simps(2) by blast
            then obtain i'' where i''def: "\<exists>x. accessStore l (Memory st) = Some x \<or> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = Some x"
              using i'def MCon_imps_Some[of " (MTArray x11 x12)" "Memory st" l] False by blast
            then obtain newLoc where nlocdef:"newLoc < Toploc (Memory st) \<and> LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t newLoc)
                                              \<or> LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (ShowL\<^sub>n\<^sub>a\<^sub>t newLoc)"
              using limits by blast
            then have "TypedMemSubPrefPtrs (Memory st) x11 x12 l loc2" using i'def False by simp
            then show ?thesis using MTArray.IH[of x11 l newLoc] MTArray i'def nlocdef
              by (metis MemLSubPrefL2_specific_imps_general \<open>MCon (MTArray x11 x12) (Memory st) l\<close> i''def
                  lessThanSome_imps_Locs_hash lessThanTopLocs_def limits linorder_not_less option.discI)
          qed
        next
          case (MTValue x2)
          then have "(\<exists>i<l1. hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) = loc2)" using TypedMemSubPrefPtrs.simps(1)[of "Memory st" l2 x2 loc loc2] f2 by auto
          then show ?thesis using MTValue by simp
        qed
      qed
    qed
  qed
  moreover show "\<not> TypedMemSubPrefPtrs (Memory st) l2 t2 loc2 loc" using calculation by blast
  ultimately show "\<not> TypedMemSubPrefPtrs (Memory st) l1 t1 loc loc2" by blast
qed


lemma cpm2mrec_somesome:
  "cpm2mrec srcl destl tp ms a = Some v''' \<longrightarrow>
  (\<forall>destl'. TypedMemSubPref destl' destl tp \<longrightarrow> ((\<exists>t. accessStore destl' v''' = Some t)
      \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v''' = Some tt)))"
proof(induction tp arbitrary:destl a v''' srcl )
  case (MTArray x1 t)
  show ?case
  proof intros
    fix destl'
    assume **:"cpm2mrec srcl destl (MTArray x1 t) ms a = Some v'''"
      and ***:"TypedMemSubPref destl' destl (MTArray x1 t)"
    have a5:"(case accessStore srcl ms of None \<Rightarrow> None | Some (MValue literal) \<Rightarrow> None
     | Some (MPointer l) \<Rightarrow>
         let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a in iter' (\<lambda>i. cpm2mrec (hash l
             (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x1)
            = Some v'''"
      using ** cpm2mrec.simps(1)[of srcl destl x1 t ms a] by simp
    then obtain l where ldef:" accessStore srcl ms = Some (MPointer l)" by (auto split:option.splits memoryvalue.splits)
    then have a6:"Some v''' = (let m = updateTypedStore destl (MPointer destl) (MTArray x1 t) a in iter' (\<lambda>i. cpm2mrec (hash l
        (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x1)"
      using a5 by auto
    then obtain m where mdef:"updateTypedStore destl (MPointer destl) (MTArray x1 t) a = m" by auto
    then have v''def:"Some v''' = iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x1" using a6 by simp
    have "(\<exists>t. accessStore destl' v''' = Some t) = (\<exists>tt. accessTypeStore destl' v''' = Some tt)"
      using ***
    proof(induction rule: iter'_induct[OF _ _ v''def[symmetric]])
      case (1)
      then show ?case by simp
    next
      case (2 x v'')
      then obtain v'
        where a10:"iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) m x = Some v'"
          and a20:"(TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
           (\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt))"
          and a30:"cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast
      then show ?case
      proof(cases "destl' = destl")
        case True


        then show ?thesis using 2
          by (metis accessStore_updateStore hash_inequality minitSelfPointers minitSingleChange_typedPref)
      next
        case f1:False
        then show ?thesis
        proof(cases "TypedMemSubPref destl' destl (MTArray x t)")
          case True
          then have "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
            by (metis ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesIntSame not_less_iff_gr_or_eq typedPrefix_imp_SubPref)
          moreover have "\<forall>i<x. \<not> TypedMemSubPref (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using True
            using TypedMemSubPref_hash_index_disjoint_typed by blast
          ultimately have i1:"\<forall>i<x. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''"
            using cpm2mrec_SubPrefixes_typedPref_typed[of _ "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t v' v''] a30
            by (meson ShowLNatDot cpm2mrec_SubPrefixes_typedPref_typed f1 hash_injective)
          have i2:"(\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt)"
            using True a20 by blast

          have i5:"\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
            using a30 cpm2mrec_SubPrefixes by blast
          moreover have i6:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
            using TypedMemSubPref_index_disjoint by blast
          ultimately have i7:"\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''" by auto
          have i8:"\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
            using cpm2mSelfPointers[OF a10] by blast

          show ?thesis using i2
            using True a30 i6 i7 cpm2mrec_SubPrefixes_both by auto
        next
          case False
          then have b5:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
            using 2 TypedMemSubPref.simps(2)[of destl' destl "(Suc x)" t] f1
            using less_Suc_eq
            by (metis TypedMemSubPref.simps(2))
          then have "accessTypeStore destl' m = accessTypeStore destl' v'"
            using False a10 cpm2mSingleChange_typedPref_typed by blast
          then have "cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" using a30 by simp
          then have IH1:"(\<forall>destl'.
        TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        (\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt))"
            using MTArray.IH[of _ "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" v' v''] by simp

          have "(\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt)"
          proof(cases "t")
            case (MTArray x11 x12)
            then have a:"Some v'' = (case accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms of None \<Rightarrow> None | Some (MValue literal) \<Rightarrow> None
     | Some (MPointer l) \<Rightarrow>
         let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v'
         in iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11)"
              using a30 cpm2mrec.simps(1)[of "(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12 ms v']
              by simp
            then obtain ll where lldef:"accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MPointer ll)" by (auto split:option.splits memoryvalue.splits)
            then have a2:"Some v'' = (let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v'
         in iter' (\<lambda>i. cpm2mrec (hash ll (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))
             (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11)" using a by simp
            then obtain m where mdef:"m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v'"
              by simp
            then have v''Def:"Some v'' = iter' (\<lambda>i. cpm2mrec (hash ll (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl
                (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11"
              using a2 lldef by presburger
            then have sameAcc:"accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) m = accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v''"
              using cpm2mSingleChange_typedPref_typed by presburger
            have "\<not> TypedMemSubPref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12)"
              by (metis LSubPrefL2_def TypedMemSubPref.simps(2) hash_flatten_right hash_inequality typedPrefix_imp_SubPref)
            then have sameAccV:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) m = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v''"
              using cpm2mSingleChange_typedPref v''Def by presburger
            have acc:"accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) m = Some (MTArray x11 x12)"
              using mdef unfolding updateTypedStore_def updateTypeStore_def accessTypeStore_def updateStore_def by auto

            have accV:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
              using sameAccV mdef
              unfolding updateTypedStore_def updateTypeStore_def accessTypeStore_def
                updateStore_def accessStore_def
              by auto
            then show ?thesis
            proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
              case True
              then have "CompMemType v'' (Suc x) t t destl destl'"
                using MTArray accV by auto
              moreover have "\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12"
                using cpm2m_TypeCompChangeIndexs[OF v''Def[symmetric]] True by auto
              ultimately show ?thesis using MTArray
                using True acc accV sameAcc by auto
            next
              case False
              then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using b5 by auto
              then have "(\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt)"
                using IH1 MTArray by simp
              then show ?thesis using MTArray accV by auto
            qed
          next
            case (MTValue x2)
            then show ?thesis using IH1 b5 by auto
          qed

          then show ?thesis by blast
        qed
      qed
    qed
    then show "(\<exists>t. accessStore destl' v''' = Some t) = (\<exists>tt. accessTypeStore destl' v''' = Some tt)" by auto
  qed
next
  case (MTValue x)
  show ?case
  proof intros
    fix destl'
    assume **:" cpm2mrec srcl destl (MTValue x) ms a = Some v'''"
    assume ***:"TypedMemSubPref destl' destl (MTValue x)"
    then have mdef:"Some v''' = (case accessStore srcl ms of None \<Rightarrow> None | Some (MValue v) \<Rightarrow> Some (updateTypedStore destl (MValue v) (MTValue x) a)
     | Some (MPointer literal) \<Rightarrow> None)"
      using ** cpm2mrec.simps(2)[of srcl destl x ms a] by simp
    then obtain v where vdef: "accessStore srcl ms = Some (MValue v)" by (auto split:option.splits memoryvalue.splits)
    then have v'''def:"Some v''' = Some (updateTypedStore destl (MValue v) (MTValue x) a)" using mdef by simp
    then have "accessTypeStore destl v''' = Some (MTValue x)" using mdef
      unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def by simp
    moreover have "accessStore destl' v''' = Some (MValue v)"
      using v'''def unfolding accessTypeStore_def updateTypedStore_def updateTypeStore_def updateStore_def accessStore_def
      using "***" by auto
    ultimately show "(\<exists>t. accessStore destl' v''' = Some t) = (\<exists>tt. accessTypeStore destl' v''' = Some tt)"
      using "***" by fastforce
  qed
qed

lemma cpm2m_TypeCompChange_somesome:
  assumes "iter' (\<lambda>i m''. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms m'') md x1 = Some v'"
  shows "(\<forall>destl'. TypedMemSubPref destl' destl (MTArray x1 t) \<longrightarrow>
          ((\<exists>t. accessStore destl' v' = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v' = Some tt)))"
proof(induction rule: iter'_induct[OF _ _ assms(1)])
  case (1)
  then show ?case by simp
next
  case (2 x v'')
  then obtain v'
    where a10: "iter' (\<lambda>i. cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t ms) md x = Some v'"
      and a20: "(\<forall>destl'. TypedMemSubPref destl' destl (MTArray x t) \<longrightarrow>
             ((\<exists>t. accessStore destl' v' = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v' = Some tt)))"
      and a30: "cpm2mrec (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t ms v' = Some v''" by blast

  show ?case
  proof intros
    fix destl'
    assume a1:"TypedMemSubPref destl' destl (MTArray (Suc x) t)"
    show "((\<exists>t. accessStore destl' v'' = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore destl' v'' = Some tt))"
    proof(cases "TypedMemSubPref destl' destl (MTArray x t)")
      case True
      then have "destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using True
        by (metis ShowLNatDot TypedMemSubPref.simps(2) hash_int_prefix hashesIntSame not_less_iff_gr_or_eq typedPrefix_imp_SubPref)
      moreover have "\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using True
        using TypedMemSubPref_index_disjoint_typed by blast
      ultimately have i1:"\<forall>destl'. destl' \<noteq> hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x) \<and> \<not> TypedMemSubPref destl'
          (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<longrightarrow>
        accessTypeStore destl' v' = accessTypeStore destl' v''"
        using cpm2mrec_SubPrefixes_typedPref_typed[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" ] a30 by simp
      have i2:"(\<exists>t. accessStore destl' v' = Some t) = (\<exists>tt. accessTypeStore destl' v' = Some tt)"
        using True a20 by blast

      have store_preserved: "\<forall>locs. \<not> LSubPrefL2 locs (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) \<longrightarrow> accessStore locs v' = accessStore locs v''"
        using a30 cpm2mrec_SubPrefixes by blast
      moreover have no_prefix_conflict: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
        using TypedMemSubPref_index_disjoint by blast
      ultimately have store_consistency: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''"
        by auto

      show ?thesis using i2
        using True \<open>\<not> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t\<close> \<open>destl' \<noteq> hash
            destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> i1 store_consistency by force

    next
      case False
      then have a2:"TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t \<or> destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)"
        using a1 unfolding TypedMemSubPref.simps
        using less_SucE by blast
      then show ?thesis
      proof(cases t)
        case (MTArray x11 x12)
        then have a:"Some v'' = (case accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms of None \<Rightarrow> None | Some (MValue literal) \<Rightarrow> None
     | Some (MPointer l) \<Rightarrow>
         let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v'
         in iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11)"
          using a30 cpm2mrec.simps(1)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x11 x12 ms v'] by auto
        then obtain l where ldef:"accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MPointer l)" by (auto split:option.splits memoryvalue.splits)
        then have a2':"Some v''= (let m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v'
         in iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))
             (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11)" using a by simp
        then obtain m where mdef:"m = updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))) (MTArray x11 x12) v'"
          by simp
        then have v''Def:"Some v'' = iter' (\<lambda>i. cpm2mrec (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash (hash destl
            (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) x12 ms) m x11"
          using a2' by presburger
        then have sameAcc:"accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) m = accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v''"
          using cpm2mSingleChange_typedPref_typed by presburger
        have "\<not> TypedMemSubPref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12)"
          by (metis LSubPrefL2_def TypedMemSubPref.simps(2) hash_flatten_right hash_inequality typedPrefix_imp_SubPref)
        then have sameAccV:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) m = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v''"
          using cpm2mSingleChange_typedPref[of l "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x12 ms m x11 v''] v''Def by simp
        have acc:"accessTypeStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) m = Some (MTArray x11 x12)"
          using mdef unfolding updateTypedStore_def updateTypeStore_def accessTypeStore_def updateStore_def by auto

        have accV:"accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) v'' = Some (MPointer (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
          using sameAccV mdef
          unfolding updateTypedStore_def updateTypeStore_def accessTypeStore_def
            updateStore_def accessStore_def
          by auto
        then show ?thesis
        proof(cases "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)")
          case True
          then have "\<forall>i<x11. TypedMemSubPref (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MTArray x11 x12)" by auto
          then have "\<forall>i<x11. accessTypeStore (hash (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12"
            using cpm2m_TypeCompChangeIndexs[OF v''Def[symmetric]] by blast
          moreover have "CompMemType v'' (Suc x) (MTArray x11 x12) (MTArray x11 x12) destl destl'"
            using MTArray True accV unfolding CompMemType.simps by blast
          ultimately show ?thesis using acc sameAcc MTArray accV
            using mtypes.simps(5) True by simp
        next
          case False
          then have "TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t" using a2 by blast
          then have "(\<exists>t. accessStore destl' v'' = Some t) = (\<exists>tt. accessTypeStore destl' v'' = Some tt)"
            using cpm2mrec_somesome[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" t ms v' v''] a30 by simp
          then show ?thesis using MTArray accV by auto
        qed
      next
        case (MTValue x2)
        then have "destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)" using a2 by simp
        then have v'':"Some v'' = (case accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms of None \<Rightarrow> None
     | Some (MValue v) \<Rightarrow> Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v') | Some (MPointer literal) \<Rightarrow> None)"
          using a30 cpm2mrec.simps(2)[of "(hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" "(hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" x2 ms v' ] MTValue by simp
        then obtain v where "accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) ms = Some (MValue v)" by (auto split:option.splits memoryvalue.splits)
        then have "Some v'' = Some (updateTypedStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) (MValue v) (MTValue x2) v')" using v'' by simp
        then show ?thesis unfolding updateTypeStore_def updateTypedStore_def accessTypeStore_def updateStore_def using MTValue
          using \<open>destl' = hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)\<close> accessTypeStore_def
          by (metis TypedMemSubPref.simps(1) a30 cpm2mrec_somesome)
      qed
    qed
  qed
qed

text \<open>Postcondition of @{const decl} with an initial value.\<close>

abbreviation declPost :: "environment \<Rightarrow> 'a state_scheme \<Rightarrow> bool \<Rightarrow> memoryT \<Rightarrow> environment \<Rightarrow> calldataT \<Rightarrow> memoryT \<Rightarrow> stack \<Rightarrow> bool"
  where "declPost ev st cp mem' e c m' k' \<equiv> TypeSafe e (Accounts st) k' m' (Storage st) c \<and>
        (\<not>cp \<longrightarrow> (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs)
                  \<and> Toploc (Memory st) \<le> Toploc (m')
                  \<and> ncpDenvalueLimit e ev k' (Stack st ) (Memory st)
                  \<and> ncpOMemInDMem (Memory st) m'
                  \<and> ncpElementsNoSubPref (Memory st) m'
                  \<and> ncpNewSelfPoint (Memory st) m'
        ) \<and> Toploc m' \<ge> Toploc mem'"

context
  fixes c cd cd' cp e ev ev' ip k' m' mem' sck' st t'' tp v
  assumes typeSafeDecl_hyps: "TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd"
      "valueCon ev cd st v t''"
      "TypeSafe ev' (Accounts st) sck' mem' (Storage st ) cd'"
      "decl ip tp (Some (v,t'')) cp cd (Memory st) (Storage st (Address ev)) (cd', mem', sck', ev') = Some (c, m', k', e)"
      "\<not>cp \<longrightarrow> (\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp mem' locs) \<and> Toploc (Memory st) \<le> Toploc (mem')
                  \<and> ncpDenvalueLimit ev' ev sck' (Stack st) (Memory st)
                  \<and> ncpOMemInDMem (Memory st) mem'
                  \<and> ncpElementsNoSubPref (Memory st) mem'
                  \<and> ncpNewSelfPoint (Memory st) mem'"
      "\<forall>struct.
       t'' = type.Memory struct \<longrightarrow>
       (\<exists>stloc tp'' p. (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and> accessStore stloc (Stack st) = Some (KMemptr p) \<and> (tp'' = struct \<and> v = (KMemptr p)
      \<or> (\<exists>len arr. p \<noteq> (extractValueType v) \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr struct p (extractValueType v))))"
      "\<forall>struct.
       t'' = Calldata struct \<longrightarrow>
       (\<exists>stloc tp'' p. (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and> accessStore stloc (Stack st) = Some (KCDptr p) \<and> (tp'' = struct \<and> v = (KCDptr p)
      \<or> (\<exists>len arr. p \<noteq> (extractValueType v) \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))"
      "\<forall>struct. tp = type.Storage struct \<longrightarrow> (\<forall>locs tp. SCon tp locs (Storage st (Address ev))
        \<longrightarrow> SCon tp locs (Storage st (Address ev'))) \<and> (\<exists>loc tp'' p. (type.Storage tp'', loc) |\<in>| fmran
        (Denvalue ev')
                                                \<and>(case loc of Stackloc stloc \<Rightarrow>
                                                                  (accessStore stloc sck' =Some (KStoptr p) \<and> ((tp'' = struct \<and> v = KStoptr p) \<or>
                                                                  ((extractValueType v) \<noteq> p \<and> CompStoType tp'' struct p (extractValueType v))))
                                                              | Storeloc stloc \<Rightarrow>
                                                                  (((tp'' = struct \<and> v = KStoptr stloc) \<or>
                                                                  ((extractValueType v) \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v))))
                                                              ))"
begin

text \<open>A value-type variable initialised with a value, converted to the declared type.\<close>

lemma typeSafeDecl_2:
  assumes "tp = Value t"
    and "Some (v, t'') = Some (KValue vc, Value t')"
    and "cp = cp0"
    and "cd = cd0"
    and "state.Memory st = mem0"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (cdc', mem'', sck'', ev'')"
    and "Some (c, m', k', e) = convert t' t vc \<bind> (\<lambda>v'. Some (cdc', mem'', astack_dup ip (Value t) (KValue v') (sck'', ev'')))"
  shows "declPost ev st cp mem' e c m' k'"
proof -
  let ?case = "declPost ev st cp mem' e c m' k'"
  note 2 = assms
  then obtain v' where a10:"(convert t' t vc) = Some v'" using decl.simps(2) by fastforce
  then have a20:"v' = vc" using convertSame by metis
  have "typeCon t' vc" using typeSafeDecl_hyps(2) 2 by simp
  then have a30:"typeCon t vc" using a10 a20 typeSafeConvert by simp
  show ?thesis
  proof(cases "Denvalue ev' $$ ip")
    case (Some a)
    then have same:"(cdc', mem', sck', ev') = (c, m', k', e)" using 2 a10 unfolding astack_dup.simps by simp
    show ?thesis
    proof intros
      show "TypeSafe e (Accounts st) k' m' (Storage st) c" using typeSafeDecl_hyps(3) same 2(7) by blast
      show "\<And>locs tp. \<not> cp \<Longrightarrow> MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using typeSafeDecl_hyps(5) same 2(7) by simp
      show "\<not> cp \<Longrightarrow> Toploc (Memory st) \<le> Toploc m'" using typeSafeDecl_hyps(5) same 2(7) by simp
      show "\<not> cp \<Longrightarrow> ncpDenvalueLimit e ev k' (Stack st) (Memory st)" using typeSafeDecl_hyps(5) same 2(7) by simp
      show "\<not> cp \<Longrightarrow> ncpOMemInDMem (Memory st) m'" using typeSafeDecl_hyps(5) same 2(7) by simp
      show "\<not> cp \<Longrightarrow> ncpElementsNoSubPref (Memory st) m'" using typeSafeDecl_hyps(5) same 2(7) by simp
      show "\<not> cp \<Longrightarrow> ncpNewSelfPoint (Memory st) m'" using typeSafeDecl_hyps(5) same 2(7) by simp
      show "Toploc mem' \<le> Toploc m'" using typeSafeDecl_hyps(5) same 2(7) by simp
    qed
  next
    case None
    then have a40:"(Some (cdc', mem', astack ip (Value t) (KValue vc) (sck', ev'))) = Some (c, m', k', e)" using 2 decl.simps(2) a10 typeSafeDecl_hyps(1) a20 by simp
    then have a50:"k' = push (KValue vc) sck'" using 2 by force

    have a60:"e = (updateEnv ip (Value t) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev')" using a40 a10 by simp
    then have a70:"Denvalue e = Denvalue(ev' \<lparr> Denvalue := fmupd ip ((Value t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) (Denvalue ev') \<rparr>)" by simp
    then have a80:"(Denvalue e) $$ ip = Some ((Value t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp

    show ?thesis unfolding TypeSafe_def
    proof(intros)

      show "unique_locations (Denvalue e)" using typeSafeDecl_hyps(3) 2(7) updateEnvUniqueLocs a40 by fastforce
    next
      have b2: "compPointers sck' (Denvalue ev')" using typeSafeDecl_hyps(3) 2(7) unfolding TypeSafe_def by auto
      have "Address ev' = Address e"using a70 a60
        by simp
      moreover have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 2(7) by simp
      ultimately show "compPointers k' (Denvalue e)"
        using compPointersNonStackUpd[of sck' ev' e ip "Value t" k' "KValue vc" ] a70 a50 typeSafeDecl_hyps(3) 2(7) b2 by simp
    next
      have *:"safeContract (Accounts st) (Storage st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def using 2(7) by auto
      have **:"Address ev' = Address e"using a70 a60
        by simp
      have ***:"Contract ev' = Contract e" using a70 a60 by simp
      show "safeContract (Accounts st) (Storage st) " using * by auto
    next
      show "balanceTypes (Accounts st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
    next
      show "svalueTypes (Svalue e)" using a60 2(7) typeSafeDecl_hyps(3) TypeSafe_def svalueTypes_def by simp
    next
      have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 2(7) by simp
      then show "lessThanTopLocs k'" using stackPushToplocSafe a50 2(7) by metis
    next
      have "lessThanTopLocs cdc'" using typeSafeDecl_hyps(3) TypeSafe_def 2(7) by simp
      then show "lessThanTopLocs c" using stackPushToplocSafe a50 2(7) a40 by simp
    next
      have "lessThanTopLocs mem'" using typeSafeDecl_hyps(3) TypeSafe_def 2(7) by simp
      then show "lessThanTopLocs m'" using 2(7) a40 by simp
    next
      have "addressFormat (Address ev')" using typeSafeDecl_hyps(3) TypeSafe_def 2(7) by simp
      then show "addressFormat(Address e)" using 2(7) a40 by auto
    next
      have "addressFormat (Sender ev')" using typeSafeDecl_hyps(3) TypeSafe_def 2(7) by simp
      then show "addressFormat (Sender e)" using 2(7) a40 by auto
    next
      show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c " unfolding typeCompat_def
      proof intros
        fix tDen lDen
        assume *: "(tDen, lDen) |\<in>| fmran (Denvalue e)"
        then obtain ip'' where a90:"Denvalue e $$ ip'' = Some (tDen, lDen)" using * by auto
        then have a100:"(Storage st (Address ev')) = (Storage st (Address e))" using typeSafeDecl_hyps(3) a60 by simp
        have a110:"m' = mem'" and a115:"cdc' = c" using a40 by simp+
        have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 2(7) by simp
        have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''" using
            lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def typeSafeDecl_hyps(3) TypeSafe_def 2(7) by auto
        then have a140:"\<forall>x y. \<not>((Denvalue ev') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc
            sck'))))" using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 2(7) by fastforce
        have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip" using a70 a140 fmranI by auto
        then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''') \<and>
            l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip" using a70
            lessThanTopLocs_def fmranI by auto
        show "denvalueCon k' m' (Storage st (Address e)) c tDen lDen"
        proof(cases lDen)
          case (Stackloc x1)
          then show ?thesis
          proof (cases "x1 = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')")
            case True
            then have a170: "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KValue vc)" using a50 by (simp add:push_def allocate_def updateStore_def accessStore_def)

            then show ?thesis
            proof(cases "accessStore x1 k'")
              case None
              then show ?thesis using True a170 Stackloc by simp
            next
              case some:(Some a)
              then have a180:"a = (KValue vc) " using a170 True by simp
              have a190:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KValue vc)" using a50 by (simp add:push_def allocate_def updateStore_def accessStore_def)
              then have "ip'' = ip" using a150 True a90 Stackloc by simp
              then have "tDen = Value t" using a90 a80 by simp
              then show ?thesis using Stackloc some a180 a30 a190 True by simp
            qed
          next
            case False

            then have "ip'' \<noteq> ip" using a160 a90 Stackloc by simp
            then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev')" using a70 Stackloc fmranI a90 False * by fastforce
            then obtain y' where a180:"accessStore x1 sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) Stackloc 2(7) by blast
            then have a190:"accessStore x1 k' = accessStore x1 sck'" using a50 False by (simp add:push_def allocate_def updateStore_def accessStore_def)
            then show ?thesis
            proof(cases "accessStore x1 k'")
              case None
              then show ?thesis using a180 a190 Stackloc by simp
            next
              case some:(Some a)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a115 a100 2(7)
                by (cases a; cases tDen; force+)
            qed
          qed
        next
          case (Storeloc x2)
          then have a170:"ip'' \<noteq> ip" using a70 Storeloc a90 by auto
          then have a180: "(tDen, lDen) |\<in>| fmran (Denvalue ev')" using a70 Storeloc fmranI a90 by fastforce
          then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def using Storeloc a100 2(7) by (cases tDen;force)
        qed
      qed
    next
      show "AddressTypes (Accounts st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by simp

    next
      have a110:"m' = mem'" using a40 by simp
      then show "\<And>locs tp. \<not> cp \<Longrightarrow> MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using typeSafeDecl_hyps(5) 2(7) typeSafeDecl_hyps(5) by (simp)
    next
      assume "\<not> cp"
      then show "Toploc (Memory st) \<le> Toploc m'" using typeSafeDecl_hyps(5) 2(7) a40 by blast
    next
      assume notCP:"\<not>cp"
      show "ncpDenvalueLimit e ev k' (Stack st) (Memory st) "
        unfolding ncpDenvalueLimit_def
      proof intros
        fix tp' locs p i
        assume a120:" (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue e) \<and> accessStore locs k' = Some (KMemptr p) \<and> i <
            Toploc (Memory st) \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''" using
            lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def typeSafeDecl_hyps(3) TypeSafe_def 2(7) by auto
        then have a140:"\<forall>x y. \<not>((Denvalue ev') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))"
          using lessThanTopLocs_def Read_Show_nat'_id typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 2(7) by fastforce
        have a150: "\<forall>ip''' . Denvalue e $$ ip''' = Some ((Value t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip" using a70 a140 fmranI by auto
        then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''') \<and>
            l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip" using a70
            lessThanTopLocs_def fmranI by auto
        show " \<exists>tp'' loc2 p'.
            (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
            accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p \<and>
                tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp'
                p' p))
            "
        proof -
          obtain ip'' where ip''def:"(Denvalue e) $$ ip'' = Some (type.Memory tp', Stackloc locs)" using a120 by blast
          then have a170:"ip'' \<noteq> ip" using a70 by auto
          then have a180: "(type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev')" using a70 fmranI ip''def by fastforce
          have a190:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))" using a160 a170
            by (metis a140 a180 fmlookup_ran_iff snd_eqD)
          then obtain y' where a200:"accessStore locs sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) 2(7) a180 by blast
          then have "accessStore locs k' = accessStore locs sck'" using a50 a120 a190 unfolding push_def allocate_def updateStore_def accessStore_def by simp
          then show " \<exists>tp'' loc2 p'.
            (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
            accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p \<and>
                tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp'
                p' p))"
            using typeSafeDecl_hyps(5) 2(7) a120 a40 a60 a120 a180 notCP ncpDenvalueLimit_def
            by (metis)
        qed

      qed
    next
      show "denvalueTypeCorrectness e k' m'"
        unfolding denvalueTypeCorrectness_def
      proof(intros)
        fix t l ptr_loc
        assume *:" (type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"
        then have "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue ev')"
          using a40 unfolding astack.simps updateEnv.simps
          by (metis (no_types, lifting) Environment.unfold_congs(5) type.distinct(3) a80 DenvalueChange fmlookup_ran_iff option.inject
              prod.inject)
        moreover have "accessStore l k' = accessStore l sck'"
          using a40 * unfolding astack.simps push_def updateStore_def accessStore_def allocate_def
          by (metis stackvalue.distinct(3) a50 accessStore_def accessStore_non_changed accessStore_updateStore allocateSameAccess option.inject
              push_def)
        ultimately show "case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
          using a40 typeSafeDecl_hyps(3) * unfolding TypeSafe_def denvalueTypeCorrectness_def using 2(7) by auto
      qed
    next
      show "subPrefixStructuralConsistency m'"
        using typeSafeDecl_hyps(3) a40 2(7) unfolding TypeSafe_def subPrefixStructuralConsistency_def by auto
    next
      show "SomeValSomeTyp m'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def using a40 2(7) by blast
    next
      assume notCP:"\<not>cp"
      then show "ncpOMemInDMem (Memory st) m'" using a40 2(7) typeSafeDecl_hyps by simp
    next
      assume notCP:"\<not>cp"
      then show "ncpElementsNoSubPref (Memory st) m'" using a40 typeSafeDecl_hyps 2 by blast
    next
      assume notCP:"\<not>cp"
      then show "ncpNewSelfPoint (Memory st) m'" using a40 typeSafeDecl_hyps 2 by blast
    next
      show "Toploc mem' \<le> Toploc m' " using a40 by simp
    qed
  qed
qed

text \<open>A calldata array initialised from a calldata pointer with copying: the array is copied into the new calldata.\<close>

lemma typeSafeDecl_9:
  assumes "tp = Calldata (MTArray x t)"
    and "Some (v, t'') = Some (KCDptr p, tv0)"
    and "cp"
    and "cd = cdc"
    and "state.Memory st = mem0"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (cdc', mem'', sck'', ev'')"
    and "Some (c, m', k', e) = (if tv0 = Calldata (MTArray x t) \<and> 0 < x \<and> Denvalue
        ev'' $$ ip = None then let l = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc cdc')); (uub, c') = allocate cdc' in cpm2m p l x t cdc c'
            \<bind> (\<lambda>c''. Some (c'', mem'', astack_dup ip (Calldata (MTArray x t)) (KCDptr l) (sck'', ev''))) else None)"
  shows "declPost ev st cp mem' e c m' k'"
proof -
  let ?case = "declPost ev st cp mem' e c m' k'"
  note 9 = assms
  then obtain l where a1:"l = ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc cdc')" by simp
  have tv0:"tv0 = Calldata (MTArray x t)" using decl.simps(9) 9(8) by (simp split:if_split_asm)
  then have locationscd':"(\<forall>tloc loc. Toploc cdc' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)
      \<longrightarrow> accessStore loc cdc' = None)" using typeSafeDecl_hyps 9 unfolding TypeSafe_def lessThanTopLocs_def by simp
  then have b1:"accessStore l cdc' = None" using a1 using Read_Show_nat'_id using LSubPrefL2_def by auto
  have b2:"x>0" using 9(8) tv0 a1 by (metis not_None_eq)
  then have Mconcd:"MCon (MTArray x t) cdc (extractValueType v)" using typeSafeDecl_hyps(2) 9(2) 9(4) tv0 by simp
  obtain c' where a2:"\<exists>dud. (dud, c') = allocate cdc'" by (simp add: allocate_def)
  then have lNotInC':"accessStore l c' = None" using b1 a1 unfolding allocate_def accessStore_def by simp
  obtain c'' where a3:"cpm2m p l x t cdc c' = Some c''" using 9 a1 a2 typeSafeDecl_hyps
    by (metis (no_types, lifting) bind.bind_lzero case_prod_conv option.discI option.exhaust)

  have NoneIp:"Denvalue ev'' $$ ip = None" using 9 by (auto split:if_splits)
  then have a4:"Some (c, m', k', e) = Some (c'', mem'', astack_dup ip (Calldata (MTArray x t)) (KCDptr l) (sck', ev''))"
    using a1 a2 a3 9(7,8) b2 tv0
    by (metis bind.bind_lunit case_prod_conv)
  then have a20:"k' = push (KCDptr l) sck'" using 9 NoneIp tv0 a3 unfolding astack_dup.simps by simp
  have a30:"e = (updateEnv ip (Calldata (MTArray x t)) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev'')" using a4 NoneIp unfolding astack_dup.simps by simp
  then have a40:"Denvalue e = Denvalue(ev' \<lparr> Denvalue := fmupd ip (Calldata (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) (Denvalue ev'') \<rparr>)" by simp
  then have a50:"(Denvalue e) $$ ip = Some (Calldata (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp
  show ?thesis unfolding TypeSafe_def
  proof(intros)
    show "unique_locations (Denvalue e)" using typeSafeDecl_hyps(3) 9(7) astack_dup_is_astack NoneIp updateEnvUniqueLocs a4 by fastforce
  next
    have b2: "compPointers sck' (Denvalue ev'')" using typeSafeDecl_hyps(3) 9(7) unfolding TypeSafe_def by auto
    have "Address ev'' = Address e"using a30 by simp
    moreover have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 9(7) by simp
    ultimately show "compPointers k' (Denvalue e)"
      using compPointersNonStackUpd[of sck' ev' e ip " Calldata (MTArray x t)" k' "KCDptr l" ]
        a40 a50 typeSafeDecl_hyps(3) 9(7) b2 a20 by simp

  next
    show "safeContract (Accounts st) (Storage st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "balanceTypes (Accounts st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "svalueTypes (Svalue e)" using a30 9(7) typeSafeDecl_hyps(3) TypeSafe_def svalueTypes_def by simp
  next
    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 9(7) by simp
    then show "lessThanTopLocs k'" using stackPushToplocSafe a20 9(7) by metis
  next
    have "addressFormat (Address ev') " using typeSafeDecl_hyps(3) TypeSafe_def 9(7) by simp
    then show "addressFormat(Address e)" using 9(7) a4 NoneIp by auto
  next
    have "addressFormat (Sender ev')" using typeSafeDecl_hyps(3) TypeSafe_def 9(7) by simp
    then show "addressFormat (Sender e)" using 9(7) a4 NoneIp by auto
  next
    show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c" unfolding typeCompat_def
    proof intros
      fix tDen lDen
      assume *: "(tDen, lDen) |\<in>| fmran (Denvalue e)"
      then obtain ip'' where a90:"Denvalue e $$ ip'' = Some (tDen, lDen)" using * by auto
      then have a100:"(Storage st (Address ev'')) = (Storage st (Address e))" using a30 by simp
      have a110:"m' = mem''" using a4 by simp
      have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 9(7) by simp
      then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''" using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
      then have a140:"\<forall>x y. \<not>((Denvalue ev'') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc
          sck'))))" using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 9(7) by fastforce
      then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))
          \<longrightarrow> ip''' = ip" using a40 lessThanTopLocs_def fmranI by auto
      then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''') \<and>
          l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip" using a40 fmranI by
          auto
      show "denvalueCon k' m' (Storage st (Address e)) c tDen lDen"
      proof(cases lDen)
        case (Stackloc x1)
        then show ?thesis
        proof (cases "x1 = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')")
          case True
          then have a170: "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KCDptr l)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using True a170 Stackloc by simp
          next
            case some:(Some a)
            then have a180:"a = KCDptr l " using a170 True by simp
            have a190:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KCDptr l)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
            then have "ip'' = ip" using a150 True a90 Stackloc by simp
            then have a200:"tDen = Calldata (MTArray x t)" using a90 a50 by simp
            then have a210:"t'' = tDen" using 9(2) tv0 by simp
            have a220:"v = KCDptr p" using 9(2) by simp
            have "c = c''" using a4 by simp
            then have "MCon (MTArray x t) c'' l" using a3 unfolding cpm2m_def
              using MCon_cpm2m[of p l t cdc c' x] Mconcd 9(2)
              by (metis a220 lNotInC' extractValueType.simps(2))
            then have "MCon (MTArray x t) c l" using a4 a110 9(7) by blast
            then show ?thesis using Stackloc some a180 a200 extractValueType.simps(4) 9(2) by simp
          qed
        next
          case False
          then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs c''"
            using a3 a1 cpm2m_def[of p l x t cdc c'] cpm2mSingleChange[of p l t cdc c' x c''] by fastforce

          have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc cdc' = None" using locationscd' a2 lNotInC' a1 by auto
          have "\<forall>locations. accessStore locations cdc' = accessStore locations c'" using a2 accessAllocate[of c' cdc'] by auto
          then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs cdc' = accessStore locs c''" using b100 a2 unfolding allocate_def by simp

          then have "ip'' \<noteq> ip" using a160 a90 Stackloc False by simp
          then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')" using a40 Stackloc fmranI a90 False * by fastforce
          then obtain y' where a180:"accessStore x1 sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) Stackloc 9 by blast
          then have a190:"accessStore x1 k' = accessStore x1 sck'" using a20 False by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using a180 a190 Stackloc by simp
          next
            case some:(Some a)
            then show ?thesis
            proof(cases a)
              case (KValue x1)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 9(7) by (cases tDen, fastforce+)
            next
              case (KCDptr x2)
              then have b10:"(case tDen of Calldata struct \<Rightarrow> MCon struct cdc' x2 | _ \<Rightarrow> False)"
                using some KCDptr a170 Stackloc a190 using typeSafeDecl_hyps(3) 9(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = Calldata struct" by (auto split:type.splits)
              then have "MCon struct cdc' x2" using b10 by simp
              then have "MCon struct c'' x2" using mconCopySingle[of l cdc' c'' struct x2] b110 b105 by auto
              then show ?thesis using Stackloc some KCDptr tden a110 a4 by simp
            next
              case (KMemptr x3)
              then have b10:"(case tDen of type.Memory struct \<Rightarrow> MCon struct mem' x3 | _ \<Rightarrow> False)"
                using some a170 Stackloc a190 using typeSafeDecl_hyps(3) 9(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = type.Memory struct" by (auto split:type.splits)
              then have "MCon struct mem' x3" using b10 by simp
              then show ?thesis using Stackloc some KMemptr tden a110 a4 9 by simp
            next
              case (KStoptr x4)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 9(7) by (cases tDen; fastforce)
            qed
          qed
        qed
      next
        case (Storeloc x2)
        then have "ip'' \<noteq> ip" using a160 a90 by simp
        then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')" using a40 Storeloc fmranI a90 * by fastforce
        then have a180:"(case tDen of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st (Address ev'')) | _ \<Rightarrow> False)" using a170 Storeloc using typeSafeDecl_hyps(3) 9(7)
          unfolding TypeSafe_def typeCompat_def by force
        then obtain typ' where tdent:"tDen = type.Storage typ'" by (auto split: type.splits)
        then have "SCon typ' x2 (Storage st (Address ev''))" using a180 by simp
        then have "SCon typ' x2 (Storage st (Address e))" using a100 by simp
        then show ?thesis using a170 Storeloc using typeSafeDecl_hyps(3) 9(7) tdent
          by simp
      qed
    qed
  next
    have b100:"lessThanTopLocs cdc'" using typeSafeDecl_hyps(3) 9(7) unfolding TypeSafe_def by blast
    have b99:"Toploc c' = Toploc c" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x c''] b2 by simp
    have " \<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs c"
      using cpm2mSingleChange[of p l t cdc c' x] a4 a3 cpm2m_def[of p l x t cdc c' ] by fastforce
    moreover have "\<forall>locations. accessStore locations cdc' = accessStore locations c'" using a2 accessAllocate[of c' cdc'] by auto
    ultimately have b10:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs cdc' = accessStore locs c" by simp
    then show "lessThanTopLocs c" using cdMemLocsToploc[of cdc' l c' c] a1 a2 b100 b99 by auto
  next
    show "lessThanTopLocs m'" using typeSafeDecl_hyps(3) 9(7) a4 unfolding TypeSafe_def by auto

  next
    show "AddressTypes (Accounts st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by simp
  next
    have a110:"m' = mem'" using a4 9 by simp
    then show "\<And>locs tp. \<not> cp \<Longrightarrow> MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using typeSafeDecl_hyps(5) 9(7) typeSafeDecl_hyps(5) by (simp)
  next
    show "denvalueTypeCorrectness e k' m'" unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t l ptr_loc
      assume *:" (type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"
      then have "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue ev')"
        using a4 unfolding astack.simps updateEnv.simps
        by (metis (no_types, lifting) type.distinct(7) a50 typeSafeDecl_hyps(4) decl_env_not_i fmlookup_ran_iff
            option.inject prod.inject)
      moreover have "accessStore l k' = accessStore l sck'"
        using a40 * unfolding astack.simps push_def updateStore_def accessStore_def allocate_def
        by (metis (no_types, lifting) accessStore_def typeSafeDecl_hyps(3,4) calculation decl_stack_change
            fmlookup_ran_iff snd_eqD TypeSafe_def stackLocs_imp_NotDen)
      ultimately show "case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
        using a4 typeSafeDecl_hyps(3) * unfolding TypeSafe_def denvalueTypeCorrectness_def using 9(7) by auto
    qed
  next
    show "subPrefixStructuralConsistency m'"
      using typeSafeDecl_hyps(3) a4 9(7) unfolding TypeSafe_def subPrefixStructuralConsistency_def by auto
  next
    show "SomeValSomeTyp m'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def using a4 9(7) by blast
  next
    assume notCp:"\<not>cp"
    then show "Toploc (Memory st) \<le> Toploc m'" using a4 typeSafeDecl_hyps 9 by auto
    then show "ncpDenvalueLimit e ev k' (Stack st) (Memory st) " using 9(3) notCp by simp
    show "ncpOMemInDMem (Memory st) m'" using a4 typeSafeDecl_hyps 9 notCp by blast
    show "ncpElementsNoSubPref (Memory st) m'"
      using a4 typeSafeDecl_hyps 9 notCp by blast
  next
    assume notCP:"\<not>cp"
    then show "ncpNewSelfPoint (Memory st) m'" using a40 typeSafeDecl_hyps 9 by blast
  next
    show "Toploc mem' \<le> Toploc m' " using 9 typeSafeDecl_hyps a4 by blast
  qed
qed

text \<open>A calldata array initialised from a memory pointer with copying: the array is copied into the new calldata.\<close>

lemma typeSafeDecl_10:
  assumes "tp = Calldata (MTArray x t)"
    and "Some (v, t'') = Some (KMemptr p, tv0)"
    and "cp"
    and "cd = cd0"
    and "state.Memory st = mem"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (cdc', mem''', sck'', ev'')"
    and "Some (c, m', k', e) = (if tv0 = type.Memory (MTArray x t) \<and> 0 < x \<and> Denvalue
        ev'' $$ ip = None then let l = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc cdc')); (uub, c') = allocate cdc' in cpm2m p l x t mem c'
            \<bind> (\<lambda>c''. Some (c'', mem''', astack_dup ip (Calldata (MTArray x t)) (KCDptr l) (sck'', ev''))) else None)"
  shows "declPost ev st cp mem' e c m' k'"
proof -
  let ?case = "declPost ev st cp mem' e c m' k'"
  note 10 = assms
  then obtain l where a1:"l = ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc cdc')" by simp
  have vk:"tv0 = type.Memory (MTArray x t)" using decl.simps(9) 10(8) by (simp split:if_split_asm)
  then have locationscd':"(\<forall>tloc loc. Toploc cdc' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)
      \<longrightarrow> accessStore loc cdc' = None)" using typeSafeDecl_hyps 10 unfolding TypeSafe_def lessThanTopLocs_def by simp
  then have b1:"accessStore l cdc' = None" using a1 using Read_Show_nat'_id using LSubPrefL2_def by auto
  have b2:"x>0" using 10(8) vk a1 by (metis not_None_eq)
  then have Mconcd:"MCon (MTArray x t) mem (extractValueType v)" using typeSafeDecl_hyps(2) 10(2) 10(4) vk 10(5) by simp
  obtain c' where a2:"\<exists>dud. (dud, c') = allocate cdc'" by (simp add: allocate_def)
  then have lNotInC':"accessStore l c' = None" using b1 a1 unfolding allocate_def accessStore_def by simp
  obtain c'' where a3:"cpm2m p l x t mem c' = Some c''" using 10 a1 a2 typeSafeDecl_hyps by (metis (no_types, lifting) bind.bind_lzero case_prod_conv option.discI option.exhaust)
  have NoneIp:"Denvalue ev'' $$ ip = None" using 10 by (auto split:if_splits)
  then have a4:"Some (c, m', k', e) = Some (c'', mem''', astack_dup ip (Calldata (MTArray x t)) (KCDptr l) (sck'', ev''))"
    using a1 a2 a3 10 typeSafeDecl_hyps decl.simps(9) vk
    by (metis (no_types, lifting) b2 bind.bind_lunit case_prod_conv)
  then have a4:"Some (c, m', k', e) = Some (c'', mem''', astack_dup ip (Calldata (MTArray x t)) (KCDptr l) (sck', ev''))"
    using 10(7) by blast
  then have a20:"k' = push (KCDptr l) sck'" using 10 NoneIp by force
  have a30:"e = (updateEnv ip (Calldata (MTArray x t)) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev'')" using a4 NoneIp by simp
  then have a40:"Denvalue e = Denvalue(ev' \<lparr> Denvalue := fmupd ip (Calldata (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) (Denvalue ev'') \<rparr>)" by simp
  then have a50:"(Denvalue e) $$ ip = Some (Calldata (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp
  show ?thesis unfolding TypeSafe_def
  proof(intros)
    show "unique_locations (Denvalue e)" using typeSafeDecl_hyps(3) 10(7) updateEnvUniqueLocs a4 NoneIp by fastforce
  next
    have b2: "compPointers sck' (Denvalue ev'')" using typeSafeDecl_hyps(3) 10(7) unfolding TypeSafe_def by auto
    have "Address ev'' = Address e"using a30 by simp
    moreover have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 10(7) by simp
    ultimately show "compPointers k' (Denvalue e)"
      using compPointersNonStackUpd[of sck' ev' e ip " Calldata (MTArray x t)" k' "KCDptr l"]
        a40 a50 typeSafeDecl_hyps(3) 10(7) b2 a20 by simp

  next
    show "safeContract (Accounts st) (Storage st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "balanceTypes (Accounts st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "svalueTypes (Svalue e)" using a30 10(7) typeSafeDecl_hyps(3) TypeSafe_def svalueTypes_def by simp
  next
    have "addressFormat (Address ev') " using typeSafeDecl_hyps(3) TypeSafe_def 10(7) by simp
    then show "addressFormat (Address e)" using 10(7) a4 NoneIp by auto
  next
    have "addressFormat (Sender ev')" using typeSafeDecl_hyps(3) TypeSafe_def 10(7) by simp
    then show "addressFormat (Sender e)" using 10(7) a4 NoneIp by auto
  next
    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 10(7) by simp
    then show "lessThanTopLocs k'" using stackPushToplocSafe a20 10(7) by metis
  next
    show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c" unfolding typeCompat_def
    proof intros
      fix tDen lDen
      assume *: "(tDen, lDen) |\<in>| fmran (Denvalue e)"
      then obtain ip'' where a90:"Denvalue e $$ ip'' = Some (tDen, lDen)" using * by auto
      then have a100:"(Storage st (Address ev'')) = (Storage st (Address e))" using a30 by simp
      have a110:"m' = mem'''" using a4 by simp
      have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 10(7) by simp
      then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''" using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
      then have a140:"\<forall>x y. \<not>((Denvalue ev'') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc
          sck'))))" using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 10(7) by fastforce
      then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))
          \<longrightarrow> ip''' = ip" using a40 lessThanTopLocs_def fmranI by auto
      then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''') \<and>
          l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip" using a40 fmranI by
          auto
      show "denvalueCon k' m' (Storage st (Address e)) c tDen lDen"
      proof(cases lDen)
        case (Stackloc x1)
        then show ?thesis
        proof (cases "x1 = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')")
          case True
          then have a170: "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KCDptr l)"
            using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using True a170 Stackloc by simp
          next
            case some:(Some a)
            then have a180:"a = KCDptr l " using a170 True by simp
            have a190:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KCDptr l)"
              using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
            then have "ip'' = ip" using a150 True a90 Stackloc by simp
            then have a200:"tDen = Calldata (MTArray x t)" using a90 a50 by simp
            have a220:"v = KMemptr p" using 10(2) by simp
            have "c = c''" using a4 by simp
            then have "MCon (MTArray x t) c'' l" using a3 unfolding cpm2m_def
              using MCon_cpm2m[of p l t mem c' x c'' ] Mconcd 10(2)
              by (metis a220 lNotInC' extractValueType.simps(3))
            then have "MCon (MTArray x t) c l" using a4 a110 10(7) by blast
            then show ?thesis using Stackloc some a180 a200 extractValueType.simps(4) 10(2) by simp
          qed
        next
          case False
          then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs c''"
            using a3 a1 cpm2m_def[of p l x t mem c'] cpm2mSingleChange[of p l t mem c' x c''] by fastforce

          have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc cdc' = None" using locationscd' a2 lNotInC' a1 by auto
          have "\<forall>locations. accessStore locations cdc' = accessStore locations c'" using a2 accessAllocate[of c' cdc'] by auto
          then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs cdc' = accessStore locs c''"
            using b100 a2 unfolding allocate_def by simp

          then have "ip'' \<noteq> ip" using a160 a90 Stackloc False by simp
          then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')"
            using a40 Stackloc fmranI a90 False * by fastforce
          then obtain y' where a180:"accessStore x1 sck' = Some y' "
            using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) Stackloc 10 by blast
          then have a190:"accessStore x1 k' = accessStore x1 sck'"
            using a20 False by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using a180 a190 Stackloc by simp
          next
            case some:(Some a)
            then show ?thesis
            proof(cases a)
              case (KValue x1)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 10(7) by (cases tDen, fastforce+)
            next
              case (KCDptr x2)
              then have b10:"(case tDen of Calldata struct \<Rightarrow> MCon struct cdc' x2 | _ \<Rightarrow> False)"
                using some KCDptr a170 Stackloc a190 using typeSafeDecl_hyps(3) 10(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = Calldata struct" by (auto split:type.splits)
              then have "MCon struct cdc' x2" using b10 by simp
              then have "MCon struct c'' x2" using mconCopySingle[of l cdc' c'' struct] b110 b105 by auto
              then show ?thesis using Stackloc some KCDptr tden a110 a4 by simp
            next
              case (KMemptr x3)
              then have b10:"(case tDen of type.Memory struct \<Rightarrow> MCon struct mem' x3 | _ \<Rightarrow> False)"
                using some a170 Stackloc a190 using typeSafeDecl_hyps(3) 10(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = type.Memory struct" by (auto split:type.splits)
              then have "MCon struct mem''' x3" using b10 10 by simp
              then show ?thesis using Stackloc some KMemptr tden a110 a4 by simp
            next
              case (KStoptr x4)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 10(7) by (cases tDen; fastforce)
            qed
          qed
        qed
      next
        case (Storeloc x2)
        then have "ip'' \<noteq> ip" using a160 a90 by simp
        then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')" using a40 Storeloc fmranI a90 * by fastforce
        then have a180:"(case tDen of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st (Address ev'')) | _ \<Rightarrow> False)"
          using a170 Storeloc using typeSafeDecl_hyps(3) 10(7)
          unfolding TypeSafe_def typeCompat_def by force
        then obtain typ' where tdent:"tDen = type.Storage typ'" by (auto split: type.splits)
        then have "SCon typ' x2 (Storage st (Address ev''))" using a180 by simp
        then have "SCon typ' x2 (Storage st (Address e))" using a100 by simp
        then show ?thesis using a170 Storeloc using typeSafeDecl_hyps(3) 10(7) tdent
          by simp
      qed
    qed
  next
    have b100:"lessThanTopLocs cdc'" using typeSafeDecl_hyps(3) 10(7) unfolding TypeSafe_def by blast
    have b99:"Toploc c' = Toploc c" using a3 a4 cpm2m_def[of p l x t mem c' ] cpm2mTopLocSame[of p l t mem c' x c''] b2 by simp
    have " \<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs c"
      using cpm2mSingleChange[of p l t mem c' x] a4 a3 cpm2m_def[of p l x t mem c' ] by fastforce
    moreover have "\<forall>locations. accessStore locations cdc' = accessStore locations c'" using a2 accessAllocate[of c' cdc'] by auto
    ultimately have b10:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs cdc' = accessStore locs c" by simp
    then show "lessThanTopLocs c" using cdMemLocsToploc[of cdc' l c' c] a1 a2 b100 b99 by auto
  next
    show "lessThanTopLocs m'" using typeSafeDecl_hyps(3) 10(7) a4 unfolding TypeSafe_def by auto
  next
    show "AddressTypes (Accounts st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by simp
  next
    show "denvalueTypeCorrectness e k' m'" unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t l ptr_loc
      assume *:" (type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"
      then have "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue ev')"
        using a4 unfolding astack.simps updateEnv.simps
        by (metis (no_types, lifting) type.distinct(7) a50 typeSafeDecl_hyps(4) decl_env_not_i fmlookup_ran_iff
            option.inject prod.inject)
      moreover have "accessStore l k' = accessStore l sck'"
        using a40 * unfolding astack.simps push_def updateStore_def accessStore_def allocate_def
        by (metis (no_types, lifting) accessStore_def typeSafeDecl_hyps(3,4) calculation decl_stack_change
            fmlookup_ran_iff snd_eqD TypeSafe_def stackLocs_imp_NotDen)
      ultimately show "case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
        using a4 typeSafeDecl_hyps(3) * unfolding TypeSafe_def denvalueTypeCorrectness_def using 10(7) by auto
    qed
  next
    show "subPrefixStructuralConsistency m'"
      using typeSafeDecl_hyps(3) a4 10(7) unfolding TypeSafe_def subPrefixStructuralConsistency_def by auto
  next
    assume notCp:"\<not>cp"
    then show "Toploc (Memory st) \<le> Toploc m'" using a4 typeSafeDecl_hyps 10 by auto
    then show "ncpDenvalueLimit e ev k' (Stack st) (Memory st) " using 10(3) notCp by simp
    show "ncpOMemInDMem (Memory st) m'" using a4 typeSafeDecl_hyps 10 notCp by blast
    show "ncpElementsNoSubPref (Memory st) m'"
      using a4 typeSafeDecl_hyps 10 notCp by blast
  next
    show "SomeValSomeTyp m'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def using a4 10(7) by blast
  next
    fix locs tp assume "\<not>cp"
    then show "MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using a4 typeSafeDecl_hyps 10 by blast
  next
    assume notCP:"\<not>cp"
    then show "ncpNewSelfPoint (Memory st) m'" using a40 typeSafeDecl_hyps 10 by blast
  next
    show "Toploc mem' \<le> Toploc m' " using 10 typeSafeDecl_hyps a4 by blast
  qed
qed

text \<open>A memory array initialised from a memory pointer with copying: the array is copied into fresh memory.\<close>

lemma typeSafeDecl_19:
  assumes "tp = type.Memory (MTArray x t)"
    and "Some (v, t'') = Some (KMemptr p, tv0)"
    and "cp"
    and "cd = cd0"
    and "state.Memory st = mem"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (cdc', mem''', sck'', ev'')"
    and "Some (c, m', k', e) = (if tv0 = type.Memory (MTArray x t) \<and> 0 < x \<and> Denvalue
        ev'' $$ ip = None then cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem''')) x t mem (snd (allocate
        mem''')) \<bind> (\<lambda>m'. Some (cdc', m', astack_dup ip (type.Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'''))) (sck'', ev''))) else None)"
  shows "declPost ev st cp mem' e c m' k'"
proof -
  let ?case = "declPost ev st cp mem' e c m' k'"
  note 19 = assms
  then obtain l where a1:"l = ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem')" by simp
  have vk:"tv0 = type.Memory (MTArray x t)" using decl.simps(9) 19(8) by (simp split:if_split_asm)
  then have locationscd':"(\<forall>tloc loc. Toploc mem' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem' = None)"
    using typeSafeDecl_hyps 19 unfolding TypeSafe_def lessThanTopLocs_def by simp
  then have b1:"accessStore l mem' = None" using a1 using Read_Show_nat'_id using LSubPrefL2_def by auto
  have b2:"x>0" using 19(8) vk a1 by (metis not_None_eq)
  then have Mconcd:"MCon (MTArray x t) mem (extractValueType v)" using typeSafeDecl_hyps(2) 19(2) 19(4) vk 19(5) by simp
  obtain c' where a2:"\<exists>dud. (dud, c') = allocate mem'" by (simp add: allocate_def)
  then have aloc:"snd (allocate mem') = c'" by (simp add: allocate_def)
  then have lNotInC':"accessStore l c' = None" using b1 a1 unfolding allocate_def accessStore_def by auto
  have NoneIp:"Denvalue ev'' $$ ip = None" using 19 by (simp split:if_splits)
  then obtain mm' where a3:"cpm2m p l x t mem c' = Some mm'" using 19 a1 a2 typeSafeDecl_hyps
    using b2 vk aloc by fastforce

  have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem' = None" using locationscd' a2 lNotInC' a1 by auto
  have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
  then have b27:"\<forall>locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
    using a3 a1 cpm2m_def[of p l x t mem c'] cpm2mSingleChange[of p l t mem c' x mm'] a2 unfolding allocate_def by fastforce

  then have subMapping:"Mapping mem' \<subseteq>\<^sub>f Mapping mm'" using b105 unfolding fmsubset_alt_def
    by (metis (mono_tags, lifting) accessStore_def fmpredI option.discI)
  then have a4:"Some (c, m', k', e) = Some (cdc', mm', astack_dup ip (type.Memory (MTArray x t)) (KMemptr l) (sck', ev'))"
    using a1 a2 a3 19 typeSafeDecl_hyps decl.simps(9) vk b2 aloc NoneIp
    by simp

  then have a20:"k' = push (KMemptr l) sck'" using NoneIp 19 unfolding astack_dup.simps by simp
  have b3:"Address ev' = Address e" using a4 NoneIp 19(7) by simp

  have a30:"e = (updateEnv ip (type.Memory (MTArray x t)) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev')" using a4 NoneIp 19(7) by simp
  then have a40:"Denvalue e = Denvalue(ev' \<lparr> Denvalue := fmupd ip (type.Memory (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) (Denvalue ev') \<rparr>)" by simp
  then have a50:"(Denvalue e) $$ ip = Some (type.Memory (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp
  have selfPoint:"\<forall>la l'. TypedMemSubPref la l (MTArray x t) \<and> accessStore la mm' = Some (MPointer l') \<longrightarrow> l' = la"
    using cpm2mSelfPointers[of p l t mem c' x mm'] a3 a1 cpm2m_def[of p l x t mem c'] by argo
  have a110:"m' = mm'" using a4 by simp

  then have nonLocChanged2_Typed:"\<forall>t' locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))
                                          \<longrightarrow> accessTypeStore locs c' = accessTypeStore locs m'"
    using cpm2mSingleChange_Typed[of ] allocateTypeSameAccess a3 a1 unfolding cpm2m_def by blast
  moreover have "\<forall>locs. accessTypeStore locs c' = accessTypeStore locs mem'" using aloc allocateTypeSameAccess by metis
  ultimately have nonLocChanged2_Typed:"\<forall>t' locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))
                                          \<longrightarrow> accessTypeStore locs mem' = accessTypeStore locs m'" by simp
  have "\<forall>destl'.
       TypedMemSubPref destl' l (MTArray x t) \<longrightarrow>
       (\<exists>st. CompMemType mm' x t st l destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' mm' = Some (MTValue pval)))"
    using a1 a3 unfolding cpm2m_def using cpm2m_TypeCompChange[of p l t mem c' x mm'] by blast
  then have mtp:"\<forall>destl'.
       TypedMemSubPref destl' l (MTArray x t) \<longrightarrow>
       (\<exists>st. CompMemType m' x t st l destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' m' = Some (MTValue pval)))" using a110 by auto

  show ?thesis unfolding TypeSafe_def
  proof(intros)
    fix locs tp assume "\<not>cp"
    then show "MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using 19 typeSafeDecl_hyps(5) by (simp split:if_splits)
  next
    show "unique_locations (Denvalue e)" using typeSafeDecl_hyps(3) 19(7) updateEnvUniqueLocs a4 NoneIp by fastforce
  next
    have b2: "compPointers sck' (Denvalue ev')" using typeSafeDecl_hyps(3) 19(7) unfolding TypeSafe_def by auto
    moreover have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 19(7) by simp
    ultimately show "compPointers k' (Denvalue e)"
      using compPointersNonStackUpd[of sck' ev' e ip "type.Memory (MTArray x t)" k' "KMemptr l" ]
        a40 a50 typeSafeDecl_hyps(3) 19(7) b2 a20 b3 by simp
  next
    show "safeContract (Accounts st) (Storage st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "balanceTypes (Accounts st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "svalueTypes (Svalue e)" using a30 19(7) typeSafeDecl_hyps(3) TypeSafe_def svalueTypes_def by simp
  next
    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 19(7) by simp
    then show "lessThanTopLocs k'" using stackPushToplocSafe a20 19(7) by metis
  next
    have "addressFormat (Sender ev')" using typeSafeDecl_hyps(3) TypeSafe_def 19(7) by simp
    then show "addressFormat (Sender e)" using 19(7) a4 NoneIp 19(7) by auto
  next
    have "addressFormat (Address ev')" using typeSafeDecl_hyps(3) TypeSafe_def 19(7) by simp
    then show "addressFormat(Address e) " using 19(7) a4 NoneIp 19(7) by auto
  next
    show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c" unfolding typeCompat_def
    proof intros
      fix tDen lDen
      assume *: "(tDen, lDen) |\<in>| fmran (Denvalue e)"
      then obtain ip'' where a90:"Denvalue e $$ ip'' = Some (tDen, lDen)" using * by auto
      then have a100:"(Storage st (Address ev')) = (Storage st (Address e))" using a30 by simp
      have a110:"m' = mm'" using a4 by simp
      have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 19(7) by simp
      then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''"
        using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
      then have a140:"\<forall>x y. \<not>((Denvalue ev') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))"
        using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 19(7) by fastforce
      then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip"
        using a40 lessThanTopLocs_def fmranI by auto
      then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''')
                        \<and> l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip"
        using a40 lessThanTopLocs_def fmranI by auto
      show "denvalueCon k' m' (Storage st (Address e)) c tDen lDen"
      proof(cases lDen)
        case (Stackloc x1)
        then show ?thesis
        proof (cases "x1 = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')")
          case True
          then have a170: "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KMemptr l)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using True a170 Stackloc by simp
          next
            case some:(Some a)
            then have a180:"a = KMemptr l " using a170 True by simp
            have a190:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KMemptr l)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
            then have "ip'' = ip" using a150 True a90 Stackloc by simp
            then have a200:"tDen = type.Memory (MTArray x t)" using a90 a50 by simp
            have a220:"v = KMemptr p" using 19(2) by simp
            have "c = cdc'" using a4 by simp
            then have "MCon (MTArray x t) mm' l" using a3 unfolding cpm2m_def
              using MCon_cpm2m[of p l t mem c' x mm' ] Mconcd 19(2) b2
              by (metis a220 lNotInC' extractValueType.simps(3))
            then have "MCon (MTArray x t) m' l" using a4 a110 19(7) by blast
            then show ?thesis using Stackloc some a180 a200 extractValueType.simps(4) 19(2) by simp
          qed
        next
          case False
          then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
            using a3 a1 cpm2m_def[of p l x t mem c'] cpm2mSingleChange[of p l t mem c' x mm'] by fastforce

          have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem' = None" using locationscd' a2 lNotInC' a1 by auto
          have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
          then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
            using b100 a2 unfolding allocate_def by simp

          then have "ip'' \<noteq> ip" using a160 a90 Stackloc False by simp
          then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev')" using a40 Stackloc fmranI a90 False * by fastforce
          then obtain y' where a180:"accessStore x1 sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) Stackloc 19 by blast
          then have a190:"accessStore x1 k' = accessStore x1 sck'"
            using a20 False by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using a180 a190 Stackloc by simp
          next
            case some:(Some a)
            then show ?thesis
            proof(cases a)
              case (KValue x1)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 19(7) by (cases tDen; fastforce)
            next
              case (KCDptr x2)
              then have b10:"(case tDen of Calldata struct \<Rightarrow> MCon struct cdc' x2 | _ \<Rightarrow> False)"
                using some a170 Stackloc a190 using typeSafeDecl_hyps(3) 19(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = Calldata struct" by (auto split:type.splits)
              then have "MCon struct cdc' x2" using b10 by simp
              then show ?thesis using Stackloc some KCDptr tden a110 a4 by simp
            next
              case (KMemptr x3)
              then have b10:"(case tDen of type.Memory struct \<Rightarrow> MCon struct mem' x3 | _ \<Rightarrow> False)"
                using some a170 Stackloc a190 using typeSafeDecl_hyps(3) 19(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = type.Memory struct" by (auto split:type.splits)
              then have "MCon struct mem' x3" using b10 by simp
              then have "MCon struct mm' x3" using mconCopySingle[of l mem' mm' struct] b110 b105 by auto
              then show ?thesis using Stackloc some KMemptr tden a110 a4 by simp
            next
              case (KStoptr x4)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 19(7) by (cases tDen; fastforce)
            qed
          qed
        qed
      next
        case (Storeloc x2)
        then have "ip'' \<noteq> ip" using a160 a90 by simp
        then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev')" using a40 Storeloc fmranI a90 * by fastforce
        then have a180:"(case tDen of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st (Address ev')) | _ \<Rightarrow> False)"
          using a170 Storeloc using typeSafeDecl_hyps(3) 19(7)
          unfolding TypeSafe_def typeCompat_def by force
        then obtain typ' where tdent:"tDen = type.Storage typ'" by (auto split: type.splits)
        then have "SCon typ' x2 (Storage st (Address ev'))" using a180 by simp
        then have "SCon typ' x2 (Storage st (Address e))" using a100 by simp
        then show ?thesis using a170 Storeloc using typeSafeDecl_hyps(3) 19(7) tdent
          by simp
      qed
    qed
  next
    show "lessThanTopLocs c" using typeSafeDecl_hyps(3) 19(7) a4 unfolding TypeSafe_def by auto
  next
    have b100:"lessThanTopLocs mem'" using typeSafeDecl_hyps(3) 19(7) unfolding TypeSafe_def by blast
    have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t mem c' ] cpm2mTopLocSame[of p l t mem c' x mm'] b2 by simp
    have " \<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs m'"
      using cpm2mSingleChange[of p l t mem c' x mm'] a4 a3 cpm2m_def[of p l x t mem c'] by fastforce
    moreover have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
    ultimately have b10:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs m' = accessStore locs mem'" by simp
    show "lessThanTopLocs m'" using cdMemLocsToploc[of mem' l c' m'] b100 a1 a2 b99 using b10 by presburger
  next
    show "AddressTypes (Accounts st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by simp
  next
    have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t mem c' ] cpm2mTopLocSame[of p l t mem c' x mm'] b2 by simp

    show "denvalueTypeCorrectness e k' m'" unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t2 l ptr_loc
      assume *:" (type.Memory t2, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"

      show "case t2 of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
      proof(cases "(type.Memory t2, Stackloc l) |\<in>| fmran(Denvalue ev')")
        case True
        moreover have sameACC:"accessStore l k' = accessStore l sck'"
          using a40 * unfolding astack.simps push_def updateStore_def accessStore_def allocate_def
          by (metis (no_types, lifting) accessStore_def typeSafeDecl_hyps(3,4) calculation decl_stack_change
              fmlookup_ran_iff snd_eqD TypeSafe_def stackLocs_imp_NotDen)
        then have old:"(case t2 of
                         MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some arr)
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc mem' = Some (MTValue val))"
          using typeSafeDecl_hyps(1) 19(7) * True TypeSafe_def typeSafeDecl_hyps(3) denvalueTypeCorrectness_def by fastforce
        have mcOld:"MCon t2 mem' ptr_loc" using * sameACC True typeSafeDecl_hyps(1) 19(7)
          unfolding TypeSafe_def typeCompat_def
          by (metis typeSafeDecl_hyps(3) sameMemTSafe)

        have lims:"\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) ptr_loc"
          using typeSafeAllPtrsNotTop[OF typeSafeDecl_hyps(3) True] * 19(7) sameACC b99 aloc unfolding allocate_def
          using LSubPrefL2_def MemLSubPrefTransitive by force
        then show ?thesis
        proof(cases t2)
          case (MTArray x11 x12)
          have nonLocChanged2_Typed_cond:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessTypeStore loc m' = accessTypeStore loc mem'"
            using nonLocChanged2_Typed by simp
          have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some x12)" using old MTArray by simp


          then show ?thesis using MTArray old' nonLocChanged2_Typed_cond lims 19(7)
            by (simp add: Mutual_NonSub_SpecificNonSub)
        next
          case (MTValue x2)
          then show ?thesis using nonLocChanged2_Typed old 19(7) lims by simp
        qed
      next
        case False
        then have inOld:"Denvalue e $$ ip = Some (type.Memory t2, Stackloc l)"
          using a40 *
          by (metis (lifting) Environment.unfold_congs(5) DenvalueChange fmranE fmranI)
        then have t2Def:"l = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) \<and> t2 = (MTArray x t)" using a40 by simp
        then have acc:"accessStore l k' = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')))"
          using a40 a20 a1 * unfolding push_def allocate_def updateStore_def accessStore_def by simp
        have "(\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some t)"
          using "*" a1 a110 a3 acc cpm2m_TypeCompChangeIndexs cpm2m_def by auto

        moreover have "(\<forall>v. accessStore ptr_loc m' = Some (MPointer v)
                        \<longrightarrow> accessTypeStore ptr_loc m' = Some (MTArray x t))"
          using "*" \<open>\<forall>locations. accessStore locations c' = accessStore locations mem'\<close> a1 a110 acc b27 lNotInC' by auto
        ultimately show ?thesis using t2Def nonLocChanged2_Typed by simp
      qed
    qed

  next
    show "subPrefixStructuralConsistency m'" unfolding subPrefixStructuralConsistency_def
    proof(intros)
      fix locs tp
      assume in1:"accessTypeStore locs m' = Some tp"

      have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
      then have nonLocChanged2:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore locs mem' = accessStore locs m'"
        using a3 a1 cpm2m_def[of p l x t mem c'] cpm2mSingleChange[of p l t mem c' x mm'] a2 a110 unfolding allocate_def by fastforce

      have nonLocChanged_Typed:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t)
              \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessTypeStore locs mem' = accessTypeStore locs m'"
        using a3 a1 cpm2m_def[of p l x t mem c'] cpm2mSingleChange_typedPref_typed[of p l t mem c' x mm'] allocateTypeSameAccess a2 a110
        by (metis aloc)

      have "MCon (MTArray x t) mm' l" using a3 unfolding cpm2m_def
        using MCon_cpm2m[of p l t mem c' x mm' ] Mconcd 19(2) b2 a1 lNotInC'
        by fastforce
      then have mcTop:"MCon (MTArray x t) m' l" using a4 a110 19(7) by blast

      have prefPtrs_imps_Pref:"\<forall>x3. TypedMemSubPrefPtrs mm' x t l x3 \<longrightarrow> TypedMemSubPref x3 l (MTArray x t)"
        using selfPoint_imps_TypedMemSubPref[OF selfPoint] a110 by blast

      show "case accessStore locs m' of None \<Rightarrow> False | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m' locs \<and> tp = MTValue val \<and> accessTypeStore locs m' = Some tp
       | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp m' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)"
      proof(cases "accessTypeStore locs mem' = Some tp")
        case True
        then have accL:"\<exists>v. accessStore locs mem' = Some v"
          using typeSafeDecl_hyps(3) 19(7) unfolding TypeSafe_def SomeValSomeTyp_def by simp
        have notSub:"\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))"
        proof
          assume c:"LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))"
          then have "accessStore locs mem' = None"
            using 19(7) nless_le a1 b105 by presburger
          then show False using accL by auto
        qed
        then have sameACC:" accessStore locs m' = accessStore locs mem'" using nonLocChanged2 19(7) by simp
        then consider (ptr) p where "accessStore locs m' = Some (MPointer p)"
          | (val) val2 where "accessStore locs m' = Some (MValue val2)"
          using typeSafeDecl_hyps(1) 19(7) True unfolding TypeSafe_def subPrefixStructuralConsistency_def
          by (metis memoryvalue.exhaust accL)
        then show ?thesis
        proof(cases)
          case ptr
          then obtain len arr where
            old:"MCon tp mem' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some arr)"
            using typeSafeDecl_hyps(3) 19(7) True sameACC unfolding TypeSafe_def subPrefixStructuralConsistency_def by fastforce
          then have lim2:"\<forall>len arr loc. tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem' len arr p loc
                        \<longrightarrow> \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) loc"
            using AccessedMemPtrsCantTop[of "mem'" tp p] typeSafeDecl_hyps(3) 19(7) unfolding TypeSafe_def by blast
          have lim:" \<not> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) p"
            using AllPtrsNotTop_MCon notSub ptr using typeSafeDecl_hyps(3) 19(7) old unfolding TypeSafe_def by blast
          have accTLoc:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<or> loc =
              (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore loc m' = accessStore loc mem'"
            using 19(7) nonLocChanged2 a1 a110 b27 by presburger
          have "MCon tp m' p" using MCon_memory_transfer[OF _ lim lim2 accTLoc] old by blast
          moreover have "\<forall>i<len. \<not> LSubPrefL2 (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" using lim
            using MemLSubPrefL2_specific_imps_general by blast
          ultimately have " MCon tp m' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)"
            using nonLocChanged2_Typed old 19(7) by simp

          then show ?thesis using ptr by auto
        next
          case val
          then have old:"\<exists>val. MCon tp mem' locs \<and> tp = MTValue val \<and> accessTypeStore locs mem' = Some tp"
            using typeSafeDecl_hyps(3) 19(7) True sameACC unfolding TypeSafe_def subPrefixStructuralConsistency_def by fastforce
          then have "\<exists>val. MCon tp m' locs \<and> tp = MTValue val \<and> accessTypeStore locs m' = Some tp"
            using nonLocChanged2_Typed MCon.simps val notSub 19(7) sameACC by fastforce
          then show ?thesis using val by auto
        qed
      next
        case False
        then have sub:"TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t) \<and> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))"
          using nonLocChanged_Typed 19(7) in1 by fastforce
        then have "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t)"
          using selfPoint_imps_TypedMemSubPref by simp
        then obtain st where stD:"(CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) locs \<and>
           (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
            | MTValue pval \<Rightarrow> accessTypeStore locs m' = Some (MTValue pval)))" using mtp a1 by blast
        then have cmp:"CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) locs " by blast

        have mcLocs:"MCon st m' locs" using cmp mcTop CompTypeRemainsMCon a1 by auto

        show ?thesis
        proof(cases st)
          case (MTArray x11 x12)
          have subs:"t = MTArray x11 x12 \<and> (\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs)) \<or>
                       (\<exists>midP subL subA i. CompMemType m' x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) midP
                       \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
            using CompMemType_imps_Mid[of m' x t x11 x12 "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" locs] cmp MTArray by simp

          then have acc:"accessStore locs m' = Some (MPointer locs)"
            using selfPoint mcLocs sub MTArray MCon_imps_TypedMemSubPref_Some mcTop a1
            by (metis MCon.simps(2) a110 option.distinct(1))

          moreover have "\<exists>len arr. MCon tp m' locs \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
                             \<and> (\<forall>v. accessStore locs m' = Some (MPointer v) \<longrightarrow> accessTypeStore locs m' = Some (MTArray len arr))"
            using in1
          proof(cases "(\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> t = MTArray x11 x12)")
            case True
            then obtain i where idef:"i<x \<and> accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs)
                                    \<and> t = MTArray x11 x12"
              by auto
            then have "TypedMemSubPref (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t) " by auto
            then have locsD:"locs = (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint idef a1 a110 by blast
            have "\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MTArray x11 x12)"
              using idef a1 a110 cpm2m_TypeCompChangeIndexs
              by (metis a3 cpm2m_def)
            then have "tp = MTArray x11 x12" using in1 locsD idef by simp
            moreover have "(\<forall>i<x11. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some x12)" using stD MTArray by simp
            ultimately show ?thesis using mcLocs MTArray in1 by blast
          next
            case False
            then obtain midP i subL subA where mid:"(CompMemType m' x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) midP
                   \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
              using subs by blast
            then have locD:"locs = (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint a110 a1
              using CompMemType_imps_in_GetAllMemoryLocations_ptr mcTop memSet_selfPoint by blast
            then obtain st2 where st2D:"(CompMemType m' x t st2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) midP \<and>
             (case st2 of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore midP m' = Some (MTValue pval)))" using mid mtp a1 a110
              using CompMemTypeSameLocsSameType CompMemType_imps_TypedMemSubPrefPtrs prefPtrs_imps_Pref by blast
            then have "st2 = (MTArray subL subA)" using mid CompMemTypeSameLocsSameType mcTop a1 by blast
            then have " \<forall>i<subL. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some subA" using st2D by simp
            then have "MTArray x11 x12 = tp" using in1 locD mid by simp
            then show ?thesis using mcLocs MTArray stD in1 by fastforce
          qed
          ultimately show ?thesis by auto
        next
          case (MTValue x2)
          then obtain v where vDef:"accessStore locs m' = Some (MValue v)"
            using mcLocs MCon.simps(1)[of x2 m' locs] by (auto split:option.splits memoryvalue.splits)
          moreover have "accessTypeStore locs m' = Some (MTValue x2)" using stD MTValue by auto
          moreover have "tp = MTValue x2" using calculation in1 by simp
          moreover have "MCon tp m' locs" using mcLocs calculation MTValue by blast
          ultimately show ?thesis using MTValue by simp
        qed
      qed
    qed
  next
    have old:"SomeValSomeTyp mem'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by blast
    have non:"\<forall>loc. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore loc mem' = None"
      using 19(7) typeSafeDecl_hyps(3) unfolding TypeSafe_def lessThanTopLocs_def
      by auto
    have "MCon (MTArray x t) mm' l" using a3 unfolding cpm2m_def
      using MCon_cpm2m[of p l t mem c' x mm' ] Mconcd 19(2) b2 a4 19(2) lNotInC'
      by fastforce
    then have mcTop:"MCon (MTArray x t) m' l" using a4 a110 19(7) by blast
    have somesomeT:"\<forall>destl'.
          TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t) \<longrightarrow>
          (\<exists>t. accessStore destl' m' = Some t) = (\<exists>tt. accessTypeStore destl' m' = Some tt)"
      using a3 unfolding cpm2m_def
      using cpm2m_TypeCompChange_somesome[of p l t mem c' x mm'] a4 a1 by blast
    show "SomeValSomeTyp m'" unfolding SomeValSomeTyp_def
    proof intros
      fix locs
      show "(\<exists>t. accessStore locs m' = Some t) = (\<exists>tt. accessTypeStore locs m' = Some tt) "
      proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t)")
        case True
        then show ?thesis using somesomeT by simp
      next
        case False
        then have "accessStore locs m' = accessStore locs mem'"
          using "19"(7)
          by (metis \<open>\<forall>locations. accessStore locations c' = accessStore locations mem'\<close> a1 a110 a3 cpm2mSingleChange_typedPref cpm2m_def)
        moreover have "accessTypeStore locs m' = accessTypeStore locs mem'"
          using False cpm2mSingleChange_typedPref_typed 19(7) allocateTypeSameAccess
          by (metis a1 a110 a3 aloc cpm2m_def)
        ultimately show ?thesis using old
          by (simp add: SomeValSomeTyp_def)
      qed
    qed
  next
    assume notCp:"\<not>cp"
    then show "Toploc (Memory st) \<le> Toploc m'" using 19(3) by auto
    then show "ncpDenvalueLimit e ev k' (Stack st) (Memory st)" using 19(3) notCp by simp
    show "ncpOMemInDMem (Memory st) m'" using 19 notCp by blast
    show "ncpElementsNoSubPref (Memory st) m'" using 19(3) notCp by blast
    show "ncpNewSelfPoint (Memory st) m'" using a40 typeSafeDecl_hyps 19(3) notCp by blast
  next
    have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t mem c' ] cpm2mTopLocSame[of p l t mem c' x mm'] b2 by simp
    then show "Toploc mem' \<le> Toploc m' " using aloc unfolding allocate_def by auto
  qed
qed

text \<open>A memory array initialised from a memory pointer without copying: the variable refers to the existing array.\<close>

lemma typeSafeDecl_20:
  assumes "tp = type.Memory (MTArray x t)"
    and "Some (v, t'') = Some (KMemptr p, tv0)"
    and "\<not> cp"
    and "cd = cd0"
    and "state.Memory st = mem0"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (cdc', mem''', sck'', ev'')"
    and "Some (c, m', k', e) = (if tv0 = type.Memory (MTArray x t) \<and> 0 < x \<and> Denvalue ev'' $$ ip = None then Some (cdc', mem''',
        astack_dup ip (type.Memory (MTArray x t)) (KMemptr p) (sck'', ev'')) else None)"
  shows "declPost ev st cp mem' e c m' k'"
proof -
  let ?case = "declPost ev st cp mem' e c m' k'"
  note 20 = assms

  then have a5:"tv0 = (type.Memory (MTArray x t))" using typeSafeDecl_hyps(4) by (metis option.distinct(1))
  have b2:"x>0" using 20(8) a5 by (metis not_None_eq)
  have NoneIp:"Denvalue ev'' $$ ip = None" using 20 by (simp split:if_splits)
  then have a10:"Some (c, m', k', e) = Some (cdc', mem''', astack_dup ip (type.Memory (MTArray x t)) (KMemptr p) (sck'', ev''))"
    using 20 typeSafeDecl_hyps b2 a5
    by (metis)
  then have a10:"Some (c, m', k', e) = Some (cdc', mem''', astack_dup ip (type.Memory (MTArray x t)) (KMemptr p) (sck', ev''))"
    using 20(7) by simp
  then have a20:"k' = push (KMemptr p) sck'" using 20 NoneIp by force

  have b3:"Address e = Address ev''" using a10 NoneIp by auto
  have a30:"e = (updateEnv ip (type.Memory (MTArray x t)) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev'')" using a10 NoneIp by simp

  then have a40:
    "Denvalue e = Denvalue(ev'' \<lparr> Denvalue := fmupd ip ((type.Memory (MTArray x t)),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) (Denvalue ev'') \<rparr>)" by simp
  then have a50:"(Denvalue e) $$ ip = Some ((type.Memory (MTArray x t)),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp
  have a4:"Address ev'' = Address e"using a30 by simp

  have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 20(7) by simp
  then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''"
    using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
  then have a140:"\<forall>x y. \<not>((Denvalue ev'') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))"
    using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 20(7) by fastforce
  then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip"
    using a40 lessThanTopLocs_def fmranI by auto
  then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''')
                      \<and> l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip"
    using a40 lessThanTopLocs_def fmranI by auto

  have c10:"(\<forall>tp' locs p i.
        (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev'') \<and> accessStore locs sck' = Some (KMemptr p) \<and> i < Toploc
            (Memory st) \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t i)\<longrightarrow>
        (\<exists>tp'' loc2 p' .
            (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
            accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p \<and>
                tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp'
                p' p))))"
    using typeSafeDecl_hyps(5) 20(3,7) unfolding ncpDenvalueLimit_def by blast
  have c20:"(\<exists>stloc tp'' p'.
           (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
           accessStore stloc (Stack st) = Some (KMemptr p') \<and>
           (tp'' = (MTArray x t) \<and> p = p' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr (MTArray x t) p' p)))"
    using typeSafeDecl_hyps(6) a5 20(2,3,7) by fastforce

  have "KMemptr p = v" using 20 by simp
  then have mconp:" MCon (MTArray x t) (Memory st) p" using typeSafeDecl_hyps(2) extractValueType.simps 20(2,8)
    by (metis type.simps(19) decl.simps(20) option.discI)
  then obtain x' y where ne2:" accessStore (hash p y) (Memory st) = Some x'" using MCon.simps
    by (meson b2 mcon_accessStore)
  have ne3:"((\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None) \<and>
   (\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
    using typeSafeDecl_hyps(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
  then have ne4:"\<exists>y tloc. tloc <Toploc (Memory st) \<and> LSubPrefL2 (hash p y) (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ne2 by blast
  then have ne6:"\<exists>tloc. tloc <Toploc (Memory st) \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using MemLSubPrefL2_specific_imps_general by auto

  have ne5:"(\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp m' locs) \<and>
               Toploc (Memory st) \<le> Toploc m' \<and> ncpDenvalueLimit ev'' ev sck' (Stack st) (Memory st) \<and> ncpOMemInDMem (Memory
                   st) m' \<and> ncpElementsNoSubPref (Memory st) m' \<and> ncpNewSelfPoint (Memory st) m'"
    using typeSafeDecl_hyps(3,5) 20(3,7) a10 by blast

  have oldLimit:"((\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None) \<and>
   (\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
    using typeSafeDecl_hyps(1) unfolding TypeSafe_def lessThanTopLocs_def by simp

  show ?thesis unfolding TypeSafe_def
  proof(intros)
    fix locs tp assume "\<not>cp"
    then show "MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using 20 typeSafeDecl_hyps(5) by (simp split:if_splits)
  next
    show "unique_locations (Denvalue e)" using typeSafeDecl_hyps(3) 20(7) updateEnvUniqueLocs a10 NoneIp by fastforce
  next
    have b2: "compPointers sck' (Denvalue ev'')" using typeSafeDecl_hyps(3) 20(7) unfolding TypeSafe_def by auto
    moreover have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 20(7) by simp
    ultimately show "compPointers k' (Denvalue e)"
      using compPointersNonStackUpd[of sck' ev'' e ip " type.Memory (MTArray x t)" k' "KMemptr p"]
        a40 a50 typeSafeDecl_hyps(3) 20(7) b2 a20 a4 by simp
  next
    show "safeContract (Accounts st) (Storage st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "balanceTypes (Accounts st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "svalueTypes (Svalue e)" using a30 20(7) typeSafeDecl_hyps(3) TypeSafe_def svalueTypes_def by simp
  next
    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 20(7) by simp
    then show "lessThanTopLocs k'" using stackPushToplocSafe a20 20(7) by metis
  next
    have "addressFormat (Address ev'')" using typeSafeDecl_hyps(3) TypeSafe_def 20(7) by simp
    then show "addressFormat (Address e)" using 20(7) a4 by (metis)
  next
    have "addressFormat (Sender ev'')" using typeSafeDecl_hyps(3) TypeSafe_def 20(7) by simp
    then show "addressFormat (Sender e)" using 20(7) a4 by (metis typeSafeDecl_hyps(4) decl_env)
  next
    show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c" unfolding typeCompat_def
    proof intros
      fix tDen lDen
      assume *: "(tDen, lDen) |\<in>| fmran (Denvalue e)"
      then obtain ip'' where a90:"Denvalue e $$ ip'' = Some (tDen, lDen)" using * by auto
      then have a100:"(Storage st (Address ev'')) = (Storage st (Address e))" using a30 by simp
      have a110:"m' = mem'" and a115:"cdc' = c" using a10 20 by simp+
      have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 20(7) by simp
      then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''" using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
      then have a140:"\<forall>x y. \<not>((Denvalue ev'') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc
          sck'))))" using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 20(7) by fastforce
      then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip" using a40 fmranI by auto
      then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''') \<and>
          l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip" using a40 fmranI by
          auto
      show "denvalueCon k' m' (Storage st (Address e)) c tDen lDen"
      proof(cases lDen)
        case (Stackloc x1)
        then show ?thesis
        proof (cases "x1 = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')")
          case True
          then have a170: "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KMemptr p)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)

          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using True a170 Stackloc by simp
          next
            case some:(Some a)
            then have a180:"a = KMemptr p " using a170 True by simp
            have a190:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KMemptr p)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
            then have "ip'' = ip" using a150 True a90 Stackloc by simp
            then have a200:"tDen = (type.Memory (MTArray x t))" using a90 a50 by simp
            then have a210:"t'' = tDen" using a5 20(2) by simp
            have "v = KMemptr p" using 20(2) by simp
            have a220:"MCon (MTArray x t) (Memory st) (extractValueType v)" using a200 a210 typeSafeDecl_hyps(2) by simp
            then show ?thesis using Stackloc some a180 a200 extractValueType.simps(4) 20(2) typeSafeDecl_hyps(3) a110 20(7) typeSafeDecl_hyps(5) 20(3) unfolding TypeSafe_def
              by (metis denvalue.simps(5) Option.option.simps(5) stackvalue.simps(19) type.simps(19) a220 prod.inject extractValueType.simps(3))
          qed
        next
          case False
          then have "ip'' \<noteq> ip" using a160 a90 Stackloc by simp
          then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')" using a40 Stackloc fmranI a90 False * by fastforce
          then obtain y' where a180:"accessStore x1 sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) Stackloc 20(7) by blast
          then have a190:"accessStore x1 k' = accessStore x1 sck'" using a20 False by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using a180 a190 Stackloc by simp
          next
            case some:(Some a)
            then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
              using a190 some Stackloc a170 * a180 a110 a115 a100 20(7)
              by (cases a; cases tDen; fastforce)
          qed
        qed
      next
        case (Storeloc x2)
        then have a170:"ip'' \<noteq> ip" using a40 Storeloc a90 by auto
        then have a180: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')" using a40 Storeloc fmranI a90 by fastforce
        then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
          using Storeloc a100 20(7) by (cases tDen;force)
      qed
    qed
  next
    have "lessThanTopLocs cdc'" using typeSafeDecl_hyps(3) TypeSafe_def 20(7) by simp
    then show "lessThanTopLocs c" using a10 by simp
  next
    have "lessThanTopLocs mem'" using typeSafeDecl_hyps(3) TypeSafe_def 20(7) by simp
    then show "lessThanTopLocs m'" using a10 20 by simp
  next
    show "AddressTypes (Accounts st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by simp
  next
    show "denvalueTypeCorrectness e k' m'" unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t2 l ptr_loc
      assume *:" (type.Memory t2, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"

      show "case t2 of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
      proof(cases "(type.Memory t2, Stackloc l) |\<in>| fmran(Denvalue ev')")
        case True
        moreover have sameACC:"accessStore l k' = accessStore l sck'"
          using a40 * unfolding astack.simps push_def updateStore_def accessStore_def allocate_def
          by (metis (no_types, lifting) accessStore_def typeSafeDecl_hyps(3,4) calculation decl_stack_change
              fmlookup_ran_iff snd_eqD TypeSafe_def stackLocs_imp_NotDen)
        then have old:"(case t2 of
                         MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some arr)
         | MTValue val \<Rightarrow> accessTypeStore ptr_loc mem' = Some (MTValue val))"
          using typeSafeDecl_hyps(1) 20(7) * True TypeSafe_def typeSafeDecl_hyps(3) denvalueTypeCorrectness_def by fastforce
        have mcOld:"MCon t2 mem' ptr_loc" using * sameACC True typeSafeDecl_hyps(1) 20(7)
          unfolding TypeSafe_def typeCompat_def
          by (metis typeSafeDecl_hyps(3) sameMemTSafe)
        have mm:"mem' = m'" using a10 20(7) by blast
        then show ?thesis
        proof(cases t2)
          case (MTArray x11 x12)
          have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some x12)" using mm old MTArray by auto

          then show ?thesis using MTArray by simp
        next
          case (MTValue x2)
          then show ?thesis using a10 20 old by simp
        qed
      next
        case False
        then have "Denvalue e $$ ip = Some (type.Memory t2, Stackloc l)"
          using a40 * 20(7)
          by (metis (no_types, lifting) typeSafeDecl_hyps(4) decl_env_not_i fmranE fmranI)
        then have t2Def:"l = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) \<and> t2 = (MTArray x t)" using a40 by simp
        then have acc:"accessStore l k' = Some (KMemptr p)"
          using a40 a20 * unfolding push_def allocate_def updateStore_def accessStore_def by simp

        obtain stloc tp'' pprnt where old:"(
         (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
         accessStore stloc (Stack st) = Some (KMemptr pprnt) \<and>
         (tp'' =(MTArray x t) \<and> p = pprnt \<or>
          (\<exists>len arr. pprnt \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr (MTArray x t) pprnt p)))"
          using typeSafeDecl_hyps(6) 20
          by (metis a5 extractValueType.simps(3) option.inject prod.inject)
        then obtain len arr where pprntTP: "tp'' = MTArray len arr" using old by blast
        then have old2:"(\<forall>i<len. accessTypeStore (hash pprnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)"
          using typeSafeDecl_hyps(1) old unfolding TypeSafe_def denvalueTypeCorrectness_def by fastforce

        have ncpOld:"ncpOMemInDMem (Memory st) m'" using ne5 by blast
        have someSome:"\<forall>loc. (\<exists>t. accessStore loc (Memory st) = Some t) \<longleftrightarrow> (\<exists>tt. accessTypeStore loc (Memory st) = Some tt)"
          using typeSafeDecl_hyps(1) unfolding TypeSafe_def SomeValSomeTyp_def by simp
        have ptrEq:"ptr_loc = p" using * acc by simp

        have "(\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some t)
                "
        proof(cases "pprnt = p")
          case True
          then have sameT:"tp'' = MTArray x t \<and> len = x \<and> arr = t" using pprntTP old by simp
          then have t'Def: "(\<forall>i<len. accessTypeStore (hash pprnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)"
            using old2 True ptrEq by blast

          show ?thesis
            using sameT ncpOld ne6 old2 ptrEq someSome oldLimit unfolding ncpOMemInDMem_def
            by (metis True)
        next
          case False
          then have comp:"CompMemType (Memory st) len arr (MTArray x t) pprnt ptr_loc" using old
            using pprntTP ptrEq by auto
          then have mids:"arr = MTArray x t \<and> (\<exists>i<len. accessStore (hash pprnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr_loc)) \<or>
                      (\<exists>midP subL subA i.
                    CompMemType (Memory st) len arr (MTArray subL subA) pprnt midP
                    \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr_loc) \<and> i < subL \<and> subA = MTArray x t)"
            using CompMemType_imps_Mid[OF comp] by simp
          then have mcPtrLoc:"MCon (MTArray x t) (Memory st) ptr_loc "
            using mconp ptrEq by blast
          have occ:"(\<forall>locs tp.
        accessTypeStore locs (Memory st) = Some tp \<longrightarrow>
        (case accessStore locs (Memory st) of None \<Rightarrow> False
         | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
         | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp (Memory st) p \<and> tp = MTArray len arr
            \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
            ))"
            using typeSafeDecl_hyps(1) unfolding TypeSafe_def subPrefixStructuralConsistency_def by auto

          have accO:"(\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some t)"
          proof (cases "arr = MTArray x t \<and> (\<exists>i<len. accessStore (hash pprnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr_loc))")
            case True
            then obtain ii where "ii<len \<and> accessStore (hash pprnt (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ptr_loc)" by blast
            then have "\<exists>len arr'. MCon arr (Memory st) ptr_loc \<and> arr = MTArray len arr'
                        \<and> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr')
                        "
              using old2 occ by fastforce
            then show ?thesis using True by blast
          next
            case False
            then obtain midP subL subA i where iidef:"(CompMemType (Memory st) len arr (MTArray subL subA) pprnt midP
                    \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr_loc) \<and> i < subL \<and> subA = MTArray x t)"
              using mids by blast
            then have "accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MTArray x t)"
              by (metis (no_types, lifting) typeSafeDecl_hyps(1) CompMemTypeSubIndexes old old2 pprntTP TypeSafe_def sameMemTSafe)
            then show ?thesis using occ iidef by fastforce
          qed


          then have "(\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some t)"
            using ncpOld ne6 ptrEq someSome oldLimit unfolding ncpOMemInDMem_def by metis
          then show ?thesis by simp
        qed

        then show ?thesis using t2Def by simp
      qed
    qed
  next
    have sameMem:"m' = mem'" using 20(7,8) by (auto split:if_splits)
    then show "subPrefixStructuralConsistency m'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by blast
  next
    show "SomeValSomeTyp m'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def using a10 20(7) by blast
  next

    assume notCp:"\<not>cp"
    then show "Toploc (Memory st) \<le> Toploc m'" using 20(7) a10 typeSafeDecl_hyps by auto

    show "ncpOMemInDMem (Memory st) m'" using 20(7) a10 typeSafeDecl_hyps notCp by blast
    show "ncpElementsNoSubPref (Memory st) m'" using 20(7) a10 typeSafeDecl_hyps notCp by blast
    show ncp:"ncpDenvalueLimit e ev k' (Stack st) (Memory st)" unfolding ncpDenvalueLimit_def
    proof intros
      fix tp' locs p''' i''
      assume asm:"(type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue e) \<and> accessStore locs k' = Some (KMemptr p''')
                  \<and> i'' < Toploc (Memory st) \<and> LSubPrefL2 p''' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')"
      then obtain i where idef:"Denvalue e $$ i = Some (type.Memory tp', Stackloc locs)" by blast

      have "ncpDenvalueLimit ev'' ev sck' (Stack st) (Memory st)" using 20 typeSafeDecl_hyps(5) by blast
      then have old:"\<forall>tp' locs p i.
     (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev'') \<and> accessStore locs sck' = Some (KMemptr p) \<and> i < Toploc
         (Memory st) \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
     (\<exists>tp'' loc2 p'.
         (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
         accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp''
             = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p)))"
        unfolding ncpDenvalueLimit_def by blast
      show "\<exists>tp'' loc2 p'.
          (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
          accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p''' \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p'''
              \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p'''))"
      proof(cases "locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
        case True
        then have b45:"tp' = (MTArray x t)" using a150 a50 True
          using idef by fastforce
        have b50:"p''' = p" using a40 a20 push_def
          by (metis stackvalue.inject(3) True accessStore_def accessStore_updateStore allocateMapping asm old.prod.exhaust option.inject snd_eqD)

        have c20:"(\<exists>stloc tp'' p'.
           (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue ev) \<and>
           accessStore stloc (Stack st) = Some (KMemptr p') \<and>
           (tp'' = (MTArray x t) \<and> p = p' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr (MTArray x t) p' p)))"
          using typeSafeDecl_hyps a5 20(2,3,7) by fastforce
        then show ?thesis using old a40 a20 asm b45 b50 by blast
      next
        case False
        then have b5:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))" using a20 a40 asm
          by (metis)
        then have "(type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev'')" using a40 a160 fmranI asm by fastforce
        moreover have "accessStore locs sck' = accessStore locs k'" using b5 a20 unfolding push_def accessStore_def updateStore_def allocate_def by auto
        ultimately show ?thesis using old asm by metis
      qed
    qed
  next
    assume notCP:"\<not>cp"
    then show "ncpNewSelfPoint (Memory st) m'" using a40 typeSafeDecl_hyps 20 a10 by blast
  next
    show "Toploc mem' \<le> Toploc m'" using a10 20 by blast
  qed
qed

text \<open>A memory array initialised from a calldata pointer: the array is copied into fresh memory.\<close>

lemma typeSafeDecl_21:
  assumes "tp = type.Memory (MTArray x t)"
    and "Some (v, t'') = Some (KCDptr p, tv0)"
    and "cp = cp0"
    and "cd = cdc"
    and "state.Memory st = mem0"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (cdc', mem''', sck'', ev'')"
    and "Some (c, m', k', e) = (if tv0 = Calldata (MTArray x t) \<and> 0 < x \<and> Denvalue
        ev'' $$ ip = None then cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem''')) x t cdc (snd (allocate
        mem''')) \<bind> (\<lambda>m'. Some (cdc', m', astack_dup ip (type.Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'''))) (sck'', ev''))) else None)"
  shows "declPost ev st cp mem' e c m' k'"
proof -
  let ?case = "declPost ev st cp mem' e c m' k'"
  note 21 = assms
  then obtain l where a1:"l = ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem')" by simp
  have vk:"tv0 = Calldata (MTArray x t)" using decl.simps(9) 21(8) by (simp split:if_split_asm)
  then have locationscd':"(\<forall>tloc loc. Toploc mem' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem' = None)"
    using typeSafeDecl_hyps(3) 21 unfolding TypeSafe_def lessThanTopLocs_def by simp
  then have b1:"accessStore l mem' = None" using a1 using Read_Show_nat'_id using LSubPrefL2_def by auto
  have b2:"x>0" using 21(8) vk a1 by (metis not_None_eq)
  then have Mconcd:"MCon (MTArray x t) cdc (extractValueType v)" using typeSafeDecl_hyps(2) 21(2) 21(4) vk 21(5) by simp
  have NoneIp:"Denvalue ev'' $$ ip = None" using 21 by (simp split:if_split_asm)
  obtain c' where a2:"\<exists>dud. (dud, c') = allocate mem'" by (simp add: allocate_def)
  then have aloc:"snd (allocate mem') = c'" by (simp add: allocate_def)
  then have lNotInC':"accessStore l c' = None" using b1 a1 unfolding allocate_def accessStore_def by auto
  obtain mm' where a3:"cpm2m p l x t cdc c' = Some mm'" using 21 a1 a2
    using b2 vk aloc NoneIp by fastforce
  then have a4:"Some (c, m', k', e) = Some (cdc', mm', astack ip (type.Memory (MTArray x t)) (KMemptr l) (sck', ev''))"
    using a1 a2 a3 21 decl.simps(9) vk b2 aloc NoneIp
    by simp
  then have a20:"k' = push (KMemptr l) sck'" by force
  have a30:"e = (updateEnv ip (type.Memory (MTArray x t)) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev'')" using a4 by simp
  then have a40:"Denvalue e = Denvalue(ev'' \<lparr> Denvalue := fmupd ip (type.Memory (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) (Denvalue ev'') \<rparr>)" by simp
  then have a50:"(Denvalue e) $$ ip = Some (type.Memory (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp

  then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
    using a3 a1 cpm2m_def[of p l x t cdc c'] cpm2mSingleChange[of p l t cdc c' x mm'] by fastforce
  have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem' = None" using locationscd' a2 lNotInC' a1 by auto
  have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
  then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
    using b100 a2 unfolding allocate_def by simp
  then have subMapping:"Mapping mem' \<subseteq>\<^sub>f Mapping mm'" using b105 unfolding fmsubset_alt_def
    by (metis (mono_tags, lifting) accessStore_def fmpredI option.distinct(1))

  have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 21(7) by simp
  then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''"
    using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
  then have a140:"\<forall>x y. \<not>((Denvalue ev'') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))"
    using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 21(7) by fastforce
  then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip"
    using a40 lessThanTopLocs_def fmranI by auto
  then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''')
                    \<and> l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip"
    using a40 lessThanTopLocs_def fmranI by auto
  have mcTop:"MCon (MTArray x t) mm' l" using a3 unfolding cpm2m_def a4
    using MCon_cpm2m[of p l t cdc c' x mm' ] Mconcd 21(2) b2 lNotInC' by fastforce
  have a110:"mm' = m'" using a4 by simp

  then have selfPoint:"\<forall>la l'. TypedMemSubPref la l (MTArray x t) \<and> accessStore la m' = Some (MPointer l') \<longrightarrow> l' = la"
    using cpm2mSelfPointers[of p l t cdc c' x mm'] a3 a1 cpm2m_def[of p l x t cdc c'] by metis
  have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
  then have b27:"\<forall>locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
    using a3 a1 cpm2m_def[of p l x t cdc c'] cpm2mSingleChange[of p l t cdc c' x mm'] a2 unfolding allocate_def by fastforce
  then have nonLocChanged2_Typed:"\<forall>t' locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))
                                            \<longrightarrow> accessTypeStore locs c' = accessTypeStore locs m'"
    using cpm2mSingleChange_Typed[of ] allocateTypeSameAccess a3 a1 a110 unfolding cpm2m_def by presburger
  moreover have "\<forall>locs. accessTypeStore locs c' = accessTypeStore locs mem'" using aloc allocateTypeSameAccess by metis
  ultimately have nonLocChanged2_Typed:"\<forall>t' locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))
                                          \<longrightarrow> accessTypeStore locs mem' = accessTypeStore locs m'" by simp
  have "\<forall>destl'.
       TypedMemSubPref destl' l (MTArray x t) \<longrightarrow>
       (\<exists>st. CompMemType mm' x t st l destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' mm' = Some (MTValue pval)))"
    using a1 a3 unfolding cpm2m_def using cpm2m_TypeCompChange[of p l t cdc c' x mm'] by blast
  then have mtp:"\<forall>destl'. TypedMemSubPref destl' l (MTArray x t) \<longrightarrow> (\<exists>st. CompMemType m' x t st l destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' m' = Some (MTValue pval)))" using a110 by blast

  show ?thesis unfolding TypeSafe_def
  proof(intros)
    have a110:"m' = mm'" using a4 by simp
    then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
      using a3 a1 cpm2m_def[of p l x t cdc c'] cpm2mSingleChange[of p l t cdc c' x mm'] by fastforce
    have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem' = None" using locationscd' a2 lNotInC' a1 by auto
    have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
    then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
      using b100 a2 unfolding allocate_def by simp

    fix locs tp assume ncp:"\<not>cp"
    then have a120:"\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp mem' locs" using typeSafeDecl_hyps(5) 21(7) by simp
    moreover have "\<forall>locs tp. MCon tp mem' locs \<longrightarrow> MCon tp mm' locs" using mconCopySingle[of l mem' mm' ] using b110 b105 by simp
    moreover have "Toploc c' > Toploc mem'" using a2 unfolding allocate_def by simp
    moreover have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x mm'] b2 by simp
    ultimately show "MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using 21 typeSafeDecl_hyps(5) 21(7) a110 a120 ncp by blast
  next
    show "unique_locations (Denvalue e)" using typeSafeDecl_hyps(3) 21(7) updateEnvUniqueLocs a4 by blast
  next
    have b2: "compPointers sck' (Denvalue ev'')" using typeSafeDecl_hyps(3) 21(7) unfolding TypeSafe_def by auto
    have "Address ev'' = Address e"using a30 by simp
    moreover have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 21(7) by simp
    ultimately show "compPointers k' (Denvalue e)"
      using compPointersNonStackUpd[of sck' ev'' e ip " type.Memory (MTArray x t)" k' "KMemptr l" ]
        a40 a50 typeSafeDecl_hyps(3) 21(7) b2 a20 by simp
  next
    show "safeContract (Accounts st) (Storage st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "balanceTypes (Accounts st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "svalueTypes (Svalue e)" using a30 21(7) typeSafeDecl_hyps(3) TypeSafe_def svalueTypes_def by simp
  next
    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 21(7) by simp
    then show "lessThanTopLocs k'" using stackPushToplocSafe a20 21(7) by metis
  next
    have "addressFormat (Address ev'') " using typeSafeDecl_hyps(3) TypeSafe_def 21(7) by simp
    then show "addressFormat(Address e) " using 21(7) a4 by auto
  next
    have "addressFormat(Sender ev'')" using typeSafeDecl_hyps(3) TypeSafe_def 21(7) by simp
    then show "addressFormat (Sender e)" using 21(7) a4 by auto
  next
    show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c" unfolding typeCompat_def
    proof intros
      fix tDen lDen
      assume *: "(tDen, lDen) |\<in>| fmran (Denvalue e)"
      then obtain ip'' where a90:"Denvalue e $$ ip'' = Some (tDen, lDen)" using * by auto
      then have a100:"(Storage st (Address ev'')) = (Storage st (Address e))" using a30 by simp
      have a110:"m' = mm'" using a4 by simp
      have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 21(7) by simp
      then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''"
        using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
      then have a140:"\<forall>x y. \<not>((Denvalue ev'') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))"
        using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 21(7) by fastforce
      then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip"
        using a40 lessThanTopLocs_def fmranI by auto
      then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''')
                        \<and> l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip"
        using a40 lessThanTopLocs_def fmranI by auto
      show "denvalueCon k' m' (Storage st (Address e)) c tDen lDen"
      proof(cases lDen)
        case (Stackloc x1)
        then show ?thesis
        proof (cases "x1 = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')")
          case True
          then have a170: "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KMemptr l)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using True a170 Stackloc by simp
          next
            case some:(Some a)
            then have a180:"a = KMemptr l " using a170 True by simp
            have a190:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KMemptr l)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
            then have "ip'' = ip" using a150 True a90 Stackloc by simp
            then have a200:"tDen = type.Memory (MTArray x t)" using a90 a50 by simp
            have a220:"v = KCDptr p" using 21(2) by simp
            have "c = cdc'" using a4 by simp
            then have "MCon (MTArray x t) mm' l" using a3 unfolding cpm2m_def
              using MCon_cpm2m[of p l t cdc c' x mm' ] Mconcd 21(2) b2
              by (metis a220 lNotInC' extractValueType.simps(2))
            then have "MCon (MTArray x t) m' l" using a4 a110 21(7) by blast
            then show ?thesis using Stackloc some a180 a200 extractValueType.simps(4) 21(2) by simp
          qed
        next
          case False
          then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
            using a3 a1 cpm2m_def[of p l x t cdc c'] cpm2mSingleChange[of p l t cdc c' x mm'] by fastforce

          have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem' = None" using locationscd' a2 lNotInC' a1 by auto
          have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
          then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
            using b100 a2 unfolding allocate_def by simp

          then have "ip'' \<noteq> ip" using a160 a90 Stackloc False by simp
          then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')" using a40 Stackloc fmranI a90 False * by fastforce
          then obtain y' where a180:"accessStore x1 sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) Stackloc 21 by blast
          then have a190:"accessStore x1 k' = accessStore x1 sck'"
            using a20 False by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using a180 a190 Stackloc by simp
          next
            case some:(Some a)
            then show ?thesis
            proof(cases a)
              case (KValue x1)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 21(7) by (cases tDen; fastforce)
            next
              case (KCDptr x2)
              then have b10:"(case tDen of Calldata struct \<Rightarrow> MCon struct cdc' x2 | _ \<Rightarrow> False)"
                using some a170 Stackloc a190 using typeSafeDecl_hyps(3) 21(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = Calldata struct" by (auto split:type.splits)
              then have "MCon struct cdc' x2" using b10 by simp
              then show ?thesis using Stackloc some KCDptr tden a110 a4 by simp
            next
              case (KMemptr x3)
              then have b10:"(case tDen of type.Memory struct \<Rightarrow> MCon struct mem' x3 | _ \<Rightarrow> False)"
                using some a170 Stackloc a190 using typeSafeDecl_hyps(3) 21(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = type.Memory struct" by (auto split:type.splits)
              then have "MCon struct mem' x3" using b10 by simp
              then have "MCon struct mm' x3" using mconCopySingle[of l mem' mm' struct] b110 b105 by auto
              then show ?thesis using Stackloc some KMemptr tden a110 a4 by simp
            next
              case (KStoptr x4)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 21(7) by (cases tDen; fastforce)
            qed
          qed
        qed
      next
        case (Storeloc x2)
        then have "ip'' \<noteq> ip" using a160 a90 by simp
        then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')" using a40 Storeloc fmranI a90 * by fastforce
        then have a180:"(case tDen of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st (Address ev'')) | _ \<Rightarrow> False)"
          using a170 Storeloc using typeSafeDecl_hyps(3) 21(7)
          unfolding TypeSafe_def typeCompat_def by force
        then obtain typ' where tdent:"tDen = type.Storage typ'" by (auto split: type.splits)
        then have "SCon typ' x2 (Storage st (Address ev''))" using a180 by simp
        then have "SCon typ' x2 (Storage st (Address e))" using a100 by simp
        then show ?thesis using a170 Storeloc using typeSafeDecl_hyps(3) 21(7) tdent
          by simp
      qed
    qed
  next
    have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x mm'] b2 by simp
    show "denvalueTypeCorrectness e k' m'" unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t2 l ptr_loc
      assume *:" (type.Memory t2, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"

      show "case t2 of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
      proof(cases "(type.Memory t2, Stackloc l) |\<in>| fmran(Denvalue ev')")
        case True
        moreover have sameACC:"accessStore l k' = accessStore l sck'"
          using a40 * unfolding astack.simps push_def updateStore_def accessStore_def allocate_def
          by (metis (no_types, lifting) accessStore_def typeSafeDecl_hyps(3,4) calculation decl_stack_change
              fmlookup_ran_iff snd_eqD TypeSafe_def stackLocs_imp_NotDen)
        then have old:"(case t2 of
                         MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some arr)
                         | MTValue val \<Rightarrow> accessTypeStore ptr_loc mem' = Some (MTValue val))"
          using typeSafeDecl_hyps(1) 21(7) * True typeSafeDecl_hyps(3) unfolding TypeSafe_def denvalueTypeCorrectness_def by simp
        have mcOld:"MCon t2 mem' ptr_loc" using * sameACC True typeSafeDecl_hyps(1) 21(7)
          unfolding TypeSafe_def typeCompat_def
          by (metis typeSafeDecl_hyps(3) sameMemTSafe)

        have lims:"\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) ptr_loc"
          using typeSafeAllPtrsNotTop[OF typeSafeDecl_hyps(3) True] * 21(7) sameACC b99 aloc unfolding allocate_def
          using LSubPrefL2_def MemLSubPrefTransitive by force
        then show ?thesis
        proof(cases t2)
          case (MTArray x11 x12)
          have nonLocChanged2_Typed_cond:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessTypeStore loc m' = accessTypeStore loc mem'"
            using nonLocChanged2_Typed by simp
          have nonLochanged:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore loc m' = accessStore loc mem'"
            using b27 a1 a110 by simp
          have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some x12)"
            using old MTArray by simp
          show ?thesis using MTArray old' nonLocChanged2_Typed_cond lims 21(7)
            using MemLSubPrefL2_specific_imps_general mtypes.simps(5) old nonLochanged
            by (metis (no_types, lifting) ext)
        next
          case (MTValue x2)
          then show ?thesis using nonLocChanged2_Typed old 21(7) lims by simp
        qed
      next
        case False
        then have "Denvalue e $$ ip = Some (type.Memory t2, Stackloc l)"
          using a40 * a4
          using typeSafeDecl_hyps(4) decl_env_not_i fmlookup_ran_iff by fastforce
        then have t2Def:"l = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) \<and> t2 = (MTArray x t)" using a40 by simp
        then have acc:"accessStore l k' = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')))"
          using a40 a20 a1 * unfolding push_def allocate_def updateStore_def accessStore_def by simp
        have "(\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some t)"
          using "*" a1 a110 a3 acc cpm2m_TypeCompChangeIndexs cpm2m_def by auto
        then show ?thesis using t2Def
          using "*" a1 a110 acc b1 b27 by fastforce
      qed
    qed
  next
    show "subPrefixStructuralConsistency m'" unfolding subPrefixStructuralConsistency_def
    proof(intros)
      fix locs tp
      assume in1:"accessTypeStore locs m' = Some tp"

      have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
      then have nonLocChanged2:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore locs mem' = accessStore locs m'"
        using a3 a1 cpm2m_def[of p l x t cdc c'] cpm2mSingleChange[of p l t cdc c' x mm'] a2 a110 unfolding allocate_def by fastforce

      have nonLocChanged_Typed:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t)
              \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessTypeStore locs mem' = accessTypeStore locs m'"
        using a3 a1 cpm2m_def[of p l x t cdc c'] cpm2mSingleChange_typedPref_typed[of p l t cdc c' x mm'] allocateTypeSameAccess a2 a110
        by (metis aloc)

      have "MCon (MTArray x t) mm' l" using a3 unfolding cpm2m_def
        using MCon_cpm2m[of p l t cdc c' x mm' ] Mconcd 21(2) b2 a1 lNotInC'
        by fastforce
      then have mcTop:"MCon (MTArray x t) m' l" using a4 a110 21(7) by blast

      have prefPtrs_imps_Pref:"\<forall>x3. TypedMemSubPrefPtrs mm' x t l x3 \<longrightarrow> TypedMemSubPref x3 l (MTArray x t)"
        using selfPoint_imps_TypedMemSubPref[OF selfPoint] a110 by blast

      show "case accessStore locs m' of None \<Rightarrow> False | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m' locs \<and> tp = MTValue val \<and> accessTypeStore locs m' = Some tp
       | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp m' p \<and> tp = MTArray len arr
\<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr) "
      proof(cases "accessTypeStore locs mem' = Some tp")
        case True
        then have accL:"\<exists>v. accessStore locs mem' = Some v"
          using typeSafeDecl_hyps(3) 21(7) unfolding TypeSafe_def SomeValSomeTyp_def by simp
        have notSub:"\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))"
        proof
          assume c:"LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))"
          then have "accessStore locs mem' = None"
            using 21(7) nless_le a1 b105 by presburger
          then show False using accL by auto
        qed
        then have sameACC:" accessStore locs m' = accessStore locs mem'" using nonLocChanged2 21(7) by simp
        then consider (ptr) p where "accessStore locs m' = Some (MPointer p)"
          | (val) val2 where "accessStore locs m' = Some (MValue val2)"
          using typeSafeDecl_hyps(1) 21(7) True unfolding TypeSafe_def subPrefixStructuralConsistency_def
          by (metis memoryvalue.exhaust accL)
        then show ?thesis
        proof(cases)
          case ptr
          then obtain len arr where
            old:"MCon tp mem' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some arr) "
            using typeSafeDecl_hyps(3) 21(7) True sameACC unfolding TypeSafe_def subPrefixStructuralConsistency_def by fastforce
          then have lim2:"\<forall>len arr loc. tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem' len arr p loc
                        \<longrightarrow> \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) loc"
            using AccessedMemPtrsCantTop[of "mem'" tp p] typeSafeDecl_hyps(3) 21(7) unfolding TypeSafe_def by blast
          have lim:" \<not> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) p"
            using AllPtrsNotTop_MCon notSub ptr using typeSafeDecl_hyps(3) 21(7) old unfolding TypeSafe_def by blast
          have accTLoc:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<or> loc =
              (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore loc m' = accessStore loc mem'"
            using 21(7) nonLocChanged2 a1 a110 b27 by presburger
          have "MCon tp m' p" using MCon_memory_transfer[OF _ lim lim2 accTLoc] old by blast
          moreover have "\<forall>i<len. \<not> LSubPrefL2 (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" using lim
            using MemLSubPrefL2_specific_imps_general by blast
          ultimately have "MCon tp m' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)"
            using nonLocChanged2_Typed old 21(7) by simp

          then show ?thesis using ptr by auto
        next
          case val
          then have old:"\<exists>val. MCon tp mem' locs \<and> tp = MTValue val \<and> accessTypeStore locs mem' = Some tp"
            using typeSafeDecl_hyps(3) 21(7) True sameACC unfolding TypeSafe_def subPrefixStructuralConsistency_def by fastforce
          then have "\<exists>val. MCon tp m' locs \<and> tp = MTValue val \<and> accessTypeStore locs m' = Some tp"
            using nonLocChanged2_Typed MCon.simps val notSub 21(7) sameACC by fastforce
          then show ?thesis using val by auto
        qed
      next
        case False
        then have sub:"TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t) \<and> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))"
          using nonLocChanged_Typed 21(7) in1 by fastforce
        then have "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t)"
          using selfPoint_imps_TypedMemSubPref by simp
        then obtain st where stD:"(CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) locs \<and>
           (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
            | MTValue pval \<Rightarrow> accessTypeStore locs m' = Some (MTValue pval)))" using mtp a1 by blast
        then have cmp:"CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) locs " by blast

        have mcLocs:"MCon st m' locs" using cmp mcTop CompTypeRemainsMCon a1 by auto

        show ?thesis
        proof(cases st)
          case (MTArray x11 x12)
          have subs:"t = MTArray x11 x12 \<and> (\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs)) \<or>
                       (\<exists>midP subL subA i. CompMemType m' x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) midP
                       \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
            using CompMemType_imps_Mid[of m' x t x11 x12 "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" locs] cmp MTArray by simp

          then have acc:"accessStore locs m' = Some (MPointer locs)"
            using selfPoint mcLocs sub MTArray MCon_imps_TypedMemSubPref_Some mcTop a1
            by (metis MCon.simps(2) option.distinct(1))

          moreover have "\<exists>len arr. MCon tp m' locs \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
                            \<and> (\<forall>v. accessStore locs m' = Some (MPointer v) \<longrightarrow> accessTypeStore locs m' = Some (MTArray len arr))"
            using in1
          proof(cases "(\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> t = MTArray x11 x12)")
            case True
            then obtain i where idef:"i<x \<and> accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs)
                                    \<and> t = MTArray x11 x12"
              by auto
            then have "TypedMemSubPref (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t) " by auto
            then have locsD:"locs = (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint idef a1 a110 by blast
            have "\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MTArray x11 x12)"
              using idef a1 a110 cpm2m_TypeCompChangeIndexs
              by (metis a3 cpm2m_def)
            then have "tp = MTArray x11 x12" using in1 locsD idef by simp
            moreover have "(\<forall>i<x11. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some x12)" using stD MTArray by simp
            ultimately show ?thesis using mcLocs MTArray in1 by blast
          next
            case False
            then obtain midP i subL subA where mid:"(CompMemType m' x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) midP
                   \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
              using subs by blast
            then have locD:"locs = (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint a110 a1
              using CompMemType_imps_in_GetAllMemoryLocations_ptr mcTop memSet_selfPoint by blast
            then obtain st2 where st2D:"(CompMemType m' x t st2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) midP \<and>
             (case st2 of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore midP m' = Some (MTValue pval)))" using mid mtp a1 a110
              using CompMemTypeSameLocsSameType CompMemType_imps_TypedMemSubPrefPtrs prefPtrs_imps_Pref by blast
            then have "st2 = (MTArray subL subA)" using mid CompMemTypeSameLocsSameType mcTop a1 by blast
            then have " \<forall>i<subL. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some subA" using st2D by simp
            then have "MTArray x11 x12 = tp" using in1 locD mid by simp
            then show ?thesis using mcLocs MTArray stD in1 by fastforce
          qed
          ultimately show ?thesis by auto
        next
          case (MTValue x2)
          then obtain v where vDef:"accessStore locs m' = Some (MValue v)"
            using mcLocs MCon.simps(1)[of x2 m' locs] by (auto split:option.splits memoryvalue.splits)
          moreover have "accessTypeStore locs m' = Some (MTValue x2)" using stD MTValue by auto
          moreover have "tp = MTValue x2" using calculation in1 by simp
          moreover have "MCon tp m' locs" using mcLocs calculation MTValue by blast
          ultimately show ?thesis using MTValue by simp
        qed
      qed
    qed
  next
    show "lessThanTopLocs c" using typeSafeDecl_hyps(3) 21(7) a4 unfolding TypeSafe_def by auto
  next
    have b100:"lessThanTopLocs mem'" using typeSafeDecl_hyps(3) 21(7) unfolding TypeSafe_def by blast
    have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x mm'] b2 by simp
    have " \<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs m'"
      using cpm2mSingleChange[of p l t cdc c' x mm'] a4 a3 cpm2m_def[of p l x t cdc c'] by fastforce
    moreover have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
    ultimately have b10:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs m' = accessStore locs mem'" by simp
    show "lessThanTopLocs m'" using cdMemLocsToploc[of mem' l c' m'] b100 a1 a2 b99 using b10 by presburger
  next
    show "AddressTypes (Accounts st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by simp
  next
    assume notCP:"\<not>cp"
    show "ncpDenvalueLimit e ev k' (Stack st) (Memory st)" unfolding ncpDenvalueLimit_def
    proof intros
      fix tp' locs p''' i''
      assume asm:" (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue e) \<and> accessStore locs k' = Some (KMemptr p''') \<and> i'' <
          Toploc (Memory st) \<and> LSubPrefL2 p''' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')"
      then obtain i where idef:"Denvalue e $$ i = Some (type.Memory tp', Stackloc locs)" by blast

      have "ncpDenvalueLimit ev'' ev sck' (Stack st) (Memory st)" using 21 notCP typeSafeDecl_hyps(5) by blast
      then have old:"\<forall>tp' locs p i.
     (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev'') \<and> accessStore locs sck' = Some (KMemptr p) \<and> i < Toploc
         (Memory st) \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
     (\<exists>tp'' loc2 p'.
         (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
         accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp''
             = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p)))"
        unfolding ncpDenvalueLimit_def by blast
      show "\<exists>tp'' loc2 p'.
          (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
          accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p''' \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p'''
              \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p'''))"
      proof(cases "locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
        case True
        then have b45:"tp' = (MTArray x t)" using a150 a50 True
          using idef by fastforce
        have b50:"p''' = l" using a40 a20 push_def
          by (metis stackvalue.inject(3) True accessStore_def accessStore_updateStore allocateMapping asm old.prod.exhaust option.inject snd_eqD)
        then have " p''' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" using a1 by blast
        moreover have "Toploc mem' \<ge> Toploc (Memory st)" using 21 notCP typeSafeDecl_hyps(5) by blast
        ultimately show ?thesis using asm
          by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general hash_inequality hash_suffixes_associative hashesIntSame le_antisym nat_less_le)
      next
        case False
        then have b5:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))" using a20 a40 asm
          by (metis)
        then have "(type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev'')" using a40 a160 fmranI asm by fastforce
        moreover have "accessStore locs sck' = accessStore locs k'" using b5 a20 unfolding push_def accessStore_def updateStore_def allocate_def by auto
        ultimately show ?thesis using old asm by metis
      qed
    qed
  next
    assume notCP:"\<not>cp"
    show "ncpOMemInDMem (Memory st) m'" unfolding ncpOMemInDMem_def
    proof intros
      fix i loc
      assume c10:" i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
      then have old:" accessStore loc (Memory st) = accessStore loc mem' \<and> accessTypeStore loc (Memory st) = accessTypeStore loc mem'"
        using typeSafeDecl_hyps(5) 21(7) notCP c10 ncpOMemInDMem_def by simp
      have " \<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs m'"
        using cpm2mSingleChange[of p l t cdc c' x mm'] a4 a3 cpm2m_def[of p l x t cdc c'] by fastforce
      moreover have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
      ultimately have b10:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs m' = accessStore locs mem'" by simp
      have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x mm'] b2 by simp
      have "Toploc (Memory st) \<le> Toploc mem'" using typeSafeDecl_hyps(5) c10 21(7) notCP by simp
      then have notI:"(ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> l" using a1 typeSafeDecl_hyps(5) c10 b99
        by (metis hashesIntSame leD)
      then show "accessStore loc (Memory st) = accessStore loc m'"
        using c10 a1 b99 a2 cdMemLocsToploc[of mem' l c' m']
        using "21"(3)
        by (metis LSubPrefL2_def old b10 hash_suffixes_associative hashesInts)

      have " \<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessTypeStore locs c' = accessTypeStore locs m'"
        using cpm2mSingleChange_Typed[of p l t cdc c' x mm'] a4 a3 cpm2m_def[of p l x t cdc c'] by fastforce
      moreover have "\<forall>locations. accessTypeStore locations c' = accessTypeStore locations mem'"
        using a2 allocateTypeSameAccess
        by (simp add: \<open>\<forall>locs. accessTypeStore locs c' = accessTypeStore locs mem'\<close>)
      ultimately have "\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessTypeStore locs m' = accessTypeStore locs mem'" by simp
      then show " accessTypeStore loc (Memory st) = accessTypeStore loc m'"
        using c10 a1 b99 a2 cdMemLocsToploc[of mem' l c' m']
        using LSubPrefL2_def old hash_suffixes_associative hashesInts 21(3) notI by metis
    qed
  next
    assume notCP:"\<not>cp"
    have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x mm'] b2 by simp

    have a110:"m' = mm'" using a4 by simp
    then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
      using a3 a1 cpm2m_def[of p l x t cdc c'] cpm2mSingleChange[of p l t cdc c' x mm'] by fastforce
    have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem' = None" using locationscd' a2 lNotInC' a1 by auto
    have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
    then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
      using b100 a2 unfolding allocate_def by simp

    fix locs tp assume ncp:"\<not>cp"
    then have a120:"\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp mem' locs" using typeSafeDecl_hyps(5) 21(7) by simp
    moreover have "\<forall>locs tp. MCon tp mem' locs \<longrightarrow> MCon tp mm' locs" using mconCopySingle[of l mem' mm' ] using b110 b105 by simp
    moreover have b98:"Toploc c' > Toploc mem'" using a2 unfolding allocate_def by simp
    moreover have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x mm'] b2 by simp
    ultimately have "MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using 21 typeSafeDecl_hyps(5) 21(7) a110 a120 ncp by blast

    have selfPoint:"\<forall>la l'. TypedMemSubPref la l (MTArray x t) \<and> accessStore la mm' = Some (MPointer l') \<longrightarrow> l' = la"
      using cpm2mSelfPointers[of p l t cdc c' x mm'] a3 a1 cpm2m_def[of p l x t cdc c'] by argo

    have sameaccess:"\<forall>locs. locs \<noteq> l \<and> \<not> TypedMemSubPref locs l (MTArray x t) \<longrightarrow> accessStore locs c' = accessStore locs mm'"
      using cpm2mSingleChange_typedPref[of p l t cdc c' x mm'] a3 a1 cpm2m_def[of p l x t cdc c'] by fastforce
    then have sameaccess:"\<forall>locs. locs \<noteq> l \<and> \<not> TypedMemSubPref locs l (MTArray x t) \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
      using b100 a2 unfolding allocate_def a2 accessAllocate[of c' mem']
      by (simp add: \<open>\<forall>locations. accessStore locations c' = accessStore locations mem'\<close>)

    have limitsOld:" ((\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None) \<and>
     (\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
      using typeSafeDecl_hyps(1) unfolding TypeSafe_def lessThanTopLocs_def using 21(7) by auto

    have limits:"((\<forall>tloc loc. Toploc mem' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem' = None) \<and>
                    (\<forall>loc y. accessStore loc mem' = Some y \<longrightarrow> (\<exists>tloc<Toploc mem'. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
      using typeSafeDecl_hyps(3) 21(7) unfolding TypeSafe_def lessThanTopLocs_def by simp

    have old:"ncpElementsNoSubPref (Memory st) mem' \<and> ncpOMemInDMem (Memory st) mem' \<and> ncpNewSelfPoint (Memory st) mem'" using 21 notCP typeSafeDecl_hyps(5) by blast
    then have sameLocs:"(\<forall>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
        accessStore loc (Memory st) = accessStore loc mem')" unfolding ncpOMemInDMem_def by blast
    have selfPointMem':" (\<forall>i loc loc2. i < Toploc mem' \<and> Toploc (Memory st) \<le> i \<and> LSubPrefL2 loc
        (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> accessStore loc mem' = Some (MPointer loc2) \<longrightarrow> loc = loc2)"
      using old unfolding ncpNewSelfPoint_def by blast
    then have old:"\<forall>i l1 t1 l2 t2 loc i2 loc2.
     i < Toploc (Memory st) \<and> Toploc (Memory st) \<le> i2 \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> LSubPrefL2
         loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> MCon (MTArray l1 t1) (Memory st) loc \<longrightarrow>
     \<not> TypedMemSubPrefPtrs mem' l2 t2 loc2 loc \<and> \<not> TypedMemSubPrefPtrs mem' l1 t1 loc loc2" using old unfolding ncpElementsNoSubPref_def by blast

    show "ncpElementsNoSubPref (Memory st) m' " unfolding ncpElementsNoSubPref_def
    proof intros
      fix i l1 t1 l2 t2 loc i2 loc2
      assume c10:"i < Toploc (Memory st) \<and> Toploc (Memory st) \<le> i2 \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and>
          LSubPrefL2 loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> MCon (MTArray l1 t1) (Memory st) loc"
      then have "accessStore loc (Memory st) = accessStore loc mem'"using sameLocs by auto
      have MConnew:"MCon (MTArray l1 t1) (Memory st) loc" using c10 by blast
      have locdef:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using c10 by simp

      then have inotl:"i < Toploc mem'" using b99 21(7) typeSafeDecl_hyps(5) ncp b98 c10 by simp
      then have inotlString:"(ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> l" using a1
        by (metis Read_Show_nat'_id linorder_neq_iff)
      have typeMemOld:"\<not> TypedMemSubPrefPtrs mem' l2 t2 loc2 loc \<and> \<not> TypedMemSubPrefPtrs mem' l1 t1 loc loc2" using old c10 MConnew by auto

      have "\<not> LSubPrefL2 loc l" using c10 inotlString
        by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general a1 hash_inequality hash_suffixes_associative)
      then have conc1:" \<not> TypedMemSubPrefPtrs m' l1 t1 loc loc2" using b105 b110 a110 MConnew a120 typeMemOld
        using inv_cpm2mTPrefOld_imps_TPref by blast
      then have hashlimit:"\<forall>f. hash loc2 f \<noteq> loc" using c10
        by (metis (no_types, opaque_lifting) MCon_imps_Some LSubPrefL2_def Not_Sub_More_Specific limitsOld not_Some_eq)

      have conc2:"\<not> TypedMemSubPrefPtrs m' l2 t2 loc2 loc"
      proof(cases " i2 < Toploc mem'")
        case True
        then have f2:" (\<forall>p loc2. i2 < Toploc mem' \<and> Toploc (Memory st) \<le> i2 \<and> LSubPrefL2 loc2
            (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> accessStore loc2 mem' = Some (MPointer p) \<longrightarrow> loc2 = p)"
          using selfPointMem' c10 by blast
        have "(ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using c10
          by (metis hashesIntSame leD)

        then have loc2NotSub:"\<not>LSubPrefL2 loc2 l" using a1 True
          by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general c10 hash_inequality hash_suffixes_associative hashesIntSame nat_neq_iff)
        show ?thesis
        proof
          assume asm:"TypedMemSubPrefPtrs m' l2 t2 loc2 loc"
          then show False using hashlimit f2 c10 b110 loc2NotSub
          proof(induction t2 arbitrary:loc2 l2)
            case (MTArray x1 t2)
            then obtain i''' l''' where i'''def:"(i'''<l2 \<and> accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t
                i''')) m' = Some (MPointer l''') \<and> (l''' = loc \<or> TypedMemSubPrefPtrs m' x1 t2 l''' loc))"
              using TypedMemSubPrefPtrs.simps(2)[of m' l2 x1 t2 loc2 loc] by blast
            then have "LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) (ShowL\<^sub>n\<^sub>a\<^sub>t i2)" using MTArray(5)
              by (metis LSubPrefL2_def Not_Sub_More_Specific)
            moreover have "\<not> LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) l" using MTArray(7)
              using MemLSubPrefL2_specific_imps_general a1 by blast

            ultimately have l'''Exp:"l''' = (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i'''))" using MTArray(4,6) i'''def
              by (metis True a110 c10)

            then show ?case
            proof(cases "l''' = loc")
              case True
              then show ?thesis using MTArray(3) l'''Exp by simp
            next
              case False
              then have "TypedMemSubPrefPtrs m' x1 t2 l''' loc" using i'''def by simp
              then show ?thesis using MTArray.IH[of x1 l'''] l'''Exp MTArray(3)
                using \<open>LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t
                    i''')) (ShowL\<^sub>n\<^sub>a\<^sub>t i2)\<close> \<open>\<not> LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) l\<close> b110 c10 f2 hash_suffixes_associative by force
            qed
          next
            case (MTValue x)
            then have "(\<exists>i<l2. hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = loc)" using TypedMemSubPrefPtrs.simps(1)[of m' l2 x loc2 loc] by auto
            then show ?case using MTValue by simp
          qed
        qed
      next
        case False
        then show ?thesis
        proof(cases "i2 = Toploc mem'")
          case True
          then have g1:"(ShowL\<^sub>n\<^sub>a\<^sub>t i2) = l" using a1 by blast
          show ?thesis
          proof
            assume asm:" TypedMemSubPrefPtrs m' l2 t2 loc2 loc"
            then show False using hashlimit c10 b105 selfPoint sameaccess
            proof(induction t2 arbitrary:loc2 l2)
              case (MTArray x1 t2)
              then obtain iIn lIn where idef: " (iIn<l2 \<and> accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) m' = Some
                  (MPointer lIn) \<and> (lIn = loc \<or> TypedMemSubPrefPtrs m' x1 t2 lIn loc))"
                using TypedMemSubPrefPtrs.simps(2)[of m' l2 x1 t2 loc2 loc] by blast
              have g2:"\<forall>i. (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> l" using g1 MTArray(4) LSubPrefL2_def
                by (metis hash_inequality hash_suffixes_associative)
              show ?case
              proof(cases "TypedMemSubPref (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) l (MTArray x t)")
                case True
                then have g4:"lIn = (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn))" using MTArray idef
                  using a110 by blast
                then show ?thesis
                proof(cases "lIn = loc")
                  case True
                  then show ?thesis using g4 MTArray by blast
                next
                  case False
                  have tp: "TypedMemSubPrefPtrs m' x1 t2 lIn loc" using False idef by simp
                  have sub: "LSubPrefL2 lIn l" using MTArray.prems(3) g1 g4 LSubPrefL2_hash_mono by metis
                  have hl: "\<forall>f. hash lIn f \<noteq> loc"
                    using sub \<open>\<not> LSubPrefL2 loc l\<close> LSubPrefL2_hash LSubPrefL2_trans by metis
                  have c: "i < Toploc (Memory st) \<and> Toploc (Memory st) \<le> i2 \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and>
                      LSubPrefL2 lIn (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> MCon (MTArray l1 t1) (Memory st) loc"
                    using MTArray.prems(3) sub g1 by simp
                  show ?thesis using MTArray.IH[of x1 lIn] tp hl c MTArray.prems(4,5,6) by blast
                qed
              next
                case False
                then have " accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) mem' = accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) mm'" using g2 MTArray by blast
                moreover have "LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) l" using g1 MTArray LSubPrefL2_def
                  by (metis hash_suffixes_associative)
                ultimately have "accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) mm' = None" using MTArray by metis
                then show ?thesis using idef
                  by (simp add: a110)
              qed
            next
              case (MTValue x')
              then show ?case by auto
            qed
          qed
        next
          case f4:False
          then have "i2> Toploc mem'" using False by auto
          then have loc2NotSub:"\<not>LSubPrefL2 loc2 l" using a1 c10
            by (metis LSubPrefL2_def f4 hash_suffixes_associative hashesInts)
          show ?thesis
          proof
            assume asm:"TypedMemSubPrefPtrs m' l2 t2 loc2 loc"
            show False
            proof(cases t2)
              case (MTArray x11 x12)
              then have h1:"(\<exists>i<l2. \<exists>l. accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = loc \<or> TypedMemSubPrefPtrs m' x11 x12 l loc))"
                using TypedMemSubPrefPtrs.simps(2)[of m' l2 x11 x12 loc2 loc] asm by blast
              then obtain i''' l''' where i'''def:"i'''<l2 \<and> accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t
                  i''')) m' = Some (MPointer l''') \<and> (l''' = loc \<or> TypedMemSubPrefPtrs m' x11 x12 l''' loc)" by blast
              then have " accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) m' = None" using loc2NotSub
                by (metis False LSubPrefL2_def MemLSubPrefL2_specific_imps_general a1 a110 b110 c10 Not_Sub_More_Specific leI locationscd')
              then show ?thesis using i'''def by simp
            next
              case (MTValue x2)
              then have "(\<exists>i<l2. hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = loc)"
                using asm TypedMemSubPrefPtrs.simps(1)[of m' l2 x2 loc2 loc] by blast
              then show ?thesis using hashlimit by simp
            qed
          qed

        qed
      qed
      then show "\<not> TypedMemSubPrefPtrs m' l2 t2 loc2 loc" using inv_cpm2mTPrefOld_imps_TPref conc2 by blast
      show "\<not> TypedMemSubPrefPtrs m' l1 t1 loc loc2" using conc1 by simp
    qed
  next
    have old:"SomeValSomeTyp mem'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by blast
    have non:"\<forall>loc. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore loc mem' = None"
      using 21(7) typeSafeDecl_hyps(3) unfolding TypeSafe_def lessThanTopLocs_def
      by auto

    have somesomeT:"\<forall>destl'.
          TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t) \<longrightarrow>
          (\<exists>t. accessStore destl' m' = Some t) = (\<exists>tt. accessTypeStore destl' m' = Some tt)"
      using a3 unfolding cpm2m_def using cpm2m_TypeCompChange_somesome[of p l t _ c' x mm'] a4 a1 by blast
    show "SomeValSomeTyp m'" unfolding SomeValSomeTyp_def
    proof intros
      fix locs
      show "(\<exists>t. accessStore locs m' = Some t) = (\<exists>tt. accessTypeStore locs m' = Some tt) "
      proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t)")
        case True
        then show ?thesis using somesomeT by simp
      next
        case False
        then have "accessStore locs m' = accessStore locs mem'"
          using "21"(7)
          by (metis \<open>\<forall>locations. accessStore locations c' = accessStore locations mem'\<close> a1 a110 a3 cpm2mSingleChange_typedPref cpm2m_def)
        moreover have "accessTypeStore locs m' = accessTypeStore locs mem'"
          using False cpm2mSingleChange_typedPref_typed 21(7) allocateTypeSameAccess
          by (metis a1 a110 a3 aloc cpm2m_def)
        ultimately show ?thesis using old
          by (simp add: SomeValSomeTyp_def)
      qed
    qed

  next
    assume notCP:"\<not>cp"
    have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x mm'] b2 by simp
    have "Toploc (Memory st) \<le> Toploc mem'" using typeSafeDecl_hyps(5) 21(7) notCP by simp
    moreover have "Toploc c' > Toploc mem'" using a2 unfolding allocate_def by simp
    then show " Toploc (Memory st) \<le> Toploc m' " using b99 notCP typeSafeDecl_hyps 21 by simp
  next
    assume notCP:"\<not>cp"
    show "ncpNewSelfPoint (Memory st) m'" unfolding ncpNewSelfPoint_def
    proof intros
      fix i loc loc2
      assume asm:"i < Toploc m' \<and> Toploc (Memory st) \<le> i \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> accessStore loc m' = Some (MPointer loc2)"
      have old:"(\<forall>i loc loc2. i < Toploc mem' \<and> Toploc (Memory st) \<le> i \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t
          i) \<and> accessStore loc mem' = Some (MPointer loc2) \<longrightarrow> loc = loc2)"
        using typeSafeDecl_hyps(5) notCP 21(7) unfolding ncpNewSelfPoint_def by blast
      have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x mm'] b2 by simp

      have a110:"m' = mm'" using a4 by simp
      then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
        using a3 a1 cpm2m_def[of p l x t cdc c'] cpm2mSingleChange[of p l t cdc c' x mm'] by fastforce
      have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem' = None" using locationscd' a2 lNotInC' a1 by auto
      have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 accessAllocate[of c' mem'] by auto
      then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
        using b100 a2 unfolding allocate_def by simp

      have g1:"Toploc c' = Suc (Toploc mem')" using a2 unfolding allocate_def by simp
      show "loc = loc2"
      proof(cases "i < Toploc mem'")
        case True
        then have "\<not> LSubPrefL2 loc l" using a1 LSubPrefL2_def
          by (metis MemLSubPrefL2_specific_imps_general Read_Show_nat'_id asm hash_inequality hash_suffixes_associative less_not_refl)
        then show ?thesis using old asm b110 a1 True a110 by auto
      next
        case False
        then have iIsTop:"i = Toploc mem'" using asm g1 b99 by simp
        have selfPoint:"\<forall>la l'. TypedMemSubPref la l (MTArray x t) \<and> accessStore la mm' = Some (MPointer l') \<longrightarrow> l' = la"
          using cpm2mSelfPointers[of p l t cdc c' x mm'] a3 a1 cpm2m_def[of p l x t cdc c'] by argo

        have sameaccess:"\<forall>locs. locs \<noteq> l \<and> \<not> TypedMemSubPref locs l (MTArray x t) \<longrightarrow> accessStore locs c' = accessStore locs mm'"
          using cpm2mSingleChange_typedPref[of p l t cdc c' x mm'] a3 a1 cpm2m_def[of p l x t cdc c'] by fastforce
        then have sameaccess:"\<forall>locs. locs \<noteq> l \<and> \<not> TypedMemSubPref locs l (MTArray x t) \<longrightarrow> accessStore locs mem' = accessStore locs mm'"
          using b100 a2 allocate_def accessAllocate[of c' mem'] by simp
        then show ?thesis using asm iIsTop
          by (metis a1 a110 a3 cpm2m_iter_dest_unchanged b105 cpm2m_def hash_inequality lNotInC' not_Some_eq selfPoint)
      qed
    qed
  next
    have b99:"Toploc c' = Toploc m'" using a3 a4 cpm2m_def[of p l x t cdc c' ] cpm2mTopLocSame[of p l t cdc c' x mm'] b2 by simp
    then show "Toploc mem' \<le> Toploc m' " using aloc unfolding allocate_def by auto
  qed
qed

text \<open>A memory array initialised from a storage pointer: the storage array is copied into fresh memory with @{const cps2m}.\<close>

lemma typeSafeDecl_22:
  assumes "tp = type.Memory (MTArray x t)"
    and "Some (v, t'') = Some (KStoptr p, type.Storage (STArray x' t'))"
    and "cp = cp0"
    and "cd = cd0"
    and "state.Memory st = mem0"
    and "state.Storage st (Address ev) = s"
    and "(cd', mem', sck', ev') = (cdc', mem''', sck'', ev'')"
    and "Some (c, m', k', e) = (if cps2mTypeCompatible (STArray x' t') (MTArray x t) \<and> Denvalue
        ev'' $$ ip = None then cps2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem''')) x' t' s (snd (allocate
        mem''')) \<bind> (\<lambda>m''. Some (cdc',
        m'', astack_dup ip (type.Memory (MTArray x t)) (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'''))) (sck'', ev''))) else None)"
  shows "declPost ev st cp mem' e c m' k'"
proof -
  let ?case = "declPost ev st cp mem' e c m' k'"
  note 22 = assms
  then obtain l where a1:"l = ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem''')" by simp
  then have locationscd':"(\<forall>tloc loc. Toploc mem''' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem''' = None)"
    using typeSafeDecl_hyps(3) 22 unfolding TypeSafe_def lessThanTopLocs_def by simp
  then have b1:"accessStore l mem''' = None" using a1 using Read_Show_nat'_id using LSubPrefL2_def by auto
  have b2:"0 < x" using 22(8) a1 cps2mTypeCompatible.simps(2)[of x' t' x t]
    by fastforce
  then have b3:"0 < x'" using 22(8) by (auto split:if_split_asm)
  have b4:"x = x'" using 22(8) by (auto split:if_split_asm)
  then have Mconcd:" SCon (STArray x' t') (extractValueType v) (Storage st (Address ev))" using typeSafeDecl_hyps(2) 22(2) 22(4) 22(5) by simp
  then have MConcd2:" SCon (STArray x' t') p s" using 22 by simp
  obtain c' where a2:"\<exists>dud. (dud, c') = allocate mem'''" by (simp add: allocate_def)
  then have aloc:"snd (allocate mem''') = c'" by (simp add: allocate_def)
  then have lNotInC':"accessStore l c' = None" using b1 a1 unfolding allocate_def accessStore_def by auto
  obtain mm' where a3:"cps2m p l x' t' s c' = Some mm'" using 22 a1 a2 typeSafeDecl_hyps
    using b2 aloc b3 by (metis (no_types, lifting) bind_eq_Some_conv option.discI)
  have NoneIp:"Denvalue ev'' $$ ip = None" using 22(8) by (auto split:if_split_asm)
  then have a4:"Some (c, m', k', e) = Some (cdc', mm', astack_dup ip (type.Memory (MTArray x t)) (KMemptr l) (sck'', ev''))"
    using a1 a2 a3 22 typeSafeDecl_hyps decl.simps(9) b2 aloc b3 NoneIp
    by (metis bind.bind_lunit not_None_eq)
  then have a4:"Some (c, m', k', e) = Some (cdc', mm', astack_dup ip (type.Memory (MTArray x t)) (KMemptr l) (sck', ev''))"
    using 22(7) by simp
  then have a20:"k' = push (KMemptr l) sck'" using 22(7) NoneIp by force
  have a30:"e = (updateEnv ip (type.Memory (MTArray x t)) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev'')" using a4 NoneIp by simp
  then have a40:"Denvalue e = Denvalue(ev'' \<lparr> Denvalue := fmupd ip (type.Memory (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) (Denvalue ev'') \<rparr>)" by simp
  then have a50:"(Denvalue e) $$ ip = Some (type.Memory (MTArray x t),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp

  have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 22(7) by simp
  then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''"
    using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
  then have a140:"\<forall>x y. \<not>((Denvalue ev'') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))"
    using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 22(7) by fastforce
  then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip"
    using a40 lessThanTopLocs_def fmranI by auto
  then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''')
                    \<and> l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip"
    using a40 lessThanTopLocs_def fmranI by auto
  have cps2mTypeComp:"cps2mTypeCompatible (STArray x' t') (MTArray x t)" using 22(8) a1 by (meson option.discI)
  have a110:"m' = mm'" using a4 by simp
  then have b27:"\<forall>locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessStore locs mem' = accessStore locs m'"
    using a3 a1 cps2m_def[of p l x' t' s c'] cps2mSingleChange[of p l t' s c' x' mm'] a2 22(7) unfolding allocate_def
    by (metis (no_types, lifting) Pair_inject allocateSameAccess aloc)
  have b27T:"\<forall>locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessTypeStore locs c' = accessTypeStore locs mm'"
    using a3 a1 cps2m_def[of p l x' t' s c'] cps2mSingleChange_both[of p l t' s c' x' mm'] a2 22(7) unfolding allocate_def
    by (metis (no_types, lifting))
  then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
    using b27 a3 a1 cps2m_def[of p l x' t' " s" c'] cps2mSingleChange[of p l t' "s" c' x' mm'] by fastforce
  have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem''' = None" using locationscd' a2 lNotInC' a1 by auto
  have "\<forall>locations. accessStore locations c' = accessStore locations mem'''" using a2 accessAllocate[of c' mem'''] by auto
  then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem''' = accessStore locs mm'"
    using b100 a2 unfolding allocate_def by simp
  have subMapping:"Mapping mem' \<subseteq>\<^sub>f Mapping mm'"
  proof -
    have "fmlookup (Mapping mem') k = Some v \<Longrightarrow> fmlookup (Mapping mm') k = Some v" for k v
      using b105[rule_format, of k] b110[rule_format, of k] 22(7) unfolding accessStore_def
      by (cases "LSubPrefL2 k l") auto
    then show ?thesis unfolding fmsubset_alt_def fmpred_iff by blast
  qed
  have mcTop1:"MCon (MTArray x t) mm' l" using a3 unfolding cpm2m_def
    using cps2m[of p l t' "s" c' x' mm' ] b3 Mconcd 22(2) b2
      cps2m_def[of p l x' t' "s" c'] b4 extractValueType.simps(4) "22"(6) 22(7)
    using MConcd2 cps2mTypeComp lNotInC' by presburger
  then have mcTop2:"MCon (MTArray x t) m' l" using a4 a110 22(7) by blast

  have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 22(7) accessAllocate[of c' mem'] by auto

  then have nonLocChanged2_Typed:"\<forall>t' locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))
                                            \<longrightarrow> accessTypeStore locs c' = accessTypeStore locs m'"
    using cps2mSingleChange_both[of ] allocateTypeSameAccess a3 a1 a110 unfolding cps2m_def using 22(7) a110 by blast
  moreover have "\<forall>locs. accessTypeStore locs c' = accessTypeStore locs mem'" using aloc allocateTypeSameAccess 22(7)
    by (metis prod.inject)
  ultimately have nonLocChanged2_Typed:"\<forall>t' locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))
                                          \<longrightarrow> accessTypeStore locs mem' = accessTypeStore locs m'" by simp
  have "\<forall>destl'.
       TypedMemSubPref destl' l (MTArray x' t) \<longrightarrow>
       (\<exists>st. CompMemType mm' x' t st l destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' mm' = Some (MTValue pval)))"
    using a1 a3 cps2mTypeComp unfolding cps2m_def using cps2m_TypeCompChange[of p l t' s c' x' mm' t] by fastforce
  then have mtp:"\<forall>destl'.
       TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x' t) \<longrightarrow>
       (\<exists>st. CompMemType m' x' t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) destl' \<and>
             (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore destl' m' = Some (MTValue pval)))" using a110 22(7) a1 by blast
  have selfPoint:"\<forall>la l'. TypedStoSubpref la l (STArray x' t') \<and> accessStore la mm' = Some (MPointer l') \<longrightarrow> l' = la"
    using cps2mSelfPointers[of p l t' "s" c' x' mm'] a3 a1 cps2m_def[of p l x' t' s c']
    by (metis \<open>\<forall>locations. accessStore locations c' = accessStore locations mem'\<close> a110 b27 lNotInC'
        option.discI)
  then have selfPoint2:"\<forall>la l'. TypedMemSubPref la l (MTArray x t) \<and> accessStore la m' = Some (MPointer l') \<longrightarrow> l' = la"
    using cps2mTypeComp a110
    using compatible_TypedStoSubpref_imps_TypedMemSubPref by presburger
  show ?thesis unfolding TypeSafe_def
  proof(intros)

    show "unique_locations (Denvalue e)" using typeSafeDecl_hyps(3) 22(7) updateEnvUniqueLocs a4 NoneIp astack_dup_is_astack by fastforce
  next
    have b2: "compPointers sck' (Denvalue ev'')" using typeSafeDecl_hyps(3) 22(7) unfolding TypeSafe_def by auto
    have "Address ev'' = Address e"using a30 by simp
    moreover have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 22(7) by simp
    ultimately show "compPointers k' (Denvalue e)"
      using compPointersNonStackUpd[of sck' ev'' e ip " type.Memory (MTArray x t)" k' "KMemptr l"]
        a40 a50 typeSafeDecl_hyps(3) 22(7) b2 a20 by simp
  next
    show "safeContract (Accounts st) (Storage st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "balanceTypes (Accounts st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "svalueTypes (Svalue e)" using a30 22(7) typeSafeDecl_hyps(3) TypeSafe_def svalueTypes_def by simp
  next
    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 22(7) by simp
    then show "lessThanTopLocs k'" using stackPushToplocSafe a20 22(7) by metis
  next
    have "addressFormat (Address ev'')" using typeSafeDecl_hyps(3) TypeSafe_def 22(7) by simp
    then show "addressFormat(Address e)" using 22(7) a4 NoneIp by auto
  next
    have "addressFormat (Sender ev'')" using typeSafeDecl_hyps(3) TypeSafe_def 22(7) by simp
    then show "addressFormat (Sender e)" using 22(7) a4 NoneIp by auto
  next
    show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c" unfolding typeCompat_def
    proof intros
      fix tDen lDen
      assume *: "(tDen, lDen) |\<in>| fmran (Denvalue e)"
      then obtain ip'' where a90:"Denvalue e $$ ip'' = Some (tDen, lDen)" using * by auto
      then have a100:"(Storage st (Address ev'')) = (Storage st (Address e))" using a30 by simp

      show "denvalueCon k' m' (Storage st (Address e)) c tDen lDen"
      proof(cases lDen)
        case (Stackloc x1)
        then show ?thesis
        proof (cases "x1 = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')")
          case True
          then have a170: "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KMemptr l)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using True a170 Stackloc by simp
          next
            case some:(Some a)
            then have a180:"a = KMemptr l " using a170 True by simp
            have a190:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KMemptr l)" using a20 by (simp add:push_def allocate_def updateStore_def accessStore_def)
            then have "ip'' = ip" using a150 True a90 Stackloc by simp
            then have a200:"tDen = type.Memory (MTArray x t)" using a90 a50 by simp
            have a220:"v = KStoptr p" using 22(2) by simp
            have a230:"cps2mTypeCompatible (STArray x' t') (MTArray x t)" using 22(8) a1 by (meson option.discI)
            have "c = cdc'" using a4 by simp
            moreover have " (\<exists>p. accessStore l c' = Some (MPointer p)) \<or> accessStore l c' = None"
              by (simp add: lNotInC')
            ultimately have "MCon (MTArray x t) mm' l" using a3 unfolding cpm2m_def
              using cps2m[of p l t' "s" c' x' mm' ] b3 Mconcd 22(2) b2
                cps2m_def[of p l x' t' "s" c'] b4 extractValueType.simps(4) "22"(6) 22(7) a100 by (metis a220 a230)
            then have "MCon (MTArray x t) m' l" using a4 a110 22(7) by blast
            then show ?thesis using Stackloc some a180 a200 extractValueType.simps(4) 22(2) by simp
          qed
        next
          case False
          then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
            using a3 a1 cps2m_def[of p l x' t' " s" c'] cps2mSingleChange[of p l t' "s" c' x' mm'] by fastforce

          have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem''' = None" using locationscd' a2 lNotInC' a1 by auto
          have "\<forall>locations. accessStore locations c' = accessStore locations mem'''" using a2 accessAllocate[of c' mem'''] by auto
          then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem''' = accessStore locs mm'"
            using b100 a2 unfolding allocate_def by simp

          then have "ip'' \<noteq> ip" using a160 a90 Stackloc False by simp
          then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')" using a40 Stackloc fmranI a90 False * by fastforce
          then obtain y' where a180:"accessStore x1 sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) Stackloc 22 by blast
          then have a190:"accessStore x1 k' = accessStore x1 sck'"
            using a20 False by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using a180 a190 Stackloc by simp
          next
            case some:(Some a)
            then show ?thesis
            proof(cases a)
              case (KValue x1)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 22(7) by (cases tDen; fastforce)
            next
              case (KCDptr x2)
              then have b10:"(case tDen of Calldata struct \<Rightarrow> MCon struct cdc' x2 | _ \<Rightarrow> False)"
                using some a170 Stackloc a190 using typeSafeDecl_hyps(3) 22(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = Calldata struct" by (auto split:type.splits)
              then have "MCon struct cdc' x2" using b10 by simp
              then show ?thesis using Stackloc some KCDptr tden a110 a4 by simp
            next
              case (KMemptr x3)
              then have b10:"(case tDen of type.Memory struct \<Rightarrow> MCon struct mem' x3 | _ \<Rightarrow> False)"
                using some a170 Stackloc a190 using typeSafeDecl_hyps(3) 22(7) unfolding TypeSafe_def typeCompat_def by force
              then obtain struct where tden: "tDen = type.Memory struct" by (auto split:type.splits)
              then have "MCon struct mem''' x3" using b10 22 by simp
              then have "MCon struct mm' x3" using mconCopySingle[of l mem''' mm' struct] b110 b105 by auto
              then show ?thesis using Stackloc some KMemptr tden a110 a4 by simp
            next
              case (KStoptr x4)
              then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
                using a190 some Stackloc a170 * a180 a110 a100 22(7) by (cases tDen; fastforce)
            qed
          qed
        qed
      next
        case (Storeloc x2)
        then have "ip'' \<noteq> ip" using a160 a90 by simp
        then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev'')" using a40 Storeloc fmranI a90 * by fastforce
        then have a180:"(case tDen of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st (Address ev'')) | _ \<Rightarrow> False)"
          using a170 Storeloc using typeSafeDecl_hyps(3) 22(7)
          unfolding TypeSafe_def typeCompat_def by force
        then obtain typ' where tdent:"tDen = type.Storage typ'" by (auto split: type.splits)
        then have "SCon typ' x2 (Storage st (Address ev''))" using a180 by simp
        then have "SCon typ' x2 (Storage st (Address e))" using a100 by simp
        then show ?thesis using a170 Storeloc using typeSafeDecl_hyps(3) 22(7) tdent
          by simp
      qed
    qed
  next
    show "lessThanTopLocs c" using typeSafeDecl_hyps(3) 22(7) a4 unfolding TypeSafe_def by auto
  next
    have b100:"lessThanTopLocs mem'''" using typeSafeDecl_hyps(3) 22(7) unfolding TypeSafe_def by blast
    have b99:"Toploc c' = Toploc m'" using a3 a4 cps2m_def[of p l x' t' "s" c'] cps2mTopLocSame[of p l t' "s" c' x' mm'] b3 by simp
    have " \<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs m'"
      using cps2mSingleChange[of p l t' "s" c' x' mm'] a4 a3 cps2m_def[of p l x' t' "s" c'] by fastforce
    moreover have "\<forall>locations. accessStore locations c' = accessStore locations mem'''" using a2 accessAllocate[of c' mem'''] 22 by auto
    ultimately have b10:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs m' = accessStore locs mem'''" by simp
    show "lessThanTopLocs m'" using cdMemLocsToploc[of mem''' l c' m'] b100 a1 a2 b99 using b10 by presburger
  next
    show "AddressTypes (Accounts st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by simp
  next
    fix locs tp assume ncp:"\<not>cp"
    have a110:"m' = mm'" using a4 by simp
    then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
      using a3 a1 cps2m_def[of p l x' t' s c'] cps2mSingleChange[of p l t' "s" c' x' mm'] by fastforce
    have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem''' = None" using locationscd' a2 lNotInC' a1 by auto
    have "\<forall>locations. accessStore locations c' = accessStore locations mem'''" using a2 accessAllocate[of c' mem'''] by auto
    then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem''' = accessStore locs mm'"
      using b100 a2 unfolding allocate_def by simp
    have a120:"\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp mem' locs" using typeSafeDecl_hyps(5) 22(7) ncp by simp
    moreover have "\<forall>locs tp. MCon tp mem''' locs \<longrightarrow> MCon tp mm' locs" using mconCopySingle[of l mem''' mm' ] using b110 b105 by simp
    moreover have "Toploc c' > Toploc mem'''" using a2 unfolding allocate_def by simp
    moreover have b99:"Toploc c' = Toploc mm'" using a1 a3 a4 cps2m_def[of p l x' t' s c'] cps2mTopLocSame[of p l t' "s" c' x' mm'] b2 by fastforce
    ultimately show "MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using typeSafeDecl_hyps(5) 22(7) a110 a120 ncp by blast
  next
    assume notCP:"\<not>cp"
    show "ncpDenvalueLimit e ev k' (Stack st) (Memory st)" unfolding ncpDenvalueLimit_def
    proof intros
      fix tp' locs p''' i''
      assume asm:" (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue e) \<and> accessStore locs k' = Some (KMemptr p''') \<and> i'' <
          Toploc (Memory st) \<and> LSubPrefL2 p''' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')"
      then obtain i where idef:"Denvalue e $$ i = Some (type.Memory tp', Stackloc locs)" by blast

      have "ncpDenvalueLimit ev'' ev sck' (Stack st) (Memory st)" using 22 notCP typeSafeDecl_hyps(5) by blast
      then have old:"\<forall>tp' locs p i.
     (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev'') \<and> accessStore locs sck' = Some (KMemptr p) \<and> i < Toploc
         (Memory st) \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
     (\<exists>tp'' loc2 p'.
         (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
         accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp''
             = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p)))"
        unfolding ncpDenvalueLimit_def by blast
      show "\<exists>tp'' loc2 p'.
          (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
          accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p''' \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p'''
              \<and> tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p'''))"
      proof(cases "locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
        case True
        have b50:"p''' = l" using a40 a20 push_def
          by (metis stackvalue.inject(3) True accessStore_def accessStore_updateStore allocateMapping asm old.prod.exhaust option.inject snd_eqD)
        then have " p''' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'''))" using a1 by blast
        moreover have "Toploc mem''' \<ge> Toploc (Memory st)" using 22 notCP typeSafeDecl_hyps(5) by blast
        ultimately show ?thesis using asm
          by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general hash_inequality hash_suffixes_associative hashesIntSame le_antisym nat_less_le)
      next
        case False
        then have b5:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))" using a20 a40 asm
          by (metis)
        then have "(type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev'')" using a40 a160 fmranI asm by fastforce
        moreover have "accessStore locs sck' = accessStore locs k'" using b5 a20 unfolding push_def accessStore_def updateStore_def allocate_def by auto
        ultimately show ?thesis using old asm by metis
      qed
    qed
  next
    assume ncp:"\<not>cp"
    show "ncpOMemInDMem (Memory st) m'" unfolding ncpOMemInDMem_def
    proof intros
      fix i loc
      assume c10:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
      then have " accessStore loc (Memory st) = accessStore loc mem'''" using typeSafeDecl_hyps(5) 22(7) ncpOMemInDMem_def ncp by auto
      have " \<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs m'"
        using cps2mSingleChange[of p l t' "s" c' x' mm'] a4 a3 cps2m_def[of p l x' t' s c'] by fastforce
      moreover have "\<forall>locations. accessStore locations c' = accessStore locations mem'''" using a2 accessAllocate[of c' mem'''] by auto
      ultimately have b10:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs m' = accessStore locs mem'''" by simp
      have b99:"Toploc c' = Toploc m'" using a3 a4 cps2m_def[of p l x' t' s c'] cps2mTopLocSame[of p l t' "s" c' x' mm'] b2
        by fastforce
      have "Toploc (Memory st) \<le> Toploc mem'''" using typeSafeDecl_hyps(5) c10 22(7) ncpOMemInDMem_def ncp by simp
      then have "(ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> l" using a1 typeSafeDecl_hyps(5) c10 b99
        by (metis hashesIntSame leD)
      then show "accessStore loc (Memory st) = accessStore loc m'" using c10 a1 b99 a2 cdMemLocsToploc[of mem''' l c' m']
        using "22"(3)
        by (metis LSubPrefL2_def \<open>accessStore loc (Memory st) = accessStore loc mem'''\<close> b10 hash_suffixes_associative hashesInts)
      have " \<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessTypeStore locs c' = accessTypeStore locs m'"
        using cps2mSingleChange_both[of p l t' "s" c' x' mm'] a4 a3 cps2m_def[of p l x' t' s c'] by fastforce
      moreover have "\<forall>locations. accessTypeStore locations c' = accessTypeStore locations mem'''" using a2 allocateTypeSameAccess
        by (metis aloc)
      ultimately have b10:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessTypeStore locs m' = accessTypeStore locs mem'''" by simp
      moreover have " accessTypeStore loc (Memory st) = accessTypeStore loc mem'''" using typeSafeDecl_hyps(5) 22(7) ncpOMemInDMem_def ncp c10 by blast
      ultimately show "accessTypeStore loc (Memory st) = accessTypeStore loc m'"
        using c10 a1 b99 a2 cdMemLocsToploc[of mem''' l c' m'] 22(3) b10 a2
        by (metis LSubPrefL2_def MemLSubPrefTransitive \<open>(ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> l\<close> hash_flatten_right hash_inequality)
    qed
  next
    assume notCP:"\<not>cp"
    have a110:"m' = mm'" using a4 by simp
    then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
      using a3 a1 cps2m_def[of p l x' t' s c'] cps2mSingleChange[of p l t' "s" c' x' mm'] by fastforce
    have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem''' = None" using locationscd' a2 lNotInC' a1 by auto
    have "\<forall>locations. accessStore locations c' = accessStore locations mem'''" using a2 accessAllocate[of c' mem'''] by auto
    then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem''' = accessStore locs mm'"
      using b100 a2 unfolding allocate_def by simp

    fix locs tp
    have a120:"\<forall>locs tp. MCon tp (Memory st) locs \<longrightarrow> MCon tp mem''' locs" using typeSafeDecl_hyps(5) 22(7) notCP by simp
    moreover have "\<forall>locs tp. MCon tp mem''' locs \<longrightarrow> MCon tp mm' locs" using mconCopySingle[of l mem''' mm' ] using b110 b105 by simp
    moreover have b98:"Toploc c' > Toploc mem'''" using a2 unfolding allocate_def by simp
    moreover have b99:"Toploc c' = Toploc m'" using a3 a4 cps2m_def[of p l x' t' s c'] cps2mTopLocSame[of p l t' "s" c' x' mm'] b2 by fastforce
    ultimately have "MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using 22 typeSafeDecl_hyps(5) 22(7) a110 a120 notCP by blast


    have sameaccess:" \<forall>locs. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x' t') \<longrightarrow> accessStore locs c' = accessStore locs mm'"
      using cps2mSingleChange_typedPref[of p l t' "s" c' x' mm'] a3 a1 cps2m_def[of p l x' t' s c'] by fastforce
    then have sameaccess:"\<forall>locs. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x' t') \<longrightarrow> accessStore locs mem''' = accessStore locs mm'"
      using b100 a2 unfolding allocate_def a2 accessAllocate[of c' mem''']
      by (simp add: \<open>\<forall>locations. accessStore locations c' = accessStore locations mem'''\<close>)

    have limitsOld:" ((\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None) \<and>
     (\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
      using typeSafeDecl_hyps(1) unfolding TypeSafe_def lessThanTopLocs_def using 22(7) by auto

    have limits:"((\<forall>tloc loc. Toploc mem''' \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc mem''' = None) \<and>
                    (\<forall>loc y. accessStore loc mem''' = Some y \<longrightarrow> (\<exists>tloc<Toploc mem'''. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))))"
      using typeSafeDecl_hyps(3) 22(7) unfolding TypeSafe_def lessThanTopLocs_def by simp

    have old:"ncpElementsNoSubPref (Memory st) mem''' \<and> ncpOMemInDMem (Memory st) mem''' \<and> ncpNewSelfPoint (Memory st) mem'''" using 22 notCP typeSafeDecl_hyps(5) by blast
    then have sameLocs:"(\<forall>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
        accessStore loc (Memory st) = accessStore loc mem''')" unfolding ncpOMemInDMem_def by blast
    have selfPointMem':" (\<forall>i loc loc2. i < Toploc
        mem''' \<and> Toploc (Memory st) \<le> i \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> accessStore loc mem''' =
        Some (MPointer loc2) \<longrightarrow> loc = loc2)"
      using old unfolding ncpNewSelfPoint_def by blast
    then have old:"\<forall>i l1 t1 l2 t2 loc i2 loc2.
     i < Toploc (Memory st) \<and> Toploc (Memory st) \<le> i2 \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> LSubPrefL2
         loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> MCon (MTArray l1 t1) (Memory st) loc \<longrightarrow>
     \<not> TypedMemSubPrefPtrs mem''' l2 t2 loc2 loc \<and> \<not> TypedMemSubPrefPtrs mem''' l1 t1 loc loc2" using old unfolding ncpElementsNoSubPref_def by blast

    show "ncpElementsNoSubPref (Memory st) m' " unfolding ncpElementsNoSubPref_def
    proof intros
      fix i l1 t1 l2 t2 loc i2 loc2
      assume c10:"i < Toploc (Memory st) \<and> Toploc (Memory st) \<le> i2 \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and>
          LSubPrefL2 loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> MCon (MTArray l1 t1) (Memory st) loc"
      then have "accessStore loc (Memory st) = accessStore loc mem'''"using sameLocs by auto
      have MConnew:"MCon (MTArray l1 t1) (Memory st) loc" using c10 by blast
      have locdef:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using c10 by simp

      then have inotl:"i < Toploc mem'''" using b99 22(7) typeSafeDecl_hyps(5) notCP b98 c10 by simp
      then have inotlString:"(ShowL\<^sub>n\<^sub>a\<^sub>t i) \<noteq> l" using a1 22(7)
        by (metis Read_Show_nat'_id linorder_neq_iff)
      have typeMemOld:"\<not> TypedMemSubPrefPtrs mem''' l2 t2 loc2 loc \<and> \<not> TypedMemSubPrefPtrs mem''' l1 t1 loc loc2" using old c10 MConnew by auto

      have "\<not> LSubPrefL2 loc l" using c10 inotlString
        by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general a1 hash_inequality hash_suffixes_associative)
      then have conc1:" \<not> TypedMemSubPrefPtrs m' l1 t1 loc loc2" using b105 b110 a110 MConnew a120 typeMemOld
        using inv_cpm2mTPrefOld_imps_TPref by blast
      then have hashlimit:"\<forall>f. hash loc2 f \<noteq> loc" using c10
        by (metis (no_types, opaque_lifting) MCon_imps_Some LSubPrefL2_def Not_Sub_More_Specific limitsOld not_Some_eq)

      have conc2:"\<not> TypedMemSubPrefPtrs m' l2 t2 loc2 loc"
      proof(cases " i2 < Toploc mem'''")
        case True
        then have f2:" (\<forall>p loc2. i2 < Toploc
            mem''' \<and> Toploc (Memory st) \<le> i2 \<and> LSubPrefL2 loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> accessStore loc2 mem''' = Some (MPointer p) \<longrightarrow> loc2 = p)"
          using selfPointMem' c10 by blast
        have "(ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using c10
          by (metis hashesIntSame leD)

        then have loc2NotSub:"\<not>LSubPrefL2 loc2 l" using a1 True
          by (metis LSubPrefL2_def MemLSubPrefL2_specific_imps_general c10 hash_inequality hash_suffixes_associative hashesIntSame nat_neq_iff)
        show ?thesis
        proof
          assume asm:"TypedMemSubPrefPtrs m' l2 t2 loc2 loc"
          then show False using hashlimit f2 c10 b110 loc2NotSub
          proof(induction t2 arbitrary:loc2 l2)
            case (MTArray x1 t2)
            then obtain i''' l''' where i'''def:"(i'''<l2 \<and> accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t
                i''')) m' = Some (MPointer l''') \<and> (l''' = loc \<or> TypedMemSubPrefPtrs m' x1 t2 l''' loc))"
              using TypedMemSubPrefPtrs.simps(2)[of m' l2 x1 t2 loc2 loc] by blast
            then have "LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) (ShowL\<^sub>n\<^sub>a\<^sub>t i2)" using MTArray(5)
              by (metis LSubPrefL2_def Not_Sub_More_Specific)
            moreover have "\<not> LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) l" using MTArray(7)
              using MemLSubPrefL2_specific_imps_general a1 by blast

            ultimately have l'''Exp:"l''' = (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i'''))" using MTArray(4,6) i'''def
              by (metis True a110 c10)

            then show ?case
            proof(cases "l''' = loc")
              case True
              then show ?thesis using MTArray(3) l'''Exp by simp
            next
              case False
              then have "TypedMemSubPrefPtrs m' x1 t2 l''' loc" using i'''def by simp
              then show ?thesis using MTArray.IH[of x1 l'''] l'''Exp MTArray(3)
                using \<open>LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t
                    i''')) (ShowL\<^sub>n\<^sub>a\<^sub>t i2)\<close> \<open>\<not> LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) l\<close> b110 c10 f2 hash_suffixes_associative by force
            qed
          next
            case (MTValue x)
            then have "(\<exists>i<l2. hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = loc)" using TypedMemSubPrefPtrs.simps(1)[of m' l2 x loc2 loc] by auto
            then show ?case using MTValue by simp
          qed
        qed
      next
        case False
        then show ?thesis
        proof(cases "i2 = Toploc mem'''")
          case True
          then have g1:"(ShowL\<^sub>n\<^sub>a\<^sub>t i2) = l" using a1 by blast
          show ?thesis
          proof
            assume asm:" TypedMemSubPrefPtrs m' l2 t2 loc2 loc"
            then show False using hashlimit c10 b105 selfPoint sameaccess
            proof(induction t2 arbitrary:loc2 l2)
              case (MTArray x1 t2)
              then obtain iIn lIn where idef: " (iIn<l2 \<and> accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) m' = Some
                  (MPointer lIn) \<and> (lIn = loc \<or> TypedMemSubPrefPtrs m' x1 t2 lIn loc))"
                using TypedMemSubPrefPtrs.simps(2)[of m' l2 x1 t2 loc2 loc] by blast
              have g2:"\<forall>i. (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> l" using g1 MTArray(4) LSubPrefL2_def
                by (metis hash_inequality hash_suffixes_associative)
              show ?case
              proof(cases "TypedStoSubpref (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) l (STArray x' t')")
                case True
                then have g4:"lIn = (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn))" using MTArray idef
                  using a110 by blast
                then show ?thesis
                proof(cases "lIn = loc")
                  case True
                  then show ?thesis using g4 MTArray by blast
                next
                  case False
                  have tp: "TypedMemSubPrefPtrs m' x1 t2 lIn loc" using False idef by simp
                  have sub: "LSubPrefL2 lIn l" using MTArray.prems(3) g1 g4 LSubPrefL2_hash_mono by metis
                  have hl: "\<forall>f. hash lIn f \<noteq> loc"
                    using sub \<open>\<not> LSubPrefL2 loc l\<close> LSubPrefL2_hash LSubPrefL2_trans by metis
                  have c: "i < Toploc (Memory st) \<and> Toploc (Memory st) \<le> i2 \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and>
                      LSubPrefL2 lIn (ShowL\<^sub>n\<^sub>a\<^sub>t i2) \<and> MCon (MTArray l1 t1) (Memory st) loc"
                    using MTArray.prems(3) sub g1 by simp
                  show ?thesis using MTArray.IH[of x1 lIn] tp hl c MTArray.prems(4,5,6) by blast
                qed
              next
                case False
                then have " accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) mem''' = accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) mm'" using g2 MTArray by blast
                moreover have "LSubPrefL2 (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) l" using g1 MTArray LSubPrefL2_def
                  by (metis hash_suffixes_associative)
                ultimately have "accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) mm' = None" using MTArray by metis
                then show ?thesis using idef
                  by (simp add: a110)
              qed
            next
              case (MTValue x')
              then show ?case by auto
            qed
          qed
        next
          case f4:False
          then have "i2> Toploc mem'''" using False by auto
          then have loc2NotSub:"\<not>LSubPrefL2 loc2 l" using a1 c10
            by (metis LSubPrefL2_def f4 hash_suffixes_associative hashesInts)
          show ?thesis
          proof
            assume asm:"TypedMemSubPrefPtrs m' l2 t2 loc2 loc"
            show False
            proof(cases t2)
              case (MTArray x11 x12)
              then have h1:"(\<exists>i<l2. \<exists>l. accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = loc \<or> TypedMemSubPrefPtrs m' x11 x12 l loc))"
                using TypedMemSubPrefPtrs.simps(2)[of m' l2 x11 x12 loc2 loc] asm by blast
              then obtain i''' l''' where i'''def:"i'''<l2 \<and> accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t
                  i''')) m' = Some (MPointer l''') \<and> (l''' = loc \<or> TypedMemSubPrefPtrs m' x11 x12 l''' loc)" by blast
              then have " accessStore (hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) m' = None" using loc2NotSub
                by (metis False LSubPrefL2_def MemLSubPrefL2_specific_imps_general a1 a110 b110 c10 Not_Sub_More_Specific leI locationscd')
              then show ?thesis using i'''def by simp
            next
              case (MTValue x2)
              then have "(\<exists>i<l2. hash loc2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) = loc)"
                using asm TypedMemSubPrefPtrs.simps(1)[of m' l2 x2 loc2 loc] by blast
              then show ?thesis using hashlimit by simp
            qed
          qed
        qed
      qed
      then show "\<not> TypedMemSubPrefPtrs m' l2 t2 loc2 loc" using inv_cpm2mTPrefOld_imps_TPref conc2 by blast
      show " \<not> TypedMemSubPrefPtrs m' l1 t1 loc loc2" using conc1 by simp
    qed
  next
    have b99:"Toploc c' = Toploc m'" using a3 a4 cps2m_def[of p l x' t' s c'] cps2mTopLocSame[of p l t' s c' x' mm'] b2 by simp
    show "denvalueTypeCorrectness e k' m'" unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t2 l ptr_loc
      assume *:" (type.Memory t2, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"

      show "case t2 of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)

       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
      proof(cases "(type.Memory t2, Stackloc l) |\<in>| fmran(Denvalue ev')")
        case True
        moreover have sameACC:"accessStore l k' = accessStore l sck'"
          using a40 * unfolding astack.simps push_def updateStore_def accessStore_def allocate_def
          by (metis (no_types, lifting) accessStore_def typeSafeDecl_hyps(3,4) calculation decl_stack_change
              fmlookup_ran_iff snd_eqD TypeSafe_def stackLocs_imp_NotDen)
        then have old:"(case t2 of
                         MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some arr)
                         | MTValue val \<Rightarrow> accessTypeStore ptr_loc mem' = Some (MTValue val))"
          using typeSafeDecl_hyps(1) 22(7) * True TypeSafe_def typeSafeDecl_hyps(3) denvalueTypeCorrectness_def by fastforce
        have mcOld:"MCon t2 mem' ptr_loc" using * sameACC True typeSafeDecl_hyps(1) 22(7)
          unfolding TypeSafe_def typeCompat_def
          by (metis typeSafeDecl_hyps(3) sameMemTSafe)

        have lims:"\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) ptr_loc"
          using typeSafeAllPtrsNotTop[OF typeSafeDecl_hyps(3) True] * 22(7) sameACC b99 aloc unfolding allocate_def
          using LSubPrefL2_def MemLSubPrefTransitive by force
        then show ?thesis
        proof(cases t2)
          case (MTArray x11 x12)
          have nonLocChanged2_Typed_cond:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessTypeStore loc m' = accessTypeStore loc mem'"
            using nonLocChanged2_Typed by simp
          have nonLochanged:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore loc m' = accessStore loc mem'"
            using b27 a1 a110 22(7) by auto
          have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some x12) "
            using old MTArray by simp

          show ?thesis
            using MTArray old' nonLocChanged2_Typed_cond lims
              22(7) nonLochanged MemLSubPrefL2_specific_imps_general mtypes.simps(5) old

            by (metis (no_types, lifting) ext)
        next
          case (MTValue x2)
          then show ?thesis using nonLocChanged2_Typed old 22(7) lims by simp
        qed
      next
        case False
        then have "Denvalue e $$ ip = Some (type.Memory t2, Stackloc l)"
          using a40 * a4 typeSafeDecl_hyps(4) decl_env_not_i fmlookup_ran_iff by fast
        then have t2Def:"l = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) \<and> t2 = (MTArray x t)" using a40 by simp
        then have acc:"accessStore l k' = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')))"
          using a40 a20 a1 * 22(7) unfolding push_def allocate_def updateStore_def accessStore_def by auto
        then have ptrEQ:"ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" using * by auto
        have conc1:"(\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some t)"
          using a3 unfolding cps2m_def using cps2m_TypeCompChangeIndexs[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'''))" t' s c' x' mm' t]
            cps2mTypeComp 22(7) "*" a110 a1 acc b4 by auto
        have "accessStore ptr_loc m' = accessStore ptr_loc mem'"
          using 22(7) ptrEQ t2Def "*" a1 a110 acc b1 b27 by simp
        moreover have "accessStore ptr_loc mem' = None"
          using 22(7) ptrEQ a1 typeSafeDecl_hyps(3) unfolding TypeSafe_def lessThanTopLocs_def
          by (meson LSubPrefL2_def order_eq_refl)
        ultimately have " (\<forall>v. accessStore ptr_loc m' = Some (MPointer v) \<longrightarrow> accessTypeStore ptr_loc m' = Some (MTArray x t))"
          by simp
        then show ?thesis using t2Def conc1 by simp
      qed
    qed
  next
    show "subPrefixStructuralConsistency m'" unfolding subPrefixStructuralConsistency_def
    proof(intros)
      fix locs tp
      assume in1:"accessTypeStore locs m' = Some tp"

      have "\<forall>locations. accessStore locations c' = accessStore locations mem'" using a2 22(7) accessAllocate[of c' mem'] by auto

      have nonLocChanged_Typed:"\<forall>locs. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t')
                            \<longrightarrow>accessTypeStore locs mem' = accessTypeStore locs m'"
        using a3 a1 unfolding cps2m_def using aloc cps2mSingleChange_typedPref_both[of p l t' s c' x mm'] allocateTypeSameAccess a2 a110
        by (simp add: \<open>\<forall>locs. accessTypeStore locs c' = accessTypeStore locs mem'\<close> b4)
      then have nonLocChanged_Typed:"\<forall>locs. locs \<noteq> l \<and> \<not> TypedMemSubPref locs l (MTArray x t)
                            \<longrightarrow>accessTypeStore locs mem' = accessTypeStore locs m'" using cps2mTypeComp
        using b4 compatible_TypedStoSubpref_imps_TypedMemSubPref_neg by presburger

      have "MCon (MTArray x t) mm' l"
        using mcTop1 by blast
      then have mcTop:"MCon (MTArray x t) m' l" using a110 by blast

      have prefPtrs_imps_Pref:"\<forall>x3. TypedMemSubPrefPtrs mm' x t l x3 \<longrightarrow> TypedMemSubPref x3 l (MTArray x t)"
        using selfPoint_imps_TypedMemSubPref[OF ] selfPoint compatible_TypedStoSubpref_imps_TypedMemSubPref_neg cps2mTypeComp a110 by blast

      show "case accessStore locs m' of None \<Rightarrow> False | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m' locs \<and> tp = MTValue val \<and> accessTypeStore locs m' = Some tp
       | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp m' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
                            "
      proof(cases "accessTypeStore locs mem' = Some tp")
        case True
        then have accL:"\<exists>v. accessStore locs mem' = Some v"
          using typeSafeDecl_hyps(3) 22(7) unfolding TypeSafe_def SomeValSomeTyp_def by simp
        have notSub:"\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))"
        proof
          assume c:"LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))"
          then have "accessStore locs mem' = None"
            using 22(7) nless_le a1 b105 by simp
          then show False using accL by auto
        qed
        then have sameACC:" accessStore locs m' = accessStore locs mem'" using b27 22(7) a1 by simp
        then consider (ptr) p where "accessStore locs m' = Some (MPointer p)"
          | (val) val2 where "accessStore locs m' = Some (MValue val2)"
          using typeSafeDecl_hyps(1) 22(7) True unfolding TypeSafe_def subPrefixStructuralConsistency_def
          by (metis memoryvalue.exhaust accL)
        then show ?thesis
        proof(cases)
          case ptr
          then obtain len arr where
            old:"MCon tp mem' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some arr)
                   "
            using typeSafeDecl_hyps(3) 22(7) True sameACC unfolding TypeSafe_def subPrefixStructuralConsistency_def by fastforce
          then have lim2:"\<forall>len arr loc. tp = MTArray len arr \<and> TypedMemSubPrefPtrs mem' len arr p loc
                        \<longrightarrow> \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) loc"
            using AccessedMemPtrsCantTop[of "mem'" tp p] typeSafeDecl_hyps(3) 22(7) unfolding TypeSafe_def by blast
          have lim:" \<not> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) p"
            using AllPtrsNotTop_MCon notSub ptr using typeSafeDecl_hyps(3) 22(7) old unfolding TypeSafe_def by blast
          have accTLoc:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<or> loc =
              (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore loc m' = accessStore loc mem'"
            using 22(7) a1 a110 b27 by simp
          have "MCon tp m' p" using MCon_memory_transfer[OF _ lim lim2 accTLoc] old by blast
          moreover have "\<forall>i<len. \<not> LSubPrefL2 (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" using lim
            using MemLSubPrefL2_specific_imps_general by blast
          ultimately have " MCon tp m' p \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)"
            using nonLocChanged2_Typed old 22(7) by simp
          then show ?thesis using ptr by auto
        next
          case val
          then have old:"\<exists>val. MCon tp mem' locs \<and> tp = MTValue val \<and> accessTypeStore locs mem' = Some tp"
            using typeSafeDecl_hyps(3) 22(7) True sameACC unfolding TypeSafe_def subPrefixStructuralConsistency_def by fastforce
          then have "\<exists>val. MCon tp m' locs \<and> tp = MTValue val \<and> accessTypeStore locs m' = Some tp"
            using nonLocChanged2_Typed MCon.simps val notSub 22(7) sameACC by fastforce
          then show ?thesis using val by auto
        qed
      next
        case False
        have "locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))"
          using False in1 nonLocChanged2_Typed by fastforce
        then have sub:"TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t)"
          using nonLocChanged_Typed a1 22(7) in1 False by auto

        then have "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t)"
          using selfPoint_imps_TypedMemSubPref by simp
        then obtain st where stD:"(CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) locs \<and>
           (case st of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
            | MTValue pval \<Rightarrow> accessTypeStore locs m' = Some (MTValue pval)))" using mtp a1
          using b4 by blast
        then have cmp:"CompMemType m' x t st (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) locs " by blast

        have mcLocs:"MCon st m' locs" using cmp mcTop CompTypeRemainsMCon a1 22(7) by blast

        show ?thesis
        proof(cases st)
          case (MTArray x11 x12)
          have subs:"t = MTArray x11 x12 \<and> (\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs)) \<or>
                       (\<exists>midP subL subA i. CompMemType m' x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) midP
                       \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
            using CompMemType_imps_Mid[of m' x t x11 x12 "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem'))" locs] cmp MTArray by simp

          then have acc:"accessStore locs m' = Some (MPointer locs)"
            using selfPoint2 mcLocs sub MTArray MCon_imps_TypedMemSubPref_Some[OF _ _ selfPoint2, of locs] mcTop a1 a110 22(7)
            by (metis False MCon.simps(2) \<open>\<forall>locs. accessTypeStore locs c' = accessTypeStore locs mem'\<close> b27T in1 nonLocChanged_Typed option.distinct(1))

          moreover have "\<exists>len arr. MCon tp m' locs \<and> tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
                              \<and> (\<forall>v. accessStore locs m' = Some (MPointer v) \<longrightarrow> accessTypeStore locs m' = Some (MTArray len arr))"
            using in1
          proof(cases "(\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> t = MTArray x11 x12)")
            case True
            then obtain i where idef:"i<x \<and> accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs)
                                    \<and> t = MTArray x11 x12"
              by auto
            then have "TypedMemSubPref (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (MTArray x t) " by auto
            then have locsD:"locs = (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint2 idef a1 a110 22(7) by blast

            have "\<forall>i<x. accessTypeStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm' = Some t"
              using a3 unfolding cps2m_def
              using a110 allocateTypeSameAccess cps2m_TypeCompChangeIndexs[of p l t' s c' x mm' t] cps2mTypeComp b4 by blast
            then have "\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MTArray x11 x12)"
              using idef a1 22(7) a110 by blast
            then have "tp = MTArray x11 x12" using in1 locsD idef by simp
            moreover have "(\<forall>i<x11. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some x12)" using stD MTArray by simp
            ultimately show ?thesis using mcLocs MTArray in1 by blast
          next
            case False
            then obtain midP i subL subA where mid:"(CompMemType m' x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) midP
                   \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
              using subs by blast
            then have locD:"locs = (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint2 a110 a1 22(7)
              using CompMemType_imps_in_GetAllMemoryLocations_ptr mcTop memSet_selfPoint by blast
            then obtain st2 where st2D:"(CompMemType m' x t st2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) midP \<and>
             (case st2 of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some parent_arr
              | MTValue pval \<Rightarrow> accessTypeStore midP m' = Some (MTValue pval)))" using mid mtp a1 a110 22(7)
              using CompMemTypeSameLocsSameType CompMemType_imps_TypedMemSubPrefPtrs prefPtrs_imps_Pref b4 by blast
            then have "st2 = (MTArray subL subA)" using mid CompMemTypeSameLocsSameType mcTop a1 22(7) by blast
            then have " \<forall>i<subL. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some subA" using st2D by simp
            then have "MTArray x11 x12 = tp" using in1 locD mid by simp
            then show ?thesis using mcLocs MTArray stD in1 by fastforce
          qed
          ultimately show ?thesis by auto
        next
          case (MTValue x2)
          then obtain v where vDef:"accessStore locs m' = Some (MValue v)"
            using mcLocs MCon.simps(1)[of x2 m' locs] by (auto split:option.splits memoryvalue.splits)
          moreover have "accessTypeStore locs m' = Some (MTValue x2)" using stD MTValue by auto
          moreover have "tp = MTValue x2" using calculation in1 by simp
          moreover have "MCon tp m' locs" using mcLocs calculation MTValue by blast
          ultimately show ?thesis using MTValue by simp
        qed
      qed
    qed
  next

    have old:"SomeValSomeTyp mem'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by blast
    have non:"\<forall>loc. LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem')) \<longrightarrow> accessStore loc mem' = None"
      using 22(7) typeSafeDecl_hyps(3) unfolding TypeSafe_def lessThanTopLocs_def
      by auto

    have somesomeT:"\<forall>destl'. TypedMemSubPref destl' l (MTArray x t) \<longrightarrow> (\<exists>t. accessStore destl' m' = Some t) = (\<exists>tt. accessTypeStore destl' m' = Some tt)"
      using a3 unfolding cps2m_def using cps2m_TypeCompChange_somesome[of p l t' s c' x mm' t] a4 a1 cps2mTypeComp 22(7) by fastforce
    show "SomeValSomeTyp m'" unfolding SomeValSomeTyp_def
    proof intros
      fix locs
      show "(\<exists>t. accessStore locs m' = Some t) = (\<exists>tt. accessTypeStore locs m' = Some tt) "
      proof(cases "TypedMemSubPref locs l (MTArray x t)")
        case True
        then show ?thesis using somesomeT by simp
      next
        case False
        show ?thesis
        proof (cases "locs = l")
          case True
          have cc0:"accessStore locs m' = accessStore locs mem'"
            using b27 a110 True
            by presburger
          have cc1:"accessTypeStore locs m' = accessTypeStore locs mem'"
            using nonLocChanged2_Typed a1 True a110
            using \<open>\<forall>locs. accessTypeStore locs c' = accessTypeStore locs mem'\<close> b27T by presburger
          then show ?thesis using old SomeValSomeTyp_def cc0 by auto
        next
          case locs_neq: False
          have nsub_mem:"\<not> TypedMemSubPref locs l (MTArray x t)"
            using False by simp
          have nsub_sto:"\<not> TypedStoSubpref locs l (STArray x' t')"
          proof
            assume sto:"TypedStoSubpref locs l (STArray x' t')"
            then have "TypedMemSubPref locs l (MTArray x t) \<or> locs = l"
              using cps2mTypeComp compatible_TypedStoSubpref_imps_TypedMemSubPref by blast
            then show False using nsub_mem locs_neq by blast
          qed
          have cc0:"accessStore locs m' = accessStore locs mem'"
            using "22"(7) a1 a110 a3 a2 \<open>\<forall>locations. accessStore locations c' = accessStore locations mem'\<close> locs_neq nsub_sto
            unfolding cps2m_def using cps2mSingleChange_typedPref[of p l t' s c' x' mm'] by simp
          have cc1:"accessTypeStore locs m' = accessTypeStore locs mem'"
            using "22"(7) a1 a110 a3 a2 \<open>\<forall>locations. accessTypeStore locations c' = accessTypeStore locations mem'\<close> locs_neq nsub_sto
            unfolding cps2m_def using cps2mSingleChange_typedPref_both[of p l t' s c' x' mm'] by simp
          then show ?thesis using old SomeValSomeTyp_def cc0 by auto
        qed
      qed
    qed

  next
    assume ncp:"\<not>cp"
    have b99:"Toploc c' = Toploc m'" using a3 a4 cps2m_def[of p l x' t' s c'] cps2mTopLocSame[of p l t' "s" c' x' mm'] b2 by fastforce
    have "Toploc (Memory st) \<le> Toploc mem'''" using typeSafeDecl_hyps(5) 22(7) ncp by simp
    moreover have "Toploc c' > Toploc mem'''" using a2 unfolding allocate_def by simp
    then show " Toploc (Memory st) \<le> Toploc m' " using b99 ncp typeSafeDecl_hyps 22 by simp
  next
    assume notCP:"\<not>cp"
    show "ncpNewSelfPoint (Memory st) m'" unfolding ncpNewSelfPoint_def
    proof intros
      fix i loc loc2
      assume asm:"i < Toploc m' \<and> Toploc (Memory st) \<le> i \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> accessStore loc m' = Some (MPointer loc2)"
      have old:"(\<forall>i loc loc2. i < Toploc
          mem''' \<and> Toploc (Memory st) \<le> i \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> accessStore loc mem''' =
          Some (MPointer loc2) \<longrightarrow> loc = loc2)"
        using typeSafeDecl_hyps(5) notCP 22(7) unfolding ncpNewSelfPoint_def by blast
      have b99:"Toploc c' = Toploc m'" using a3 a4 cps2m_def[of p l x' t' s c'] cps2mTopLocSame[of p l t' "s" c' x' mm'] b2 by fastforce

      have a110:"m' = mm'" using a4 by simp
      then have b100:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs c' = accessStore locs mm'"
        using a3 a1 cps2m_def cps2mSingleChange[of p l t' "s" c' x' mm'] by fastforce
      have b105:"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem''' = None" using locationscd' a2 lNotInC' a1 by auto
      have "\<forall>locations. accessStore locations c' = accessStore locations mem'''" using a2 accessAllocate[of c' mem'''] by auto
      then have b110:"\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem''' = accessStore locs mm'"
        using b100 a2 unfolding allocate_def by simp

      have g1:"Toploc c' = Suc (Toploc mem''')" using a2 unfolding allocate_def by simp
      show "loc = loc2"
      proof(cases "i < Toploc mem'''")
        case True
        then have "\<not> LSubPrefL2 loc l" using a1 LSubPrefL2_def
          by (metis MemLSubPrefL2_specific_imps_general Read_Show_nat'_id asm hash_inequality hash_suffixes_associative less_not_refl)
        then show ?thesis using old asm b110 a1 True a110 by auto
      next
        case False
        then have iIsTop:"i = Toploc mem'''" using asm g1 b99 by simp
        have selfPoint:"\<forall>la l'. la \<noteq> l \<and> TypedStoSubpref la l (STArray x' t') \<and> accessStore la mm' = Some (MPointer l') \<longrightarrow> l' = la"
          using cps2mSelfPointers[of p l t' "s" c' x' mm'] a3 a1 cps2m_def
          by auto

        have sameaccess:"\<forall>locs. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x' t') \<longrightarrow> accessStore locs c' = accessStore locs mm'"
          using cps2mSingleChange_typedPref[of p l t' "s" c' x' mm'] a3 a1 cps2m_def by fastforce
        then have sameaccess:"\<forall>locs. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x' t') \<longrightarrow> accessStore locs mem''' = accessStore locs mm'"
          using b100 a2 allocate_def accessAllocate[of c' mem'''] by simp
        then show ?thesis using asm iIsTop
          by (metis a1 a110 a3 b105 cps2mAccessPrePost cps2m_def hash_inequality lNotInC' not_Some_eq selfPoint)
      qed
    qed
  next
    have b99:"Toploc c' = Toploc m'" using a3 a4 cps2m_def[of p l x' t' "s" c'] cps2mTopLocSame[of p l t' "s" c' x' mm'] b3 by simp
    then show "Toploc mem' \<le> Toploc m' " using aloc 22 unfolding allocate_def by auto
  qed
qed

text \<open>A storage array initialised from a storage pointer: the variable refers to the storage array.\<close>

lemma typeSafeDecl_42:
  assumes "tp = type.Storage (STArray x t)"
    and "Some (v, t'') = Some (KStoptr p, tv0)"
    and "cp = cp0"
    and "cd = cd0"
    and "state.Memory st = mem0"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (cdc', mem'', sck'', ev'')"
    and "Some (c, m', k', e) = (if tv0 = type.Storage (STArray x t) \<and> Denvalue ev'' $$ ip = None then Some (cdc', mem'', astack_dup ip
        (type.Storage (STArray x t)) (KStoptr p) (sck'', ev'')) else None)"
  shows "declPost ev st cp mem' e c m' k'"
proof -
  let ?case = "declPost ev st cp mem' e c m' k'"
  note 42 = assms
  then have a10:"t'' = type.Storage (STArray x t)" using decl.simps(2) by (simp split:if_splits)
  have NoneIp:" Denvalue ev'' $$ ip = None" using 42 by (simp split:if_splits)
  then have a40:"Some (c, m', k', e) = Some (cdc', mem'', astack ip (type.Storage (STArray x t)) (KStoptr p) (sck', ev''))"
    using 42 decl.simps(2) a10 typeSafeDecl_hyps(1) by simp
  then have k'Def:"k' = push (KStoptr p) sck'" by force

  have eDef:"e = updateEnv ip (type.Storage (STArray x t)) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev''"using a40 unfolding astack.simps by blast
  then have eIP:"(Denvalue e) $$ ip = Some ((type.Storage (STArray x t)),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp
  have sameADD:"Address ev' = Address e"
    using typeSafeDecl_hyps(4) decl_env by blast

  have wxDef:"tv0 = type.Storage (STArray x t)" using 42(8) by (simp split:if_splits)

  have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 42(7) by simp
  then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''"
    using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
  then have a140:"\<forall>x y. \<not>((Denvalue ev'') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))"
    using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 42(7) by fastforce
  then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip"
    using a40 lessThanTopLocs_def fmranI by auto

  obtain locO tpO pO where oldAccess:"(
         (type.Storage tpO, locO) |\<in>| fmran (Denvalue ev') \<and>
         (case locO of
          Stackloc stloc \<Rightarrow>
            accessStore stloc sck' = Some (KStoptr pO) \<and> (tpO = (STArray x t) \<and> v = KStoptr pO \<or> extractValueType v \<noteq>
                pO \<and> CompStoType tpO (STArray x t) pO (extractValueType v))
          | Storeloc stloc \<Rightarrow> tpO = (STArray x t) \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tpO (STArray x t) stloc (extractValueType v)))"
    using typeSafeDecl_hyps 42 wxDef by blast

  have compOld: " (\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
        (type.Storage tp1, l1) |\<in>| fmran (Denvalue ev') \<and>
        (type.Storage tp2, l2) |\<in>| fmran (Denvalue ev') \<and>
        (l1 = Stackloc l1' \<and> accessStore l1' sck' = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
        (l2 = Stackloc l2' \<and> accessStore l2' sck' = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
        (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
    using typeSafeDecl_hyps(3) 42 unfolding TypeSafe_def compPointers_def by blast
  then have compOld':"(\<forall>tp1 l1 l1' l2' stl1 stl2.
        (type.Storage tp1, l1) |\<in>| fmran (Denvalue ev') \<and>
        (l1 = Stackloc l1' \<and> accessStore l1' sck' = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
        (locO = Stackloc l2' \<and> accessStore l2' sck' = Some (KStoptr stl2) \<and> stl2 = pO \<or> locO = Storeloc stl2) \<longrightarrow>
        (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tpO stl1 stl2 else if TypedStoSubpref stl1 stl2 tpO then CompStoType tpO tp1 stl2 stl1 else True))"
    using oldAccess by blast
  show ?thesis unfolding TypeSafe_def
  proof(intros)
    show "unique_locations (Denvalue e)" using typeSafeDecl_hyps(3) 42(7) updateEnvUniqueLocs a40 by fastforce
  next
    have b2: "compPointers sck' (Denvalue ev')" using typeSafeDecl_hyps(3) 42(7) unfolding TypeSafe_def by auto

    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 42(7) by simp
    show "compPointers k' (Denvalue e)" unfolding compPointers_def
    proof intros
      fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
      assume in1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
      then obtain i1 i2 where iDef:" Denvalue e $$ i1 = Some (type.Storage tp1, l1) \<and> Denvalue e$$ i2 = Some (type.Storage tp2, l2)" by blast

      consider (bothStacks) "l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1)
                    \<and> l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2)"
        | (StackLoc1) "l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1) \<and> l2 = Storeloc stl2"
        | (StackLoc2) "l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2) \<and> l1 = Storeloc stl1"
        | (StoreLocs) "l1 = Storeloc stl1 \<and> l2 = Storeloc stl2" using in1 by auto

      then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases)
        case bothStacks
        then show ?thesis
        proof(cases "l1 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
          case True
          then have stl1IsP:"stl1 = p" using in1 k'Def typeSafeDecl_hyps 42 unfolding push_def allocate_def accessStore_def updateStore_def by auto
          have "i1 = ip" using iDef eDef a150 True by blast
          then have tp1IsStArray:"tp1 = STArray x t" using iDef eDef by auto
          then show ?thesis
          proof(cases "l2 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
            case True
            then have stl2IsP:"stl2 = p" using in1 k'Def typeSafeDecl_hyps 42 unfolding push_def allocate_def accessStore_def updateStore_def by auto
            have "i2 = ip" using iDef eDef a150 True by blast
            then have tp2IsStArray:"tp2 = STArray x t" using iDef eDef by auto
            then show ?thesis using stl2IsP tp2IsStArray tp1IsStArray stl1IsP by auto
          next
            case False
            then have acc2:"accessStore l2' k' = accessStore l2' sck'"
              using k'Def bothStacks
              by (metis accessStore_def accessStore_non_changed allocateMapping k'Def push_def snd_conv surj_pair)
            then have i2NotIP:"i2 \<noteq> ip" using eDef iDef False by auto
            then have tp2InOld:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')" using eDef
              using fmranI iDef by fastforce
            have sameAcc2:" accessStore l2' sck' = Some (KStoptr stl2)" using acc2 in1 bothStacks by auto
            then show ?thesis
            proof(cases locO)
              case (Stackloc x1)
              then have acc:"accessStore x1 sck' = Some (KStoptr pO)" using oldAccess by simp
              then have cc:"(tpO = STArray x t \<and> v = KStoptr pO \<or> extractValueType v \<noteq> pO \<and> CompStoType tpO (STArray x t) pO (extractValueType v))"
                using compOld oldAccess using 42(7) Stackloc by simp
              have comps:"(if TypedStoSubpref pO stl2 tp2 then CompStoType tp2 tpO stl2 pO else
                            if TypedStoSubpref stl2 pO tpO then CompStoType tpO tp2 pO stl2 else True)"
                using compOld' sameAcc2 bothStacks tp2InOld Stackloc 42(7) acc by blast
              then show ?thesis
              proof(cases "v = KStoptr pO")
                case True
                then have "tpO = STArray x t" using cc True by simp
                then have sames:"stl1 = pO \<and> tp1 = tpO" using tp1IsStArray True 42 stl1IsP in1 by blast

                then show ?thesis using compPointers_if_sym[OF comps] comps by simp
              next
                case False
                then have comps2:"CompStoType tpO (STArray x t) pO stl1" using stl1IsP cc 42 by simp

                then show ?thesis using compPointers_if_child[OF comps comps2]
                  compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
              qed
            next
              case (Storeloc x2)
              then have cc:"(tpO = STArray x t \<and> v = KStoptr x2 \<or> extractValueType v \<noteq> x2 \<and> CompStoType tpO (STArray x t) x2 (extractValueType v))"
                using compOld oldAccess using 42(7) by simp
              have comps:"(if TypedStoSubpref x2 stl2 tp2 then CompStoType tp2 tpO stl2 x2 else
                            if TypedStoSubpref stl2 x2 tpO then CompStoType tpO tp2 x2 stl2 else True)"
                using compOld' sameAcc2 bothStacks tp2InOld Storeloc 42(7) by blast
              then show ?thesis
              proof(cases "v = KStoptr x2")
                case True
                then have "tpO = STArray x t" using cc True by simp
                then have sames:"stl1 = x2\<and> tp1 = tpO" using tp1IsStArray True 42 stl1IsP in1 by blast

                then show ?thesis using compPointers_if_sym[OF comps] comps by simp
              next
                case False
                then have comps2:"CompStoType tpO (STArray x t) x2 stl1" using stl1IsP cc 42 by simp
                then show ?thesis using compPointers_if_child[OF comps comps2]
                  compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
              qed
            qed
          qed
        next
          case False
          then have acc1:"accessStore l1' k' = accessStore l1' sck'"
            using k'Def bothStacks
            by (metis accessStore_def accessStore_non_changed allocateMapping k'Def push_def snd_conv surj_pair)

          then have i1NotIp:"i1 \<noteq> ip" using False eDef iDef by auto
          then have In''1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev'')" using eDef
            using fmranI iDef by fastforce
          then show ?thesis
          proof(cases "l2 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
            case True
            then have stl2IsP:"stl2 = p" using in1 k'Def typeSafeDecl_hyps 42 unfolding push_def allocate_def accessStore_def updateStore_def by auto
            have "i2 = ip" using iDef eDef a150 True by blast
            then have tp2IsStArray:"tp2 = STArray x t" using iDef eDef by auto
            have tp1InOld:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev')" using In''1 42(7) by blast
            then show ?thesis
            proof(cases locO)
              case (Stackloc x1)
              then have acc:"accessStore x1 sck' = Some (KStoptr pO)" using oldAccess by simp
              then have cc:"(tpO = STArray x t \<and> v = KStoptr pO \<or> extractValueType v \<noteq> pO \<and> CompStoType tpO (STArray x t) pO (extractValueType v))"
                using compOld oldAccess using 42(7) Stackloc by simp
              have comps:"(if TypedStoSubpref pO stl1 tp1 then CompStoType tp1 tpO stl1 pO else
                            if TypedStoSubpref stl1 pO tpO then CompStoType tpO tp1 pO stl1 else True)"
                using compOld' acc1 in1 bothStacks tp1InOld Stackloc 42(7) acc by metis
              then show ?thesis
              proof(cases "v = KStoptr pO")
                case True
                then have "tpO = STArray x t" using cc True by simp
                then have sames:"stl2 = pO \<and> tp2 = tpO" using tp2IsStArray True 42 stl2IsP in1 by blast

                then show ?thesis using compPointers_if_sym[OF comps] comps by simp

              next
                case False
                then have comps2:"CompStoType tpO (STArray x t) pO stl2" using stl2IsP cc 42 by simp

                then show ?thesis using compPointers_if_child[OF comps comps2]
                  compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp2IsStArray by (simp only:)
              qed
            next
              case (Storeloc x2)
              then have cc:"(tpO = STArray x t \<and> v = KStoptr x2 \<or> extractValueType v \<noteq> x2 \<and> CompStoType tpO (STArray x t) x2 (extractValueType v))"
                using compOld oldAccess using 42(7) by simp
              have comps:"(if TypedStoSubpref x2 stl1 tp1 then CompStoType tp1 tpO stl1 x2 else
                            if TypedStoSubpref stl1 x2 tpO then CompStoType tpO tp1 x2 stl1 else True)"
                using compOld' acc1 in1 bothStacks tp1InOld Storeloc 42(7) by metis
              then show ?thesis
              proof(cases "v = KStoptr x2")
                case True
                then have "tpO = STArray x t" using cc True by simp
                then have sames:"stl2 = x2\<and> tp2 = tpO" using tp2IsStArray True 42 stl2IsP in1 by blast
                then show ?thesis using compPointers_if_sym[OF comps] comps by simp
              next
                case False
                then have comps2:"CompStoType tpO (STArray x t) x2 stl2" using stl2IsP cc 42 by simp

                then show ?thesis using compPointers_if_child[OF comps comps2]
                  compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp2IsStArray by (simp only:)
              qed
            qed
          next
            case f2:False
            then have acc2:"accessStore l2' k' = accessStore l2' sck'"
              using k'Def bothStacks
              by (metis accessStore_def accessStore_non_changed allocateMapping k'Def push_def snd_conv surj_pair)
            then have i2NotIP:"i2 \<noteq> ip" using eDef iDef f2 by auto
            then have In''2:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')" using eDef
              using fmranI iDef by fastforce
            have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev') \<and>
     (type.Storage tp2, l2) |\<in>| fmran (Denvalue ev') \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' sck' = Some (KStoptr stl1)) \<and>
     (l2 = Stackloc l2' \<and> accessStore l2' sck' = Some (KStoptr stl2))" using 42(7) In''2 In''1 bothStacks acc1 acc2 in1 by auto
            then show ?thesis using b2 unfolding compPointers_def by blast
          qed
        qed
      next
        case StackLoc1
        then have "i2 \<noteq> ip" using iDef eDef by auto
        then have In''2:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')" using eDef
          using fmranI iDef by fastforce
        then show ?thesis
        proof(cases "l1 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
          case True
          then have stl1IsP:"stl1 = p" using in1 k'Def typeSafeDecl_hyps 42 unfolding push_def allocate_def accessStore_def updateStore_def by auto
          have "i1 = ip" using iDef eDef a150 True by blast
          then have tp1IsStArray:"tp1 = STArray x t" using iDef eDef by auto
          then show ?thesis
          proof(cases locO)
            case (Stackloc x1)
            then have acc:"accessStore x1 sck' = Some (KStoptr pO)" using oldAccess by simp
            then have cc:"(tpO = STArray x t \<and> v = KStoptr pO \<or> extractValueType v \<noteq> pO \<and> CompStoType tpO (STArray x t) pO (extractValueType v))"
              using compOld oldAccess using 42(7) Stackloc by simp
            have comps:"(if TypedStoSubpref pO stl2 tp2 then CompStoType tp2 tpO stl2 pO else
                            if TypedStoSubpref stl2 pO tpO then CompStoType tpO tp2 pO stl2 else True)"
              using compOld' In''2 Stackloc 42(7) acc StackLoc1 by blast
            then show ?thesis
            proof(cases "v = KStoptr pO")
              case True
              then have "tpO = STArray x t" using cc True by simp
              then have sames:"stl1 = pO \<and> tp1 = tpO" using tp1IsStArray True 42 stl1IsP in1 by blast

              then show ?thesis using compPointers_if_sym[OF comps] comps by simp
            next
              case False
              then have comps2:"CompStoType tpO (STArray x t) pO stl1" using stl1IsP cc 42 by simp
              then show ?thesis using compPointers_if_child[OF comps comps2]
                compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
            qed
          next
            case (Storeloc x2)
            then have cc:"(tpO = STArray x t \<and> v = KStoptr x2 \<or> extractValueType v \<noteq> x2 \<and> CompStoType tpO (STArray x t) x2 (extractValueType v))"
              using compOld oldAccess using 42(7) by simp
            have comps:"(if TypedStoSubpref x2 stl2 tp2 then CompStoType tp2 tpO stl2 x2 else
                            if TypedStoSubpref stl2 x2 tpO then CompStoType tpO tp2 x2 stl2 else True)"
              using compOld' StackLoc1 In''2 Storeloc 42(7) by blast
            then show ?thesis
            proof(cases "v = KStoptr x2")
              case True
              then have "tpO = STArray x t" using cc True by simp
              then have sames:"stl1 = x2\<and> tp1 = tpO" using tp1IsStArray True 42 stl1IsP in1 by blast

              then show ?thesis using compPointers_if_sym[OF comps] comps by simp
            next
              case False
              then have comps2:"CompStoType tpO (STArray x t) x2 stl1" using stl1IsP cc 42 by simp

              then show ?thesis using compPointers_if_child[OF comps comps2]
                compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
            qed
          qed
        next
          case False
          then have "i1 \<noteq> ip" using iDef eDef by auto
          then have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev'')"
            using eDef iDef fmranI by fastforce
          moreover have "accessStore l1' sck' = Some (KStoptr stl1)"
            using StackLoc1 k'Def False unfolding push_def allocate_def accessStore_def updateStore_def by auto
          ultimately show ?thesis using compOld 42(7) StackLoc1 using In''2 by blast
        qed
      next
        case StackLoc2
        then have "i1 \<noteq> ip" using iDef eDef by auto
        then have In''2:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev'')" using eDef
          using fmranI iDef by fastforce
        then show ?thesis
        proof(cases "l2 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
          case True
          then have stl1IsP:"stl2 = p" using in1 k'Def typeSafeDecl_hyps 42 unfolding push_def allocate_def accessStore_def updateStore_def by auto
          have "i2 = ip" using iDef eDef a150 True by blast
          then have tp1IsStArray:"tp2 = STArray x t" using iDef eDef by auto
          then show ?thesis
          proof(cases locO)
            case (Stackloc x1)
            then have acc:"accessStore x1 sck' = Some (KStoptr pO)" using oldAccess by simp
            then have cc:"(tpO = STArray x t \<and> v = KStoptr pO \<or> extractValueType v \<noteq> pO \<and> CompStoType tpO (STArray x t) pO (extractValueType v))"
              using compOld oldAccess using 42(7) Stackloc by simp
            have comps:"(if TypedStoSubpref pO stl1 tp1 then CompStoType tp1 tpO stl1 pO else
                            if TypedStoSubpref stl1 pO tpO then CompStoType tpO tp1 pO stl1 else True)"
              using compOld' In''2 Stackloc 42(7) acc StackLoc2 by blast
            then show ?thesis
            proof(cases "v = KStoptr pO")
              case True

              then have "tpO = STArray x t" using cc True by simp
              then have sames:"stl2 = pO \<and> tp2 = tpO" using tp1IsStArray True 42 stl1IsP in1 by blast

              then show ?thesis using compPointers_if_sym[OF comps] comps by simp
            next
              case False
              then have comps2:"CompStoType tpO (STArray x t) pO stl2" using stl1IsP cc 42 by simp

              then show ?thesis using compPointers_if_child[OF comps comps2]
                compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
            qed
          next
            case (Storeloc x2)
            then have cc:"(tpO = STArray x t \<and> v = KStoptr x2 \<or> extractValueType v \<noteq> x2 \<and> CompStoType tpO (STArray x t) x2 (extractValueType v))"
              using compOld oldAccess using 42(7) by simp
            have comps:"(if TypedStoSubpref x2 stl1 tp1 then CompStoType tp1 tpO stl1 x2 else
                            if TypedStoSubpref stl1 x2 tpO then CompStoType tpO tp1 x2 stl1 else True)"
              using compOld' StackLoc2 In''2 Storeloc 42(7) by blast
            then show ?thesis
            proof(cases "v = KStoptr x2")
              case True

              then have "tpO = STArray x t" using cc True by simp
              then have sames:"stl2 = x2\<and> tp2 = tpO" using tp1IsStArray True 42 stl1IsP in1 by simp

              then show ?thesis using compPointers_if_sym[OF comps] comps by simp
            next
              case False
              then have comps2:"CompStoType tpO (STArray x t) x2 stl2" using stl1IsP cc 42 by simp

              then show ?thesis using compPointers_if_child[OF comps comps2]
                compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
            qed
          qed
        next
          case False
          then have "i2 \<noteq> ip" using iDef eDef by auto
          then have "(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')"
            using eDef iDef fmranI by fastforce
          moreover have "accessStore l2' sck' = Some (KStoptr stl2)"
            using StackLoc2 k'Def False unfolding push_def allocate_def accessStore_def updateStore_def by auto
          ultimately show ?thesis using compOld 42(7) StackLoc2 using In''2 by blast
        qed
      next
        case StoreLocs
        then have "i1 \<noteq> ip" using iDef eDef by auto
        moreover have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev'')" using eDef
          using fmranI iDef calculation by fastforce
        moreover have "i2 \<noteq> ip" using iDef eDef StoreLocs by auto
        moreover have In''2:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')" using eDef calculation
          using fmranI iDef by fastforce
        ultimately show ?thesis using compOld StoreLocs 42(7) by blast
      qed
    qed
  next
    have *:"safeContract (Accounts st) (Storage st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def using 42(7) by auto
    have **:"Address ev' = Address e" using eDef 42(7) by simp
    have ***:"Contract ev' = Contract e" using eDef 42(7) by simp
    show "safeContract (Accounts st) (Storage st) " using * by auto
  next
    show "balanceTypes (Accounts st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "svalueTypes (Svalue e)" using eDef 42(7) typeSafeDecl_hyps(3) TypeSafe_def svalueTypes_def by simp
  next
    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 42(7) by simp
    then show "lessThanTopLocs k'" using stackPushToplocSafe k'Def 42(7) by metis
  next
    have "lessThanTopLocs cdc'" using typeSafeDecl_hyps(3) TypeSafe_def 42(7) by simp
    then show "lessThanTopLocs c" using stackPushToplocSafe 42(7) a40 by simp
  next
    have "lessThanTopLocs mem''" using typeSafeDecl_hyps(3) TypeSafe_def 42(7) by simp
    then show "lessThanTopLocs m'" using 42(7) a40 by simp
  next
    have "addressFormat (Address ev')" using typeSafeDecl_hyps(3) TypeSafe_def 42(7) by simp
    then show "addressFormat(Address e)" using 42(7) a40 by auto
  next
    have "addressFormat (Sender ev')" using typeSafeDecl_hyps(3) TypeSafe_def 42(7) by simp
    then show "addressFormat (Sender e)" using 42(7) a40 by auto
  next
    show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c " unfolding typeCompat_def
    proof intros
      fix tDen lDen
      assume *: "(tDen, lDen) |\<in>| fmran (Denvalue e)"
      then obtain ip'' where a90:"Denvalue e $$ ip'' = Some (tDen, lDen)" using * by auto
      then have a100:"(Storage st (Address ev')) = (Storage st (Address e))" using typeSafeDecl_hyps(3) eDef
        using sameADD by presburger
      have a110:"m' = mem''" and a115:"cdc' = c" using a40 by simp+

      then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''') \<and>
          l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip"
        using eDef lessThanTopLocs_def fmranI by auto
      show "denvalueCon k' m' (Storage st (Address e)) c tDen lDen"
      proof(cases lDen)
        case (Stackloc x1)
        then show ?thesis
        proof (cases "x1 = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')")
          case True
          then have a170: "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KStoptr p)"
            using k'Def by (simp add:push_def allocate_def updateStore_def accessStore_def)

          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using True a170 Stackloc by simp
          next
            case some:(Some a)
            then have a180:"a = (KStoptr p) " using a170 True by simp
            then have "ip'' = ip" using a150 True a90 Stackloc by simp
            then have "tDen = type.Storage (STArray x t)" using a90 eDef by simp
            moreover have "(\<forall>locs tp. SCon tp locs (Storage st (Address ev)) \<longrightarrow> SCon tp locs (Storage st (Address ev')))"
              using typeSafeDecl_hyps(8) 42 wxDef by simp
            moreover have "SCon (STArray x t) p (Storage st (Address e))"
              using typeSafeDecl_hyps(2) 42(2) wxDef calculation sameADD by simp
            ultimately show ?thesis using Stackloc some a180 by simp
          qed
        next
          case False

          then have "ip'' \<noteq> ip" using a160 a90 Stackloc by simp
          then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev')" using eDef Stackloc fmranI a90 False * 42(7) by fastforce
          then obtain y' where a180:"accessStore x1 sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) Stackloc 42(7) by blast
          then have a190:"accessStore x1 k' = accessStore x1 sck'" using k'Def False by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using a180 a190 Stackloc by simp
          next
            case some:(Some a)
            then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
              using a190 some Stackloc a170 * a180 a110 a115 a100 42(7) by (cases a; cases tDen; force+)
          qed
        qed
      next
        case (Storeloc x2)
        then have a170:"ip'' \<noteq> ip" using eDef Storeloc a90 by auto
        then have a180: "(tDen, lDen) |\<in>| fmran (Denvalue ev')" using eDef 42(7) Storeloc fmranI a90 by fastforce
        then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def using Storeloc a100 42(7) by (cases tDen;force)
      qed
    qed
  next
    show "AddressTypes (Accounts st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by simp

  next
    have a110:"m' = mem''" using a40 by simp
    then show "\<And>locs tp. \<not> cp \<Longrightarrow> MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using typeSafeDecl_hyps(5) 42(7) typeSafeDecl_hyps(5) by (simp)
  next
    assume "\<not> cp"
    then show "Toploc (Memory st) \<le> Toploc m'" using typeSafeDecl_hyps(5) 42(7) a40 by blast
  next
    assume notCP:"\<not>cp"
    show "ncpDenvalueLimit e ev k' (Stack st) (Memory st) "
      unfolding ncpDenvalueLimit_def
    proof intros
      fix tp' locs p'' i
      assume a120:" (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue e) \<and> accessStore locs k' = Some (KMemptr
          p'') \<and> i < Toploc (Memory st) \<and> LSubPrefL2 p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)"

      then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''') \<and>
          l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip"
        using eDef lessThanTopLocs_def fmranI by auto
      show " \<exists>tp'' loc2 p'.
          (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
          accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p'' \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p'' \<and>
              tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p''))
          "
      proof -
        obtain ip'' where ip''def:"(Denvalue e) $$ ip'' = Some (type.Memory tp', Stackloc locs)" using a120 by blast
        then have a170:"ip'' \<noteq> ip" using eDef by auto
        then have a180: "(type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev')" using eDef 42(7) fmranI ip''def by fastforce
        have a190:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))" using a160 a170 k'Def
          using a150 ip''def by blast

        then obtain y' where a200:"accessStore locs sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) 42(7) a180 by blast
        then have "accessStore locs k' = accessStore locs sck'" using k'Def a120 a190 unfolding push_def allocate_def updateStore_def accessStore_def by simp
        then show " \<exists>tp'' loc2 p'.
          (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
          accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p'' \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p'' \<and>
              tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p''))"
          using typeSafeDecl_hyps(5) 42(7) a120 a40 eDef k'Def a120 a180 notCP ncpDenvalueLimit_def
          by (metis)
      qed
    qed
  next
    assume notCP:"\<not>cp"
    then show "ncpOMemInDMem (Memory st) m'" using a40 42(7) typeSafeDecl_hyps by simp
  next
    assume notCP:"\<not>cp"
    then show "ncpElementsNoSubPref (Memory st) m'" using a40 typeSafeDecl_hyps 42 by blast
  next
    assume notCP:"\<not>cp"
    then show "ncpNewSelfPoint (Memory st) m'" using a40 typeSafeDecl_hyps 42 by blast
  next
    show "Toploc mem' \<le> Toploc m' " using a40 42 by simp
  next
    show "denvalueTypeCorrectness e k' m'" unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t l ptr_loc
      assume *:" (type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"
      then have "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue ev')"
        using a40 unfolding astack.simps updateEnv.simps using type.distinct(7) typeSafeDecl_hyps(4) decl_env_not_i fmlookup_ran_iff
          option.inject prod.inject
        by fastforce
      moreover have "accessStore l k' = accessStore l sck'"
        using a40 * unfolding astack.simps push_def updateStore_def accessStore_def allocate_def
        by (metis (no_types, lifting) accessStore_def typeSafeDecl_hyps(3,4) calculation decl_stack_change
            fmlookup_ran_iff snd_eqD TypeSafe_def stackLocs_imp_NotDen)
      ultimately show "case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
        using a40 typeSafeDecl_hyps(3) * unfolding TypeSafe_def denvalueTypeCorrectness_def using 42(7) by auto
    qed
  next
    show "subPrefixStructuralConsistency m'"
      using typeSafeDecl_hyps(3) a40 42(7) unfolding TypeSafe_def subPrefixStructuralConsistency_def by auto
  next
    show "SomeValSomeTyp m'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def using a40 42(7) by blast
  qed
qed

text \<open>A storage mapping initialised from a storage pointer: the variable refers to the mapping.\<close>

lemma typeSafeDecl_43:
  assumes "tp = type.Storage (STMap t t')"
    and "Some (v, t'') = Some (KStoptr p, tv0)"
    and "cp = cp0"
    and "cd = cd0"
    and "state.Memory st = mem0"
    and "state.Storage st (Address ev) = sto0"
    and "(cd', mem', sck', ev') = (cdc', mem'', sck'', ev'')"
    and "Some (c, m', k', e) = (if tv0 = type.Storage (STMap t t') \<and> Denvalue ev'' $$ ip = None then Some (cdc', mem'', astack_dup ip
        (type.Storage (STMap t t')) (KStoptr p) (sck'', ev'')) else None)"
  shows "declPost ev st cp mem' e c m' k'"
proof -
  let ?case = "declPost ev st cp mem' e c m' k'"
  note 43 = assms
  then have a10:"t'' = type.Storage (STMap t t')" using decl.simps(2) by (simp split:if_splits)
  have NoneIp:" Denvalue ev'' $$ ip = None" using 43 by (simp split:if_splits)
  then have a40:"Some (c, m', k', e) = Some (cdc', mem'', astack ip (type.Storage (STMap t t')) (KStoptr p) (sck', ev''))"
    using 43 decl.simps(2) a10 typeSafeDecl_hyps(1) by simp
  then have k'Def:"k' = push (KStoptr p) sck'" by force

  have eDef:"e = updateEnv ip (type.Storage (STMap t t')) (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) ev''"using a40 unfolding astack.simps by blast
  then have eIP:"(Denvalue e) $$ ip = Some ((type.Storage (STMap t t')),(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" by simp
  have sameADD:"Address ev' = Address e"
    using typeSafeDecl_hyps(4) decl_env by blast

  have wxDef:"tv0 = type.Storage (STMap t t')" using 43(8) by (simp split:if_splits)

  have a120:"lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 43(7) by simp
  then have a130:"\<forall>v'''. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) sck' \<noteq> Some v'''"
    using lessThanTopLocs_def Read_Show_nat'_id using LSubPrefL2_def by auto
  then have a140:"\<forall>x y. \<not>((Denvalue ev'') $$ x = Some y \<and> (snd y) = (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))"
    using TypeSafe_def typeSafeDecl_hyps(3) typeSafeAllStacklocsExist fmranI 43(7) by fastforce
  then have a150: "\<forall>ip''' t'''. Denvalue e $$ ip''' = Some (t''',(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))) \<longrightarrow> ip''' = ip"
    using a40 lessThanTopLocs_def fmranI by auto

  obtain locO tpO pO where oldAccess:"(
         (type.Storage tpO, locO) |\<in>| fmran (Denvalue ev') \<and>
         (case locO of
          Stackloc stloc \<Rightarrow>
            accessStore stloc sck' = Some (KStoptr pO) \<and> (tpO = (STMap t t') \<and> v = KStoptr pO \<or> extractValueType v \<noteq> pO
                \<and> CompStoType tpO (STMap t t') pO (extractValueType v))
          | Storeloc stloc \<Rightarrow> tpO = (STMap t t') \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tpO (STMap t t') stloc (extractValueType v)))"
    using typeSafeDecl_hyps 43 wxDef by blast

  have compOld: " (\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
        (type.Storage tp1, l1) |\<in>| fmran (Denvalue ev') \<and>
        (type.Storage tp2, l2) |\<in>| fmran (Denvalue ev') \<and>
        (l1 = Stackloc l1' \<and> accessStore l1' sck' = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
        (l2 = Stackloc l2' \<and> accessStore l2' sck' = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
        (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
    using typeSafeDecl_hyps(3) 43 unfolding TypeSafe_def compPointers_def by blast
  then have compOld':"(\<forall>tp1 l1 l1' l2' stl1 stl2.
        (type.Storage tp1, l1) |\<in>| fmran (Denvalue ev') \<and>
        (l1 = Stackloc l1' \<and> accessStore l1' sck' = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
        (locO = Stackloc l2' \<and> accessStore l2' sck' = Some (KStoptr stl2) \<and> stl2 = pO \<or> locO = Storeloc stl2) \<longrightarrow>
        (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tpO stl1 stl2 else if TypedStoSubpref stl1 stl2 tpO then CompStoType tpO tp1 stl2 stl1 else True))"
    using oldAccess by blast
  show ?thesis unfolding TypeSafe_def
  proof(intros)
    show "unique_locations (Denvalue e)" using typeSafeDecl_hyps(3) 43(7) updateEnvUniqueLocs a40 by fastforce
  next
    have b2: "compPointers sck' (Denvalue ev')" using typeSafeDecl_hyps(3) 43(7) unfolding TypeSafe_def by auto

    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 43(7) by simp
    show "compPointers k' (Denvalue e)" unfolding compPointers_def
    proof intros
      fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
      assume in1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
      then obtain i1 i2 where iDef:" Denvalue e $$ i1 = Some (type.Storage tp1, l1) \<and> Denvalue e$$ i2 = Some (type.Storage tp2, l2)" by blast

      consider (bothStacks) "l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1)
                    \<and> l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2)"
        | (StackLoc1) "l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1) \<and> l2 = Storeloc stl2"
        | (StackLoc2) "l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2) \<and> l1 = Storeloc stl1"
        | (StoreLocs) "l1 = Storeloc stl1 \<and> l2 = Storeloc stl2" using in1 by auto

      then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases)
        case bothStacks
        then show ?thesis
        proof(cases "l1 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
          case True
          then have stl1IsP:"stl1 = p" using in1 k'Def typeSafeDecl_hyps 43 unfolding push_def allocate_def accessStore_def updateStore_def by auto
          have "i1 = ip" using iDef eDef a150 True by blast
          then have tp1IsStArray:"tp1 = STMap t t'" using iDef eDef by auto
          then show ?thesis
          proof(cases "l2 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
            case True
            then have stl2IsP:"stl2 = p" using in1 k'Def typeSafeDecl_hyps 43 unfolding push_def allocate_def accessStore_def updateStore_def by auto
            have "i2 = ip" using iDef eDef a150 True by blast
            then have tp2IsStArray:"tp2 = STMap t t'" using iDef eDef by auto
            then show ?thesis using stl2IsP tp2IsStArray tp1IsStArray stl1IsP by auto
          next
            case False
            then have acc2:"accessStore l2' k' = accessStore l2' sck'"
              using k'Def bothStacks
              by (metis accessStore_def accessStore_non_changed allocateMapping k'Def push_def snd_conv surj_pair)
            then have i2NotIP:"i2 \<noteq> ip" using eDef iDef False by auto
            then have tp2InOld:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')" using eDef
              using fmranI iDef by fastforce
            have sameAcc2:" accessStore l2' sck' = Some (KStoptr stl2)" using acc2 in1 bothStacks by auto
            then show ?thesis
            proof(cases locO)
              case (Stackloc x1)
              then have acc:"accessStore x1 sck' = Some (KStoptr pO)" using oldAccess by simp
              then have cc:"(tpO = STMap t t' \<and> v = KStoptr pO \<or> extractValueType v \<noteq> pO \<and> CompStoType tpO (STMap t t') pO (extractValueType v))"
                using compOld oldAccess using 43(7) Stackloc by simp
              have comps:"(if TypedStoSubpref pO stl2 tp2 then CompStoType tp2 tpO stl2 pO else
                            if TypedStoSubpref stl2 pO tpO then CompStoType tpO tp2 pO stl2 else True)"
                using compOld' sameAcc2 bothStacks tp2InOld Stackloc 43(7) acc by blast
              then show ?thesis
              proof(cases "v = KStoptr pO")
                case True

                then have "tpO = STMap t t'" using cc True by simp
                then have sames:"stl1 = pO \<and> tp1 = tpO" using tp1IsStArray True 43 stl1IsP in1 by blast

                then show ?thesis using compPointers_if_sym[OF comps] comps by simp
              next
                case False
                then have comps2:"CompStoType tpO (STMap t t') pO stl1" using stl1IsP cc 43 by simp

                then show ?thesis using compPointers_if_child[OF comps comps2]
                  compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
              qed
            next
              case (Storeloc x2)
              then have cc:"(tpO = STMap t t' \<and> v = KStoptr x2 \<or> extractValueType v \<noteq> x2 \<and> CompStoType tpO (STMap t t') x2 (extractValueType v))"
                using compOld oldAccess using 43(7) by simp
              have comps:"(if TypedStoSubpref x2 stl2 tp2 then CompStoType tp2 tpO stl2 x2 else
                            if TypedStoSubpref stl2 x2 tpO then CompStoType tpO tp2 x2 stl2 else True)"
                using compOld' sameAcc2 bothStacks tp2InOld Storeloc 43(7) by blast
              then show ?thesis
              proof(cases "v = KStoptr x2")
                case True

                then have "tpO = STMap t t'" using cc True by simp
                then have sames:"stl1 = x2\<and> tp1 = tpO" using tp1IsStArray True 43 stl1IsP in1 by blast

                then show ?thesis using compPointers_if_sym[OF comps] comps by simp
              next
                case False
                then have comps2:"CompStoType tpO (STMap t t') x2 stl1" using stl1IsP cc 43 by simp

                then show ?thesis using compPointers_if_child[OF comps comps2]
                  compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
              qed

            qed
          qed
        next
          case False
          then have acc1:"accessStore l1' k' = accessStore l1' sck'"
            using k'Def bothStacks
            by (metis accessStore_def accessStore_non_changed allocateMapping k'Def push_def snd_conv surj_pair)

          then have i1NotIp:"i1 \<noteq> ip" using False eDef iDef by auto
          then have In''1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev'')" using eDef
            using fmranI iDef by fastforce
          then show ?thesis
          proof(cases "l2 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
            case True
            then have stl2IsP:"stl2 = p" using in1 k'Def typeSafeDecl_hyps 43 unfolding push_def allocate_def accessStore_def updateStore_def by auto
            have "i2 = ip" using iDef eDef a150 True by blast
            then have tp2IsStArray:"tp2 = STMap t t'" using iDef eDef by auto
            have tp1InOld:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev')" using In''1 43(7) by blast
            then show ?thesis
            proof(cases locO)
              case (Stackloc x1)
              then have acc:"accessStore x1 sck' = Some (KStoptr pO)" using oldAccess by simp
              then have cc:"(tpO = STMap t t' \<and> v = KStoptr pO \<or> extractValueType v \<noteq> pO \<and> CompStoType tpO (STMap t t') pO (extractValueType v))"
                using compOld oldAccess using 43(7) Stackloc by simp
              have comps:"(if TypedStoSubpref pO stl1 tp1 then CompStoType tp1 tpO stl1 pO else
                            if TypedStoSubpref stl1 pO tpO then CompStoType tpO tp1 pO stl1 else True)"
                using compOld' acc1 in1 bothStacks tp1InOld Stackloc 43(7) acc by metis
              then show ?thesis
              proof(cases "v = KStoptr pO")
                case True

                then have "tpO = STMap t t'" using cc True by simp
                then have sames:"stl2 = pO \<and> tp2 = tpO" using tp2IsStArray True 43 stl2IsP in1 by blast

                then show ?thesis using compPointers_if_sym[OF comps] comps by simp
              next
                case False
                then have comps2:"CompStoType tpO (STMap t t') pO stl2" using stl2IsP cc 43 by simp

                then show ?thesis using compPointers_if_child[OF comps comps2]
                  compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp2IsStArray by (simp only:)
              qed
            next
              case (Storeloc x2)
              then have cc:"(tpO = STMap t t' \<and> v = KStoptr x2 \<or> extractValueType v \<noteq> x2 \<and> CompStoType tpO (STMap t t') x2 (extractValueType v))"
                using compOld oldAccess using 43(7) by simp
              have comps:"(if TypedStoSubpref x2 stl1 tp1 then CompStoType tp1 tpO stl1 x2 else
                            if TypedStoSubpref stl1 x2 tpO then CompStoType tpO tp1 x2 stl1 else True)"
                using compOld' acc1 in1 bothStacks tp1InOld Storeloc 43(7) by metis
              then show ?thesis
              proof(cases "v = KStoptr x2")
                case True
                then have "tpO = STMap t t'" using cc True by simp
                then have sames:"stl2 = x2\<and> tp2 = tpO" using tp2IsStArray True 43 stl2IsP in1 by blast

                then show ?thesis using compPointers_if_sym[OF comps] comps by simp
              next
                case False
                then have comps2:"CompStoType tpO (STMap t t') x2 stl2" using stl2IsP cc 43 by simp

                then show ?thesis using compPointers_if_child[OF comps comps2]
                  compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp2IsStArray by (simp only:)
              qed
            qed
          next
            case f2:False
            then have acc2:"accessStore l2' k' = accessStore l2' sck'"
              using k'Def bothStacks
              by (metis accessStore_def accessStore_non_changed allocateMapping k'Def push_def snd_conv surj_pair)
            then have i2NotIP:"i2 \<noteq> ip" using eDef iDef f2 by auto
            then have In''2:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')" using eDef
              using fmranI iDef by fastforce
            have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev') \<and>
     (type.Storage tp2, l2) |\<in>| fmran (Denvalue ev') \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' sck' = Some (KStoptr stl1)) \<and>
     (l2 = Stackloc l2' \<and> accessStore l2' sck' = Some (KStoptr stl2))" using 43(7) In''2 In''1 bothStacks acc1 acc2 in1 by auto
            then show ?thesis using b2 unfolding compPointers_def by blast
          qed
        qed
      next
        case StackLoc1
        then have "i2 \<noteq> ip" using iDef eDef by auto
        then have In''2:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')" using eDef
          using fmranI iDef by fastforce
        then show ?thesis
        proof(cases "l1 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
          case True
          then have stl1IsP:"stl1 = p" using in1 k'Def typeSafeDecl_hyps 43 unfolding push_def allocate_def accessStore_def updateStore_def by auto
          have "i1 = ip" using iDef eDef a150 True by blast
          then have tp1IsStArray:"tp1 = STMap t t'" using iDef eDef by auto
          then show ?thesis
          proof(cases locO)
            case (Stackloc x1)
            then have acc:"accessStore x1 sck' = Some (KStoptr pO)" using oldAccess by simp
            then have cc:"(tpO = STMap t t' \<and> v = KStoptr pO \<or> extractValueType v \<noteq> pO \<and> CompStoType tpO (STMap t t') pO (extractValueType v))"
              using compOld oldAccess using 43(7) Stackloc by simp
            have comps:"(if TypedStoSubpref pO stl2 tp2 then CompStoType tp2 tpO stl2 pO else
                            if TypedStoSubpref stl2 pO tpO then CompStoType tpO tp2 pO stl2 else True)"
              using compOld' In''2 Stackloc 43(7) acc StackLoc1 by blast
            then show ?thesis
            proof(cases "v = KStoptr pO")
              case True

              then have "tpO = STMap t t'" using cc True by simp
              then have sames:"stl1 = pO \<and> tp1 = tpO" using tp1IsStArray True 43 stl1IsP in1 by blast

              then show ?thesis using compPointers_if_sym[OF comps] comps by simp
            next
              case False
              then have comps2:"CompStoType tpO (STMap t t') pO stl1" using stl1IsP cc 43 by simp
              then show ?thesis using compPointers_if_child[OF comps comps2]
                compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
            qed
          next
            case (Storeloc x2)
            then have cc:"(tpO = STMap t t' \<and> v = KStoptr x2 \<or> extractValueType v \<noteq> x2 \<and> CompStoType tpO (STMap t t') x2 (extractValueType v))"
              using compOld oldAccess using 43(7) by simp
            have comps:"(if TypedStoSubpref x2 stl2 tp2 then CompStoType tp2 tpO stl2 x2 else
                            if TypedStoSubpref stl2 x2 tpO then CompStoType tpO tp2 x2 stl2 else True)"
              using compOld' StackLoc1 In''2 Storeloc 43(7) by blast
            then show ?thesis
            proof(cases "v = KStoptr x2")
              case True
              then have "tpO = STMap t t'" using cc True by simp
              then have sames:"stl1 = x2\<and> tp1 = tpO" using tp1IsStArray True 43 stl1IsP in1 by blast

              then show ?thesis using compPointers_if_sym[OF comps] comps by simp
            next
              case False
              then have comps2:"CompStoType tpO (STMap t t') x2 stl1" using stl1IsP cc 43 by simp
              then show ?thesis using compPointers_if_child[OF comps comps2]
                compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
            qed
          qed
        next
          case False
          then have "i1 \<noteq> ip" using iDef eDef by auto
          then have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev'')"
            using eDef iDef fmranI by fastforce
          moreover have "accessStore l1' sck' = Some (KStoptr stl1)"
            using StackLoc1 k'Def False unfolding push_def allocate_def accessStore_def updateStore_def by auto
          ultimately show ?thesis using compOld 43(7) StackLoc1 using In''2 by blast
        qed
      next
        case StackLoc2
        then have "i1 \<noteq> ip" using iDef eDef by auto
        then have In''2:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev'')" using eDef
          using fmranI iDef by fastforce
        then show ?thesis
        proof(cases "l2 = Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))")
          case True
          then have stl1IsP:"stl2 = p" using in1 k'Def typeSafeDecl_hyps 43 unfolding push_def allocate_def accessStore_def updateStore_def by auto
          have "i2 = ip" using iDef eDef a150 True by blast
          then have tp1IsStArray:"tp2 = STMap t t'" using iDef eDef by auto
          then show ?thesis
          proof(cases locO)
            case (Stackloc x1)
            then have acc:"accessStore x1 sck' = Some (KStoptr pO)" using oldAccess by simp
            then have cc:"(tpO = STMap t t' \<and> v = KStoptr pO \<or> extractValueType v \<noteq> pO \<and> CompStoType tpO (STMap t t') pO (extractValueType v))"
              using compOld oldAccess using 43(7) Stackloc by simp
            have comps:"(if TypedStoSubpref pO stl1 tp1 then CompStoType tp1 tpO stl1 pO else
                            if TypedStoSubpref stl1 pO tpO then CompStoType tpO tp1 pO stl1 else True)"
              using compOld' In''2 Stackloc 43(7) acc StackLoc2 by blast
            then show ?thesis
            proof(cases "v = KStoptr pO")
              case True

              then have "tpO = STMap t t'" using cc True by simp
              then have sames:"stl2 = pO \<and> tp2 = tpO" using tp1IsStArray True 43 stl1IsP in1 by blast

              then show ?thesis using compPointers_if_sym[OF comps] comps by simp
            next
              case False
              then have comps2:"CompStoType tpO (STMap t t') pO stl2" using stl1IsP cc 43 by simp

              then show ?thesis using compPointers_if_child[OF comps comps2]
                compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
            qed
          next
            case (Storeloc x2)
            then have cc:"(tpO = STMap t t' \<and> v = KStoptr x2 \<or> extractValueType v \<noteq> x2 \<and> CompStoType tpO (STMap t t') x2 (extractValueType v))"
              using compOld oldAccess using 43(7) by simp
            have comps:"(if TypedStoSubpref x2 stl1 tp1 then CompStoType tp1 tpO stl1 x2 else
                            if TypedStoSubpref stl1 x2 tpO then CompStoType tpO tp1 x2 stl1 else True)"
              using compOld' StackLoc2 In''2 Storeloc 43(7) by blast
            then show ?thesis
            proof(cases "v = KStoptr x2")
              case True
              then have "tpO = STMap t t'" using cc True by simp
              then have sames:"stl2 = x2\<and> tp2 = tpO" using tp1IsStArray True 43 stl1IsP in1 by simp

              then show ?thesis using compPointers_if_sym[OF comps] comps by simp

            next
              case False
              then have comps2:"CompStoType tpO (STMap t t') x2 stl2" using stl1IsP cc 43 by simp
              then show ?thesis using compPointers_if_child[OF comps comps2]
                compPointers_if_sym[OF compPointers_if_child[OF comps comps2]] tp1IsStArray by (simp only:)
            qed
          qed
        next
          case False
          then have "i2 \<noteq> ip" using iDef eDef by auto
          then have "(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')"
            using eDef iDef fmranI by fastforce
          moreover have "accessStore l2' sck' = Some (KStoptr stl2)"
            using StackLoc2 k'Def False unfolding push_def allocate_def accessStore_def updateStore_def by auto
          ultimately show ?thesis using compOld 43(7) StackLoc2 using In''2 by blast
        qed
      next
        case StoreLocs
        then have "i1 \<noteq> ip" using iDef eDef by auto
        moreover have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev'')" using eDef
          using fmranI iDef calculation by fastforce
        moreover have "i2 \<noteq> ip" using iDef eDef StoreLocs by auto
        moreover have In''2:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue ev'')" using eDef calculation
          using fmranI iDef by fastforce
        ultimately show ?thesis using compOld StoreLocs 43(7) by blast
      qed
    qed
  next
    have *:"safeContract (Accounts st) (Storage st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def using 43(7) by auto
    have **:"Address ev' = Address e" using eDef 43(7) by simp
    have ***:"Contract ev' = Contract e" using eDef 43(7) by simp
    show "safeContract (Accounts st) (Storage st) " using * by auto
  next
    show "balanceTypes (Accounts st)" using typeSafeDecl_hyps(1) TypeSafe_def by simp
  next
    show "svalueTypes (Svalue e)" using eDef 43(7) typeSafeDecl_hyps(3) TypeSafe_def svalueTypes_def by simp
  next
    have "lessThanTopLocs sck'" using typeSafeDecl_hyps(3) TypeSafe_def 43(7) by simp
    then show "lessThanTopLocs k'" using stackPushToplocSafe k'Def 43(7) by metis
  next
    have "lessThanTopLocs cdc'" using typeSafeDecl_hyps(3) TypeSafe_def 43(7) by simp
    then show "lessThanTopLocs c" using stackPushToplocSafe 43(7) a40 by simp
  next
    have "lessThanTopLocs mem''" using typeSafeDecl_hyps(3) TypeSafe_def 43(7) by simp
    then show "lessThanTopLocs m'" using 43(7) a40 by simp
  next
    have "addressFormat (Address ev')" using typeSafeDecl_hyps(3) TypeSafe_def 43(7) by simp
    then show "addressFormat(Address e)" using 43(7) a40 by auto
  next
    have "addressFormat (Sender ev')" using typeSafeDecl_hyps(3) TypeSafe_def 43(7) by simp
    then show "addressFormat (Sender e)" using 43(7) a40 by auto
  next
    show "typeCompat (Denvalue e) k' m' (Storage st (Address e)) c " unfolding typeCompat_def
    proof intros
      fix tDen lDen
      assume *: "(tDen, lDen) |\<in>| fmran (Denvalue e)"
      then obtain ip'' where a90:"Denvalue e $$ ip'' = Some (tDen, lDen)" using * by auto
      then have a100:"(Storage st (Address ev')) = (Storage st (Address e))" using typeSafeDecl_hyps(3) eDef
        using sameADD by presburger
      have a110:"m' = mem''" and a115:"cdc' = c" using a40 by simp+

      then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''') \<and>
          l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip"
        using eDef lessThanTopLocs_def fmranI by auto
      show "denvalueCon k' m' (Storage st (Address e)) c tDen lDen"
      proof(cases lDen)
        case (Stackloc x1)
        then show ?thesis
        proof (cases "x1 = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')")
          case True
          then have a170: "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) k' = Some (KStoptr p)"
            using k'Def by (simp add:push_def allocate_def updateStore_def accessStore_def)

          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using True a170 Stackloc by simp
          next
            case some:(Some a)
            then have a180:"a = (KStoptr p) " using a170 True by simp
            then have "ip'' = ip" using a150 True a90 Stackloc by simp
            then have "tDen = type.Storage (STMap t t')" using a90 eDef by simp
            moreover have "(\<forall>locs tp. SCon tp locs (Storage st (Address ev)) \<longrightarrow> SCon tp locs (Storage st (Address ev')))"
              using typeSafeDecl_hyps(8) 43 wxDef by simp
            moreover have "SCon (STMap t t') p (Storage st (Address e))"
              using typeSafeDecl_hyps(2) 43(2) wxDef calculation sameADD by simp
            ultimately show ?thesis using Stackloc some a180 by simp
          qed
        next
          case False
          then have "ip'' \<noteq> ip" using a160 a90 Stackloc by simp
          then have a170: "(tDen, lDen) |\<in>| fmran (Denvalue ev')" using eDef Stackloc fmranI a90 False * 43(7) by fastforce
          then obtain y' where a180:"accessStore x1 sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) Stackloc 43(7) by blast
          then have a190:"accessStore x1 k' = accessStore x1 sck'" using k'Def False by (simp add:push_def allocate_def updateStore_def accessStore_def)
          then show ?thesis
          proof(cases "accessStore x1 k'")
            case None
            then show ?thesis using a180 a190 Stackloc by simp
          next
            case some:(Some a)
            then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def
              using a190 some Stackloc a170 * a180 a110 a115 a100 43(7) by (cases a; cases tDen; force+)
          qed
        qed
      next
        case (Storeloc x2)
        then have a170:"ip'' \<noteq> ip" using eDef Storeloc a90 by auto
        then have a180: "(tDen, lDen) |\<in>| fmran (Denvalue ev')" using eDef 43(7) Storeloc fmranI a90 by fastforce
        then show ?thesis using typeSafeDecl_hyps(3) unfolding TypeSafe_def typeCompat_def using Storeloc a100 43(7) by (cases tDen;force)
      qed
    qed
  next
    show "AddressTypes (Accounts st)" using typeSafeDecl_hyps(3) unfolding TypeSafe_def by simp
  next

    have a110:"m' = mem''" using a40 by simp
    then show "\<And>locs tp. \<not> cp \<Longrightarrow> MCon tp (Memory st) locs \<Longrightarrow> MCon tp m' locs" using typeSafeDecl_hyps(5) 43(7) typeSafeDecl_hyps(5) by (simp)
  next
    assume "\<not> cp"
    then show "Toploc (Memory st) \<le> Toploc m'" using typeSafeDecl_hyps(5) 43(7) a40 by blast
  next
    assume notCP:"\<not>cp"
    show "ncpDenvalueLimit e ev k' (Stack st) (Memory st) "
      unfolding ncpDenvalueLimit_def
    proof intros
      fix tp' locs p'' i
      assume a120:" (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue e) \<and> accessStore locs k' = Some (KMemptr
          p'') \<and> i < Toploc (Memory st) \<and> LSubPrefL2 p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)"

      then have a160:"\<forall>ip''' t''' l'''. Denvalue e $$ ip''' = Some(t''', l''') \<and>
          l''' \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<longrightarrow> ip''' \<noteq> ip"
        using eDef lessThanTopLocs_def fmranI by auto
      show " \<exists>tp'' loc2 p'.
          (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
          accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p'' \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p'' \<and>
              tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p''))
          "
      proof -
        obtain ip'' where ip''def:"(Denvalue e) $$ ip'' = Some (type.Memory tp', Stackloc locs)" using a120 by blast
        then have a170:"ip'' \<noteq> ip" using eDef by auto
        then have a180: "(type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue ev')" using eDef 43(7) fmranI ip''def by fastforce
        have a190:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))" using a160 a170 k'Def
          using a150 ip''def by blast

        then obtain y' where a200:"accessStore locs sck' = Some y' " using typeSafeAllStacklocsExist typeSafeDecl_hyps(3) 43(7) a180 by blast
        then have "accessStore locs k' = accessStore locs sck'" using k'Def a120 a190 unfolding push_def allocate_def updateStore_def accessStore_def by simp
        then show " \<exists>tp'' loc2 p'.
          (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue ev) \<and>
          accessStore loc2 (Stack st) = Some (KMemptr p') \<and> (p' = p'' \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p'' \<and>
              tp'' = MTArray len arr \<and> CompMemType (Memory st) len arr tp' p' p''))"
          using typeSafeDecl_hyps(5) 43(7) a120 a40 eDef k'Def a120 a180 notCP ncpDenvalueLimit_def
          by (metis)
      qed
    qed
  next
    assume notCP:"\<not>cp"
    then show "ncpOMemInDMem (Memory st) m'" using a40 43(7) typeSafeDecl_hyps by simp
  next
    assume notCP:"\<not>cp"
    then show "ncpElementsNoSubPref (Memory st) m'" using a40 typeSafeDecl_hyps 43 by blast
  next
    assume notCP:"\<not>cp"
    then show "ncpNewSelfPoint (Memory st) m'" using a40 typeSafeDecl_hyps 43 by blast
  next
    show "Toploc mem' \<le> Toploc m' " using a40 43 by simp
  next
    show "denvalueTypeCorrectness e k' m'" unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t l ptr_loc
      assume *:" (type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l k' = Some (KMemptr ptr_loc)"
      then have "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue ev')"
        using a40 unfolding astack.simps updateEnv.simps using type.distinct(7) typeSafeDecl_hyps(4) decl_env_not_i fmlookup_ran_iff
          option.inject prod.inject
        by fastforce
      moreover have "accessStore l k' = accessStore l sck'"
        using a40 * unfolding astack.simps push_def updateStore_def accessStore_def allocate_def
        by (metis (no_types, lifting) accessStore_def typeSafeDecl_hyps(3,4) calculation decl_stack_change
            fmlookup_ran_iff snd_eqD TypeSafe_def stackLocs_imp_NotDen)
      ultimately show "case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc m' = Some (MTValue val)"
        using a40 typeSafeDecl_hyps(3) * unfolding TypeSafe_def denvalueTypeCorrectness_def using 43(7) by auto
    qed
  next
    show "subPrefixStructuralConsistency m'"
      using typeSafeDecl_hyps(3) a40 43(7) unfolding TypeSafe_def subPrefixStructuralConsistency_def by auto
  next
    show "SomeValSomeTyp m'" using typeSafeDecl_hyps(3) unfolding TypeSafe_def using a40 43(7) by blast
  qed
qed


lemma typeSafeDecl:
  shows "declPost ev st cp mem' e c m' k'" using typeSafeDecl_hyps(4)
proof(cases rule:decl.elims)
  case (1 t _ _ _ _ c m k e)
  then show ?thesis using typeSafeDecl_hyps by blast
next
  case (2 t v t' _ _ _ _ cd' mem'' sck'' ev'')
  from 2 show ?thesis by (rule typeSafeDecl_2)
next
  case 3
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 4
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 5
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 6
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 7
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 8
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case (9 x t p _ cd _ _ cd' mem'' sck'' ev'')
  from 9 show ?thesis by (rule typeSafeDecl_9)
next
  case (10 x t p _ _ mem _ cd' mem''' sck'' ev'')
  from 10 show ?thesis by (rule typeSafeDecl_10)
next
  case (11 v _ _ _ _ _ _)
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 12
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 13
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case (14 v _ _ _ _ _ _ _)
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 15
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 16
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case 17
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case (18 x t _ _ _ _ c m k e)
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case (19 x t p _ _ mem _ cd' mem''' sck'' ev'')
  from 19 show ?thesis by (rule typeSafeDecl_19)
next
  case (20 x t p _ _ _ _ cd' mem''' sck'' ev'')
  from 20 show ?thesis by (rule typeSafeDecl_20)
next
  case (21 x t p _ _ cd _ _ cd' mem''' sck'' ev'')
  from 21 show ?thesis by (rule typeSafeDecl_21)
next
  case (22 x t p x' t' _ _ _ s cd' mem''' sck'' ev'')
  from 22 show ?thesis by (rule typeSafeDecl_22)
next
  case (23 v _ _ _ _ _ _)
  then show ?thesis using typeSafeDecl_hyps(1) by simp
next
  case (24 _ v _ _ _ _ _)
  then show ?thesis by simp
next
  case 25
  then show ?thesis by simp
next
  case (26 v _ _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (27 v _ _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (28 _ _ v _ _ _ _ _)
  then show ?thesis by simp
next
  case (29 _ _ v _ _ _ _ _)
  then show ?thesis by simp
next
  case (30 _ _ v _ _ _ _ _)
  then show ?thesis by simp
next
  case 31
  then show ?thesis by simp
next
  case 32
  then show ?thesis by simp
next
  case (33 _ v _ _ _ _)
  then show ?thesis by simp
next
  case 34
  then show ?thesis by simp
next
  case (35 v _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (36 v _ _ _ _ _ _)
  then show ?thesis by simp
next
  case (37 _ _ v _ _ _ _)
  then show ?thesis by simp
next
  case (38 _ _ v _ _ _ _)
  then show ?thesis by simp
next
  case (39 _ _ v _ _ _ _)
  then show ?thesis by simp
next
  case 40
  then show ?thesis by simp
next
  case 41
  then show ?thesis by simp
next
  case (42 x t p _ _ _ _ _ cd' mem'' sck'' ev'')
  from 42 show ?thesis by (rule typeSafeDecl_42)
next
  case (43 t t' p _ _ _ _ _ cd' mem'' sck'' ev'')
  from 43 show ?thesis by (rule typeSafeDecl_43)
next
  case (44 v _ xk xl xm xn xo)
  then show ?thesis by simp
next
  case (45 v _ _ _ xk xl xm xn xo)
  then show ?thesis by simp
next
  case (46 v _ _ _ xk xl xm xn xo)
  then show ?thesis by simp
next
  case (47 v _ _ _ xk xl xm xn xo)
  then show ?thesis by simp
next
  case (48 v xj xk xl xm xn xo)
  then show ?thesis by simp
next
  case (49 xi xk xl xm xn xo)
  then show ?thesis by simp
next
  case (50 xi _ _ xk xl xm xn xo)
  then show ?thesis by simp
next
  case (51 xi _ _ xk xl xm xn xo)
  then show ?thesis by simp
next
  case (52 xi _ _ xk xl xm xn xo)
  then show ?thesis by simp
qed


end

end

end
